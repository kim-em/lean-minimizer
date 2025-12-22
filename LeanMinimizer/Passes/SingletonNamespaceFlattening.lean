/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass
import LeanMinimizer.Passes.EmptyScopeRemoval
import LeanMinimizer.Passes.Deletion

/-!
# Singleton Namespace Flattening Pass

This pass flattens namespaces that contain exactly one declaration.

```lean
namespace Foo
def bar := 42
end Foo
```

becomes:

```lean
def Foo.bar := 42
```

This is a cleanup pass that runs after empty scope removal and deletion.
-/

namespace LeanMinimizer

open Lean

/-- Declaration keywords that can be flattened. -/
def declKeywords : List String := ["def", "theorem", "lemma", "abbrev", "instance", "structure", "inductive", "class"]

/-- Check if a command is a flattenable declaration (not a scoping command like variable/open/section/namespace). -/
def isFlattenableDeclaration (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Command.declaration ||
  stx.isOfKind `Lean.Parser.Command.instance

/-- Find the declaration keyword position in the command text.
    Returns (keyword, position after keyword) if found. -/
def findDeclKeyword (text : String) : Option (String × Nat) := do
  -- Skip any leading attributes @[...], docstrings /-- ... -/, and modifiers
  let mut pos := 0
  let len := text.utf8ByteSize

  while pos < len do
    -- Skip whitespace
    while pos < len && (String.Pos.Raw.get text ⟨pos⟩).isWhitespace do
      pos := pos + 1

    if pos >= len then failure

    let c := String.Pos.Raw.get text ⟨pos⟩

    -- Skip @[...] attribute blocks
    if c == '@' && pos + 1 < len && String.Pos.Raw.get text ⟨pos + 1⟩ == '[' then
      pos := pos + 2
      let mut depth := 1
      while pos < len && depth > 0 do
        let ch := String.Pos.Raw.get text ⟨pos⟩
        if ch == '[' then depth := depth + 1
        else if ch == ']' then depth := depth - 1
        pos := pos + 1
      continue

    -- Skip /-- ... -/ docstrings
    if c == '/' && pos + 2 < len &&
       String.Pos.Raw.get text ⟨pos + 1⟩ == '-' &&
       String.Pos.Raw.get text ⟨pos + 2⟩ == '-' then
      pos := pos + 3
      while pos + 1 < len do
        if String.Pos.Raw.get text ⟨pos⟩ == '-' &&
           String.Pos.Raw.get text ⟨pos + 1⟩ == '/' then
          pos := pos + 2
          break
        pos := pos + 1
      continue

    -- Try to match a declaration keyword
    for keyword in declKeywords do
      let keyLen := keyword.utf8ByteSize
      if pos + keyLen <= len then
        let candidate := String.Pos.Raw.extract text ⟨pos⟩ ⟨pos + keyLen⟩
        if candidate == keyword then
          -- Check that it's followed by whitespace (not a prefix of another word)
          if pos + keyLen >= len ||
             (String.Pos.Raw.get text ⟨pos + keyLen⟩).isWhitespace then
            return (keyword, pos + keyLen)

    -- Check for modifiers like "protected", "private", "partial", "noncomputable", "unsafe"
    let modifiers := ["protected", "private", "partial", "noncomputable", "unsafe", "scoped", "local"]
    let mut foundModifier := false
    for modifier in modifiers do
      let modLen := modifier.utf8ByteSize
      if pos + modLen <= len then
        let candidate := String.Pos.Raw.extract text ⟨pos⟩ ⟨pos + modLen⟩
        if candidate == modifier then
          if pos + modLen >= len ||
             (String.Pos.Raw.get text ⟨pos + modLen⟩).isWhitespace then
            pos := pos + modLen
            foundModifier := true
            break
    if foundModifier then continue

    -- Not a recognized prefix, give up
    break

  failure

/-- Find the declaration name position in the command text.
    Returns (nameStart, nameEnd) as byte positions if found.
    The name is the identifier after the declaration keyword. -/
def findDeclNameRange (text : String) : Option (Nat × Nat) := do
  let (_, afterKeyword) ← findDeclKeyword text
  let len := text.utf8ByteSize

  -- Skip whitespace after keyword
  let mut pos := afterKeyword
  while pos < len && (String.Pos.Raw.get text ⟨pos⟩).isWhitespace do
    pos := pos + 1

  if pos >= len then failure

  let nameStart := pos

  -- Read the identifier (may include dots for qualified names, may include unicode)
  -- Identifier chars: alphanumeric, underscore, apostrophe, and dots for qualified names
  while pos < len do
    let c := String.Pos.Raw.get text ⟨pos⟩
    if c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '«' || c == '»' then
      pos := pos + 1
    else
      break

  if pos == nameStart then failure

  return (nameStart, pos)

/-- Insert the namespace prefix before the declaration name in the command text.
    Returns the modified text. -/
def insertNamespacePrefix (text : String) (nsName : Name) : Option String := do
  let (nameStart, _) ← findDeclNameRange text
  let nsPrefix := nsName.toString ++ "."
  let before := String.Pos.Raw.extract text ⟨0⟩ ⟨nameStart⟩
  let after := String.Pos.Raw.extract text ⟨nameStart⟩ text.rawEndPos
  return before ++ nsPrefix ++ after

/-- Find a singleton namespace pattern: namespace X, one declaration, end X.
    Returns (namespaceIdx, declIdx, endIdx, namespaceName) if found. -/
def findSingletonNamespace (steps : Array CompilationStep) :
    Option (Nat × Nat × Nat × Name) := Id.run do
  if steps.size < 3 then
    return none

  for i in [:steps.size - 2] do
    if h1 : i < steps.size then
      if h2 : i + 1 < steps.size then
        if h3 : i + 2 < steps.size then
          let stx1 := steps[i].stx
          let stx2 := steps[i + 1].stx
          let stx3 := steps[i + 2].stx

          -- Check for namespace X
          if let some nsName := getNamespaceName? stx1 then
            -- Check that middle command is a flattenable declaration
            if isFlattenableDeclaration stx2 && !isScopeCommand stx2 then
              -- Check for matching end X
              if let some endName := getEndName? stx3 then
                if nsName == endName then
                  return some (i, i + 1, i + 2, nsName)

  return none

/-- Flatten a singleton namespace by modifying the declaration name.
    Returns the new source string. -/
def flattenSingletonNamespace (source : String) (headerEndPos : String.Pos.Raw)
    (steps : Array CompilationStep) (nsIdx declIdx endIdx : Nat) (nsName : Name) : Option String := do
  -- Get the declaration command
  let declStep ← steps[declIdx]?

  -- Get the declaration text
  let declText := String.Pos.Raw.extract source declStep.startPos declStep.endPos

  -- Insert namespace prefix into the declaration name
  let modifiedDecl ← insertNamespacePrefix declText nsName

  -- Build the new steps array: remove namespace and end, keep modified declaration
  let mut newSteps : Array CompilationStep := #[]
  for h : j in [:steps.size] do
    if j == nsIdx || j == endIdx then
      continue
    else
      newSteps := newSteps.push steps[j]

  -- Reconstruct source, but with the modified declaration text
  -- We need custom reconstruction since we're changing the declaration text
  let mut result := String.Pos.Raw.extract source ⟨0⟩ headerEndPos

  if newSteps.isEmpty then
    return result

  let mut lastEnd : String.Pos.Raw := headerEndPos
  let mut prevIdx : Option Nat := none

  for step in newSteps do
    let startPos := step.startPos
    -- Only add gap if steps are consecutive in original ordering
    let shouldAddGap := match prevIdx with
      | none => step.idx == 0
      | some p => step.idx == p + 1 || step.idx == nsIdx + 1  -- Special case: decl follows namespace
    if shouldAddGap && startPos > lastEnd then
      result := result ++ String.Pos.Raw.extract source lastEnd startPos

    -- Add the command text (modified for declaration, original for others)
    if step.idx == declIdx then
      result := result ++ modifiedDecl
    else
      result := result ++ String.Pos.Raw.extract source step.startPos step.endPos

    lastEnd := step.endPos
    prevIdx := some step.idx

  -- Add any trailing content after last command
  if lastEnd < source.rawEndPos then
    result := result ++ String.Pos.Raw.extract source lastEnd source.rawEndPos

  return result

/-- The singleton namespace flattening pass.

    Flattens namespaces that contain exactly one declaration by adding the
    namespace prefix to the declaration name and removing the wrapper.

    This is a cleanup pass that runs after deletion and empty scope removal. -/
unsafe def singletonNamespaceFlatteningPass : Pass where
  name := "Singleton Namespace Flattening"
  cliFlag := "singleton-ns"
  run := fun ctx => do
    -- Only process steps before marker
    let stepsBeforeMarker := ctx.steps.filter (·.idx < ctx.markerIdx)
    let stepsFromMarker := ctx.steps.filter (·.idx ≥ ctx.markerIdx)

    match findSingletonNamespace stepsBeforeMarker with
    | none =>
      return { source := ctx.source, changed := false, action := .continue }
    | some (nsIdx, declIdx, endIdx, nsName) =>
      -- Build full steps array for flattening
      let allSteps := stepsBeforeMarker ++ stepsFromMarker

      match flattenSingletonNamespace ctx.source ctx.headerEndPos allSteps nsIdx declIdx endIdx nsName with
      | none =>
        -- Failed to flatten, skip this one
        if ctx.verbose then
          IO.eprintln s!"  Failed to flatten singleton namespace {nsName}"
        return { source := ctx.source, changed := false, action := .continue }
      | some newSource =>
        -- Test if the new source compiles
        if ← testCompilesSubprocess newSource ctx.fileName then
          if ctx.verbose then
            IO.eprintln s!"  Flattened singleton namespace {nsName}"
          -- Use .repeat to run again for other singleton namespaces
          return { source := newSource, changed := true, action := .repeat }
        else
          -- Doesn't compile, skip this namespace
          if ctx.verbose then
            IO.eprintln s!"  Skipping singleton namespace {nsName} (doesn't compile after flattening)"
          return { source := ctx.source, changed := false, action := .continue }

end LeanMinimizer
