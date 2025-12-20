/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Extends Clause Simplification Pass

This pass simplifies `extends` clauses in structure definitions.

For each parent in an extends clause:
1. Try removing the parent entirely
2. If that fails, try replacing it with its parents (grandparents), deduplicating

This follows the same pattern as ImportMinimization: try to remove, then try to replace
with transitive dependencies.
-/

namespace LeanMinimizer

open Lean Elab Frontend Parser

/-! ## Structure syntax utilities -/

/-- Check if syntax is a structure command -/
def isStructureCmd (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Command.declaration &&
  stx.getNumArgs >= 2 &&
  (stx.getArg 1).isOfKind `Lean.Parser.Command.structure

/-- Get the structure syntax from a declaration command -/
def getStructureSyntax? (stx : Syntax) : Option Syntax := do
  if !isStructureCmd stx then failure
  return stx.getArg 1

/-- Get the structure name from structure syntax -/
def getStructureName? (structStx : Syntax) : Option Name := do
  -- structure syntax: "structure" declId ...
  if structStx.getNumArgs < 2 then failure
  let declId := structStx.getArg 1
  -- declId has structure: ident optUnivDeclPart
  if declId.getNumArgs < 1 then failure
  let ident := declId.getArg 0
  if !ident.isIdent then failure
  return ident.getId

/-- Information about a parent in an extends clause -/
structure ParentInfo where
  /-- The parent name as it appears in source -/
  name : Name
  /-- Start position in source -/
  startPos : String.Pos.Raw
  /-- End position in source -/
  endPos : String.Pos.Raw
  deriving Repr, Inhabited

/-- Find the extends clause syntax in a structure.
    Returns the extends clause syntax node if present.

    Structure syntax has extends clause wrapper at arg 3, containing the actual extends syntax. -/
def findExtendsClause? (structStx : Syntax) : Option Syntax := do
  -- Structure syntax: structureTk declId optDeclSig (extends)? (where fields)? optDeriving
  -- The extends clause is wrapped in arg 3
  if structStx.getNumArgs <= 3 then failure
  let extendsWrapper := structStx.getArg 3
  if extendsWrapper.isNone || extendsWrapper.getNumArgs == 0 then failure
  let extendsStx := extendsWrapper.getArg 0
  if extendsStx.isOfKind `Lean.Parser.Command.«extends» then
    return extendsStx
  failure

/-- Extract parent info from extends clause syntax.

    Extends syntax structure:
    - Arg 0: "extends" keyword
    - Arg 1: null wrapper containing structParent nodes (comma-separated)
    - Arg 2: null (trailing)

    Each structParent has:
    - Arg 0: null (modifiers?)
    - Arg 1: ident (the parent name) -/
def extractParentsFromExtends (extendsStx : Syntax) : Array ParentInfo := Id.run do
  let mut result := #[]
  -- Get the wrapper containing parents (arg 1)
  if extendsStx.getNumArgs < 2 then return #[]
  let parentsWrapper := extendsStx.getArg 1
  -- Iterate through structParent nodes
  for i in [:parentsWrapper.getNumArgs] do
    let item := parentsWrapper.getArg i
    -- Skip separators (commas)
    if item.isAtom then continue
    -- Check if it's a structParent
    if item.isOfKind `Lean.Parser.Command.structParent then
      -- structParent has: modifiers? ident
      -- The ident is typically at arg 1
      if item.getNumArgs >= 2 then
        let identArg := item.getArg 1
        if identArg.isIdent then
          if let some startPos := item.getPos? then
            if let some endPos := item.getTailPos? then
              result := result.push { name := identArg.getId, startPos, endPos }
  return result

/-- Get the source range of the entire extends clause (including "extends" keyword) -/
def getExtendsClauseRange? (extendsStx : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := do
  let startPos ← extendsStx.getPos?
  let endPos ← extendsStx.getTailPos?
  return (startPos, endPos)

/-! ## Environment queries -/

/-- Get the parent structure names for a structure from the environment -/
def getStructureParents (env : Environment) (structName : Name) : Array Name := Id.run do
  let some info := Lean.getStructureInfo? env structName
    | return #[]
  return info.parentInfo.map (·.structName)

/-! ## Source manipulation -/

/-- Render a list of parent names as an extends clause.
    Returns empty string if no parents. -/
def renderExtendsClause (parents : Array Name) : String :=
  if parents.isEmpty then
    ""
  else
    " extends " ++ ", ".intercalate (parents.map toString).toList

/-- Replace the extends clause in source with new parents.
    If parents is empty, removes the extends clause entirely. -/
def replaceExtendsClause (source : String) (extendsRange : String.Pos.Raw × String.Pos.Raw)
    (newParents : Array Name) : String :=
  let before := String.Pos.Raw.extract source ⟨0⟩ extendsRange.1
  let after := String.Pos.Raw.extract source extendsRange.2 source.rawEndPos
  before ++ renderExtendsClause newParents ++ after

/-- Run lean on source and return (exitCode, output).
    Note: Lean outputs errors to stdout, not stderr. -/
def runLeanOnSource (source : String) (fileName : String) : IO (UInt32 × String) := do
  let rand ← IO.rand 0 999999999
  let tempFile := System.FilePath.mk s!"/tmp/lean-minimize-extends-{← IO.monoNanosNow}-{rand}.lean"
  IO.FS.writeFile tempFile source

  let leanPath ← IO.getEnv "LEAN_PATH"
  let leanSysroot ← IO.getEnv "LEAN_SYSROOT"
  let path ← IO.getEnv "PATH"

  let env : Array (String × Option String) := #[
    ("LEAN_PATH", leanPath),
    ("LEAN_SYSROOT", leanSysroot),
    ("PATH", path)
  ]

  let cwd := (System.FilePath.mk fileName).parent.getD (System.FilePath.mk ".")
  let result ← IO.Process.output {
    cmd := "lean"
    args := #[tempFile.toString]
    env := env
    cwd := some cwd
  }

  IO.FS.removeFile tempFile
  -- Lean outputs errors to stdout, not stderr
  return (result.exitCode, result.stdout)

/-- Test if source compiles using subprocess for memory isolation -/
def testSourceCompilesForExtends (source : String) (fileName : String) : IO Bool := do
  let (exitCode, _) ← runLeanOnSource source fileName
  return exitCode == 0

/-- Extract error line numbers from lean stderr output.
    Error format: filename:line:col: error: ... -/
def extractErrorLineNumbers (stderr : String) : Array Nat := Id.run do
  let mut result := #[]
  for line in stderr.splitOn "\n" do
    -- Look for pattern like "filename:42:0: error:"
    if line.containsSubstr ": error:" then
      -- Parse line number - it's between first and second ':'
      let parts := line.splitOn ":"
      if parts.length >= 2 then
        if let some lineNum := parts[1]?.bind (·.trimAscii.toString.toNat?) then
          if !result.contains lineNum then
            result := result.push lineNum
  return result

/-- Check if a line is a sorry-field assignment (like "foo := sorry") -/
def isSorryFieldLine (line : String) : Bool :=
  let trimmed := line.trimAscii.toString
  trimmed.containsSubstr ":= sorry" || trimmed.containsSubstr ":=sorry"

/-- Delete lines at given line numbers (1-indexed) from source -/
def deleteLines (source : String) (lineNumbers : Array Nat) : String := Id.run do
  let lines := source.splitOn "\n"
  let mut result := #[]
  for i in [:lines.length] do
    let lineNum := i + 1  -- 1-indexed
    if !lineNumbers.contains lineNum then
      result := result.push lines[i]!
  "\n".intercalate result.toList

/-- Try to compile source, and if it fails on sorry-field lines only,
    try removing those lines. Returns (success, final_source). -/
def tryCompileWithSorryFieldRemoval (source : String) (fileName : String) (verbose : Bool) :
    IO (Bool × String) := do
  let (exitCode, output) ← runLeanOnSource source fileName
  if exitCode == 0 then
    return (true, source)

  -- Compilation failed - check if errors are on sorry-field lines
  let errorLines := extractErrorLineNumbers output
  if errorLines.isEmpty then
    return (false, source)

  -- Check if all error lines contain ":= sorry"
  let sourceLines := source.splitOn "\n"
  let mut allAreSorryFields := true
  for lineNum in errorLines do
    if lineNum > 0 && lineNum <= sourceLines.length then
      let line := sourceLines[lineNum - 1]!
      if !isSorryFieldLine line then
        allAreSorryFields := false
        break

  if !allAreSorryFields then
    return (false, source)

  if verbose then
    IO.eprintln s!"        Errors on {errorLines.size} sorry-field lines, trying to remove them..."

  -- All errors are on sorry-field lines - try removing them
  let newSource := deleteLines source errorLines
  let (newExitCode, _) ← runLeanOnSource newSource fileName
  if newExitCode == 0 then
    if verbose then
      IO.eprintln s!"        Successfully removed {errorLines.size} sorry-field lines"
    return (true, newSource)
  else
    return (false, source)

/-! ## The pass -/

/-- The extends clause simplification pass.

    For each structure before the marker (working upward from just before marker):
    For each parent in its extends clause:
    1. Try removing the parent entirely
    2. If that fails, try replacing with grandparents (the parent's own parents)

    Returns `.repeat` on success to allow further simplification. -/
def extendsSimplificationPass : Pass where
  name := "Extends Simplification"
  cliFlag := "extends"
  run := fun ctx => do
    if ctx.verbose then
      IO.eprintln s!"  Looking for structures with extends clauses..."

    -- Process structures from just before marker going upward
    for i in (List.range ctx.markerIdx).reverse do
      let some step := ctx.steps[i]?
        | continue

      -- Check if this is a structure with extends
      let some structStx := getStructureSyntax? step.stx
        | continue
      let some extendsStx := findExtendsClause? structStx
        | continue
      let some extendsRange := getExtendsClauseRange? extendsStx
        | continue

      let parents := extractParentsFromExtends extendsStx
      if parents.isEmpty then continue

      -- Get the environment after this command (so we can look up parent info)
      let env := step.after

      if ctx.verbose then
        IO.eprintln s!"    Found structure at index {i} with {parents.size} parents..."

      -- Try each parent for removal or replacement
      for parent in parents do
        if ctx.verbose then
          IO.eprintln s!"      Trying to remove parent {parent.name}..."

        -- Try 1: Remove this parent entirely
        let remainingParents := parents.filter (·.name != parent.name)
        let remainingNames := remainingParents.map (·.name)
        let newSource := replaceExtendsClause ctx.source extendsRange remainingNames

        -- Try compilation, with fallback to removing sorry-field lines if needed
        let (success, finalSource) ← tryCompileWithSorryFieldRemoval newSource ctx.fileName ctx.verbose
        if success then
          if ctx.verbose then
            IO.eprintln s!"        Removed parent {parent.name}"
          -- Restart to allow Deletion pass to remove newly-unused structures
          return { source := finalSource, changed := true, action := .restart }

        -- Try 2: Replace with grandparents
        let grandparents := getStructureParents env parent.name
        if !grandparents.isEmpty then
          if ctx.verbose then
            IO.eprintln s!"      Trying to replace {parent.name} with its {grandparents.size} parents..."

          -- Build new parent list: remove current, add grandparents (avoiding duplicates)
          let mut newParents := remainingNames
          for gp in grandparents do
            if !newParents.contains gp then
              newParents := newParents.push gp

          let newSource := replaceExtendsClause ctx.source extendsRange newParents

          -- Try compilation, with fallback to removing sorry-field lines if needed
          let (success, finalSource) ← tryCompileWithSorryFieldRemoval newSource ctx.fileName ctx.verbose
          if success then
            if ctx.verbose then
              IO.eprintln s!"        Replaced {parent.name} with its parents"
            -- Restart to allow Deletion pass to remove newly-unused structures
            return { source := finalSource, changed := true, action := .restart }

    -- No changes possible
    if ctx.verbose then
      IO.eprintln s!"  No extends simplifications possible"
    return { source := ctx.source, changed := false, action := .continue }

end LeanMinimizer
