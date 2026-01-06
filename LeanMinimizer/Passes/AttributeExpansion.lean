/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass
import LeanMinimizer.Dependencies
import Lean.PrettyPrinter

/-!
# Attribute Expansion Pass

This pass expands "generative" attributes like `@[to_dual]`, `@[to_additive]`, `@[simps]`,
and `@[reassoc]` that create additional declarations.

The problem: These attributes generate new constants that aren't visible in source syntax,
making dependency analysis fail. Later code may reference the generated constants, but the
minimizer doesn't know they came from the attributed declaration.

The solution: Find the last command with a generative attribute, strip the attribute,
and pretty-print the generated declarations as explicit source code.

Example:
  Input:  `@[to_dual] instance bot : Bot (WithBot α) := ⟨none⟩`
  Output: `instance bot : Bot (WithBot α) := ⟨none⟩`
          `instance _root_.WithTop.top : Top (WithTop α) := ⟨none⟩`
-/

namespace LeanMinimizer

open Lean Meta PrettyPrinter Elab

/-- Generative attributes that create additional declarations -/
def generativeAttrs : List String := ["to_dual", "to_additive", "simps", "reassoc"]

/-! ## Attribute detection and stripping -/

/-- Check if a string contains any of the generative attributes.
    Looks for patterns like `@[to_dual` or `@[..., to_dual` -/
def hasGenerativeAttr (s : String) : Bool :=
  generativeAttrs.any fun attr =>
    s.containsSubstr s!"@[{attr}" ||
    s.containsSubstr s!", {attr}" ||
    s.containsSubstr s!",{attr}"

/-- Find the position range of the @[...] block in a command string.
    Returns (startPos, endPos) as byte positions. -/
def findAttrBlockRange (s : String) : Option (Nat × Nat) := Id.run do
  let endPos := s.rawEndPos.byteIdx
  -- Find @ character
  let mut i := 0
  while i < endPos do
    if String.Pos.Raw.get s ⟨i⟩ == '@' then
      -- Check for @[
      if i + 1 < endPos && String.Pos.Raw.get s ⟨i + 1⟩ == '[' then
        let startPos := i
        -- Find matching ]
        let mut depth := 1
        let mut pos := i + 2
        while pos < endPos && depth > 0 do
          let c := String.Pos.Raw.get s ⟨pos⟩
          if c == '[' then depth := depth + 1
          else if c == ']' then depth := depth - 1
          pos := pos + 1
        if depth == 0 then
          return some (startPos, pos)
    i := i + 1
  return none

/-- Find the byte position of a substring in a string, or none if not found. -/
def findSubstrPos (s : String) (pattern : String) : Option Nat := Id.run do
  let sLen := s.utf8ByteSize
  let pLen := pattern.utf8ByteSize
  if pLen > sLen then return none
  for i in [:sLen - pLen + 1] do
    let substr := String.Pos.Raw.extract s ⟨i⟩ ⟨i + pLen⟩
    if substr == pattern then return some i
  return none

/-- Extract the `(attr := ...)` attributes from a generative attribute string.
    For example, `to_dual (attr := simp) foo` returns `some "simp"`.
    Returns `none` if no `(attr := ...)` is present. -/
def extractAttrFromGenerativeAttr (attrStr : String) : Option String := Id.run do
  -- Look for "(attr := " pattern
  let pattern := "(attr := "
  let some startIdx := findSubstrPos attrStr pattern
    | return none

  -- Find the matching closing paren
  let contentStart := startIdx + pattern.length
  let mut depth := 1
  let mut pos := contentStart
  let bytes := attrStr.utf8ByteSize

  while pos < bytes && depth > 0 do
    let c := String.Pos.Raw.get attrStr ⟨pos⟩
    if c == '(' then depth := depth + 1
    else if c == ')' then depth := depth - 1
    pos := pos + 1

  if depth != 0 then return none

  -- Extract content between "(attr := " and ")"
  let content := String.Pos.Raw.extract attrStr ⟨contentStart⟩ ⟨pos - 1⟩
  let trimmed := content.trimAscii.toString
  if trimmed.isEmpty then none else some trimmed

/-- Strip generative attributes from an attribute block, keeping others.
    Returns the new attribute block (or empty string if all removed).
    Preserves (attr := X) from generative attributes by keeping X. -/
def stripGenerativeAttrsFromBlock (attrBlock : String) : String := Id.run do
  -- attrBlock is like "@[to_dual, simp]" or "@[to_dual /-- doc -/]"
  -- We need to parse and filter the attributes

  -- Remove @[ prefix and ] suffix
  let blockLen := attrBlock.utf8ByteSize
  if blockLen < 3 then return ""

  -- Extract inner content between @[ and ]
  let inner := String.Pos.Raw.extract attrBlock ⟨2⟩ ⟨blockLen - 1⟩

  -- Split by comma (being careful about nested brackets and strings)
  let mut attrs : Array String := #[]
  let mut current := ""
  let mut depth := 0
  let mut inString := false

  for c in inner.toList do
    if c == '"' && depth == 0 then inString := !inString
    if !inString then
      if c == '[' || c == '(' || c == '{' then depth := depth + 1
      else if c == ']' || c == ')' || c == '}' then depth := depth - 1

    if c == ',' && depth == 0 && !inString then
      let trimmed := current.trimAscii.toString
      if !trimmed.isEmpty then
        attrs := attrs.push trimmed
      current := ""
    else
      current := current.push c

  let trimmed := current.trimAscii.toString
  if !trimmed.isEmpty then
    attrs := attrs.push trimmed

  -- Filter and transform generative attributes
  -- For generative attrs with (attr := X), we keep X but remove the generative attr
  let mut filtered : Array String := #[]
  for attr in attrs do
    if generativeAttrs.any fun ga => attr.startsWith ga then
      -- This is a generative attribute - extract any (attr := ...) to keep
      if let some extracted := extractAttrFromGenerativeAttr attr then
        filtered := filtered.push extracted
      -- Otherwise drop the whole generative attribute
    else
      -- Keep non-generative attributes
      filtered := filtered.push attr

  if filtered.isEmpty then
    ""
  else
    "@[" ++ ", ".intercalate filtered.toList ++ "]"

/-- Extract the `(attr := ...)` attributes from an attribute block for generative attrs.
    Searches the block for any generative attribute and extracts its (attr := ...) if present. -/
def extractAttrsFromBlock (attrBlock : String) : Option String := Id.run do
  -- Remove @[ prefix and ] suffix
  let blockLen := attrBlock.utf8ByteSize
  if blockLen < 3 then return none

  let inner := String.Pos.Raw.extract attrBlock ⟨2⟩ ⟨blockLen - 1⟩

  -- Split by comma (being careful about nested brackets)
  let mut attrs : Array String := #[]
  let mut current := ""
  let mut depth := 0
  let mut inString := false

  for c in inner.toList do
    if c == '"' && depth == 0 then inString := !inString
    if !inString then
      if c == '[' || c == '(' || c == '{' then depth := depth + 1
      else if c == ']' || c == ')' || c == '}' then depth := depth - 1

    if c == ',' && depth == 0 && !inString then
      let trimmed := current.trimAscii.toString
      if !trimmed.isEmpty then
        attrs := attrs.push trimmed
      current := ""
    else
      current := current.push c

  let trimmed := current.trimAscii.toString
  if !trimmed.isEmpty then
    attrs := attrs.push trimmed

  -- Find generative attributes and extract their (attr := ...)
  for attr in attrs do
    if generativeAttrs.any fun ga => attr.startsWith ga then
      if let some extracted := extractAttrFromGenerativeAttr attr then
        return some extracted

  return none

/-- Skip leading whitespace in a string -/
def skipLeadingWhitespace (s : String) : String := Id.run do
  let bytes := s.utf8ByteSize
  let mut skipTo := 0
  while skipTo < bytes do
    let c := String.Pos.Raw.get s ⟨skipTo⟩
    if c == ' ' || c == '\t' then
      skipTo := skipTo + 1
    else
      break
  return String.Pos.Raw.extract s ⟨skipTo⟩ ⟨bytes⟩

/-- Strip generative attributes from command text.
    Returns the command with generative attributes removed. -/
def stripGenerativeAttrs (cmdText : String) : String :=
  match findAttrBlockRange cmdText with
  | none => cmdText
  | some (startPos, endPos) =>
    let attrBlock := String.Pos.Raw.extract cmdText ⟨startPos⟩ ⟨endPos⟩
    let newAttrBlock := stripGenerativeAttrsFromBlock attrBlock

    let before := String.Pos.Raw.extract cmdText ⟨0⟩ ⟨startPos⟩
    let after := String.Pos.Raw.extract cmdText ⟨endPos⟩ ⟨cmdText.utf8ByteSize⟩

    -- Handle whitespace after attribute block
    let after := if newAttrBlock.isEmpty then
      skipLeadingWhitespace after
    else
      after

    before ++ newAttrBlock ++ (if newAttrBlock.isEmpty then "" else " ") ++ after

/-! ## Constant filtering -/

/-- Check if a constant name is user-facing (not internal/auxiliary) -/
def isUserFacing (name : Name) : Bool :=
  !name.isInternalDetail

/-- Check if a constant is an auto-generated structure/class method -/
def isAutoGenerated (name : Name) : Bool :=
  let lastName := match name with
    | .str _ s => s
    | _ => ""
  -- Auto-generated methods for structures/classes
  lastName ∈ ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType",
              "mk", "ctorIdx", "ext", "ext_iff", "brecOn", "below", "ibelow",
              "binductionOn", "ndrec", "ndrecOn", "toCtorIdx"] ||
  lastName.endsWith ".noConfusion"

/-- Get the last component of a name as a string -/
def lastNameComponent (n : Name) : String := match n with
  | .str _ s => s
  | .num _ num => toString num
  | .anonymous => ""

/-! ## Pretty-printing declarations -/

/-- Determine the declaration kind for a constant.
    Preserves the actual declaration kind (theorem vs def) from the source. -/
def getDeclKind (env : Environment) (info : ConstantInfo) : String :=
  -- Check if it's an instance (has @[instance] attribute)
  if instanceExtension.getState env |>.instanceNames.contains info.name then "instance"
  else match info with
  -- Preserve actual declaration kind
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  -- For other kinds (inductive, ctor, rec, quot), fall back to def
  | _ => "def"

/-- Pretty-print a constant as a declaration string.
    Uses _root_.FullName to avoid namespace issues.
    If `attrs` is provided, prepends `@[attrs]` to the declaration. -/
def ppConstantDecl (env : Environment) (name : Name) (attrs : Option String := none)
    : MetaM (Option String) := do
  let some info := env.find? name
    | return none

  let kind := getDeclKind env info

  -- Pretty-print the type
  let typeStr ← withOptions (fun o => o
    |>.setBool `pp.fullNames true
    |>.setBool `pp.universes false) do
    let fmt ← Meta.ppExpr info.type
    return fmt.pretty

  -- Pretty-print the value if available
  let valueStr ← match info.value? with
    | some value => withOptions (fun o => o
        |>.setBool `pp.fullNames true
        |>.setBool `pp.universes false) do
        let fmt ← Meta.ppExpr value
        return fmt.pretty
    | none => pure "sorry"

  let attrPrefix := match attrs with
    | some a => s!"@[{a}] "
    | none => ""

  return some s!"{attrPrefix}{kind} _root_.{name} : {typeStr} := {valueStr}"

/-! ## The pass -/

/-- Find the last command index that has a generative attribute -/
def findLastGenerativeAttrCmd (steps : Array CompilationStep) (markerIdx : Nat) : Option Nat := do
  -- Search from marker-1 down to 0
  for i in (List.range markerIdx).reverse do
    let some step := steps[i]?
      | continue
    let cmdText := step.stx.reprint.getD ""
    if hasGenerativeAttr cmdText then
      return i
  failure

/-- Get the name of the declaration in a command syntax -/
def getDeclName? (stx : Syntax) : Option Name := do
  -- Try to find a declId in the syntax
  let inner := getInnerDecl? stx
  let inner ← inner
  -- declId is usually at arg 1 for most declarations
  for i in [:inner.getNumArgs] do
    let child := inner[i]!
    if child.isOfKind `Lean.Parser.Command.declId then
      if child.getNumArgs > 0 then
        let nameNode := child[0]!
        if nameNode.isIdent then
          return nameNode.getId
  -- For instances: look for namedName (the optional instance name)
  -- Instance syntax: `instance` optNamedName optDeclSig declVal
  if inner.isOfKind `Lean.Parser.Command.instance then
    -- The optional name is at args[1] (after `instance` keyword)
    if inner.getNumArgs > 1 then
      let optName := inner[1]!
      -- optNamedName has structure: (ident (":" priority)?)?
      if !optName.isNone && optName.getNumArgs > 0 then
        let nameNode := optName[0]!
        if nameNode.isIdent then
          return nameNode.getId
  failure

/-- Run a MetaM computation in IO with a given environment -/
def runMetaM (env : Environment) (fileName : String) (x : MetaM α) : IO α := do
  let mctx : Meta.Context := {}
  let mstate : Meta.State := {}
  let cctx : Core.Context := { fileName := fileName, fileMap := default }
  let cstate : Core.State := { env := env }
  match ← (x.run mctx mstate |>.run cctx cstate).toIO' with
  | .ok ((result, _), _) => return result
  | .error e => throw <| IO.userError s!"MetaM error: {← e.toMessageData.toString}"

/-- The attribute expansion pass.

    Finds the last command with a generative attribute (before the marker),
    strips the attribute, and adds explicit declarations for generated constants.
    Repeats until no more generative attributes, then restarts if any changes made. -/
def attributeExpansionPass : Pass where
  name := "Attribute Expansion"
  cliFlag := "attr-expansion"
  needsSubprocess := true
  run := fun ctx => do
    if ctx.verbose then
      IO.eprintln s!"  Looking for generative attributes..."

    -- Find the last command with a generative attribute
    let some cmdIdx := findLastGenerativeAttrCmd ctx.steps ctx.markerIdx
      | do
        if ctx.verbose then
          IO.eprintln s!"  No generative attributes found"
        return { source := ctx.source, changed := false, action := .continue }

    if h : cmdIdx < ctx.steps.size then
      let step := ctx.steps[cmdIdx]
      let cmdText := step.stx.reprint.getD ""

      if ctx.verbose then
        IO.eprintln s!"  Found generative attribute at command {cmdIdx}"

      -- Get all constants added by this command
      let newConstants := getNewConstants step

      -- Get the source constant name (the one explicitly declared)
      -- First try to parse from syntax
      let syntaxName := getDeclName? step.stx
      let newConstantsArr := newConstants.toArray

      -- Only consider user-facing constants (exclude auto-generated structure methods)
      let userFacingConstants := newConstantsArr.filter fun n =>
        isUserFacing n && !isAutoGenerated n

      -- Also try to find the source from new constants by matching against syntax name
      -- This handles cases where syntaxName is `bot` but the constant is `WithBot.bot`
      let sourceConstName : Option Name :=
        if let some name := syntaxName then
          -- Look for a constant whose last component matches
          let nameStr := lastNameComponent name
          userFacingConstants.find? (fun c => lastNameComponent c == nameStr) |>.orElse fun _ => some name
        else
          -- Fall back to looking for a constant whose namespace appears in the code
          -- For `to_dual`: if we have both WithBot.bot and WithTop.top, the source
          -- is the one that matches the namespace in the code (e.g., "WithBot" appears in command)
          let cmdTextLower := cmdText.toLower
          userFacingConstants.find? (fun c =>
            -- Check if any part of the constant's namespace appears in the command
            let parts := c.toString.splitOn "."
            parts.any fun part => cmdTextLower.containsSubstr part.toLower)

      -- If we couldn't identify the source constant, this is fatal
      if sourceConstName.isNone then
        IO.eprintln ""
        IO.eprintln "FATAL: Could not identify source constant from syntax."
        IO.eprintln s!"  Command: {cmdText}"
        IO.eprintln s!"  New constants: {newConstantsArr.map (·.toString)}"
        IO.eprintln "Please file a bug report."
        return { source := ctx.source, changed := false, action := .fatal }

      -- Filter to user-facing constants, excluding the source constant
      let generatedConstants := userFacingConstants.filter fun name =>
        sourceConstName != some name

      if ctx.verbose then
        IO.eprintln s!"    Source constant: {sourceConstName}"
        IO.eprintln s!"    Generated constants: {generatedConstants.map (·.toString)}"

      -- Strip the generative attribute from the original command
      let strippedCmd := stripGenerativeAttrs cmdText

      -- Extract any (attr := ...) from the generative attribute to add to generated decls
      let generatedAttrs := match findAttrBlockRange cmdText with
        | some (startPos, endPos) =>
          let attrBlock := String.Pos.Raw.extract cmdText ⟨startPos⟩ ⟨endPos⟩
          extractAttrsFromBlock attrBlock
        | none => none

      -- Pretty-print the generated constants
      let mut generatedDecls : Array String := #[]
      for name in generatedConstants do
        let declStr? ← runMetaM step.after ctx.fileName (ppConstantDecl step.after name generatedAttrs)
        if let some declStr := declStr? then
          generatedDecls := generatedDecls.push declStr

      -- Build the new source
      let cmdStartPos := step.startPos
      let cmdEndPos := step.endPos

      let before := String.Pos.Raw.extract ctx.source ⟨0⟩ cmdStartPos
      let after := String.Pos.Raw.extract ctx.source cmdEndPos ⟨ctx.source.utf8ByteSize⟩

      let newCmdSection := strippedCmd ++ "\n" ++
        (generatedDecls.map (· ++ "\n")).foldl (· ++ ·) ""

      let newSource := before ++ newCmdSection ++ after

      -- Verify it compiles
      let (success, errorOutput) ← testCompilesSubprocessWithError newSource ctx.fileName
      if success then
        if ctx.verbose then
          IO.eprintln s!"    Success: expanded attribute, added {generatedDecls.size} declarations"
        -- Repeat to expand more attributes, then restart to let deletion pass clean up
        return { source := newSource, changed := true, action := .repeatThenRestart }
      else
        -- Write the failed source to a debug file
        let debugFile := ctx.fileName ++ ".attr-expansion-debug.lean"
        IO.FS.writeFile debugFile newSource
        IO.eprintln s!"    FAILED to expand attribute (doesn't compile)"
        IO.eprintln s!"    Debug: wrote attempted source to {debugFile}"
        IO.eprintln s!"    Original command:"
        IO.eprintln s!"      {cmdText}"
        IO.eprintln s!"    Stripped command:"
        IO.eprintln s!"      {strippedCmd}"
        IO.eprintln s!"    Generated declarations:"
        for decl in generatedDecls do
          IO.eprintln s!"      {decl}"
        IO.eprintln s!"    Compilation error:"
        for line in errorOutput.splitOn "\n" do
          if !line.isEmpty then
            IO.eprintln s!"      {line}"

        -- Try without the generated declarations (just strip the attribute)
        let simpleSource := before ++ strippedCmd ++ "\n" ++ after
        let (simpleSuccess, simpleError) ← testCompilesSubprocessWithError simpleSource ctx.fileName
        if simpleSuccess then
          IO.eprintln s!"    Partial success: stripped attribute only (generated decls had errors)"
          return { source := simpleSource, changed := true, action := .restart }
        else
          IO.eprintln s!"    Also failed when just stripping attribute (without generating decls):"
          for line in simpleError.splitOn "\n" do
            if !line.isEmpty then
              IO.eprintln s!"      {line}"
          IO.eprintln ""
          IO.eprintln "FATAL: Could not expand generative attribute."
          IO.eprintln "The minimizer cannot continue because dependency analysis will be incorrect."
          IO.eprintln "Please investigate the generated declarations above and fix the issue."
          return { source := ctx.source, changed := false, action := .fatal }
    else
      return { source := ctx.source, changed := false, action := .continue }

end LeanMinimizer
