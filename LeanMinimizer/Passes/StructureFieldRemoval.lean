/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass
import LeanMinimizer.LakefileOptions

/-!
# Structure Field Removal Pass

This pass removes fields from structure/class definitions when ALL assignments
to that field in the file are `sorry`.

For each structure/class definition (not in stable sections):
1. Find each field in the structure definition
2. Find ALL field assignments with that field name anywhere in the file
3. Check if they're ALL `sorry`
4. If so, try removing:
   - The field line from the structure definition
   - All matching field assignment lines from where-structures
5. Test compilation
6. If fails, add key to failedChanges

This enables further minimization since simpler structures may not need
certain parent structures.
-/

namespace LeanMinimizer

open Lean Elab Frontend Parser

/-! ## Structure/class detection -/

/-- Check if syntax is a structure command -/
def isStructureOrClassCmd (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Command.declaration &&
  stx.getNumArgs >= 2 &&
  ((stx.getArg 1).isOfKind `Lean.Parser.Command.structure ||
   (stx.getArg 1).isOfKind `Lean.Parser.Command.classInductive)

/-- Get the structure/class syntax from a declaration command -/
def getStructureOrClassSyntax? (stx : Syntax) : Option Syntax := do
  if !isStructureOrClassCmd stx then failure
  return stx.getArg 1

/-- Get the structure/class name from structure/class syntax -/
def getStructureOrClassName? (stx : Syntax) : Option Name := do
  -- structure/class syntax: "structure"/"class" declId ...
  if stx.getNumArgs < 2 then failure
  let declId := stx.getArg 1
  -- declId has structure: ident optUnivDeclPart
  if declId.getNumArgs < 1 then failure
  let ident := declId.getArg 0
  if !ident.isIdent then failure
  return ident.getId

/-! ## Field extraction -/

/-- Information about a field definition in a structure -/
structure FieldLineInfo where
  /-- The field name -/
  name : String
  /-- Line number (1-indexed) of the field definition -/
  lineNum : Nat
  deriving Repr, Inhabited

/-- Extract field names and line numbers from a structure/class definition.
    Looks for lines that match the pattern of field definitions:
    - Start with an identifier (the field name)
    - Followed by `:` (type annotation)

    Uses a text-based approach for simplicity. -/
def extractStructureFieldLines (stx : Syntax) (source : String) : Array FieldLineInfo := Id.run do
  -- Get the source range of the structure
  let some startPos := stx.getPos?
    | return #[]
  let some endPos := stx.getTailPos?
    | return #[]

  let structSource := String.Pos.Raw.extract source startPos endPos
  let lines := structSource.splitOn "\n"

  let mut result : Array FieldLineInfo := #[]
  let mut inBody := false

  -- Find the line number where the structure starts in the overall source
  let beforeStruct := String.Pos.Raw.extract source ⟨0⟩ startPos
  let startLineNum := beforeStruct.splitOn "\n" |>.length

  let linesArr := lines.toArray
  for idx in [:linesArr.size] do
    let line := linesArr[idx]!
    let trimmed := line.trimAsciiStart.toString

    -- Look for "where" to know we're in the body
    -- "where" can be on the same line as "structure" or on its own line
    if trimmed.containsSubstr "where" then
      inBody := true
      -- If "where" is on its own line, skip it; otherwise continue to process
      -- further lines (the line with "where" won't contain field definitions)
      continue

    if !inBody then continue

    -- Skip empty lines and comments
    if trimmed.isEmpty then continue
    if trimmed.startsWith "--" then continue
    if trimmed.startsWith "/-" then continue

    -- Check if this looks like a field definition: starts with ident, then has `:`
    -- Pattern: fieldName : Type  or  fieldName : Type := default
    -- Split on first ':' to extract field name
    let parts := trimmed.splitOn ":"
    if parts.length >= 2 then
      let beforeColon := parts[0]!.trimAscii.toString
      -- beforeColon should be a simple identifier (no spaces, starts with letter/underscore)
      if !beforeColon.isEmpty && isValidFieldName beforeColon then
        result := result.push {
          name := beforeColon
          lineNum := startLineNum + idx
        }

  return result
where
  isValidFieldName (s : String) : Bool :=
    !s.isEmpty &&
    s.all (fun c => c.isAlphanum || c == '_') &&
    (s.front.isAlpha || s.front == '_')

/-! ## Field assignment detection -/

/-- Information about a field assignment line -/
structure FieldAssignmentInfo where
  /-- Line number (1-indexed) -/
  lineNum : Nat
  /-- Whether this is a sorry assignment -/
  isSorry : Bool
  deriving Repr, Inhabited

/-- Check if a line is a sorry-field assignment (like "foo := sorry") -/
def isSorryFieldAssignment (line : String) : Bool :=
  let trimmed := line.trimAscii.toString
  trimmed.endsWith ":= sorry" || trimmed.endsWith ":=sorry" || trimmed == "sorry"

/-- Check if a trimmed line is a field assignment for the given field name.
    Pattern: fieldName := ... -/
def isFieldAssignmentLine (trimmedLine : String) (fieldName : String) : Bool :=
  -- Must start with fieldName
  if !trimmedLine.startsWith fieldName then
    false
  else
    -- Check what follows the field name
    let rest := trimmedLine.drop fieldName.length
    let restTrimmed := rest.trimAsciiStart.toString
    -- Must have ":=" after field name (possibly with whitespace)
    restTrimmed.startsWith ":="

/-- Find all field assignments with the given name in the source.
    Returns line numbers (1-indexed) and whether each is a sorry assignment. -/
def findFieldAssignmentLines (fieldName : String) (source : String) : Array FieldAssignmentInfo := Id.run do
  let linesArr := source.splitOn "\n" |>.toArray
  let mut result : Array FieldAssignmentInfo := #[]

  for idx in [:linesArr.size] do
    let line := linesArr[idx]!
    let trimmed := line.trimAsciiStart.toString
    if isFieldAssignmentLine trimmed fieldName then
      result := result.push {
        lineNum := idx + 1  -- 1-indexed
        isSorry := isSorryFieldAssignment line
      }

  return result

/-- Check if all assignments are sorry -/
def allAssignmentsAreSorry (assignments : Array FieldAssignmentInfo) : Bool :=
  !assignments.isEmpty && assignments.all (·.isSorry)

/-! ## Source manipulation -/

/-- Delete lines at given line numbers (1-indexed) from source -/
def deleteLinesFromSource (source : String) (lineNumbers : Array Nat) : String := Id.run do
  let linesArr := source.splitOn "\n" |>.toArray
  let lineSet : Std.HashSet Nat := lineNumbers.foldl (·.insert ·) {}
  let mut result := #[]
  for idx in [:linesArr.size] do
    let line := linesArr[idx]!
    let lineNum := idx + 1  -- 1-indexed
    if !lineSet.contains lineNum then
      result := result.push line
  "\n".intercalate result.toList

/-! ## Compilation testing -/

/-- Run lean on source and return (exitCode, output). -/
def runLeanOnSourceForField (source : String) (fileName : String) : IO (UInt32 × String) := do
  let rand ← IO.rand 0 999999999
  let tempDir ← getTempDir
  let tempFile := tempDir / s!"lean-minimize-field-{← IO.monoNanosNow}-{rand}.lean"
  IO.FS.writeFile tempFile source

  let leanPath ← IO.getEnv "LEAN_PATH"
  let leanSysroot ← IO.getEnv "LEAN_SYSROOT"
  let path ← IO.getEnv "PATH"

  let env : Array (String × Option String) := #[
    ("LEAN_PATH", leanPath),
    ("LEAN_SYSROOT", leanSysroot),
    ("PATH", path)
  ]

  -- Get leanOptions from the project's lakefile
  let leanOptions ← getLeanOptionsForFile fileName

  let cwd := (System.FilePath.mk fileName).parent.getD (System.FilePath.mk ".")
  try
    let result ← IO.Process.output {
      cmd := "lean"
      args := leanOptions ++ #[tempFile.toString]
      env := env
      cwd := some cwd
    }
    return (result.exitCode, result.stdout)
  finally
    try IO.FS.removeFile tempFile catch _ => pure ()

/-- Test if source compiles -/
def testSourceCompilesForField (source : String) (fileName : String) : IO Bool := do
  let (exitCode, _) ← runLeanOnSourceForField source fileName
  return exitCode == 0

/-! ## The pass -/

/-- The structure field removal pass.

    For each structure/class before the marker (working upward from just before marker):
    For each field in its definition:
    1. Find all field assignments with that name anywhere in the file
    2. If all are sorry, try removing the field and all its assignments
    3. Test compilation

    Returns `.repeatThenRestart` on success to continue removing fields
    until exhausted, then restart from pass 0. -/
def structureFieldRemovalPass : Pass where
  name := "Structure Field Removal"
  cliFlag := "field-removal"
  needsSubprocess := true
  run := fun ctx => do
    if ctx.verbose then
      IO.eprintln s!"  Looking for structure/class fields to remove..."

    -- Compute stable indices to skip (if not in complete sweep mode)
    let stableIndices := if ctx.isCompleteSweep then
      {}
    else
      computeStableIndices ctx.subprocessCommands ctx.stableSections ctx.markerIdx ctx.topmostEndIdx

    let mut failedKeys : Array String := #[]

    -- Process structures from just before marker going upward
    for i in (List.range ctx.markerIdx).reverse do
      -- Skip indices in stable sections during unstable-only sweeps
      -- (We only skip the structure DEFINITION, not the assignments)
      if stableIndices.contains i then
        continue
      let some step := ctx.steps[i]?
        | continue

      -- Check if this is a structure or class
      let some structStx := getStructureOrClassSyntax? step.stx
        | continue
      let some structName := getStructureOrClassName? structStx
        | continue

      if ctx.verbose then
        IO.eprintln s!"    Found structure/class: {structName}"

      -- Extract fields from this structure
      let fields := extractStructureFieldLines structStx ctx.source
      if fields.isEmpty then
        continue

      if ctx.verbose then
        IO.eprintln s!"      Found {fields.size} fields: {fields.map (·.name)}"

      -- Try removing each field
      for field in fields do
        let removeKey := s!"field:{structName}/{field.name}/remove"

        -- Skip if already in memory
        if ctx.failedChanges.contains removeKey then
          if ctx.verbose then
            IO.eprintln s!"      Skipping field {field.name} (in memory)"
          continue

        -- Find ALL assignments to this field anywhere in the file
        let assignments := findFieldAssignmentLines field.name ctx.source

        if ctx.verbose then
          IO.eprintln s!"      Field {field.name}: found {assignments.size} assignments"

        -- Check if all assignments are sorry
        if !allAssignmentsAreSorry assignments then
          if ctx.verbose then
            IO.eprintln s!"        Not all sorry, skipping"
          continue

        if ctx.verbose then
          IO.eprintln s!"        All assignments are sorry, trying removal..."

        -- Collect all line numbers to delete
        let linesToDelete := #[field.lineNum] ++ assignments.map (·.lineNum)

        -- Remove the field definition and all assignments
        let newSource := deleteLinesFromSource ctx.source linesToDelete

        -- Test compilation
        if ← testSourceCompilesForField newSource ctx.fileName then
          if ctx.verbose then
            IO.eprintln s!"        Success! Removed field {field.name} and {assignments.size} assignments"
          return {
            source := newSource
            changed := true
            action := .repeatThenRestart
            newFailedChanges := failedKeys
          }
        else
          if ctx.verbose then
            IO.eprintln s!"        Compilation failed, remembering"
          failedKeys := failedKeys.push removeKey

    return {
      source := ctx.source
      changed := false
      action := .continue
      newFailedChanges := failedKeys
    }

end LeanMinimizer
