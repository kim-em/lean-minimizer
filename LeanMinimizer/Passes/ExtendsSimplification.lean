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
  /-- The parent name (used for identification) -/
  name : Name
  /-- The full source text of this parent (e.g., "Module R L") -/
  sourceText : String
  /-- Start position in source -/
  startPos : String.Pos.Raw
  /-- End position in source -/
  endPos : String.Pos.Raw
  deriving Repr, Inhabited

/-- Recursively search for an extends clause in syntax tree -/
partial def findExtendsInSyntax (stx : Syntax) : Option Syntax :=
  if stx.isOfKind `Lean.Parser.Command.«extends» then
    some stx
  else
    -- Search through children
    let rec loop (i : Nat) : Option Syntax :=
      if i >= stx.getNumArgs then none
      else if let some result := findExtendsInSyntax (stx.getArg i) then result
      else loop (i + 1)
    loop 0

/-- Find the extends clause syntax in a structure.
    Returns the extends clause syntax node if present.

    The extends clause can be in different positions depending on whether the
    structure has type parameters:
    - Without params: `structure B extends A` has extends at arg 3
    - With params: `structure B (R : Type) extends A R` has extends inside arg 2
      (the ppIndent wrapper containing optDeclSig and optional extends) -/
def findExtendsClause? (structStx : Syntax) : Option Syntax :=
  findExtendsInSyntax structStx

/-- Find the first ident in a syntax tree -/
partial def findFirstIdent (stx : Syntax) : Option Name :=
  if stx.isIdent then
    some stx.getId
  else
    let rec loop (i : Nat) : Option Name :=
      if i >= stx.getNumArgs then none
      else if let some result := findFirstIdent (stx.getArg i) then result
      else loop (i + 1)
    loop 0

/-- Extract parent info from extends clause syntax.

    Extends syntax structure:
    - Arg 0: "extends" keyword
    - Arg 1: null wrapper containing structParent nodes (comma-separated)

    Each structParent contains the parent type, which may be:
    - A simple ident (e.g., `A`)
    - A type application (e.g., `A R` or `Module R L`) -/
def extractParentsFromExtends (extendsStx : Syntax) (source : String) : Array ParentInfo := Id.run do
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
      -- structParent contains the parent type expression
      -- Find the first ident in the type - that's the parent name
      if let some name := findFirstIdent item then
        if let some startPos := item.getPos? then
          if let some endPos := item.getTailPos? then
            -- Extract the source text for this parent
            let sourceText := String.Pos.Raw.extract source startPos endPos
            result := result.push { name, sourceText, startPos, endPos }
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

/-- Render a list of parents as an extends clause.
    Returns empty string if no parents.
    Uses the full sourceText from each parent to preserve type arguments. -/
def renderExtendsClause (parents : Array ParentInfo) : String :=
  if parents.isEmpty then
    ""
  else
    " extends " ++ ", ".intercalate (parents.map (·.sourceText)).toList

/-- Replace the extends clause in source with new parents.
    If parents is empty, removes the extends clause entirely. -/
def replaceExtendsClause (source : String) (extendsRange : String.Pos.Raw × String.Pos.Raw)
    (newParents : Array ParentInfo) : String :=
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

    Returns `.repeatThenRestart` on success to continue simplifying extends clauses
    until exhausted, then restart from pass 0 to allow other passes to run. -/
def extendsSimplificationPass : Pass where
  name := "Extends Simplification"
  cliFlag := "extends"
  needsSubprocess := true
  run := fun ctx => do
    if ctx.verbose then
      IO.eprintln s!"  Looking for structures with extends clauses..."

    -- Compute stable indices to skip (if not in complete sweep mode)
    let stableIndices := if ctx.isCompleteSweep then
      {}
    else
      computeStableIndices ctx.subprocessCommands ctx.stableSections

    let mut failedKeys : Array String := #[]

    -- Process structures from just before marker going upward
    for i in (List.range ctx.markerIdx).reverse do
      -- Skip indices in stable sections during unstable-only sweeps
      if stableIndices.contains i then
        continue
      let some step := ctx.steps[i]?
        | continue

      -- Check if this is a structure with extends
      let some structStx := getStructureSyntax? step.stx
        | continue
      let some structName := getStructureName? structStx
        | continue
      let some extendsStx := findExtendsClause? structStx
        | continue
      let some extendsRange := getExtendsClauseRange? extendsStx
        | continue

      let parents := extractParentsFromExtends extendsStx ctx.source
      if parents.isEmpty then continue

      -- Get the environment after this command (so we can look up parent info)
      let env := step.after

      if ctx.verbose then
        IO.eprintln s!"    Found structure {structName} at index {i} with {parents.size} parents..."

      -- Try each parent for removal or replacement
      for parent in parents do
        -- Try 1: Remove this parent entirely
        let removeKey := s!"extends:{structName}/{parent.name}/remove"

        -- Skip if already in memory
        if ctx.failedChanges.contains removeKey then
          if ctx.verbose then
            IO.eprintln s!"      Skipping remove {parent.name} (in memory)"
        else
          if ctx.verbose then
            IO.eprintln s!"      Trying to remove parent {parent.name}..."

          let remainingParents := parents.filter (·.name != parent.name)
          let newSource := replaceExtendsClause ctx.source extendsRange remainingParents

          -- Try compilation, with fallback to removing sorry-field lines if needed
          let (success, finalSource) ← tryCompileWithSorryFieldRemoval newSource ctx.fileName ctx.verbose
          if success then
            if ctx.verbose then
              IO.eprintln s!"        Removed parent {parent.name}"
            -- Repeat to simplify more extends, then restart for Deletion pass
            return { source := finalSource, changed := true, action := .repeatThenRestart,
                     newFailedChanges := failedKeys }
          else
            -- Record this as a failed change
            failedKeys := failedKeys.push removeKey

        -- Try 2: Replace with grandparents
        let replaceKey := s!"extends:{structName}/{parent.name}/replace"

        -- Skip if already in memory
        if ctx.failedChanges.contains replaceKey then
          if ctx.verbose then
            IO.eprintln s!"      Skipping replace {parent.name} (in memory)"
        else
          -- Note: grandparents are just names from the environment, so we create
          -- synthetic ParentInfo entries. This works for simple cases but may fail
          -- if the grandparents need type arguments.
          let grandparents := getStructureParents env parent.name
          if !grandparents.isEmpty then
            if ctx.verbose then
              IO.eprintln s!"      Trying to replace {parent.name} with its {grandparents.size} parents..."

            -- Build new parent list: remove current, add grandparents (avoiding duplicates)
            let remainingParents := parents.filter (·.name != parent.name)
            let remainingNames := remainingParents.map (·.name)
            let mut newParents := remainingParents
            for gp in grandparents do
              if !remainingNames.contains gp then
                -- Create synthetic ParentInfo with just the name (no type args)
                newParents := newParents.push { name := gp, sourceText := toString gp, startPos := 0, endPos := 0 }

            let newSource := replaceExtendsClause ctx.source extendsRange newParents

            -- Try compilation, with fallback to removing sorry-field lines if needed
            let (success, finalSource) ← tryCompileWithSorryFieldRemoval newSource ctx.fileName ctx.verbose
            if success then
              if ctx.verbose then
                IO.eprintln s!"        Replaced {parent.name} with its parents"
              -- Repeat to simplify more extends, then restart for Deletion pass
              return { source := finalSource, changed := true, action := .repeatThenRestart,
                       newFailedChanges := failedKeys }
            else
              -- Record this as a failed change
              failedKeys := failedKeys.push replaceKey

    -- No changes possible
    if ctx.verbose then
      IO.eprintln s!"  No extends simplifications possible"
    return { source := ctx.source, changed := false, action := .continue, newFailedChanges := failedKeys }

end LeanMinimizer
