/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass
import LeanMinimizer.Basic

/-!
# Empty Scope Removal Pass

This pass removes empty scope pairs: adjacent `section X ... end X` and `namespace X ... end X`.
It runs repeatedly to handle nested empty scopes.

This pass is necessary because the deletion pass cannot delete scope commands individually
(as that would change scoping semantics), so we need a separate pass to clean up empty scopes.
-/

namespace LeanMinimizer

open Lean

/-- Extract name after a keyword from reprinted syntax string.
    For synthetic nodes created by subprocess execution, the syntax structure
    may not have proper args, but the reprinted string contains the full text.
    E.g., for "namespace Foo", returns `Foo`. -/
def parseNameFromRepr (keyword : String) (repr : String) : Option Name := do
  -- Find the keyword in the reprinted string
  let repr := repr.trimAscii.toString
  if !repr.startsWith keyword then failure
  -- Get the rest after the keyword
  let rest := (repr.drop keyword.length).trimAscii.toString
  if rest.isEmpty then
    return Name.anonymous
  -- The name is the first word after the keyword
  let name := rest.takeWhile (fun c => !c.isWhitespace)
  if name.isEmpty then
    return Name.anonymous
  return name.toName

/-- Check if a command is a section command, returning the section name if so. -/
def getSectionName? (stx : Syntax) : Option Name :=
  if stx.isOfKind `Lean.Parser.Command.section then
    -- section has optional identifier
    let args := stx.getArgs
    if args.size > 1 && !args[1]!.isNone then
      some args[1]!.getId
    else
      -- Fallback: parse from reprinted string for synthetic nodes
      match stx.reprint with
      | some repr => parseNameFromRepr "section" repr
      | none => some Name.anonymous
  else
    none

/-- Check if a command is a namespace command, returning the namespace name if so. -/
def getNamespaceName? (stx : Syntax) : Option Name :=
  if stx.isOfKind `Lean.Parser.Command.namespace then
    let args := stx.getArgs
    if args.size > 1 then
      some args[1]!.getId
    else
      -- Fallback: parse from reprinted string for synthetic nodes
      match stx.reprint with
      | some repr => parseNameFromRepr "namespace" repr
      | none => none
  else
    none

/-- Check if a command is an end command, returning the end name if so (anonymous if no name). -/
def getEndName? (stx : Syntax) : Option Name :=
  if stx.isOfKind `Lean.Parser.Command.end then
    let args := stx.getArgs
    if args.size > 1 && !args[1]!.isNone then
      some args[1]!.getId
    else
      -- Fallback: parse from reprinted string for synthetic nodes
      match stx.reprint with
      | some repr => parseNameFromRepr "end" repr
      | none => some Name.anonymous
  else
    none

/-- Reconstruct source from compilation steps using their recorded positions.

    The header (from position 0 to headerEndPos) is always included.
    Only includes gaps between steps that are consecutive in the original ordering
    (i.e., steps where `idx` values differ by exactly 1). This ensures that when
    steps are removed, their content is properly excluded from the reconstruction. -/
def reconstructSourceFromSteps (source : String) (headerEndPos : String.Pos.Raw)
    (steps : Array CompilationStep) : String := Id.run do
  -- Always include the header
  let mut result := String.Pos.Raw.extract source ⟨0⟩ headerEndPos

  if steps.isEmpty then
    return result

  let mut lastEnd : String.Pos.Raw := headerEndPos
  let mut prevIdx : Option Nat := none

  for step in steps do
    let startPos := step.startPos
    -- Only add gap if steps are consecutive in original ordering
    -- (i.e., no removed steps between them)
    let shouldAddGap := match prevIdx with
      | none => step.idx == 0  -- First step: only if it was the original first command
      | some p => step.idx == p + 1  -- Otherwise: only if consecutive
    if shouldAddGap && startPos > lastEnd then
      result := result ++ String.Pos.Raw.extract source lastEnd startPos

    -- Add the command text
    result := result ++ String.Pos.Raw.extract source step.startPos step.endPos

    lastEnd := step.endPos
    prevIdx := some step.idx

  -- Add any trailing content after last command
  if lastEnd < source.rawEndPos then
    result := result ++ String.Pos.Raw.extract source lastEnd source.rawEndPos

  return result

/-- An empty scope pair: the indices and positions of the opening and closing commands. -/
structure EmptyScopePair where
  /-- Index of opening command (section/namespace) in the steps array -/
  openIdx : Nat
  /-- Index of closing command (end) in the steps array -/
  closeIdx : Nat
  /-- Start position of opening command (for memory key) -/
  startPos : String.Pos.Raw
  /-- End position of closing command -/
  endPos : String.Pos.Raw
  deriving Repr

/-- Generate a memory key for an empty scope pair based on its position. -/
def EmptyScopePair.memoryKey (pair : EmptyScopePair) : String :=
  s!"empty-scope:{pair.startPos}"

/-- Find all empty scope pairs in the steps array.
    Returns pairs in order of appearance. -/
def findAllEmptyScopePairs (steps : Array CompilationStep) : Array EmptyScopePair := Id.run do
  let mut pairs : Array EmptyScopePair := #[]
  if steps.size < 2 then
    return pairs

  for i in [:steps.size - 1] do
    if h1 : i < steps.size then
      if h2 : i + 1 < steps.size then
        let step1 := steps[i]
        let step2 := steps[i + 1]
        let stx1 := step1.stx
        let stx2 := step2.stx

        -- Check for section X ... end X
        if let some sectionName := getSectionName? stx1 then
          if let some endName := getEndName? stx2 then
            if sectionName == endName || (sectionName == Name.anonymous && endName == Name.anonymous) then
              pairs := pairs.push {
                openIdx := i
                closeIdx := i + 1
                startPos := step1.startPos
                endPos := step2.endPos
              }
              continue  -- Don't also check namespace

        -- Check for namespace X ... end X
        if let some nsName := getNamespaceName? stx1 then
          if let some endName := getEndName? stx2 then
            if nsName == endName then
              pairs := pairs.push {
                openIdx := i
                closeIdx := i + 1
                startPos := step1.startPos
                endPos := step2.endPos
              }

  return pairs

/-- Remove specified pairs from steps array. Pairs must be non-overlapping.
    Returns steps with the pairs removed. -/
def removeEmptyScopePairs (steps : Array CompilationStep) (pairs : Array EmptyScopePair) :
    Array CompilationStep := Id.run do
  if pairs.isEmpty then return steps

  -- Collect all indices to remove
  let mut indicesToRemove : Std.HashSet Nat := {}
  for pair in pairs do
    indicesToRemove := indicesToRemove.insert pair.openIdx
    indicesToRemove := indicesToRemove.insert pair.closeIdx

  -- Filter out the removed indices
  let mut result : Array CompilationStep := #[]
  for h : i in [:steps.size] do
    if !indicesToRemove.contains i then
      result := result.push steps[i]
  return result

/-- The empty scope removal pass.

    Removes adjacent empty scope pairs (section X ... end X or namespace X ... end X).
    Runs repeatedly to handle nested empty scopes.

    This is a cleanup pass that runs after deletion to remove scope commands that
    are now empty after their contents were deleted.

    Verifies compilation after removal because removing a namespace can break
    `open` commands that reference it. -/
unsafe def emptyScopeRemovalPass : Pass where
  name := "Empty Scope Removal"
  cliFlag := "empty-scope"
  run := fun ctx => do
    -- Only process steps before marker
    let stepsBeforeMarker := ctx.steps.filter (·.idx < ctx.markerIdx)
    let stepsFromMarker := ctx.steps.filter (·.idx ≥ ctx.markerIdx)

    -- Find all empty scope pairs
    let allPairs := findAllEmptyScopePairs stepsBeforeMarker

    -- Filter out pairs already known to fail
    let pairsToTry := allPairs.filter fun pair =>
      !ctx.failedChanges.contains pair.memoryKey

    if pairsToTry.isEmpty then
      return { source := ctx.source, changed := false, action := .continue }

    if ctx.verbose then
      IO.eprintln s!"  Found {pairsToTry.size} empty scope pairs to try"

    -- Try removing all pairs at once
    let stepsWithAllRemoved := removeEmptyScopePairs stepsBeforeMarker pairsToTry
    let allRemovedSource := reconstructSourceFromSteps ctx.source ctx.headerEndPos
        (stepsWithAllRemoved ++ stepsFromMarker)

    if ← testCompilesSubprocess allRemovedSource ctx.fileName then
      -- All removals succeeded
      if ctx.verbose then
        IO.eprintln s!"  Removed all {pairsToTry.size} pairs ({pairsToTry.size * 2} commands) at once"
      return { source := allRemovedSource, changed := true, action := .repeat }

    -- Batch removal failed - fall back to one-by-one
    if ctx.verbose then
      IO.eprintln s!"  Batch removal failed, trying one-by-one"

    let mut currentSteps := stepsBeforeMarker
    let mut anyChanged := false
    let mut newFailedChanges : Array String := #[]

    for pair in pairsToTry do
      -- Need to re-find the pair in current steps since indices shift after removals
      let currentPairs := findAllEmptyScopePairs currentSteps
      -- Find by position matching
      let matchingPair? := currentPairs.find? fun p => p.startPos == pair.startPos
      let some currentPair := matchingPair? | continue

      let stepsWithOneRemoved := removeEmptyScopePairs currentSteps #[currentPair]
      let testSource := reconstructSourceFromSteps ctx.source ctx.headerEndPos
          (stepsWithOneRemoved ++ stepsFromMarker)

      if ← testCompilesSubprocess testSource ctx.fileName then
        if ctx.verbose then
          IO.eprintln s!"    Removed pair at position {pair.startPos}"
        currentSteps := stepsWithOneRemoved
        anyChanged := true
      else
        if ctx.verbose then
          IO.eprintln s!"    Failed to remove pair at position {pair.startPos}"
        newFailedChanges := newFailedChanges.push pair.memoryKey

    if !anyChanged then
      return { source := ctx.source, changed := false, action := .continue,
               newFailedChanges := newFailedChanges }

    -- Reconstruct final source
    let newSource := reconstructSourceFromSteps ctx.source ctx.headerEndPos
        (currentSteps ++ stepsFromMarker)

    -- Use .repeat to run again in case there are now newly-adjacent empty scopes
    return { source := newSource, changed := true, action := .repeat,
             newFailedChanges := newFailedChanges }

end LeanMinimizer
