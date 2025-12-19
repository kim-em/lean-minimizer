/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Empty Scope Removal Pass

This pass removes empty scope pairs: adjacent `section X ... end X` and `namespace X ... end X`.
It runs repeatedly to handle nested empty scopes.

This pass is necessary because the deletion pass cannot delete scope commands individually
(as that would change scoping semantics), so we need a separate pass to clean up empty scopes.
-/

namespace LeanMinimizer

open Lean

/-- Check if a command is a section command, returning the section name if so. -/
def getSectionName? (stx : Syntax) : Option Name :=
  if stx.isOfKind `Lean.Parser.Command.section then
    -- section has optional identifier
    let args := stx.getArgs
    if args.size > 1 && !args[1]!.isNone then
      some args[1]!.getId
    else
      some Name.anonymous
  else
    none

/-- Check if a command is a namespace command, returning the namespace name if so. -/
def getNamespaceName? (stx : Syntax) : Option Name :=
  if stx.isOfKind `Lean.Parser.Command.namespace then
    let args := stx.getArgs
    if args.size > 1 then
      some args[1]!.getId
    else
      none
  else
    none

/-- Check if a command is an end command, returning the end name if so (anonymous if no name). -/
def getEndName? (stx : Syntax) : Option Name :=
  if stx.isOfKind `Lean.Parser.Command.end then
    let args := stx.getArgs
    if args.size > 1 && !args[1]!.isNone then
      some args[1]!.getId
    else
      some Name.anonymous
  else
    none

/-- Reconstruct source from compilation steps using their recorded positions. -/
def reconstructSourceFromSteps (source : String) (steps : Array CompilationStep) : String := Id.run do
  if steps.isEmpty then
    return ""

  let mut result := ""
  let mut lastEnd : String.Pos.Raw := 0

  for step in steps do
    -- Add any whitespace/content between last command and this one
    let startPos := step.startPos
    if startPos > lastEnd then
      result := result ++ String.Pos.Raw.extract source lastEnd startPos

    -- Add the command text
    result := result ++ String.Pos.Raw.extract source step.startPos step.endPos

    lastEnd := step.endPos

  -- Add any trailing content after last command
  if lastEnd < source.rawEndPos then
    result := result ++ String.Pos.Raw.extract source lastEnd source.rawEndPos

  return result

/-- Find and remove one empty scope pair (section/namespace immediately followed by matching end).
    Returns the new list of steps and whether a removal was made. -/
def removeOneEmptyScopePair (steps : Array CompilationStep) : Array CompilationStep × Bool := Id.run do
  if steps.size < 2 then
    return (steps, false)

  for i in [:steps.size - 1] do
    if h1 : i < steps.size then
      if h2 : i + 1 < steps.size then
        let stx1 := steps[i].stx
        let stx2 := steps[i + 1].stx

        -- Check for section X ... end X
        if let some sectionName := getSectionName? stx1 then
          if let some endName := getEndName? stx2 then
            -- Anonymous section matches anonymous end, named section matches same-named end
            if sectionName == endName || (sectionName == Name.anonymous && endName == Name.anonymous) then
              -- Found empty section pair, remove both (remove i+1 first, then i)
              let newSteps := (steps.eraseIdx! (i + 1)).eraseIdx! i
              return (newSteps, true)

        -- Check for namespace X ... end X
        if let some nsName := getNamespaceName? stx1 then
          if let some endName := getEndName? stx2 then
            if nsName == endName then
              -- Found empty namespace pair, remove both
              let newSteps := (steps.eraseIdx! (i + 1)).eraseIdx! i
              return (newSteps, true)

  return (steps, false)

/-- Repeatedly remove empty scope pairs until no more can be found. -/
def removeAllEmptyScopePairs (steps : Array CompilationStep) : Array CompilationStep × Nat := Id.run do
  let mut currentSteps := steps
  let mut totalRemoved : Nat := 0
  let mut changed := true

  while changed do
    let (newSteps, removed) := removeOneEmptyScopePair currentSteps
    if removed then
      currentSteps := newSteps
      totalRemoved := totalRemoved + 2  -- Each pair is 2 commands
    else
      changed := false

  return (currentSteps, totalRemoved)

/-- The empty scope removal pass.

    Removes adjacent empty scope pairs (section X ... end X or namespace X ... end X).
    Runs repeatedly to handle nested empty scopes.

    This is a cleanup pass that runs after deletion to remove scope commands that
    are now empty after their contents were deleted. -/
unsafe def emptyScopeRemovalPass : Pass where
  name := "Empty Scope Removal"
  cliFlag := "empty-scope"
  run := fun ctx => do
    -- Only process steps before marker
    let stepsBeforeMarker := ctx.steps.filter (·.idx < ctx.markerIdx)
    let stepsFromMarker := ctx.steps.filter (·.idx ≥ ctx.markerIdx)

    let (newStepsBeforeMarker, removed) := removeAllEmptyScopePairs stepsBeforeMarker

    if removed == 0 then
      return { source := ctx.source, changed := false, action := .continue }

    if ctx.verbose then
      IO.eprintln s!"  Removed {removed} empty scope commands ({removed / 2} pairs)"

    -- Reconstruct source from remaining steps
    let allNewSteps := newStepsBeforeMarker ++ stepsFromMarker
    let newSource := reconstructSourceFromSteps ctx.source allNewSteps

    -- Use .repeat to run again in case there are now newly-adjacent empty scopes
    return { source := newSource, changed := true, action := .repeat }

end LeanMinimizer
