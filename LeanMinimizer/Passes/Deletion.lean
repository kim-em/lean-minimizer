/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Command Deletion Passes

Two deletion strategies are used in sequence:

1. **Binary deletion** (`binaryDeletionPass`): Uses binary search to quickly remove
   large blocks of commands. Runs once per cycle (returns `.continue`). Most effective
   right after import inlining brings in a large chunk of new code.

2. **Linear deletion** (`linearDeletionPass`): Tries removing each command one at a time.
   Repeats until no more commands can be removed (returns `.repeat`). More efficient than
   binary deletion when most commands are needed, since it avoids the overhead of testing
   large block removals that will fail.
-/

namespace LeanMinimizer

open Lean

/-- Check if a command is a section, namespace, or end command.
    These should not be deleted individually to preserve proper scoping. -/
def isScopeCommand (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Command.namespace ||
  stx.isOfKind `Lean.Parser.Command.section ||
  stx.isOfKind `Lean.Parser.Command.end

/-- Common setup for deletion passes: compute candidates, stable/frozen/scope indices,
    create MinState, and verify original compiles. -/
unsafe def setupDeletion (ctx : PassContext) :
    IO (MinState × Array Nat × Array Nat × Array Nat) := do
  -- Compute stable indices to skip (if not in complete sweep mode)
  let stableIndices := if ctx.isCompleteSweep then
    {}
  else
    computeStableIndices ctx.subprocessCommands ctx.stableSections ctx.markerIdx ctx.topmostEndIdx

  if ctx.verbose then
    if !ctx.isCompleteSweep && !ctx.stableSections.isEmpty then
      IO.eprintln s!"  (Unstable-only sweep: skipping {stableIndices.size} stable indices)"

  -- Create MinState using pre-elaborated data (no re-parsing needed)
  let state ← mkMinStateFromContext ctx

  -- Build candidate list: all indices before marker, excluding:
  -- - scope commands (section/namespace/end)
  -- - stable indices (during unstable-only sweeps)
  let allIndices := (Array.range ctx.markerIdx).filter fun idx =>
    if h : idx < ctx.steps.size then
      !isScopeCommand ctx.steps[idx].stx && !stableIndices.contains idx
    else
      !stableIndices.contains idx

  -- Show first and last candidate commands for sanity checking
  if ctx.verbose && !allIndices.isEmpty then
    let getPreview (idx : Nat) : String :=
      if h : idx < ctx.subprocessCommands.size then
        let text := ctx.subprocessCommands[idx].stxRepr.trimAscii.toString
        let preview := if text.length > 60 then (text.take 60).toString ++ "..." else text
        s!"[{idx}] {preview}"
      else s!"[{idx}] <unknown>"
    IO.eprintln s!"  First candidate: {getPreview allIndices[0]!}"
    if allIndices.size > 1 then
      IO.eprintln s!"  Last candidate:  {getPreview allIndices[allIndices.size - 1]!}"

  -- Stable indices must be present for compilation but are not candidates for deletion
  let frozenIndices := stableIndices.toArray

  -- Verify original compiles (include frozen indices in the test)
  let originalIndices := (Array.range ctx.markerIdx).toList
    |>.eraseDups |>.toArray |>.qsort (· < ·)
  if ctx.verbose then
    IO.eprintln s!"  (allIndices: {allIndices.size}, frozenIndices: {frozenIndices.size}, originalIndices: {originalIndices.size})"
  if !(← testCompiles state originalIndices) then
    throw <| IO.userError "Source does not compile"

  let scopeIndices := (Array.range ctx.markerIdx).filter fun idx =>
    if h : idx < ctx.steps.size then
      isScopeCommand ctx.steps[idx].stx
    else
      false

  return (state, allIndices, scopeIndices, frozenIndices)

/-- Finalize deletion results: combine kept indices with scope/frozen indices,
    compute removal count, and reconstruct source if changed. -/
def finalizeDeletion (ctx : PassContext) (state : MinState) (allIndices : Array Nat)
    (keptNonScopeIndices : Array Nat) (scopeIndices : Array Nat) (frozenIndices : Array Nat)
    (action : PassAction) : IO PassResult := do
  -- Combine kept non-scope indices with all scope indices and frozen indices
  -- Deduplicate because scopeIndices and frozenIndices may overlap
  let keptIndices := (keptNonScopeIndices ++ scopeIndices ++ frozenIndices).toList
    |>.eraseDups |>.toArray |>.qsort (· < ·)

  -- Calculate how many commands were removed
  -- "removed" = candidates that were NOT kept
  let removed := allIndices.size - keptNonScopeIndices.size
  let changed := removed > 0

  if ctx.verbose then
    let finalTestCount ← state.testCount.get
    IO.eprintln s!"  Removed {removed} of {allIndices.size} candidate commands ({finalTestCount} tests)"

  if !changed then
    return { source := ctx.source, changed := false, action := .continue }

  let newSource := reconstructSource state keptIndices
  return { source := newSource, changed := true, action }

/-- Binary deletion pass: uses binary search to quickly remove large blocks of commands.

    Runs once per cycle (returns `.continue`), then hands off to linear deletion
    for fine-grained cleanup. Most effective right after import inlining brings in
    a large chunk of new code.

    Section, namespace, and end commands are excluded from deletion to prevent
    silently changing the scoping semantics. -/
unsafe def binaryDeletionPass : Pass where
  name := "Binary Deletion"
  cliFlag := "delete"
  run := fun ctx => do
    let (state, allIndices, scopeIndices, frozenIndices) ← setupDeletion ctx
    let keptNonScopeIndices ← binaryDelete defaultSplitHeuristic state allIndices
    finalizeDeletion ctx state allIndices keptNonScopeIndices scopeIndices frozenIndices .continue

/-- Linear deletion pass: tries removing each command one at a time.

    Repeats until no more commands can be removed. More efficient than binary deletion
    after the initial bulk cleanup, since it avoids the overhead of testing large block
    removals that will mostly fail.

    Section, namespace, and end commands are excluded from deletion to prevent
    silently changing the scoping semantics. -/
unsafe def linearDeletionPass : Pass where
  name := "Linear Deletion"
  cliFlag := "linear-delete"
  run := fun ctx => do
    let (state, allIndices, scopeIndices, frozenIndices) ← setupDeletion ctx
    let keptNonScopeIndices ← linearDelete state allIndices
    finalizeDeletion ctx state allIndices keptNonScopeIndices scopeIndices frozenIndices .repeat

end LeanMinimizer
