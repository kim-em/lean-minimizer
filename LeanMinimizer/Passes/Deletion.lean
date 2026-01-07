/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Command Deletion Pass

This pass removes unnecessary commands using binary deletion.
-/

namespace LeanMinimizer

open Lean

/-- Check if a command is a section, namespace, or end command.
    These should not be deleted individually to preserve proper scoping. -/
def isScopeCommand (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Command.namespace ||
  stx.isOfKind `Lean.Parser.Command.section ||
  stx.isOfKind `Lean.Parser.Command.end

/-- The command deletion pass.

    Uses binary deletion to find a minimal set of commands needed before the marker.

    Note: section, namespace, and end commands are excluded from deletion to prevent
    silently changing the scoping semantics. A separate pass handles removing empty
    scope pairs. -/
unsafe def deletionPass : Pass where
  name := "Command Deletion"
  cliFlag := "delete"
  run := fun ctx => do
    -- Compute effective upper bound: min of real marker and temp marker (if set)
    -- This enables parsimonious restarts - only delete in the active region
    let effectiveMarkerIdx := match ctx.tempMarkerIdx with
      | some tempIdx => min ctx.markerIdx tempIdx
      | none => ctx.markerIdx

    -- Compute stable indices to skip (if not in complete sweep mode)
    let stableIndices := if ctx.isCompleteSweep then
      {}
    else
      computeStableIndices ctx.subprocessCommands ctx.stableSections

    if ctx.verbose then
      if ctx.tempMarkerIdx.isSome then
        IO.eprintln s!"  (Parsimonious mode: processing up to index {effectiveMarkerIdx}, \
          temp marker at {ctx.tempMarkerIdx.get!})"
      if !ctx.isCompleteSweep && !ctx.stableSections.isEmpty then
        IO.eprintln s!"  (Unstable-only sweep: skipping {stableIndices.size} stable indices)"

    -- Create MinState using pre-elaborated data (no re-parsing needed)
    let state ← mkMinStateFromContext ctx

    -- Build candidate list: all indices before effective marker, excluding:
    -- - scope commands (section/namespace/end)
    -- - stable indices (during unstable-only sweeps)
    let allIndices := (Array.range effectiveMarkerIdx).filter fun idx =>
      if h : idx < ctx.steps.size then
        !isScopeCommand ctx.steps[idx].stx && !stableIndices.contains idx
      else
        !stableIndices.contains idx

    -- In parsimonious mode, commands from effectiveMarkerIdx to markerIdx-1 are "frozen"
    -- They are the original commands that shouldn't be touched during this pass
    -- These must be included in all tests since reconstructSource only auto-includes markerIdx+
    -- Also include stable indices as frozen (they must be present for compilation but not candidates)
    let frozenIndices := Id.run do
      let mut frozen := if ctx.tempMarkerIdx.isSome then
        (Array.range ctx.markerIdx).filter (· >= effectiveMarkerIdx)
      else
        #[]
      -- Add stable indices to frozen list
      for idx in stableIndices do
        if idx < effectiveMarkerIdx && !frozen.contains idx then
          frozen := frozen.push idx
      return frozen

    -- Verify original compiles (include frozen indices in the test)
    -- Note: binaryDelete internally uses Array.range state.markerIdx as currentlyKept,
    -- which includes the frozen indices. But this initial test bypasses binaryDelete.
    -- Deduplicate and sort the indices (frozenIndices may overlap with Array.range)
    let originalIndices := (Array.range effectiveMarkerIdx ++ frozenIndices).toList
      |>.eraseDups |>.toArray |>.qsort (· < ·)
    if ctx.verbose then
      IO.eprintln s!"  (allIndices: {allIndices.size}, frozenIndices: {frozenIndices.size}, originalIndices: {originalIndices.size})"
    if !(← testCompiles state originalIndices) then
      throw <| IO.userError "Source does not compile"

    -- Run binary deletion
    -- Note: keptIndices will only contain non-scope commands, but we need to
    -- add back the scope commands that were excluded from deletion
    let scopeIndices := (Array.range effectiveMarkerIdx).filter fun idx =>
      if h : idx < ctx.steps.size then
        isScopeCommand ctx.steps[idx].stx
      else
        false
    -- binaryDelete internally includes frozenIndices in currentlyKept because it uses
    -- Array.range state.markerIdx, and frozen indices are in [effectiveMarkerIdx, markerIdx)
    let keptNonScopeIndices ← binaryDelete defaultSplitHeuristic state allIndices
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
    -- Use .repeat to run again in case more can be removed with fresh elaboration
    return { source := newSource, changed := true, action := .repeat }

end LeanMinimizer
