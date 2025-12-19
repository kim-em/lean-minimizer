/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Command Deletion Pass

This pass removes unnecessary commands using delta debugging with dependency-guided heuristics.
It uses pre-elaborated compilation steps to compute which commands are reachable from the
invariant section, avoiding redundant elaboration.
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

    Uses delta debugging to find a minimal set of commands needed before the marker.
    Pre-computed dependency analysis guides the search by trying to remove
    unreachable commands first.

    Note: section, namespace, and end commands are excluded from deletion to prevent
    silently changing the scoping semantics. A separate pass handles removing empty
    scope pairs. -/
unsafe def deletionPass : Pass where
  name := "Command Deletion"
  cliFlag := "delete"
  run := fun ctx => do
    if ctx.verbose then
      IO.eprintln s!"  Analyzing dependencies from pre-elaborated data..."

    -- Use pre-elaborated steps to compute dependency reachability
    let stepsBeforeMarker := ctx.steps.filter (·.idx < ctx.markerIdx)
    let invariantSteps := ctx.steps.filter (·.idx ≥ ctx.markerIdx)

    -- Build dependency graph and find reachable commands
    let analyses := analyzeSteps stepsBeforeMarker
    let deps := buildDependencyMap analyses
    let invariantDeps := findInvariantDependencies stepsBeforeMarker invariantSteps
    let reachable := computeReachable deps invariantDeps

    if ctx.verbose then
      IO.eprintln s!"  Dependency analysis: {reachable.size} commands reachable from invariant"

    -- Create MinState for ddmin using pre-elaborated data (no re-parsing needed)
    let state ← mkMinStateFromContext ctx

    -- Build candidate list: all indices before marker, excluding scope commands
    -- We never delete section/namespace/end individually to preserve scoping semantics
    let allIndices := (Array.range ctx.markerIdx).filter fun idx =>
      if h : idx < ctx.steps.size then
        !isScopeCommand ctx.steps[idx].stx
      else
        true

    -- Verify original compiles
    let originalIndices := Array.range ctx.markerIdx
    if !(← testCompiles state originalIndices) then
      throw <| IO.userError "Source does not compile"

    -- Run ddmin with pre-computed dependency heuristic
    -- Note: keptIndices will only contain non-scope commands, but we need to
    -- add back the scope commands that were excluded from deletion
    let scopeIndices := (Array.range ctx.markerIdx).filter fun idx =>
      if h : idx < ctx.steps.size then
        isScopeCommand ctx.steps[idx].stx
      else
        false
    let heuristic := precomputedDependencyHeuristic reachable
    let keptNonScopeIndices ← ddmin heuristic state allIndices
    -- Combine kept non-scope indices with all scope indices
    let keptIndices := (keptNonScopeIndices ++ scopeIndices).qsort (· < ·)

    let removed := ctx.markerIdx - keptIndices.size
    let changed := removed > 0

    if ctx.verbose then
      let finalTestCount ← state.testCount.get
      IO.eprintln s!"  Removed {removed} of {ctx.markerIdx} commands ({finalTestCount} tests)"

    if !changed then
      return { source := ctx.source, changed := false, action := .continue }

    let newSource := reconstructSource state keptIndices
    -- Use .repeat to run again in case more can be removed with fresh elaboration
    return { source := newSource, changed := true, action := .repeat }

end LeanMinimizer
