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

/-- The command deletion pass.

    Uses delta debugging to find a minimal set of commands needed before the marker.
    Pre-computed dependency analysis guides the search by trying to remove
    unreachable commands first. -/
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

    -- Verify original compiles
    let allIndices := Array.range ctx.markerIdx
    if !(← testCompiles state allIndices) then
      throw <| IO.userError "Source does not compile"

    -- Run ddmin with pre-computed dependency heuristic
    let heuristic := precomputedDependencyHeuristic reachable
    let keptIndices ← ddmin heuristic state allIndices

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
