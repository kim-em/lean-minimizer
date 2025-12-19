/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.DependencyHeuristic

open Lean LeanMinimizer

/-- Test that dependency analysis correctly identifies reachable commands.

For the input:
```
def a := 1           -- cmd 0
def b := a           -- cmd 1, depends on 0
def c := b           -- cmd 2, depends on 1
def unrelated := 999 -- cmd 3, no deps
/-- info: 1 -/       -- cmd 4, docstring (included with marker for #guard_msgs)
#guard_msgs in       -- cmd 5
#eval c
```

Since marker is #guard_msgs, markerIdx will be 4 (including the docstring).
Commands before marker: [0, 1, 2, 3].

The dependency analysis should identify cmds 0,1,2 as reachable (dependency chain
from #eval c) and cmd 3 as unreachable.
-/
unsafe def test : IO Bool := do
  initSearchPath (← findSysroot)

  let input := "def a := 1\ndef b := a\ndef c := b\ndef unrelated := 999\n/-- info: 1 -/\n#guard_msgs in\n#eval c\n"
  let fileName := "<test>"
  let marker := "#guard_msgs"

  -- Run frontend to get compilation steps (same as production code)
  let steps ← runFrontend input fileName

  -- Find the marker index
  let some markerIdx := findMarkerIdxInSteps steps marker
    | do
      IO.println "  ✗ DependencyHeuristic: marker not found"
      return false

  -- Verify the marker includes the docstring
  if markerIdx != 4 then
    IO.println s!"  ✗ DependencyHeuristic: markerIdx should be 4 (docstring), got {markerIdx}"
    return false

  -- Split steps (same as deletionPass)
  let stepsBeforeMarker := steps.filter (·.idx < markerIdx)
  let invariantSteps := steps.filter (·.idx ≥ markerIdx)

  -- Build dependency graph and compute reachability (same as deletionPass)
  let analyses := analyzeSteps stepsBeforeMarker
  let deps := buildDependencyMap analyses
  let invariantDeps := findInvariantDependencies stepsBeforeMarker invariantSteps
  let reachable := computeReachable deps invariantDeps

  -- Cmds 0,1,2 should be reachable (dependency chain from #eval c)
  if !reachable.contains 0 || !reachable.contains 1 || !reachable.contains 2 then
    IO.println s!"  ✗ DependencyHeuristic: cmds 0,1,2 should be reachable, got reachable={reachable.toList}"
    return false

  -- Cmd 3 should NOT be reachable
  if reachable.contains 3 then
    IO.println s!"  ✗ DependencyHeuristic: cmd 3 should not be reachable, got reachable={reachable.toList}"
    return false

  -- Verify exactly 3 commands are reachable
  if reachable.size != 3 then
    IO.println s!"  ✗ DependencyHeuristic: should have exactly 3 reachable cmds, got {reachable.size}: {reachable.toList}"
    return false

  IO.println "  ✓ DependencyHeuristic"
  return true

end LeanMinimizerTest.Component.DependencyHeuristic
