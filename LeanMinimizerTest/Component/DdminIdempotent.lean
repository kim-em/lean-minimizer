/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.DdminIdempotent

open Lean LeanMinimizer

/-- Test that ddmin correctly removes all removable commands in a single pass.

For the input:
```
def a := 1           -- cmd 0
def b := a           -- cmd 1, depends on 0
def c := b           -- cmd 2, depends on 1
def d := c           -- cmd 3, depends on 2
#guard_msgs in       -- cmd 4 (marker)
example : 1 = 1 := rfl
```

Since the marker doesn't depend on a, b, c, or d, ALL of them should be removed.

The key insight: With proper end-biased deletion, ddmin should:
1. First try removing later commands (c, d) which succeeds
2. Then remove earlier commands (a, b) which also succeeds

But with beginning-biased deletion (the bug):
1. Try removing earlier commands (a, b) first, which FAILS because c, d depend on them
2. Try removing later commands (c, d), which succeeds
3. Now we'd need ANOTHER pass to remove a, b

This test verifies that after one call to ddmin, ALL removable commands are gone.
-/
unsafe def test : IO Bool := do
  initSearchPath (← findSysroot)

  let input := "def a := 1\ndef b := a\ndef c := b\ndef d := c\n\n#guard_msgs in\nexample : 1 = 1 := rfl\n"
  let fileName := "<ddmin-test>"
  let marker := "#guard_msgs"

  -- Run frontend to get compilation steps and header info
  let frontend ← runFrontend input fileName
  let steps := frontend.steps

  -- Find the marker index
  let some markerIdx := findMarkerIdxInSteps steps marker
    | do
      IO.println "  ✗ DdminIdempotent: marker not found"
      return false

  -- Verify marker is at index 4 (cmds 0,1,2,3 before it)
  if markerIdx != 4 then
    IO.println s!"  ✗ DdminIdempotent: markerIdx should be 4, got {markerIdx}"
    IO.println s!"    steps: {steps.map (fun s => (s.idx, s.stx.getKind.toString))}"
    return false

  -- Create MinState using the same conversion as production code
  let testCount ← IO.mkRef 0
  let minState : MinState := {
    input := input
    fileName := fileName
    header := frontend.header
    headerEndPos := frontend.headerEndPos
    allCommands := steps.map (·.toCmdInfo)
    markerIdx := markerIdx
    verbose := false
    testCount := testCount
    outputFile := none
  }

  -- Initial candidates: all indices before the marker
  let candidates := Array.range markerIdx  -- [0, 1, 2, 3]

  -- Call ddmin once with default heuristic (no dependency info)
  let kept ← ddmin defaultSplitHeuristic minState candidates

  -- All commands should be removed (kept should be empty)
  if kept.isEmpty then
    IO.println "  ✓ DdminIdempotent"
    return true
  else
    IO.println s!"  ✗ DdminIdempotent: expected all commands removed, but kept {kept.toList}"
    IO.println s!"    This demonstrates the bug: ddmin is not end-biased, requiring multiple passes"
    IO.println s!"    Total compilation tests: {← testCount.get}"
    return false

end LeanMinimizerTest.Component.DdminIdempotent
