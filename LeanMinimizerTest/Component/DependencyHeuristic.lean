/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.DependencyHeuristic

open Lean LeanMinimizer

/-- Test that dependencyHeuristic correctly identifies unreachable commands.

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
Candidates are [0, 1, 2, 3].

The heuristic should suggest removing cmd 3 (unrelated) first,
while keeping cmds 0,1,2 (reachable via dependency chain from #eval c).
-/
unsafe def test : IO Bool := do
  initSearchPath (← findSysroot)

  let input := "def a := 1\ndef b := a\ndef c := b\ndef unrelated := 999\n/-- info: 1 -/\n#guard_msgs in\n#eval c\n"
  let fileName := "<test>"
  let marker := "#guard_msgs"

  -- Parse the file to get header and commands
  let (header, headerEndPos, allCommands) ← parseFileCommands input fileName

  -- Find the marker (for #guard_msgs, this includes the preceding docstring)
  let some markerIdx := findMarkerIdx allCommands input marker
    | do
      IO.println "  ✗ DependencyHeuristic: marker not found"
      return false

  -- Verify the marker includes the docstring
  if markerIdx != 4 then
    IO.println s!"  ✗ DependencyHeuristic: markerIdx should be 4 (docstring), got {markerIdx}"
    return false

  -- Create the MinState
  let testCount ← IO.mkRef 0
  let state : MinState := {
    input := input
    fileName := fileName
    header := header
    headerEndPos := headerEndPos
    allCommands := allCommands
    markerIdx := markerIdx
    verbose := false
    testCount := testCount
  }

  -- Call the heuristic with all candidates before marker
  let candidates := Array.range markerIdx  -- [0, 1, 2, 3]
  let (tryRemove, keepForNow) ← dependencyHeuristic state candidates

  -- The heuristic should suggest trying to remove only cmd 3 (unrelated).
  -- Reachable/kept: cmds 0, 1, 2 (dependency chain from #eval c)

  if !tryRemove.contains 3 then
    IO.println s!"  ✗ DependencyHeuristic: should suggest removing cmd 3 (unrelated), got tryRemove={tryRemove.toList}"
    return false

  if tryRemove.size != 1 then
    IO.println s!"  ✗ DependencyHeuristic: should only suggest removing 1 cmd, got tryRemove={tryRemove.toList}"
    return false

  -- Cmds 0,1,2 (dependency chain) should be kept
  if !keepForNow.contains 0 || !keepForNow.contains 1 || !keepForNow.contains 2 then
    IO.println s!"  ✗ DependencyHeuristic: should keep cmds 0,1,2, got keepForNow={keepForNow.toList}"
    return false

  IO.println "  ✓ DependencyHeuristic"
  return true

end LeanMinimizerTest.Component.DependencyHeuristic
