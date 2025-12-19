/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.BuildDependencyMap

open Lean LeanMinimizer

/-- Test that buildDependencyMap correctly builds the dependency graph -/
unsafe def test : IO Bool := do
  let input := "def a := 1\ndef b := a\ndef c := b\ndef unrelated := 99\n"
  let frontend ← runFrontend input "<test>"
  let allSteps := frontend.steps

  -- Should have at least 4 commands (may have extra EOF marker)
  if allSteps.size < 4 then
    IO.println s!"  ✗ BuildDependencyMap: expected at least 4 steps, got {allSteps.size}"
    return false
  -- Use only the first 4 steps for the test
  let steps := allSteps[:4].toArray

  let analyses := analyzeSteps steps
  let deps := buildDependencyMap analyses

  if deps.size != 4 then
    IO.println s!"  ✗ BuildDependencyMap: expected 4 deps entries, got {deps.size}"
    return false

  let some deps1 := deps[1]? | do
    IO.println "  ✗ BuildDependencyMap: missing deps[1]"
    return false
  let some deps2 := deps[2]? | do
    IO.println "  ✗ BuildDependencyMap: missing deps[2]"
    return false
  let some deps3 := deps[3]? | do
    IO.println "  ✗ BuildDependencyMap: missing deps[3]"
    return false

  -- deps[1] should contain 0 (b depends on a)
  if !deps1.contains 0 then
    IO.println s!"  ✗ BuildDependencyMap: b should depend on a"
    return false

  -- deps[2] should contain 1 (c depends on b)
  if !deps2.contains 1 then
    IO.println s!"  ✗ BuildDependencyMap: c should depend on b"
    return false

  -- deps[3] should be empty (unrelated has no deps in file)
  if !deps3.isEmpty then
    IO.println s!"  ✗ BuildDependencyMap: unrelated should have no deps, got {deps3.toList}"
    return false

  IO.println "  ✓ BuildDependencyMap"
  return true

end LeanMinimizerTest.Component.BuildDependencyMap
