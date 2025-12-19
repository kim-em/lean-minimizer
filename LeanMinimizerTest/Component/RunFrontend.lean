/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.RunFrontend

open Lean LeanMinimizer

/-- Test that runFrontend correctly processes a simple file and returns CompilationSteps -/
unsafe def test : IO Bool := do
  let input := "def foo := 1\ndef bar := foo + 1\n#check bar\n"
  let steps ← runFrontend input "<test>"

  -- Should have at least 3 commands (may have extra EOF marker)
  if steps.size < 3 then
    IO.println s!"  ✗ RunFrontend: expected at least 3 steps, got {steps.size}"
    return false

  -- The meaningful commands should have InfoTrees
  for step in steps[:3] do
    if step.trees.isEmpty then
      IO.println s!"  ✗ RunFrontend: step {step.idx} has no InfoTrees"
      return false

  IO.println "  ✓ RunFrontend"
  return true

end LeanMinimizerTest.Component.RunFrontend
