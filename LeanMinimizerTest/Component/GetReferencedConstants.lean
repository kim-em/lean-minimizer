/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.GetReferencedConstants

open Lean LeanMinimizer

/-- Test that getReferencedConstants correctly extracts references from InfoTrees -/
unsafe def test : IO Bool := do
  let input := "def base := 1\ndef derived := base + 1\n"
  let steps ← runFrontend input "<test>"

  let some step1 := steps[1]? | do
    IO.println "  ✗ GetReferencedConstants: expected at least 2 steps"
    return false

  let step1Refs := getReferencedConstants step1

  -- Second step should reference `base`
  if !step1Refs.contains `base then
    IO.println s!"  ✗ GetReferencedConstants: step 1 should reference base"
    return false

  IO.println "  ✓ GetReferencedConstants"
  return true

end LeanMinimizerTest.Component.GetReferencedConstants
