/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.GetNewConstants

open Lean LeanMinimizer

/-- Test that getNewConstants correctly identifies newly defined constants -/
unsafe def test : IO Bool := do
  let input := "def myConst := 42\ndef anotherConst := myConst\n"
  let frontend ← runFrontend input "<test>"
  let steps := frontend.steps

  let some step0 := steps[0]? | do
    IO.println "  ✗ GetNewConstants: expected at least 1 step"
    return false
  let some step1 := steps[1]? | do
    IO.println "  ✗ GetNewConstants: expected at least 2 steps"
    return false

  let step0NewConsts := getNewConstants step0
  let step1NewConsts := getNewConstants step1

  -- First step should define `myConst`
  if !step0NewConsts.contains `myConst then
    IO.println s!"  ✗ GetNewConstants: step 0 should define myConst"
    return false

  -- Second step should define `anotherConst`
  if !step1NewConsts.contains `anotherConst then
    IO.println s!"  ✗ GetNewConstants: step 1 should define anotherConst"
    return false

  IO.println "  ✓ GetNewConstants"
  return true

end LeanMinimizerTest.Component.GetNewConstants
