/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer

namespace LeanMinimizerTest.Component.ComputeReachable

open Lean LeanMinimizer

/-- Test that computeReachable correctly computes transitive closure -/
unsafe def test : IO Bool := do
  -- Create a simple dependency graph: 0 <- 1 <- 2, 3 (isolated)
  let deps : Array (Array Nat) := #[#[], #[0], #[1], #[]]

  -- Reachable from 2 should be {0, 1, 2}
  let reachableFrom2 : Array Nat := computeReachable deps #[2]
  if !reachableFrom2.contains 0 || !reachableFrom2.contains 1 || !reachableFrom2.contains 2 then
    IO.println "  ✗ ComputeReachable: reachable from 2 should be {0,1,2}"
    return false

  -- 3 should not be reachable from 2
  if reachableFrom2.contains 3 then
    IO.println s!"  ✗ ComputeReachable: 3 should not be reachable from 2"
    return false

  IO.println "  ✓ ComputeReachable"
  return true

end LeanMinimizerTest.Component.ComputeReachable
