/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Passes.ImportInlining

namespace LeanMinimizerTest.Component.StripAssertNotExists

open LeanMinimizer

/-- Test that stripAssertNotExists correctly removes assert_not_exists lines. -/
unsafe def test : IO Bool := do
  -- Test 1: Simple case with assert_not_exists at start (followed by blank line)
  let input1 := "assert_not_exists Field\n\ndef foo := 1"
  let expected1 := "\ndef foo := 1"  -- blank line is preserved, assert_not_exists line removed
  let result1 := stripAssertNotExists input1
  if result1 != expected1 then
    IO.println s!"  ✗ StripAssertNotExists test 1 failed"
    IO.println s!"    expected: {repr expected1}"
    IO.println s!"    got:      {repr result1}"
    return false

  -- Test 2: assert_not_exists with leading whitespace (line is filtered out entirely)
  let input2 := "  assert_not_exists MyType\ndef bar := 2"
  let expected2 := "def bar := 2"
  let result2 := stripAssertNotExists input2
  if result2 != expected2 then
    IO.println s!"  ✗ StripAssertNotExists test 2 failed"
    IO.println s!"    expected: {repr expected2}"
    IO.println s!"    got:      {repr result2}"
    return false

  -- Test 3: Multiple assert_not_exists lines (both filtered out)
  let input3 := "assert_not_exists A\nassert_not_exists B\ndef x := 1"
  let expected3 := "def x := 1"
  let result3 := stripAssertNotExists input3
  if result3 != expected3 then
    IO.println s!"  ✗ StripAssertNotExists test 3 failed"
    IO.println s!"    expected: {repr expected3}"
    IO.println s!"    got:      {repr result3}"
    return false

  -- Test 4: No assert_not_exists (should be unchanged)
  let input4 := "def y := 1\ndef z := 2"
  let result4 := stripAssertNotExists input4
  if result4 != input4 then
    IO.println s!"  ✗ StripAssertNotExists test 4 failed"
    IO.println s!"    expected: {repr input4}"
    IO.println s!"    got:      {repr result4}"
    return false

  -- Test 5: assert_not_exists in the middle (line removed, others preserved)
  let input5 := "def a := 1\nassert_not_exists Middle\ndef b := 2"
  let expected5 := "def a := 1\ndef b := 2"
  let result5 := stripAssertNotExists input5
  if result5 != expected5 then
    IO.println s!"  ✗ StripAssertNotExists test 5 failed"
    IO.println s!"    expected: {repr expected5}"
    IO.println s!"    got:      {repr result5}"
    return false

  IO.println "  ✓ StripAssertNotExists"
  return true

end LeanMinimizerTest.Component.StripAssertNotExists
