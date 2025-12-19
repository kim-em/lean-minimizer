/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Dependencies

/-!
# Multi-Pass Minimization Framework

This module provides a framework for running multiple minimization passes in sequence.
Each pass can declare what should happen after it makes progress:
- `restart`: Go back to the first pass
- `repeat`: Run the same pass again
- `continue`: Move to the next pass
-/

namespace LeanMinimizer

open Lean

/-- Action to take after a pass succeeds -/
inductive PassAction where
  /-- Go back to first pass -/
  | restart
  /-- Run this pass again -/
  | repeat
  /-- Move to next pass -/
  | continue
  deriving Repr, BEq, Inhabited

/-- Context provided to each pass -/
structure PassContext where
  /-- Current source code -/
  source : String
  /-- File name -/
  fileName : String
  /-- Marker pattern -/
  marker : String
  /-- Whether to print verbose output -/
  verbose : Bool
  /-- Full elaboration data for all commands -/
  steps : Array CompilationStep
  /-- Index of the marker command -/
  markerIdx : Nat

/-- Result of running a pass -/
structure PassResult where
  /-- The (possibly modified) source code -/
  source : String
  /-- Whether any changes were made -/
  changed : Bool
  /-- What to do next (only used if changed=true) -/
  action : PassAction
  deriving Inhabited

/-- A minimization pass -/
structure Pass where
  /-- Human-readable name for logging -/
  name : String
  /-- CLI flag name (for --no-{cliFlag}) -/
  cliFlag : String
  /-- Run the pass -/
  run : PassContext → IO PassResult

/-- Find the marker index in CompilationStep array.
    For #guard_msgs, also includes the preceding docstring if present. -/
def findMarkerIdxInSteps (steps : Array CompilationStep) (marker : String) : Option Nat := do
  let idx ← steps.findIdx? fun step =>
    let stxStr := step.stx.reprint.getD ""
    containsSubstr stxStr marker

  -- For #guard_msgs, check if the previous command is a docstring
  if marker == "#guard_msgs" && idx > 0 then
    if h : idx - 1 < steps.size then
      let prevStep := steps[idx - 1]
      let prevStr := prevStep.stx.reprint.getD ""
      if prevStr.trimLeft.startsWith "/-" then
        return idx - 1

  return idx

/-- Run passes in sequence according to their on-success actions -/
unsafe def runPasses (passes : Array Pass) (input : String)
    (fileName : String) (marker : String) (verbose : Bool) : IO String := do
  if passes.isEmpty then
    return input

  let mut source := input
  let mut passIdx : Nat := 0
  let maxIterations := 1000  -- Safety limit
  let mut iterations := 0

  while passIdx < passes.size && iterations < maxIterations do
    iterations := iterations + 1
    let some pass := passes[passIdx]? | break

    if verbose then
      IO.eprintln s!"[Pass {passIdx}] Running: {pass.name}"

    -- Elaborate the current source
    let steps ← runFrontend source fileName
    let some markerIdx := findMarkerIdxInSteps steps marker
      | throw <| IO.userError s!"Marker pattern '{marker}' not found in any command.

Add a marker to identify the section you want to preserve. The recommended
approach is to use #guard_msgs to capture the exact error:

  /-- error: unknown identifier 'foo' -/
  #guard_msgs in
  #check foo

Alternatively, use --marker to specify a different pattern."

    let ctx : PassContext := { source, fileName, marker, verbose, steps, markerIdx }
    let result ← pass.run ctx

    if !result.changed then
      if verbose then
        IO.eprintln s!"  No changes, moving to next pass"
      passIdx := passIdx + 1
      continue

    source := result.source
    match result.action with
    | .restart =>
      if verbose then
        IO.eprintln s!"  Changes made, restarting from first pass"
      passIdx := 0
    | .repeat =>
      if verbose then
        IO.eprintln s!"  Changes made, repeating pass"
      -- passIdx stays the same
    | .continue =>
      if verbose then
        IO.eprintln s!"  Changes made, moving to next pass"
      passIdx := passIdx + 1

  if iterations >= maxIterations then
    IO.eprintln s!"Warning: reached maximum iterations ({maxIterations})"

  return source

end LeanMinimizer
