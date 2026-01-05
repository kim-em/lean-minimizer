/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Dependencies
import LeanMinimizer.Subprocess

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
  /-- Run this pass again, and restart from pass 0 when it eventually makes no changes -/
  | repeatThenRestart
  /-- Move to next pass -/
  | continue
  /-- Stop immediately with error -/
  | fatal
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
  /-- The parsed header syntax -/
  header : Syntax
  /-- End position of header -/
  headerEndPos : String.Pos.Raw
  /-- Whether the header has a `module` keyword (for subprocess mode) -/
  hasModule : Bool := false
  /-- Whether the header has `prelude` (for subprocess mode) -/
  hasPrelude : Bool := false
  /-- Header reconstructed without module keyword and import modifiers (for subprocess mode) -/
  headerWithoutModule : String := ""
  /-- Imports extracted from header (for subprocess mode) -/
  imports : Array SubprocessImportInfo := #[]
  /-- Full elaboration data for all commands (with positions) -/
  steps : Array CompilationStep
  /-- Subprocess command info with dependency data (for passes that need it) -/
  subprocessCommands : Array SubprocessCmdInfo := #[]
  /-- Index of the marker command -/
  markerIdx : Nat
  /-- Output file path for intermediate results (optional) -/
  outputFile : Option String := none
  /-- Memory of failed changes: keys are pass-specific strings -/
  failedChanges : Std.HashSet String := {}
  /-- Temporary marker for parsimonious restarts. If set, this acts as
      an additional invariant boundary. Commands containing this text
      (and all after) should be treated as invariant. -/
  tempMarker : Option String := none
  /-- Index of temp marker in commands, if tempMarker is set.
      Computed by finding first command containing tempMarker text. -/
  tempMarkerIdx : Option Nat := none

/-- Result of running a pass -/
structure PassResult where
  /-- The (possibly modified) source code -/
  source : String
  /-- Whether any changes were made -/
  changed : Bool
  /-- What to do next (only used if changed=true) -/
  action : PassAction
  /-- Failed changes to add to memory (keys are pass-specific strings) -/
  newFailedChanges : Array String := #[]
  /-- Whether to clear the failed changes memory -/
  clearMemory : Bool := false
  /-- Temporary marker text for parsimonious restarts.
      When set with a restart action, subsequent passes will use this
      as an additional invariant boundary until it's cleared.
      The marker is the text content of the first command that should be
      treated as invariant (and all commands after it). -/
  tempMarker : Option String := none
  deriving Inhabited

/-- A minimization pass -/
structure Pass where
  /-- Human-readable name for logging -/
  name : String
  /-- CLI flag name (for --no-{cliFlag}) -/
  cliFlag : String
  /-- Whether this pass needs to run in a subprocess with full elaboration.
      Tier 2 passes (body-replacement, extends, import-minimization) need this
      because they require Environment/InfoTrees that can't easily be serialized. -/
  needsSubprocess : Bool := false
  /-- Run the pass -/
  run : PassContext → IO PassResult

/-- Find the marker index in CompilationStep array.
    For #guard_msgs, also includes the preceding docstring if present. -/
def findMarkerIdxInSteps (steps : Array CompilationStep) (marker : String) : Option Nat := do
  let idx ← steps.findIdx? fun step =>
    let stxStr := step.stx.reprint.getD ""
    stxStr.containsSubstr marker

  -- For #guard_msgs, check if the previous command is a standalone docstring
  -- (not a declaration with a docstring attached)
  if marker == "#guard_msgs" && idx > 0 then
    if h : idx - 1 < steps.size then
      let prevStep := steps[idx - 1]
      -- Only match if the previous step is a docstring command, not a declaration
      if prevStep.stx.isOfKind `Lean.Parser.Command.docComment then
        return idx - 1

  return idx

/-- Find the index of a temporary marker in CompilationStep array.
    Returns the index of the first command whose reprinted syntax contains the marker text. -/
def findTempMarkerIdxInSteps (steps : Array CompilationStep) (tempMarker : String) : Option Nat :=
  steps.findIdx? fun step =>
    let stxStr := step.stx.reprint.getD ""
    stxStr.containsSubstr tempMarker

/-- Find the index of a temporary marker in subprocess command array. -/
def findTempMarkerIdxInSubprocess (commands : Array SubprocessCmdInfo) (tempMarker : String) : Option Nat :=
  commands.findIdx? fun cmd =>
    cmd.stxRepr.containsSubstr tempMarker

/-- Create a MinState from PassContext, using pre-elaborated data.
    This avoids re-parsing the file. -/
def mkMinStateFromContext (ctx : PassContext) : IO MinState := do
  let testCount ← IO.mkRef 0
  return {
    input := ctx.source
    fileName := ctx.fileName
    header := ctx.header
    headerEndPos := ctx.headerEndPos
    allCommands := ctx.steps.map (·.toCmdInfo)
    markerIdx := ctx.markerIdx
    verbose := ctx.verbose
    testCount
    outputFile := ctx.outputFile
  }

/-- Convert SubprocessPassResult to PassResult -/
def SubprocessPassResult.toPassResult (result : SubprocessPassResult) : PassResult :=
  let action := match result.action with
    | "restart" => PassAction.restart
    | "repeat" => PassAction.repeat
    | "repeatThenRestart" => PassAction.repeatThenRestart
    | "fatal" => PassAction.fatal
    | _ => PassAction.continue  -- Default to continue for unknown values
  { source := result.source, changed := result.changed, action,
    newFailedChanges := result.newFailedChanges, clearMemory := result.clearMemory }

/-- Run passes in sequence according to their on-success actions.
    Uses subprocess-based elaboration to avoid [init] conflicts.

    Tier 1 passes run in the orchestrator with serialized data.
    Tier 2 passes (needsSubprocess=true) run in a subprocess with full elaboration.

    When `fullRestarts` is true, parsimonious restarts are disabled and all restarts
    process the entire file (for debugging/comparison). -/
unsafe def runPasses (passes : Array Pass) (input : String)
    (fileName : String) (marker : String) (verbose : Bool)
    (outputFile : Option String := none) (fullRestarts : Bool := false) : IO String := do
  if passes.isEmpty then
    return input

  let mut source := input
  let mut passIdx : Nat := 0
  let maxIterations := 1000  -- Safety limit
  let mut iterations := 0
  let mut pendingRestart := false  -- Track if we need to restart after a repeatThenRestart cycle
  let mut failedChanges : Std.HashSet String := {}  -- Memory of failed changes
  let mut tempMarker : Option String := none  -- Temporary marker for parsimonious restarts

  -- Write initial source to output file if specified
  if let some outPath := outputFile then
    IO.FS.writeFile outPath source

  while passIdx < passes.size && iterations < maxIterations do
    iterations := iterations + 1
    let some pass := passes[passIdx]? | break

    if verbose then
      IO.eprintln s!"[Pass {passIdx}] Running: {pass.name}"

    let result ← if pass.needsSubprocess then
      -- Tier 2 pass: run in subprocess with full elaboration
      let subResult ← runPassSubprocess pass.cliFlag source fileName marker verbose failedChanges
      pure subResult.toPassResult
    else
      -- Tier 1 pass: run in orchestrator with serialized data
      -- Elaborate the current source via subprocess to avoid [init] conflicts
      let subprocessResult ← runAnalyzeSubprocess source fileName
      let some markerIdx := findMarkerIdxInSubprocessSteps subprocessResult.commands marker
        | throw <| IO.userError (markerNotFoundError marker)

      -- Convert subprocess result to PassContext data
      let (header, headerEndPos, steps) ← subprocessResult.toPassContextData

      -- Compute temp marker index if we have a temp marker
      let tempMarkerIdx := tempMarker.bind fun tm =>
        findTempMarkerIdxInSubprocess subprocessResult.commands tm

      let ctx : PassContext := {
        source, fileName, marker, verbose
        header
        headerEndPos
        hasModule := subprocessResult.hasModule
        hasPrelude := subprocessResult.hasPrelude
        headerWithoutModule := subprocessResult.headerWithoutModule
        imports := subprocessResult.imports
        steps
        subprocessCommands := subprocessResult.commands
        markerIdx
        outputFile
        failedChanges
        tempMarker
        tempMarkerIdx
      }
      pass.run ctx

    -- Handle clearMemory flag (must happen BEFORE adding new keys,
    -- otherwise the sentinel key gets immediately cleared)
    if result.clearMemory then
      failedChanges := {}

    -- Merge new failed changes into memory
    for key in result.newFailedChanges do
      failedChanges := failedChanges.insert key

    if !result.changed then
      -- If we were in a repeatThenRestart cycle, restart now
      if pendingRestart then
        if verbose then
          IO.eprintln s!"  No more changes, restarting from first pass"
        pendingRestart := false
        passIdx := 0
      else
        if verbose then
          IO.eprintln s!"  No changes, moving to next pass"
        passIdx := passIdx + 1
        -- If we've completed all passes with a temp marker active, clear it and restart
        -- to process commands that were previously beyond the temp marker boundary
        if passIdx >= passes.size && tempMarker.isSome then
          if verbose then
            IO.eprintln s!"  All passes complete with temp marker active, clearing and restarting"
          tempMarker := none
          passIdx := 0
      continue

    -- Verify source actually changed when pass claims it did
    -- (skip this check for clearMemory passes, which restart without changing source)
    if result.source == source && !result.clearMemory then
      throw <| IO.userError s!"FATAL: Pass '{pass.name}' reported changes but source is unchanged.\n\
        This is a bug in the pass implementation. The pass returned changed=true \
        but the source text is identical to the input."

    source := result.source

    -- Write updated source to output file if specified
    if let some outPath := outputFile then
      IO.FS.writeFile outPath source

    match result.action with
    | .restart =>
      -- Capture temp marker if pass returned one (for parsimonious restarts)
      -- Skip if fullRestarts mode is enabled
      -- IMPORTANT: Don't override an existing temp marker - the first one should persist
      -- through the entire parsimonious cycle (e.g., for transitive import inlining)
      if result.tempMarker.isSome && !fullRestarts && tempMarker.isNone then
        tempMarker := result.tempMarker
        if verbose then
          IO.eprintln s!"  Changes made, restarting with temp marker (parsimonious restart)"
      else if tempMarker.isSome then
        -- Keep existing temp marker
        if verbose then
          IO.eprintln s!"  Changes made, restarting (keeping existing temp marker)"
      else
        -- No temp marker
        if verbose then
          IO.eprintln s!"  Changes made, restarting from first pass"
      pendingRestart := false
      passIdx := 0
    | .repeat =>
      if verbose then
        IO.eprintln s!"  Changes made, repeating pass"
      -- passIdx stays the same
    | .repeatThenRestart =>
      if verbose then
        IO.eprintln s!"  Changes made, repeating pass (will restart when done)"
      pendingRestart := true
      -- passIdx stays the same
    | .continue =>
      if verbose then
        IO.eprintln s!"  Changes made, moving to next pass"
      passIdx := passIdx + 1
    | .fatal =>
      -- Write current source to output for debugging, then exit
      if let some outPath := outputFile then
        IO.FS.writeFile outPath source
      throw <| IO.userError "Minimization aborted due to fatal error (see above)"

  if iterations >= maxIterations then
    IO.eprintln s!"Warning: reached maximum iterations ({maxIterations})"

  return source

/-- Sentinel key used to track that we've already done the final sweep -/
private def finalSweepSentinel : String := "__final_sweep_done__"

/-- A pass that clears the failed changes memory and restarts if non-empty.
    This ensures a final sweep without memory to catch any changes that became
    possible due to context changes from other passes.

    Only triggers ONE final sweep - uses a sentinel key to prevent infinite loops. -/
def clearMemoryPass : Pass where
  name := "Clear Memory"
  cliFlag := "clear-memory"
  run := fun ctx => do
    -- Check if we've already done the final sweep
    if ctx.failedChanges.contains finalSweepSentinel then
      if ctx.verbose then
        IO.eprintln s!"  Final sweep already done, finishing"
      return { source := ctx.source, changed := false, action := .continue }
    -- Check if there's anything in memory worth sweeping for
    if ctx.failedChanges.isEmpty then
      if ctx.verbose then
        IO.eprintln s!"  Memory is empty, no final sweep needed"
      return { source := ctx.source, changed := false, action := .continue }
    else
      if ctx.verbose then
        IO.eprintln s!"  Memory has {ctx.failedChanges.size} failed changes, clearing for final sweep"
      -- Clear memory but add sentinel so we only do this once
      return { source := ctx.source, changed := true, action := .restart,
               clearMemory := true, newFailedChanges := #[finalSweepSentinel] }

end LeanMinimizer
