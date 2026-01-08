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

## Verbose Output Convention

When `verbose` is enabled, use consistent indentation for log messages:
- No indent: Warnings, errors, and top-level status
- 2 spaces: Pass-level operations (e.g., `"  Testing:..."`, `"  Analyzing..."`)
- 4 spaces: Sub-operations within a pass (e.g., `"    ddmin:..."`, `"    Found..."`)
- 6 spaces: Results and outcomes (e.g., `"      → Success"`, `"      Removed..."`)

Use `→` prefix for outcomes/results. Keep messages concise for readability.
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
  /-- Sections that have been fully processed and are considered stable.
      Commands within stable sections are skipped during unstable-only sweeps. -/
  stableSections : Std.HashSet String := {}
  /-- Whether this is a complete sweep (process all including stable sections)
      or an unstable-only sweep (skip stable sections to save time). -/
  isCompleteSweep : Bool := true

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
  /-- Optional "search after" text for temp marker.
      When set, the temp marker search will first find a command containing
      this text, then search for tempMarker only in commands after that.
      This is used by import inlining to ensure we find the temp marker in
      the original content, not in newly inlined content that might contain
      similar text. -/
  tempMarkerSearchAfter : Option String := none
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

/-- Find the index of a temporary marker in subprocess command array.
    If `searchAfter` is provided, first find a command containing that text,
    then search for `tempMarker` only in commands after that position. -/
def findTempMarkerIdxInSubprocess (commands : Array SubprocessCmdInfo) (tempMarker : String)
    (searchAfter : Option String := none) : Option Nat :=
  match searchAfter with
  | none =>
    commands.findIdx? fun cmd =>
      cmd.stxRepr.containsSubstr tempMarker
  | some afterText =>
    -- First find the "search after" command
    let afterIdx? := commands.findIdx? fun cmd =>
      cmd.stxRepr.containsSubstr afterText
    match afterIdx? with
    | none => none  -- searchAfter text not found
    | some afterIdx => Id.run do
      -- Search for tempMarker only in commands after afterIdx
      for i in [afterIdx + 1:commands.size] do
        if commands[i]!.stxRepr.containsSubstr tempMarker then
          return some i
      return none

/-- Extract section name from tempMarkerSearchAfter text.
    The format is "end ModuleName", so we strip the "end " prefix. -/
def extractSectionName (tempMarkerSearchAfter : Option String) : Option String :=
  tempMarkerSearchAfter.bind fun s =>
    if s.startsWith "end " then
      some (s.drop 4).toString  -- Drop "end " and convert Slice to String
    else
      none

/-- Find indices of commands that fall within a named section.
    Scans for `section Name` and `end Name` pairs and returns all indices between them. -/
def findSectionIndices (commands : Array SubprocessCmdInfo) (sectionName : String) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  let mut inSection := false
  let sectionStart := s!"section {sectionName}"
  let sectionEnd := s!"end {sectionName}"
  for i in [:commands.size] do
    let cmd := commands[i]!
    if cmd.stxRepr.containsSubstr sectionStart then
      inSection := true
    if inSection then
      result := result.push i
    if cmd.stxRepr.containsSubstr sectionEnd then
      inSection := false
  return result

/-- Compute all indices that fall within any stable section. -/
def computeStableIndices (commands : Array SubprocessCmdInfo)
    (stableSections : Std.HashSet String) : Std.HashSet Nat := Id.run do
  let mut result : Std.HashSet Nat := {}
  for sectionName in stableSections do
    let indices := findSectionIndices commands sectionName
    for idx in indices do
      result := result.insert idx
  return result

/-- Compute the byte position ranges covered by stable sections.
    Returns array of (startPos, endPos) byte positions. -/
def computeStablePositionRanges (commands : Array SubprocessCmdInfo)
    (stableSections : Std.HashSet String) : Array (Nat × Nat) := Id.run do
  let stableIndices := computeStableIndices commands stableSections
  if stableIndices.isEmpty then return #[]

  let mut ranges : Array (Nat × Nat) := #[]
  let mut currentStart : Option Nat := none
  let mut lastEnd : Nat := 0

  for cmd in commands do
    if stableIndices.contains cmd.idx then
      match currentStart with
      | none =>
        currentStart := some cmd.startPos
        lastEnd := cmd.endPos
      | some _ =>
        lastEnd := cmd.endPos
    else
      if let some start := currentStart then
        ranges := ranges.push (start, lastEnd)
        currentStart := none

  -- Close any open range
  if let some start := currentStart then
    ranges := ranges.push (start, lastEnd)

  return ranges

/-- Check if a byte position falls within any stable position range. -/
def isInStableRange (pos : Nat) (ranges : Array (Nat × Nat)) : Bool :=
  ranges.any fun (start, stop) => pos >= start && pos < stop

/-- Find the topmost `section X` / `end X` pair in commands.
    Returns (sectionName, endCommandIdx, nextCommandText) where:
    - sectionName: the name of the section (e.g., "Mathlib.Foo")
    - endCommandIdx: index of the `end X` command
    - nextCommandText: text of the command after `end X` (used as temp marker)
    Returns none if no complete section pair is found before markerIdx. -/
def findTopmostSection (commands : Array SubprocessCmdInfo) (markerIdx : Nat) :
    Option (String × Nat × Option String) := Id.run do
  -- Find the first `section X` command
  for i in [:min commands.size markerIdx] do
    let cmd := commands[i]!
    let text := cmd.stxRepr.trimAscii
    if text.startsWith "section " then
      -- Extract section name (everything after "section ")
      let sectionName := (text.drop 7).takeWhile (· != '\n') |>.trimAscii |>.toString
      if sectionName.isEmpty then continue
      -- Find matching `end X`
      let endText := s!"end {sectionName}"
      for j in [i + 1:min commands.size markerIdx] do
        let endCmd := commands[j]!
        if endCmd.stxRepr.trimAscii.startsWith endText then
          -- Found the matching end. Get text of next command if available.
          let nextText := if j + 1 < commands.size && j + 1 < markerIdx then
            some commands[j + 1]!.stxRepr
          else
            none
          return some (sectionName, j, nextText)
  return none

/-- Find all `section X` / `end X` pairs in commands up to markerIdx.
    Returns an array of (sectionName, endCommandIdx). -/
def findAllSections (commands : Array SubprocessCmdInfo) (markerIdx : Nat) :
    Array (String × Nat) := Id.run do
  let mut result : Array (String × Nat) := #[]
  for i in [:min commands.size markerIdx] do
    let cmd := commands[i]!
    let text := cmd.stxRepr.trimAscii
    if text.startsWith "section " then
      let sectionName := (text.drop 7).takeWhile (· != '\n') |>.trimAscii |>.toString
      if sectionName.isEmpty then continue
      let endText := s!"end {sectionName}"
      for j in [i + 1:min commands.size markerIdx] do
        let endCmd := commands[j]!
        if endCmd.stxRepr.trimAscii.startsWith endText then
          result := result.push (sectionName, j)
          break
  return result

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
    process the entire file (for debugging/comparison).

    The `completeSweepBudget` parameter (0.0 to 1.0) controls how much time is spent
    on "complete sweeps" that include stable sections. Default 0.20 means at most
    20% of runtime is spent reprocessing stable sections.

    When `initialTempMarker` is set (e.g., from --resume), processing starts with
    that temp marker active, focusing work on the most recent section first. -/
unsafe def runPasses (passes : Array Pass) (input : String)
    (fileName : String) (marker : String) (verbose : Bool)
    (outputFile : Option String := none) (fullRestarts : Bool := false)
    (completeSweepBudget : Float := 0.20)
    (initialTempMarker : Option String := none)
    (initialTempMarkerSearchAfter : Option String := none)
    (initialStableSections : Std.HashSet String := {}) : IO String := do
  if passes.isEmpty then
    return input

  let mut source := input
  let mut passIdx : Nat := 0
  -- Safety limit to prevent infinite loops. In practice, minimization converges in
  -- far fewer iterations (typically < 100). If this limit is hit, it likely indicates
  -- a bug in pass logic (e.g., a pass that always reports changes but doesn't modify source).
  let maxIterations := 1000
  let mut iterations := 0
  let mut pendingRestart := false  -- Track if we need to restart after a repeatThenRestart cycle
  let mut failedChanges : Std.HashSet String := {}  -- Memory of failed changes
  -- Initialize temp marker from parameters (e.g., from --resume)
  let mut tempMarker : Option String := initialTempMarker
  let mut tempMarkerSearchAfter : Option String := initialTempMarkerSearchAfter

  -- Stable section tracking
  let mut stableSections : Std.HashSet String := initialStableSections  -- Sections that have been fully processed
  -- If we have an initial temp marker, extract the section name for tracking
  let mut currentProcessingSection : Option String := extractSectionName initialTempMarkerSearchAfter

  -- Log initial temp marker if set
  if verbose && initialTempMarker.isSome then
    let sectionInfo := currentProcessingSection.map (s!" (section: {·})") |>.getD ""
    IO.eprintln s!"  Starting with initial temp marker (from --resume){sectionInfo}"
  -- Log initial stable sections if any
  if verbose && !initialStableSections.isEmpty then
    IO.eprintln s!"  Pre-populated {initialStableSections.size} stable sections from resume"

  -- Time budget tracking for complete sweeps
  let mut totalRuntime : Nat := 0        -- Total milliseconds spent in passes
  let mut completeSweepTime : Nat := 0   -- Milliseconds spent in complete sweeps
  let mut isCompleteSweep : Bool := true -- Whether current cycle is a complete sweep
  let mut cycleHadChanges : Bool := false  -- Track if current cycle made any changes
  let mut finalSweepDone : Bool := false  -- Prevent infinite final sweep loops

  -- Write initial source to output file if specified
  if let some outPath := outputFile then
    IO.FS.writeFile outPath source

  while passIdx < passes.size && iterations < maxIterations do
    iterations := iterations + 1
    let some pass := passes[passIdx]? | break

    -- At start of new cycle (passIdx == 0), decide sweep type based on time budget
    if passIdx == 0 then
      cycleHadChanges := false
      let budgetUsed := if totalRuntime > 0 then
        completeSweepTime.toFloat / totalRuntime.toFloat
      else 0.0
      isCompleteSweep := budgetUsed < completeSweepBudget || stableSections.isEmpty
      if verbose then
        if stableSections.isEmpty then
          IO.eprintln s!"  Starting sweep (no stable sections)"
        else
          let totalSec := totalRuntime.toFloat / 1000.0
          let completeSec := completeSweepTime.toFloat / 1000.0
          let pct := (budgetUsed * 100).toUInt32
          let budgetPct := (completeSweepBudget * 100).toUInt32
          if isCompleteSweep then
            IO.eprintln s!"  Starting complete sweep: budget {pct}% < {budgetPct}% allows reprocessing stable sections"
            IO.eprintln s!"    (complete: {completeSec}s, total: {totalSec}s, stable sections: {stableSections.size})"
          else
            IO.eprintln s!"  Starting unstable-only sweep: budget {pct}% >= {budgetPct}%, skipping {stableSections.size} stable sections"
            IO.eprintln s!"    (complete: {completeSec}s, total: {totalSec}s)"

    if verbose then
      IO.eprintln s!"[Pass {passIdx}] Running: {pass.name}"

    -- Time the pass execution
    let startTime ← IO.monoNanosNow
    let result ← if pass.needsSubprocess then
      -- Tier 2 pass: run in subprocess with full elaboration
      let subResult ← runPassSubprocess pass.cliFlag source fileName marker verbose failedChanges
          stableSections isCompleteSweep tempMarker tempMarkerSearchAfter
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
        findTempMarkerIdxInSubprocess subprocessResult.commands tm tempMarkerSearchAfter

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
        stableSections
        isCompleteSweep
      }
      pass.run ctx

    -- Track elapsed time
    let endTime ← IO.monoNanosNow
    let elapsedMs := (endTime - startTime) / 1000000  -- Convert to milliseconds (already Nat)
    totalRuntime := totalRuntime + elapsedMs
    if isCompleteSweep then
      completeSweepTime := completeSweepTime + elapsedMs

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
        -- If we've completed all passes with a temp marker active
        if passIdx >= passes.size && tempMarker.isSome then
          -- If no changes in this cycle, mark the current section as stable
          if !cycleHadChanges then
            if let some sectionName := currentProcessingSection then
              stableSections := stableSections.insert sectionName
              if verbose then
                IO.eprintln s!"  Marking section '{sectionName}' as stable"
          -- Clear temp marker and restart
          if verbose then
            IO.eprintln s!"  All passes complete with temp marker active, clearing and restarting"
          tempMarker := none
          tempMarkerSearchAfter := none
          currentProcessingSection := none
          passIdx := 0
        -- Final complete sweep: if all passes complete, no temp marker, but stable sections exist
        -- Only do this ONCE to prevent infinite loops
        else if passIdx >= passes.size && tempMarker.isNone && !stableSections.isEmpty && !finalSweepDone then
          if verbose then
            IO.eprintln s!"  All passes complete, triggering final complete sweep (clearing {stableSections.size} stable sections)"
          stableSections := {}
          finalSweepDone := true
          passIdx := 0
      continue

    -- Verify source actually changed when pass claims it did
    -- (skip this check for clearMemory passes, which restart without changing source)
    if result.source == source && !result.clearMemory then
      throw <| IO.userError s!"FATAL: Pass '{pass.name}' reported changes but source is unchanged.\n\
        This is a bug in the pass implementation. The pass returned changed=true \
        but the source text is identical to the input."

    -- Track that this cycle had changes
    cycleHadChanges := true
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
        tempMarkerSearchAfter := result.tempMarkerSearchAfter
        -- Extract section name from tempMarkerSearchAfter ("end ModuleName" → "ModuleName")
        currentProcessingSection := extractSectionName result.tempMarkerSearchAfter
        if verbose then
          let sectionInfo := currentProcessingSection.map (s!" (section: {·})") |>.getD ""
          IO.eprintln s!"  Changes made, restarting with temp marker (parsimonious restart){sectionInfo}"
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
