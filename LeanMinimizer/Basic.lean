/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.Frontend
import Lean.Elab.Command
import Lean.Util.Path

/-!
# Minimize: A Lean test case minimizer

This tool finds commands in a Lean file that can be removed while preserving
compilation of a marked "invariant" section.

Usage:
  lake exe minimize <file.lean> [--marker <pattern>]

The tool finds a marker in the file (default: "invariant") and uses delta debugging
to find a minimal set of commands before the marker that are needed for the file
to compile.
-/

/-- Check if `needle` is a substring of `haystack` -/
def String.containsSubstr (haystack needle : String) : Bool :=
  -- Use splitOn: if needle is present, splitOn will return > 1 element
  needle.isEmpty || (haystack.splitOn needle).length > 1

namespace LeanMinimizer

open Lean Elab Frontend Parser

/-- Help string for the command line interface -/
def help : String := "Lean test case minimizer

Usage: lake exe minimize [OPTIONS] <FILE>

Arguments:
  <FILE>
    The Lean file to minimize.

Options:
  --marker <PATTERN>
    Pattern to search for in commands to identify the invariant section.
    Default: \"#guard_msgs\"

  -q, --quiet
    Suppress progress information during minimization.

  -o, --output <FILE>
    Write output to FILE. Defaults to <input>.out.lean if not specified.
    The file is updated after each successful minimization step,
    allowing you to follow along in an editor as the minimization progresses.

  --no-module-removal
    Disable the module system removal pass.

  --no-delete
    Disable the command deletion pass.

  --no-sorry
    Disable the body replacement pass (replacing bodies with sorry).

  --no-import-minimization
    Disable the import minimization pass.

  --no-import-inlining
    Disable the import inlining pass.

  --no-text-subst
    Disable the text substitution pass.

  --no-extends
    Disable the extends clause simplification pass.

  --resume
    Resume a previous minimization run. If the output file exists, use it
    as the input instead of the original file. This allows continuing an
    interrupted minimization.

  --only-<PASS>
    Run only the specified pass once. Available passes:
      --only-module-removal    Module system removal
      --only-delete            Command deletion
      --only-empty-scope       Empty scope removal
      --only-sorry             Body replacement (sorry)
      --only-text-subst        Text substitution
      --only-extends           Extends simplification
      --only-attr-expansion    Attribute expansion
      --only-import-minimization  Import minimization
      --only-import-inlining   Import inlining

  --help
    Show this help message.

Example:
  lake exe minimize test.lean
  lake exe minimize test.lean --marker \"section invariant\"

The tool will find the first command containing the marker pattern and
remove as many commands before it as possible while keeping the file
compilable. It uses dependency analysis to identify which commands are
actually needed by the invariant section and removes unneeded commands first.

Tip: Use #guard_msgs to mark the section you want to preserve:

  /-- error: unknown identifier 'foo' -/
  #guard_msgs in
  #check foo

This captures the exact error message, making it ideal for bug reports
and regression tests.
"

/-- Parsed command line arguments -/
structure Args where
  file : String
  marker : String := "#guard_msgs"
  quiet : Bool := false
  help : Bool := false
  /-- Output file to write intermediate results to -/
  outputFile : Option String := none
  /-- Disable the module system removal pass -/
  noModuleRemoval : Bool := false
  /-- Disable the deletion pass -/
  noDelete : Bool := false
  /-- Disable the body replacement pass -/
  noSorry : Bool := false
  /-- Disable the import minimization pass -/
  noImportMinimization : Bool := false
  /-- Disable the import inlining pass -/
  noImportInlining : Bool := false
  /-- Disable the text substitution pass -/
  noTextSubst : Bool := false
  /-- Disable the extends clause simplification pass -/
  noExtendsSimplification : Bool := false
  /-- Run only a specific pass (by CLI flag name) -/
  onlyPass : Option String := none
  /-- Resume from output file if it exists -/
  resume : Bool := false
  /-- Disable parsimonious restarts (for debugging) -/
  fullRestarts : Bool := false
  /-- Budget for complete sweeps as fraction of runtime (0.0-1.0, default 0.20) -/
  completeSweepBudget : Float := 0.20

/-- Check if verbose output is enabled (default is verbose, --quiet disables) -/
def Args.verbose (args : Args) : Bool := !args.quiet

/-- Parse command line arguments -/
def parseArgs (args : List String) : Except String Args := do
  let rec go (args : List String) (acc : Args) : Except String Args :=
    match args with
    | [] =>
      if acc.file.isEmpty && !acc.help then
        .error "No input file specified"
      else
        .ok acc
    | "--help" :: rest => go rest { acc with help := true }
    | "--quiet" :: rest => go rest { acc with quiet := true }
    | "-q" :: rest => go rest { acc with quiet := true }
    | "--marker" :: pattern :: rest => go rest { acc with marker := pattern }
    | "--marker" :: [] => .error "--marker requires an argument"
    | "-o" :: path :: rest => go rest { acc with outputFile := some path }
    | "--output" :: path :: rest => go rest { acc with outputFile := some path }
    | "-o" :: [] => .error "-o requires an argument"
    | "--output" :: [] => .error "--output requires an argument"
    | "--no-delete" :: rest => go rest { acc with noDelete := true }
    | "--no-module-removal" :: rest => go rest { acc with noModuleRemoval := true }
    | "--no-sorry" :: rest => go rest { acc with noSorry := true }
    | "--no-import-minimization" :: rest => go rest { acc with noImportMinimization := true }
    | "--no-import-inlining" :: rest => go rest { acc with noImportInlining := true }
    | "--no-text-subst" :: rest => go rest { acc with noTextSubst := true }
    | "--no-extends" :: rest => go rest { acc with noExtendsSimplification := true }
    | "--only-delete" :: rest => go rest { acc with onlyPass := some "delete" }
    | "--only-module-removal" :: rest => go rest { acc with onlyPass := some "module-removal" }
    | "--only-sorry" :: rest => go rest { acc with onlyPass := some "body-replacement" }
    | "--only-import-minimization" :: rest => go rest { acc with onlyPass := some "import-minimization" }
    | "--only-import-inlining" :: rest => go rest { acc with onlyPass := some "import-inlining" }
    | "--only-text-subst" :: rest => go rest { acc with onlyPass := some "text-subst" }
    | "--only-extends" :: rest => go rest { acc with onlyPass := some "extends" }
    | "--only-attr-expansion" :: rest => go rest { acc with onlyPass := some "attr-expansion" }
    | "--only-empty-scope" :: rest => go rest { acc with onlyPass := some "empty-scope" }
    | "--resume" :: rest => go rest { acc with resume := true }
    | "--full-restarts" :: rest => go rest { acc with fullRestarts := true }
    | "--complete-sweep-budget" :: value :: rest =>
      -- Parse as percentage (0-100) and convert to fraction
      match value.toNat? with
      | some n =>
        if n > 100 then
          .error "--complete-sweep-budget must be between 0 and 100 (percentage)"
        else
          go rest { acc with completeSweepBudget := n.toFloat / 100.0 }
      | none => .error s!"--complete-sweep-budget requires an integer percentage (0-100, got '{value}')"
    | "--complete-sweep-budget" :: [] => .error "--complete-sweep-budget requires an argument"
    | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"Unknown option: {arg}"
      else if acc.file.isEmpty then
        go rest { acc with file := arg }
      else
        .error s!"Unexpected argument: {arg}"
  if args.isEmpty then
    .ok { file := "", help := true }
  else
    go args { file := "" }

/-- Error message when marker is not found in the file -/
def markerNotFoundError (marker : String) : String :=
  s!"Marker pattern '{marker}' not found in any command.

Add a marker to identify the section you want to preserve. The recommended
approach is to use #guard_msgs to capture the exact error:

  /-- error: unknown identifier 'foo' -/
  #guard_msgs in
  #check foo

Alternatively, use --marker to specify a different pattern."

/-- Information about a parsed command -/
structure CmdInfo where
  /-- Index in the command array -/
  idx : Nat
  /-- The parsed syntax -/
  stx : Syntax
  /-- Start position in the source file (includes leading whitespace/comments from previous) -/
  startPos : String.Pos.Raw
  /-- End position in the source file (including trailing whitespace) -/
  endPos : String.Pos.Raw
  deriving Inhabited

/-- State for the minimization process -/
structure MinState where
  /-- Original file content -/
  input : String
  /-- File name -/
  fileName : String
  /-- The header syntax -/
  header : Syntax
  /-- End position of header (including trailing whitespace) -/
  headerEndPos : String.Pos.Raw
  /-- All commands (before + invariant) -/
  allCommands : Array CmdInfo
  /-- Index of the marker command -/
  markerIdx : Nat
  /-- Whether to print verbose output -/
  verbose : Bool
  /-- Counter for compilation tests -/
  testCount : IO.Ref Nat
  /-- Output file to write intermediate results to (optional) -/
  outputFile : Option String := none

/-- A heuristic for splitting candidates during delta debugging.

    Given the minimization state and current candidate indices, returns a split
    `(tryRemoveFirst, tryRemoveSecond)` that partitions the candidates.

    The algorithm will:
    1. Try removing `tryRemoveFirst` (keeping `tryRemoveSecond`)
    2. If that fails, try removing `tryRemoveSecond` (keeping `tryRemoveFirst`)
    3. If both fail, recurse on each half

    A good heuristic puts commands likely to be removable in `tryRemoveFirst`.

    The heuristic has access to:
    - `state.allCommands` for command syntax and source positions
    - `state.input` for the original file content
    - `state.markerIdx` for the marker position
-/
def SplitHeuristic := MinState → Array Nat → IO (Array Nat × Array Nat)

/-- Default heuristic: split candidates in half by index.
    This is the standard delta debugging approach. -/
def defaultSplitHeuristic : SplitHeuristic := fun _ candidates => do
  let n := candidates.size / 2
  return (candidates[:n].toArray, candidates[n:].toArray)

/-- Get source text for a command from the original input (includes leading comments) -/
def CmdInfo.getSource (cmd : CmdInfo) (input : String) : String :=
  String.Pos.Raw.extract input cmd.startPos cmd.endPos

/-- Skip whitespace and line comments starting from a position -/
partial def skipWhitespaceAndComments (input : String) (startPos : String.Pos.Raw) (endPos : String.Pos.Raw) : String.Pos.Raw :=
  let endN := endPos.byteIdx
  let rec loop (pos : Nat) : Nat :=
    if pos >= endN then pos
    else
      let c := String.Pos.Raw.get input ⟨pos⟩
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
        loop (pos + 1)
      else if c == '-' && pos + 1 < endN && String.Pos.Raw.get input ⟨pos + 1⟩ == '-' then
        -- Line comment: skip to end of line
        let rec skipLine (p : Nat) : Nat :=
          if p >= endN then p
          else if String.Pos.Raw.get input ⟨p⟩ == '\n' then loop (p + 1)
          else skipLine (p + 1)
        skipLine (pos + 2)
      else
        pos
  ⟨loop startPos.byteIdx⟩

/-- Skip trailing whitespace and line comments, going backwards from endPos.
    Returns the position after the first newline following actual content.
    This preserves the newline separator between commands. -/
partial def skipTrailingWhitespaceAndComments (input : String) (startPos : String.Pos.Raw) (endPos : String.Pos.Raw) : String.Pos.Raw :=
  let startN := startPos.byteIdx
  -- First, find where trailing whitespace/comments start by going backwards
  let rec findContentEnd (pos : Nat) : Nat :=
    if pos <= startN then startN
    else
      let prevPos := pos - 1
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == ' ' || c == '\t' || c == '\r' then
        findContentEnd prevPos
      else if c == '\n' then
        -- Check if line before this is a comment
        let rec checkLineComment (p : Nat) : Option Nat :=
          if p <= startN then none
          else
            let pp := p - 1
            let cc := String.Pos.Raw.get input ⟨pp⟩
            if cc == '\n' then none  -- Reached previous line without finding --
            else if cc == '-' && pp > startN && String.Pos.Raw.get input ⟨pp - 1⟩ == '-' then
              some (pp - 1)  -- Found start of --
            else checkLineComment pp
        match checkLineComment prevPos with
        | some commentStart => findContentEnd commentStart
        | none => findContentEnd prevPos  -- Blank line, continue
      else
        pos  -- Found actual content
  let contentEnd := findContentEnd endPos.byteIdx
  -- Now find the first newline after contentEnd (to include it as separator)
  let rec findNewline (pos : Nat) : Nat :=
    if pos >= endPos.byteIdx then endPos.byteIdx
    else if String.Pos.Raw.get input ⟨pos⟩ == '\n' then pos + 1
    else findNewline (pos + 1)
  ⟨findNewline contentEnd⟩

/-- Get source text for just the syntax (excludes leading AND trailing comments) -/
def CmdInfo.getSyntaxSource (cmd : CmdInfo) (input : String) : String :=
  let actualStart := skipWhitespaceAndComments input cmd.startPos cmd.endPos
  let actualEnd := skipTrailingWhitespaceAndComments input cmd.startPos cmd.endPos
  String.Pos.Raw.extract input actualStart actualEnd

/-- Find where trailing whitespace and line comments end, going backwards from a position -/
partial def findHeaderEnd (input : String) (endPos : String.Pos.Raw) : String.Pos.Raw :=
  -- Go backwards from endPos to find where actual content ends
  -- We want to strip trailing whitespace and line comments
  let endN := endPos.byteIdx
  let rec loop (pos : Nat) : Nat :=
    if pos == 0 then 0
    else
      let prevPos := pos - 1
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == ' ' || c == '\t' || c == '\r' then
        loop prevPos
      else if c == '\n' then
        -- Check if the line before this newline is a comment
        let rec checkLineComment (p : Nat) : Option Nat :=
          if p == 0 then none
          else
            let pp := p - 1
            let cc := String.Pos.Raw.get input ⟨pp⟩
            if cc == '\n' then none  -- Reached previous line
            else if cc == '-' && pp > 0 && String.Pos.Raw.get input ⟨pp - 1⟩ == '-' then
              some (pp - 1)  -- Found start of --
            else checkLineComment pp
        match checkLineComment prevPos with
        | some commentStart => loop commentStart
        | none => pos  -- Not a comment line, keep newline
      else
        pos  -- Found actual content
  ⟨loop endN⟩

/-- Reconstruct source from header and selected command indices -/
def reconstructSource (state : MinState) (keepIndices : Array Nat) : String := Id.run do
  -- Include header, but strip trailing comments
  let headerEnd := findHeaderEnd state.input state.headerEndPos
  let mut result := String.Pos.Raw.extract state.input ⟨0⟩ headerEnd

  -- Track if we need to add separator
  let mut needsSep := false

  -- Add kept commands before marker (in sorted order to preserve original order)
  -- Use getSyntaxSource to strip leading comments - comments should be dropped with their command
  let sortedIndices := keepIndices.qsort (· < ·)
  for idx in sortedIndices do
    if idx < state.markerIdx then
      let cmd := state.allCommands[idx]!
      let src := cmd.getSyntaxSource state.input
      -- Add blank line between commands
      if needsSep then
        if !result.endsWith "\n" then
          result := result ++ "\n\n"
        else if !result.endsWith "\n\n" then
          result := result ++ "\n"
      result := result ++ src
      needsSep := true

  -- Always include marker and everything after (preserve full source including docstrings)
  for i in [state.markerIdx : state.allCommands.size] do
    let cmd := state.allCommands[i]!
    let src := cmd.getSyntaxSource state.input
    -- Add blank line between commands
    if needsSep then
      if !result.endsWith "\n" then
        result := result ++ "\n\n"
      else if !result.endsWith "\n\n" then
        result := result ++ "\n"
    result := result ++ src
    needsSep := true

  result

/-- Test if source compiles by running lean in a subprocess.
    This isolates memory usage - when the subprocess exits, all Lean caches are freed. -/
def testCompilesSubprocess (source : String) (fileName : String) : IO Bool := do
  -- Use a name based on input file and PID to avoid conflicts in parallel runs
  let baseName := (System.FilePath.mk fileName).fileName.getD "test"
  let pid ← IO.Process.getPID
  let tempFile := System.FilePath.mk s!"/tmp/.lean-minimize-{pid}-{baseName}"
  IO.FS.writeFile tempFile source

  -- Get environment variables for lean
  let leanPath ← IO.getEnv "LEAN_PATH"
  let leanSysroot ← IO.getEnv "LEAN_SYSROOT"
  let path ← IO.getEnv "PATH"

  let env : Array (String × Option String) := #[
    ("LEAN_PATH", leanPath),
    ("LEAN_SYSROOT", leanSysroot),
    ("PATH", path)
  ]

  -- Run lean to check compilation
  let result ← IO.Process.output {
    cmd := "lean"
    args := #[tempFile.toString]
    env := env
  }

  -- Clean up temp file
  IO.FS.removeFile tempFile

  return result.exitCode == 0

/-- Check if source compiles using subprocess, returning error output if it fails -/
def testCompilesSubprocessWithError (source : String) (fileName : String) : IO (Bool × String) := do
  -- Use a name based on input file and PID to avoid conflicts in parallel runs
  let baseName := (System.FilePath.mk fileName).fileName.getD "test"
  let pid ← IO.Process.getPID
  let tempFile := System.FilePath.mk s!"/tmp/.lean-minimize-{pid}-{baseName}"
  IO.FS.writeFile tempFile source

  -- Get environment variables for lean
  let leanPath ← IO.getEnv "LEAN_PATH"
  let leanSysroot ← IO.getEnv "LEAN_SYSROOT"
  let path ← IO.getEnv "PATH"

  let env : Array (String × Option String) := #[
    ("LEAN_PATH", leanPath),
    ("LEAN_SYSROOT", leanSysroot),
    ("PATH", path)
  ]

  -- Run lean to check compilation
  let result ← IO.Process.output {
    cmd := "lean"
    args := #[tempFile.toString]
    env := env
  }

  -- Clean up temp file
  IO.FS.removeFile tempFile

  let success := result.exitCode == 0
  -- lean prints errors to stdout, so capture both
  let errorOutput := if success then "" else (result.stdout ++ result.stderr)
  return (success, errorOutput)

/-- Check if reconstructed source compiles (using subprocess for memory isolation) -/
def testCompiles (state : MinState) (keepIndices : Array Nat) : IO Bool := do
  state.testCount.modify (· + 1)
  let source := reconstructSource state keepIndices
  testCompilesSubprocess source state.fileName

/-- Write current progress to the output file if configured -/
def writeProgress (state : MinState) (keepIndices : Array Nat) : IO Unit := do
  if let some outPath := state.outputFile then
    let source := reconstructSource state keepIndices
    IO.FS.writeFile outPath source

/-- Delta debugging algorithm to find minimal required commands.

    The `heuristic` parameter controls how candidates are split at each step.
    Use `defaultSplitHeuristic` for standard binary splitting.

    This implementation is END-BIASED: it tries to remove later commands first,
    which works better for forward-declared code where later items depend on earlier ones.

    Parameters:
    - `candidates`: indices we're trying to remove
    - `currentlyKept`: all indices currently being kept (updated as we successfully remove items)

    Returns: the final set of indices that must be kept -/
unsafe def ddminCore (heuristic : SplitHeuristic) (state : MinState)
    (candidates : Array Nat) (currentlyKept : Array Nat) : IO (Array Nat) := do
  -- Base case: no candidates to try removing
  if candidates.size == 0 then
    return currentlyKept

  if candidates.size == 1 then
    -- Try removing this single command
    let idx := candidates[0]!
    let withoutThis := currentlyKept.filter (· != idx)
    if state.verbose then
      IO.eprintln s!"  Testing: try remove [{idx}]"
    if (← testCompiles state withoutThis) then
      if state.verbose then
        IO.eprintln s!"    → Success: removed [{idx}]"
      writeProgress state withoutThis
      return withoutThis
    if state.verbose then
      IO.eprintln s!"    → Failed: must keep [{idx}]"
    return currentlyKept

  -- Use heuristic to split candidates
  let (firstHalf, secondHalf) ← heuristic state candidates

  -- END-BIASED: Try removing second half (later indices) first!
  -- This works better for forward-declared code where later items depend on earlier ones.
  let withoutSecond := currentlyKept.filter (!secondHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"  Testing: try remove {secondHalf.toList} (keep {firstHalf.toList})"
  if (← testCompiles state withoutSecond) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {secondHalf.toList}, recursing on {firstHalf.toList}"
    writeProgress state withoutSecond
    return ← ddminCore heuristic state firstHalf withoutSecond

  -- Try removing first half
  let withoutFirst := currentlyKept.filter (!firstHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"    → Failed, trying: remove {firstHalf.toList} (keep {secondHalf.toList})"
  if (← testCompiles state withoutFirst) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {firstHalf.toList}, recursing on {secondHalf.toList}"
    writeProgress state withoutFirst
    return ← ddminCore heuristic state secondHalf withoutFirst

  -- Both halves are needed; recurse on each (but skip singletons - already tested)
  -- Process second half first (end-biased), then first half with updated kept set
  if state.verbose then
    IO.eprintln s!"    → Failed: both halves needed, recursing on each"

  -- Skip singleton halves - the failed half-tests already proved they're required
  let afterSecond ← if secondHalf.size == 1 then pure currentlyKept
                    else ddminCore heuristic state secondHalf currentlyKept
  let afterFirst ← if firstHalf.size == 1 then pure afterSecond
                   else ddminCore heuristic state firstHalf afterSecond
  return afterFirst

/-- Delta debugging algorithm to find minimal required commands.

    The `heuristic` parameter controls how candidates are split at each step.
    Use `defaultSplitHeuristic` for standard binary splitting.

    Returns: the indices that must be kept (subset of candidates) -/
unsafe def ddmin (heuristic : SplitHeuristic) (state : MinState) (candidates : Array Nat) :
    IO (Array Nat) := do
  -- Start with ALL indices before marker as currently kept (not just candidates).
  -- This ensures scope commands (section/namespace/end) that aren't in candidates
  -- are still included when testing compilation.
  let allIndices := Array.range state.markerIdx
  let finalKept ← ddminCore heuristic state candidates allIndices
  -- Return only the candidates that were kept (filter out non-candidate indices like scopes)
  return finalKept.filter (candidates.contains ·)

/-- Simpler binary deletion algorithm for command deletion.
    Unlike ddmin, this never tries removing the first half as an alternative.

    Algorithm:
    - Try deleting the second half (rounding up)
    - If that works, continue on the first half
    - If that didn't work and second half was a single declaration, continue on first half
    - Otherwise, recurse: first on second half, then on first half -/
unsafe def binaryDeleteCore (heuristic : SplitHeuristic) (state : MinState)
    (candidates : Array Nat) (currentlyKept : Array Nat) : IO (Array Nat) := do
  -- Base case: no candidates to try removing
  if candidates.size == 0 then
    return currentlyKept

  if candidates.size == 1 then
    -- Try removing this single command
    let idx := candidates[0]!
    let withoutThis := currentlyKept.filter (· != idx)
    if state.verbose then
      IO.eprintln s!"  Testing: try remove [{idx}]"
    if (← testCompiles state withoutThis) then
      if state.verbose then
        IO.eprintln s!"    → Success: removed [{idx}]"
      writeProgress state withoutThis
      return withoutThis
    if state.verbose then
      IO.eprintln s!"    → Failed: must keep [{idx}]"
    return currentlyKept

  -- Use heuristic to split candidates (secondHalf rounds up)
  let (firstHalf, secondHalf) ← heuristic state candidates

  -- Try removing second half
  let withoutSecond := currentlyKept.filter (!secondHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"  Testing: try remove {secondHalf.toList} (keep {firstHalf.toList})"
  if (← testCompiles state withoutSecond) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {secondHalf.toList}, continuing on {firstHalf.toList}"
    writeProgress state withoutSecond
    return ← binaryDeleteCore heuristic state firstHalf withoutSecond

  -- Second half removal failed
  if state.verbose then
    IO.eprintln s!"    → Failed"

  if secondHalf.size == 1 then
    -- Single item can't be deleted, continue on first half only
    if state.verbose then
      IO.eprintln s!"    Single item in second half, continuing on first half"
    return ← binaryDeleteCore heuristic state firstHalf currentlyKept
  else
    -- Recurse: first on second half, then on first half
    if state.verbose then
      IO.eprintln s!"    Recursing into second half, then first half"
    let afterSecond ← binaryDeleteCore heuristic state secondHalf currentlyKept
    return ← binaryDeleteCore heuristic state firstHalf afterSecond

/-- Simpler binary deletion algorithm for command deletion.
    Entry point that sets up initial state.

    Returns: the indices that must be kept (subset of candidates) -/
unsafe def binaryDelete (heuristic : SplitHeuristic) (state : MinState) (candidates : Array Nat) :
    IO (Array Nat) := do
  -- Start with ALL indices before marker as currently kept (not just candidates).
  -- This ensures scope commands (section/namespace/end) that aren't in candidates
  -- are still included when testing compilation.
  let allIndices := Array.range state.markerIdx
  let finalKept ← binaryDeleteCore heuristic state candidates allIndices
  -- Return only the candidates that were kept (filter out non-candidate indices like scopes)
  return finalKept.filter (candidates.contains ·)

/-- Create a split heuristic that uses pre-computed reachability data.
    Commands not in `reachable` are tried for removal first.

    Since ddmin is end-biased (tries removing secondHalf first), we return
    (reachable, unreachable) so that unreachable commands are tried for removal first. -/
def precomputedDependencyHeuristic (reachable : Array Nat) : SplitHeuristic := fun state candidates => do
  let unreachable := candidates.filter fun idx => !reachable.contains idx
  let reachableInCandidates := candidates.filter fun idx => reachable.contains idx

  if state.verbose then
    IO.eprintln s!"  Pre-computed deps: {reachableInCandidates.size} reachable, {unreachable.size} likely removable"

  -- If we have both reachable and unreachable, split by reachability.
  -- Return (reachable, unreachable) so end-biased ddmin tries removing unreachable first.
  if unreachable.isEmpty || reachableInCandidates.isEmpty then
    defaultSplitHeuristic state candidates
  else
    return (reachableInCandidates, unreachable)

end LeanMinimizer
