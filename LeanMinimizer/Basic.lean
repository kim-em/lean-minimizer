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

  --verbose
    Print progress information during minimization.

  --no-module-removal
    Disable the module system removal pass.

  --no-delete
    Disable the command deletion pass.

  --no-import-minimization
    Disable the import minimization pass.

  --no-import-inlining
    Disable the import inlining pass.

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
  verbose : Bool := false
  help : Bool := false
  /-- Disable the module system removal pass -/
  noModuleRemoval : Bool := false
  /-- Disable the deletion pass -/
  noDelete : Bool := false
  /-- Disable the import minimization pass -/
  noImportMinimization : Bool := false
  /-- Disable the import inlining pass -/
  noImportInlining : Bool := false

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
    | "--verbose" :: rest => go rest { acc with verbose := true }
    | "--marker" :: pattern :: rest => go rest { acc with marker := pattern }
    | "--marker" :: [] => .error "--marker requires an argument"
    | "--no-delete" :: rest => go rest { acc with noDelete := true }
    | "--no-module-removal" :: rest => go rest { acc with noModuleRemoval := true }
    | "--no-import-minimization" :: rest => go rest { acc with noImportMinimization := true }
    | "--no-import-inlining" :: rest => go rest { acc with noImportInlining := true }
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
      -- Add newline separator between commands if needed
      if needsSep && !result.endsWith "\n" then
        result := result ++ "\n"
      result := result ++ src
      -- Add extra blank line after section/namespace end statements
      if cmd.stx.isOfKind `Lean.Parser.Command.end then
        result := result ++ "\n"
      needsSep := true

  -- Always include marker and everything after (preserve full source including docstrings)
  for i in [state.markerIdx : state.allCommands.size] do
    let cmd := state.allCommands[i]!
    let src := cmd.getSyntaxSource state.input
    if needsSep && !result.endsWith "\n" then
      result := result ++ "\n"
    result := result ++ src
    needsSep := true

  result

/-- Test if source compiles by running lean in a subprocess.
    This isolates memory usage - when the subprocess exits, all Lean caches are freed. -/
def testCompilesSubprocess (source : String) (_fileName : String) : IO Bool := do
  -- Create temp file (fileName is kept for API compatibility but not used in temp path)
  let tempFile := System.FilePath.mk s!"/tmp/lean-minimize-test-{← IO.monoMsNow}.lean"
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

/-- Check if reconstructed source compiles (using subprocess for memory isolation) -/
def testCompiles (state : MinState) (keepIndices : Array Nat) : IO Bool := do
  state.testCount.modify (· + 1)
  let source := reconstructSource state keepIndices
  testCompilesSubprocess source state.fileName

/-- Delta debugging algorithm to find minimal required commands.

    The `heuristic` parameter controls how candidates are split at each step.
    Use `defaultSplitHeuristic` for standard binary splitting. -/
unsafe def ddmin (heuristic : SplitHeuristic) (state : MinState) (candidates : Array Nat) :
    IO (Array Nat) := do
  -- Base case: empty or single element
  if candidates.size == 0 then
    return #[]

  if candidates.size == 1 then
    -- Try removing this single command
    if state.verbose then
      IO.eprintln s!"  Testing: try remove [{candidates[0]!}]"
    let others := (Array.range state.markerIdx).filter (· ∉ candidates)
    if (← testCompiles state others) then
      if state.verbose then
        IO.eprintln s!"    → Success: removed [{candidates[0]!}]"
      return #[]
    if state.verbose then
      IO.eprintln s!"    → Failed: must keep [{candidates[0]!}]"
    return candidates

  -- Use heuristic to split candidates
  let (firstHalf, secondHalf) ← heuristic state candidates

  if state.verbose then
    IO.eprintln s!"  Testing: try remove {firstHalf.toList} (keep {secondHalf.toList})"

  -- Try keeping only second half (removing first half)
  let withoutFirst := (Array.range state.markerIdx).filter (!firstHalf.contains ·)
  if (← testCompiles state withoutFirst) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {firstHalf.toList}, recursing on {secondHalf.toList}"
    return ← ddmin heuristic state secondHalf

  if state.verbose then
    IO.eprintln s!"    → Failed, trying: remove {secondHalf.toList} (keep {firstHalf.toList})"

  -- Try keeping only first half (removing second half)
  let withoutSecond := (Array.range state.markerIdx).filter (!secondHalf.contains ·)
  if (← testCompiles state withoutSecond) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {secondHalf.toList}, recursing on {firstHalf.toList}"
    return ← ddmin heuristic state firstHalf

  -- Both halves are needed; recurse on each
  if state.verbose then
    IO.eprintln s!"    → Failed: both halves needed, recursing on each"

  let keptFirst ← ddmin heuristic state firstHalf
  let keptSecond ← ddmin heuristic state secondHalf
  return keptFirst ++ keptSecond

/-- Create a split heuristic that uses pre-computed reachability data.
    Commands not in `reachable` are tried for removal first. -/
def precomputedDependencyHeuristic (reachable : Array Nat) : SplitHeuristic := fun state candidates => do
  -- Only use dependency info at top level; fall back to default for recursive calls
  if candidates.size < state.markerIdx then
    defaultSplitHeuristic state candidates
  else
    let unreachable := candidates.filter fun idx => !reachable.contains idx
    let reachableInCandidates := candidates.filter fun idx => reachable.contains idx

    if state.verbose then
      IO.eprintln s!"  Pre-computed deps: {reachable.size} reachable, {unreachable.size} likely removable"

    if unreachable.isEmpty || reachableInCandidates.isEmpty then
      defaultSplitHeuristic state candidates
    else
      return (unreachable, reachableInCandidates)

end LeanMinimizer
