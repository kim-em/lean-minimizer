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
    Default: \"invariant\"

  --verbose
    Print progress information during minimization.

  --help
    Show this help message.

Example:
  lake exe minimize test.lean --marker \"KEEP BELOW\"

The tool will find the first command containing the marker pattern and
remove as many commands before it as possible while keeping the file
compilable.
"

/-- Parsed command line arguments -/
structure Args where
  file : String
  marker : String := "invariant"
  verbose : Bool := false
  help : Bool := false

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

/-- Check if `needle` is a substring of `haystack` -/
partial def containsSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else
    let rec loop (i : Nat) : Bool :=
      if i + needle.length > haystack.length then false
      else if haystack.extract ⟨i⟩ ⟨i + needle.length⟩ == needle then true
      else loop (i + 1)
    loop 0

/-- Information about a parsed command -/
structure CmdInfo where
  /-- Index in the command array -/
  idx : Nat
  /-- The parsed syntax -/
  stx : Syntax
  /-- Start position in the source file -/
  startPos : String.Pos
  /-- End position in the source file (including trailing whitespace) -/
  endPos : String.Pos
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
  headerEndPos : String.Pos
  /-- All commands (before + invariant) -/
  allCommands : Array CmdInfo
  /-- Index of the marker command -/
  markerIdx : Nat
  /-- Whether to print verbose output -/
  verbose : Bool
  /-- Counter for compilation tests -/
  testCount : IO.Ref Nat

/-- Get source text for a command from the original input -/
def CmdInfo.getSource (cmd : CmdInfo) (input : String) : String :=
  input.extract cmd.startPos cmd.endPos

/-- Parse a file into header and commands with positions -/
unsafe def parseFileCommands (input : String) (fileName : String) :
    IO (Syntax × String.Pos × Array CmdInfo) := do
  let inputCtx := Parser.mkInputContext input fileName

  -- Parse header
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  if messages.hasErrors then
    throw <| IO.userError "File has errors in header/imports"

  -- Get header end position from parser state
  let headerEndPos := parserState.pos

  -- Parse commands (without elaborating)
  let env ← mkEmptyEnvironment
  let mut commands : Array CmdInfo := #[]
  let mut pstate := parserState
  let mut idx := 0
  let mut prevEndPos := headerEndPos

  while true do
    let pmctx : ParserModuleContext := {
      env := env
      options := {}
      currNamespace := Name.anonymous
      openDecls := []
    }

    let (cmd, pstate', _) := Parser.parseCommand inputCtx pmctx pstate {}
    pstate := pstate'

    if Parser.isTerminalCommand cmd then
      break

    let endPos := pstate.pos
    commands := commands.push {
      idx := idx
      stx := cmd
      startPos := prevEndPos  -- Include leading whitespace from previous
      endPos := endPos
    }
    prevEndPos := endPos
    idx := idx + 1

  return (header, headerEndPos, commands)

/-- Find the index of the marker command -/
def findMarkerIdx (commands : Array CmdInfo) (input : String) (marker : String) : Option Nat :=
  commands.findIdx? fun cmd =>
    let src := cmd.getSource input
    containsSubstr src marker

/-- Reconstruct source from header and selected command indices -/
def reconstructSource (state : MinState) (keepIndices : Array Nat) : String := Id.run do
  -- Always include header (from start of file to headerEndPos)
  let mut result := state.input.extract ⟨0⟩ state.headerEndPos

  -- Add kept commands before marker
  for idx in keepIndices do
    if idx < state.markerIdx then
      let cmd := state.allCommands[idx]!
      result := result ++ cmd.getSource state.input

  -- Always include marker and everything after
  for i in [state.markerIdx : state.allCommands.size] do
    let cmd := state.allCommands[i]!
    result := result ++ cmd.getSource state.input

  result

/-- Check if reconstructed source compiles -/
unsafe def testCompiles (state : MinState) (keepIndices : Array Nat) : IO Bool := do
  state.testCount.modify (· + 1)
  let source := reconstructSource state keepIndices

  let inputCtx := Parser.mkInputContext source state.fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  if messages.hasErrors then
    return false

  let (env, messages) ← processHeader header {} messages inputCtx
  if messages.hasErrors then
    return false

  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  return !s.commandState.messages.hasErrors

/-- Delta debugging algorithm to find minimal required commands -/
unsafe def ddmin (state : MinState) (candidates : Array Nat) : IO (Array Nat) := do
  -- Base case: empty or single element
  if candidates.size == 0 then
    return #[]

  if candidates.size == 1 then
    -- Try removing this single command
    let others := (Array.range state.markerIdx).filter (· ∉ candidates)
    if (← testCompiles state others) then
      if state.verbose then
        IO.eprintln s!"  Removed command {candidates[0]!}"
      return #[]
    return candidates

  -- Split into two halves
  let n := candidates.size / 2
  let firstHalf := candidates[:n].toArray
  let secondHalf := candidates[n:].toArray

  if state.verbose then
    IO.eprintln s!"  Testing split: {firstHalf.size} + {secondHalf.size} commands"

  -- Try keeping only second half (removing first half)
  let withoutFirst := (Array.range state.markerIdx).filter (!firstHalf.contains ·)
  if (← testCompiles state withoutFirst) then
    if state.verbose then
      IO.eprintln s!"  First half removable, recursing on second half"
    return ← ddmin state secondHalf

  -- Try keeping only first half (removing second half)
  let withoutSecond := (Array.range state.markerIdx).filter (!secondHalf.contains ·)
  if (← testCompiles state withoutSecond) then
    if state.verbose then
      IO.eprintln s!"  Second half removable, recursing on first half"
    return ← ddmin state firstHalf

  -- Both halves are needed; recurse on each
  if state.verbose then
    IO.eprintln s!"  Both halves needed, recursing on each"

  let keptFirst ← ddmin state firstHalf
  let keptSecond ← ddmin state secondHalf
  return keptFirst ++ keptSecond

/-- Main minimization function -/
unsafe def minimize (input : String) (fileName : String) (marker : String) (verbose : Bool) :
    IO String := do
  if verbose then
    IO.eprintln s!"Parsing {fileName}..."

  let (header, headerEndPos, commands) ← parseFileCommands input fileName

  if verbose then
    IO.eprintln s!"Found {commands.size} commands"

  -- Find marker
  let some markerIdx := findMarkerIdx commands input marker
    | throw <| IO.userError s!"Marker pattern '{marker}' not found in any command"

  if verbose then
    IO.eprintln s!"Marker found at command {markerIdx}"
    IO.eprintln s!"Commands before marker: {markerIdx}"

  -- Initialize state
  let testCount ← IO.mkRef 0
  let state : MinState := {
    input, fileName, header, headerEndPos
    allCommands := commands
    markerIdx
    verbose
    testCount
  }

  -- Verify original file compiles
  let allIndices := Array.range markerIdx
  if !(← testCompiles state allIndices) then
    throw <| IO.userError "Original file does not compile"

  if verbose then
    IO.eprintln "Original file compiles, starting minimization..."

  -- Run ddmin on commands before marker
  let keptIndices ← ddmin state allIndices

  let finalTestCount ← testCount.get
  let removed := markerIdx - keptIndices.size

  if verbose then
    IO.eprintln ""
    IO.eprintln s!"Minimization complete:"
    IO.eprintln s!"  Compilation tests: {finalTestCount}"
    IO.eprintln s!"  Commands removed: {removed} of {markerIdx}"
    IO.eprintln s!"  Commands kept: {keptIndices.size}"

  let result := reconstructSource state keptIndices
  return result

end LeanMinimizer
