/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass
import LeanMinimizer.Basic

/-!
# Open Argument Minimization Pass

This pass removes unnecessary arguments from `open X Y Z` and `open scoped X Y` commands.
For example, if `open Nat Int List` can be reduced to `open Nat List` while still compiling,
this pass will make that change.

Only handles basic forms:
- `open X Y Z ...` (multiple namespaces)
- `open scoped X Y ...` (scoped open with multiple namespaces)

Does NOT handle complex forms like `open X (a b c)`, `open X hiding Y`, or `open X renaming Y → Z`.
-/

namespace LeanMinimizer

open Lean

/-- An open command with its position and parsed arguments. -/
structure OpenCommand where
  /-- Start position of the entire open command (byte offset) -/
  startPos : Nat
  /-- End position of the entire open command (byte offset, excluding trailing newline) -/
  endPos : Nat
  /-- Whether this is `open scoped` -/
  isScoped : Bool
  /-- The namespace arguments -/
  args : Array String
  deriving Repr

/-- Generate a memory key for an open argument removal attempt. -/
def openArgMemoryKey (cmdPos : Nat) (argName : String) : String :=
  s!"open-arg:{cmdPos}:{argName}"

/-- Check if a line contains complex open syntax that we should skip. -/
def isComplexOpenLine (line : String) : Bool :=
  line.containsSubstr "hiding" ||
  line.containsSubstr "renaming" ||
  line.containsSubstr "(" ||
  line.containsSubstr ")"

/-- Parse an open command line into an OpenCommand structure.
    Returns none if the line is not a basic open command or is too complex. -/
def parseOpenCommand (line : String) (lineStartPos : Nat) : Option OpenCommand := do
  let trimmed := line.trimAsciiStart.toString

  -- Must start with "open "
  if !trimmed.startsWith "open " then failure

  -- Skip complex forms
  if isComplexOpenLine trimmed then failure

  -- Check if it's `open scoped`
  let (isScoped, afterKeyword) := if trimmed.startsWith "open scoped " then
    (true, (trimmed.drop 12).trimAsciiStart.toString)
  else
    (false, (trimmed.drop 5).trimAsciiStart.toString)

  -- Split remaining text into arguments (namespace names)
  -- Stop at newline or end of string
  let argsPart := afterKeyword.takeWhile (· != '\n')
  let args := argsPart.split (· == ' ') |>.filter (!·.isEmpty) |>.map (·.toString) |>.toArray

  if args.isEmpty then failure

  -- Calculate end position (line start + line length without trailing newline)
  let lineWithoutNewline := line.trimAscii.toString
  let endPos := lineStartPos + lineWithoutNewline.rawEndPos.byteIdx

  return {
    startPos := lineStartPos
    endPos := endPos
    isScoped := isScoped
    args := args
  }

/-- Reconstruct an open command text from its components. -/
def reconstructOpenCommand (isScoped : Bool) (args : Array String) : String :=
  let openPrefix := if isScoped then "open scoped " else "open "
  openPrefix ++ String.intercalate " " args.toList

/-- Find all open commands in the source before the marker position.
    Returns array of (lineStartPos, line, OpenCommand). -/
def findOpenCommands (source : String) (markerPos : Nat) :
    Array (Nat × String × OpenCommand) := Id.run do
  let mut result : Array (Nat × String × OpenCommand) := #[]
  let mut lineStart : Nat := 0
  let endPos := min markerPos source.rawEndPos.byteIdx

  let mut i : Nat := 0
  while i < endPos do
    -- Find end of line
    let mut lineEnd := i
    while lineEnd < endPos && String.Pos.Raw.get source ⟨lineEnd⟩ != '\n' do
      lineEnd := lineEnd + 1

    -- Extract line (include newline if present)
    let line := String.Pos.Raw.extract source ⟨lineStart⟩ (if lineEnd < source.rawEndPos.byteIdx then ⟨lineEnd + 1⟩ else ⟨lineEnd⟩)

    -- Try to parse as open command
    if let some cmd := parseOpenCommand line lineStart then
      result := result.push (lineStart, line, cmd)

    -- Move to next line
    i := lineEnd + 1
    lineStart := i

  return result

/-- Find the position of a substring in a string, returning the byte offset. -/
def findOpenSubstrPos (source : String) (needle : String) : Option Nat := Id.run do
  let sourceLen := source.rawEndPos.byteIdx
  let needleLen := needle.rawEndPos.byteIdx
  if needleLen > sourceLen then return none
  for i in [:sourceLen - needleLen + 1] do
    let candidate := String.Pos.Raw.extract source ⟨i⟩ ⟨i + needleLen⟩
    if candidate == needle then return some i
  return none

/-- The open argument minimization pass.

    Tries to remove individual arguments from `open X Y Z` and `open scoped X Y` commands.
    Uses memory to avoid retrying failed removals. -/
unsafe def openMinimizationPass : Pass where
  name := "Open Minimization"
  cliFlag := "open-minimization"
  run := fun ctx => do
    -- Find marker position (byte offset)
    let markerPos : Nat := ctx.steps.find? (·.idx == ctx.markerIdx) |>.map (·.startPos.byteIdx) |>.getD ctx.source.rawEndPos.byteIdx

    -- Find all open commands before marker
    let openCmds := findOpenCommands ctx.source markerPos

    if openCmds.isEmpty then
      return { source := ctx.source, changed := false, action := .continue }

    if ctx.verbose then
      IO.eprintln s!"  Found {openCmds.size} open commands to check"

    let mut currentSource := ctx.source
    let mut anyChanged := false
    let mut newFailedChanges : Array String := #[]

    for (cmdPos, originalLine, cmd) in openCmds do
      -- Skip if only one argument (can't remove it)
      if cmd.args.size <= 1 then continue

      -- Try removing each argument
      for h : argIdx in [:cmd.args.size] do
        let arg := cmd.args[argIdx]
        let memKey := openArgMemoryKey cmdPos arg

        -- Skip if already known to fail
        if ctx.failedChanges.contains memKey then continue

        -- Create new args array without this argument
        let newArgs := cmd.args.eraseIdx argIdx

        -- Skip if would leave no arguments (shouldn't happen due to size check, but be safe)
        if newArgs.isEmpty then continue

        -- Reconstruct the open command
        let newCmdText := reconstructOpenCommand cmd.isScoped newArgs

        -- Find and replace in current source
        -- We need to find the original line in current source (positions may have shifted)
        let trimmedOriginal := originalLine.trimAscii.toString
        if let some pos := findOpenSubstrPos currentSource trimmedOriginal then
          let newSourceCandidate :=
            String.Pos.Raw.extract currentSource ⟨0⟩ ⟨pos⟩ ++
            newCmdText ++
            String.Pos.Raw.extract currentSource ⟨pos + trimmedOriginal.rawEndPos.byteIdx⟩ currentSource.rawEndPos

          if ← testCompilesSubprocess newSourceCandidate ctx.fileName then
            if ctx.verbose then
              IO.eprintln s!"    Removed '{arg}' from open command"
            currentSource := newSourceCandidate
            anyChanged := true
            -- Don't break - try removing more args from this command
          else
            newFailedChanges := newFailedChanges.push memKey

    if !anyChanged then
      return { source := ctx.source, changed := false, action := .continue,
               newFailedChanges := newFailedChanges }

    -- Repeat to catch any further opportunities
    return { source := currentSource, changed := true, action := .repeat,
             newFailedChanges := newFailedChanges }

end LeanMinimizer
