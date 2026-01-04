/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Text Substitution Pass

This pass performs various text substitutions to simplify minimized files.
All mini-passes are batched together - if any makes changes, we restart.
Replacements are only applied above the invariant section (marker command).

Mini-passes:
1. Comment removal (/- ... -/, /-- ... -/, -- ...)
2. lemma → theorem
3. Type* → Type _
4. Type _ / Type u → Type
5. ℕ → Nat, ℤ → Int, ℚ → Rat
6. Attribute removal (@[...])
7. Modifier removal (unsafe/protected/private/noncomputable)
8. Priority removal (from attributes and instances)
-/

namespace LeanMinimizer

open Lean

/-! ## Core infrastructure -/

/-- A text replacement: position range and what to replace it with -/
structure Replacement where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  replacement : String
  deriving Repr

/-- Apply a single replacement to source -/
def applyReplacement (source : String) (r : Replacement) : String :=
  let before := String.Pos.Raw.extract source ⟨0⟩ r.startPos
  let after := String.Pos.Raw.extract source r.endPos source.rawEndPos
  before ++ r.replacement ++ after

/-- Apply multiple replacements (must be sorted descending by position) -/
def applyReplacements (source : String) (rs : Array Replacement) : String :=
  rs.foldl (init := source) fun s r => applyReplacement s r

/-- A mini-pass finds replacements in source -/
structure MiniPass where
  name : String
  findReplacements : String → Array Replacement
  /-- If true, don't filter out replacements inside comments (for comment removal pass) -/
  skipCommentFilter : Bool := false

/-! ## String scanning helpers -/

/-- Check if a character is an identifier character -/
def isIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- Compute array of (start, end) byte positions for all comments in source.
    Includes line comments (-- ...) and block comments (/- ... -/).
    Also includes string literals. -/
partial def computeCommentRanges (source : String) : Array (Nat × Nat) := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    let c := String.Pos.Raw.get source ⟨i⟩
    -- Line comment: -- to end of line
    if c == '-' && i + 1 < endPos && String.Pos.Raw.get source ⟨i + 1⟩ == '-' then
      let start := i
      i := i + 2
      while i < endPos && String.Pos.Raw.get source ⟨i⟩ != '\n' do
        i := i + 1
      result := result.push (start, i)
    -- Block comment: /- to -/
    else if c == '/' && i + 1 < endPos && String.Pos.Raw.get source ⟨i + 1⟩ == '-' then
      let start := i
      i := i + 2
      let mut depth := 1
      while i < endPos && depth > 0 do
        if i + 1 < endPos then
          let c1 := String.Pos.Raw.get source ⟨i⟩
          let c2 := String.Pos.Raw.get source ⟨i + 1⟩
          if c1 == '/' && c2 == '-' then
            depth := depth + 1
            i := i + 2
            continue
          else if c1 == '-' && c2 == '/' then
            depth := depth - 1
            i := i + 2
            continue
        i := i + 1
      result := result.push (start, i)
    -- String literal: " to " (handle escapes)
    else if c == '"' then
      let start := i
      i := i + 1
      while i < endPos do
        let sc := String.Pos.Raw.get source ⟨i⟩
        if sc == '\\' && i + 1 < endPos then
          i := i + 2  -- Skip escaped char
        else if sc == '"' then
          i := i + 1
          break
        else
          i := i + 1
      result := result.push (start, i)
    else
      i := i + 1
  return result

/-- Check if a byte position is inside any of the given ranges -/
def isInsideRanges (pos : Nat) (ranges : Array (Nat × Nat)) : Bool :=
  ranges.any fun (start, stop) => pos >= start && pos < stop

/-- Check if character at given byte position is a word boundary.
    A word boundary exists if the character before `pos` is not an id char
    and the character at `pos + len` is not an id char. -/
def isWordBoundaryAt (s : String) (pos : Nat) (len : Nat) : Bool :=
  let endPos := s.rawEndPos.byteIdx
  let before := if pos == 0 then true
    else
      let prevPos := pos - 1
      if prevPos < endPos then
        !isIdChar (String.Pos.Raw.get s ⟨prevPos⟩)
      else true
  let after :=
    let nextPos := pos + len
    if nextPos < endPos then
      !isIdChar (String.Pos.Raw.get s ⟨nextPos⟩)
    else true
  before && after

/-- Check if source starting at byte position matches the given needle -/
def matchesAt (source : String) (pos : Nat) (needle : String) : Bool :=
  if pos + needle.utf8ByteSize > source.rawEndPos.byteIdx then false
  else
    let slice := String.Pos.Raw.extract source ⟨pos⟩ ⟨pos + needle.utf8ByteSize⟩
    slice == needle

/-- Skip whitespace starting at position, return new position -/
def skipWhitespace (source : String) (pos : Nat) : Nat :=
  let endPos := source.rawEndPos.byteIdx
  let rec loop (p : Nat) : Nat :=
    if p >= endPos then p
    else
      let c := String.Pos.Raw.get source ⟨p⟩
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
        loop (p + 1)
      else p
  loop pos

/-- Find matching bracket, handling nesting. Returns position after closing bracket.
    Starts at position after the opening bracket. -/
partial def findMatchingBracket (source : String) (pos : Nat) : Option Nat :=
  let endPos := source.rawEndPos.byteIdx
  let rec loop (p : Nat) (depth : Nat) : Option Nat :=
    if p >= endPos then none
    else
      let c := String.Pos.Raw.get source ⟨p⟩
      if c == '[' then loop (p + 1) (depth + 1)
      else if c == ']' then
        if depth == 0 then some (p + 1)
        else loop (p + 1) (depth - 1)
      else loop (p + 1) depth
  loop pos 0

/-- Find matching paren, handling nesting. Returns position after closing paren.
    Starts at position after the opening paren. -/
partial def findMatchingParen (source : String) (pos : Nat) : Option Nat :=
  let endPos := source.rawEndPos.byteIdx
  let rec loop (p : Nat) (depth : Nat) : Option Nat :=
    if p >= endPos then none
    else
      let c := String.Pos.Raw.get source ⟨p⟩
      if c == '(' then loop (p + 1) (depth + 1)
      else if c == ')' then
        if depth == 0 then some (p + 1)
        else loop (p + 1) (depth - 1)
      else loop (p + 1) depth
  loop pos 0

/-- Scan for identifier starting at position. Returns (endPos, ident) or none. -/
def scanIdent (source : String) (pos : Nat) : Option (Nat × String) :=
  let endPos := source.rawEndPos.byteIdx
  if pos >= endPos then none
  else
    let firstChar := String.Pos.Raw.get source ⟨pos⟩
    if !firstChar.isAlpha && firstChar != '_' then none
    else
      let rec loop (p : Nat) : Nat :=
        if p >= endPos then p
        else
          let c := String.Pos.Raw.get source ⟨p⟩
          if isIdChar c then loop (p + 1)
          else p
      let identEnd := loop (pos + 1)
      some (identEnd, String.Pos.Raw.extract source ⟨pos⟩ ⟨identEnd⟩)

/-! ## Mini-pass implementations -/

/-- Find all comments: block comments (including docstrings), and line comments -/
def findCommentReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    -- Block comments: /- (catches /-, /--, /--!, etc.)
    if matchesAt source i "/-" then
      let start := i
      i := i + 2
      let mut depth := 1
      -- Find matching -/ (handling nested comments)
      while i < endPos && depth > 0 do
        if i + 1 < endPos then
          let c1 := String.Pos.Raw.get source ⟨i⟩
          let c2 := String.Pos.Raw.get source ⟨i + 1⟩
          if c1 == '/' && c2 == '-' then
            depth := depth + 1
            i := i + 2
            continue
          else if c1 == '-' && c2 == '/' then
            depth := depth - 1
            i := i + 2
            continue
        i := i + 1
      -- Consume trailing whitespace (including newlines)
      while i < endPos do
        let c := String.Pos.Raw.get source ⟨i⟩
        if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
          i := i + 1
        else
          break
      result := result.push { startPos := ⟨start⟩, endPos := ⟨i⟩, replacement := "" }
    -- Single-line comments: --
    else if matchesAt source i "--" then
      -- Walk back to include leading whitespace on the same line (stop at newline or non-whitespace)
      let mut start := i
      while start > 0 do
        let prevChar := String.Pos.Raw.get source ⟨start - 1⟩
        if prevChar == ' ' || prevChar == '\t' then
          start := start - 1
        else
          break
      -- Only include leading whitespace if the previous char was a newline (comment is on its own line)
      -- Otherwise, keep the whitespace (e.g., `foo := 1  -- comment`)
      let finalStart := if start > 0 && String.Pos.Raw.get source ⟨start - 1⟩ != '\n' then i else start
      i := i + 2
      -- Find end of line
      while i < endPos && String.Pos.Raw.get source ⟨i⟩ != '\n' do
        i := i + 1
      -- Include the newline if present
      if i < endPos then
        i := i + 1
      result := result.push { startPos := ⟨finalStart⟩, endPos := ⟨i⟩, replacement := "" }
    else
      i := i + 1
  return result

/-- Find all occurrences of `lemma` keyword -/
def findLemmaReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    if matchesAt source i "lemma" && isWordBoundaryAt source i 5 then
      result := result.push { startPos := ⟨i⟩, endPos := ⟨i + 5⟩, replacement := "theorem" }
      i := i + 5
    else
      i := i + 1
  return result

/-- Find all occurrences of `Type*` -/
def findTypeStarReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    if matchesAt source i "Type" && isWordBoundaryAt source i 4 then
      -- Skip whitespace after Type
      let afterType := skipWhitespace source (i + 4)
      -- Check for *
      if afterType < endPos && String.Pos.Raw.get source ⟨afterType⟩ == '*' then
        result := result.push { startPos := ⟨i⟩, endPos := ⟨afterType + 1⟩, replacement := "Type _" }
        i := afterType + 1
      else
        i := i + 4
    else
      i := i + 1
  return result

/-- Find all occurrences of `Type _` or `Type u` (simple universe variable) -/
def findTypeUniverseReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    if matchesAt source i "Type" && isWordBoundaryAt source i 4 then
      -- Must have whitespace after Type
      let afterType := i + 4
      if afterType < endPos then
        let c := String.Pos.Raw.get source ⟨afterType⟩
        if c == ' ' || c == '\t' then
          let afterWs := skipWhitespace source afterType
          if afterWs < endPos then
            let nextChar := String.Pos.Raw.get source ⟨afterWs⟩
            -- Check for `_`
            if nextChar == '_' then
              let afterUnderscore := afterWs + 1
              -- Make sure _ is not followed by more identifier chars
              if afterUnderscore >= endPos || !isIdChar (String.Pos.Raw.get source ⟨afterUnderscore⟩) then
                result := result.push { startPos := ⟨i⟩, endPos := ⟨afterUnderscore⟩, replacement := "Type" }
                i := afterUnderscore
                continue
            -- Check for simple lowercase identifier (universe variable)
            else if nextChar.isLower then
              if let some (identEnd, _) := scanIdent source afterWs then
                -- Make sure it's not followed by more complex universe expression
                let afterIdent := skipWhitespace source identEnd
                if afterIdent >= endPos ||
                   (String.Pos.Raw.get source ⟨afterIdent⟩ != '+' &&
                    !matchesAt source afterIdent "max" &&
                    !matchesAt source afterIdent "imax") then
                  result := result.push { startPos := ⟨i⟩, endPos := ⟨identEnd⟩, replacement := "Type" }
                  i := identEnd
                  continue
      i := i + 4
    else
      i := i + 1
  return result

/-- Find all occurrences of Unicode number type symbols -/
def findUnicodeReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    -- ℕ is E2 84 95 in UTF-8
    if i + 2 < endPos then
      let b0 := source.toUTF8[i]!
      let b1 := source.toUTF8[i+1]!
      let b2 := source.toUTF8[i+2]!
      if b0 == 0xE2 && b1 == 0x84 then
        if b2 == 0x95 then  -- ℕ
          result := result.push { startPos := ⟨i⟩, endPos := ⟨i + 3⟩, replacement := "Nat" }
          i := i + 3
          continue
        else if b2 == 0xA4 then  -- ℤ
          result := result.push { startPos := ⟨i⟩, endPos := ⟨i + 3⟩, replacement := "Int" }
          i := i + 3
          continue
        else if b2 == 0x9A then  -- ℚ
          result := result.push { startPos := ⟨i⟩, endPos := ⟨i + 3⟩, replacement := "Rat" }
          i := i + 3
          continue
    i := i + 1
  return result

/-- Find all attribute blocks @[...] -/
def findAttributeReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    if matchesAt source i "@[" then
      if let some closeBracket := findMatchingBracket source (i + 2) then
        -- Also consume trailing whitespace (but not newlines)
        let mut afterAttr := closeBracket
        while afterAttr < endPos do
          let c := String.Pos.Raw.get source ⟨afterAttr⟩
          if c == ' ' || c == '\t' then
            afterAttr := afterAttr + 1
          else
            break
        result := result.push { startPos := ⟨i⟩, endPos := ⟨afterAttr⟩, replacement := "" }
        i := afterAttr
      else
        i := i + 2
    else
      i := i + 1
  return result

/-- Find all modifier keywords (unsafe, protected, private, noncomputable) -/
def findModifierReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let modifiers := #["unsafe", "protected", "private", "noncomputable"]
  let mut i := 0
  while i < endPos do
    let mut found := false
    for modifier in modifiers do
      if matchesAt source i modifier && isWordBoundaryAt source i modifier.utf8ByteSize then
        -- Consume trailing whitespace
        let afterMod := skipWhitespace source (i + modifier.utf8ByteSize)
        result := result.push { startPos := ⟨i⟩, endPos := ⟨afterMod⟩, replacement := "" }
        i := afterMod
        found := true
        break
    if !found then
      i := i + 1
  return result

/-- Find priority specifications in attributes: @[simp 100] → @[simp] -/
def findAttributePriorityReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    if matchesAt source i "@[" then
      -- Inside attribute, look for "identifier number" pattern
      if let some closeBracket := findMatchingBracket source (i + 2) then
        -- Scan inside the attribute for identifier followed by number
        let mut j := i + 2
        while j < closeBracket - 1 do
          if let some (identEnd, _) := scanIdent source j then
            -- Check if followed by whitespace and number
            let afterIdent := skipWhitespace source identEnd
            if afterIdent < closeBracket - 1 then
              let c := String.Pos.Raw.get source ⟨afterIdent⟩
              if c.isDigit then
                -- Found a number, scan to end of number
                let mut numEnd := afterIdent
                while numEnd < closeBracket - 1 && (String.Pos.Raw.get source ⟨numEnd⟩).isDigit do
                  numEnd := numEnd + 1
                -- Replace the space+number with nothing
                result := result.push { startPos := ⟨identEnd⟩, endPos := ⟨numEnd⟩, replacement := "" }
                j := numEnd
                continue
            j := identEnd
          else
            j := j + 1
        i := closeBracket
      else
        i := i + 2
    else
      i := i + 1
  return result

/-- Find instance priority specifications: (priority := ...) -/
def findInstancePriorityReplacements (source : String) : Array Replacement := Id.run do
  let mut result := #[]
  let endPos := source.rawEndPos.byteIdx
  let mut i := 0
  while i < endPos do
    if matchesAt source i "(priority" then
      -- Check for := after optional whitespace
      let afterPriority := skipWhitespace source (i + 9)
      if matchesAt source afterPriority ":=" then
        -- Find matching paren
        if let some closeParen := findMatchingParen source (i + 1) then
          -- Also consume trailing whitespace (but not newlines)
          let mut afterParen := closeParen
          while afterParen < endPos do
            let c := String.Pos.Raw.get source ⟨afterParen⟩
            if c == ' ' || c == '\t' then
              afterParen := afterParen + 1
            else
              break
          result := result.push { startPos := ⟨i⟩, endPos := ⟨afterParen⟩, replacement := "" }
          i := afterParen
          continue
    i := i + 1
  return result

/-! ## Main pass -/

/-- All mini-passes to run.
    Order matters: comment removal first, priority removal before attribute removal. -/
def miniPasses : Array MiniPass := #[
  { name := "Comment removal", findReplacements := findCommentReplacements, skipCommentFilter := true },
  { name := "lemma→theorem", findReplacements := findLemmaReplacements },
  { name := "Type*→Type _", findReplacements := findTypeStarReplacements },
  { name := "Type _/Type u→Type", findReplacements := findTypeUniverseReplacements },
  { name := "Unicode symbols", findReplacements := findUnicodeReplacements },
  { name := "Attribute priorities", findReplacements := findAttributePriorityReplacements },
  { name := "Instance priorities", findReplacements := findInstancePriorityReplacements },
  { name := "Attribute removal", findReplacements := findAttributeReplacements },
  { name := "Modifier removal", findReplacements := findModifierReplacements }
]

/-- Compute a memory key for a replacement -/
def replacementKey (source : String) (r : Replacement) : String :=
  let oldText := String.Pos.Raw.extract source r.startPos r.endPos
  s!"text:{oldText}→{r.replacement}"

/-- Try replacements: all at once first, then one-by-one from bottom up.
    Returns (newSource?, newlyFailedKeys).
    Skips replacements that are already in failedChanges. -/
def tryReplacements (source : String) (replacements : Array Replacement)
    (fileName : String) (verbose : Bool)
    (failedChanges : Std.HashSet String) : IO (Option String × Array String) := do
  if replacements.isEmpty then
    return (none, #[])

  -- Sort by position descending (so we apply from bottom to top)
  let sorted := replacements.qsort (fun a b => a.startPos.byteIdx > b.startPos.byteIdx)

  -- Filter out replacements that are already in memory (known to fail)
  let filtered := sorted.filter fun r =>
    let key := replacementKey source r
    !failedChanges.contains key

  if filtered.isEmpty then
    if verbose then
      IO.eprintln s!"      All {sorted.size} replacements already in memory, skipping"
    return (none, #[])

  let skippedCount := sorted.size - filtered.size
  if skippedCount > 0 && verbose then
    IO.eprintln s!"      Skipping {skippedCount} replacements from memory"

  -- Try all at once (only with filtered replacements)
  let allAtOnce := applyReplacements source filtered
  if ← testCompilesSubprocess allAtOnce fileName then
    if verbose then
      IO.eprintln s!"      Applied all {filtered.size} replacements at once"
    return (some allAtOnce, #[])

  -- Try one by one from bottom up
  let mut currentSource := source
  let mut anyChanged := false
  let mut failedKeys : Array String := #[]
  for r in filtered do
    let key := replacementKey currentSource r
    let newSource := applyReplacement currentSource r
    if ← testCompilesSubprocess newSource fileName then
      currentSource := newSource
      anyChanged := true
    else
      -- Record this as a failed change
      failedKeys := failedKeys.push key

  if anyChanged then
    return (some currentSource, failedKeys)
  else
    return (none, failedKeys)

/-- The text substitution pass.

    Runs all mini-passes in sequence. If any makes changes, restarts. -/
def textSubstitutionPass : Pass where
  name := "Text Substitution"
  cliFlag := "text-subst"
  run := fun ctx => do
    let mut source := ctx.source
    let mut anyChanged := false
    let mut allFailedKeys : Array String := #[]

    if ctx.verbose then
      IO.eprintln "  Running text substitution mini-passes..."

    -- Get the position of the invariant section (marker command)
    let markerPos := if h : ctx.markerIdx < ctx.subprocessCommands.size then
      ctx.subprocessCommands[ctx.markerIdx].startPos
    else
      source.utf8ByteSize  -- Fallback: allow whole file

    for miniPass in miniPasses do
      let allReplacements := miniPass.findReplacements source
      -- Apply comment filter unless this pass removes comments
      let replacements := if miniPass.skipCommentFilter then
        allReplacements
      else
        -- Compute comment ranges for current source (must recompute after each change)
        let commentRanges := computeCommentRanges source
        allReplacements.filter fun r => !isInsideRanges r.startPos.byteIdx commentRanges
      -- Filter out replacements at or after the invariant section
      let replacements := replacements.filter fun r => r.startPos.byteIdx < markerPos
      if !replacements.isEmpty then
        if ctx.verbose then
          IO.eprintln s!"    {miniPass.name}: found {replacements.size} potential replacements"
        let (result, failedKeys) ← tryReplacements source replacements ctx.fileName ctx.verbose ctx.failedChanges
        allFailedKeys := allFailedKeys ++ failedKeys
        if let some newSource := result then
          source := newSource
          anyChanged := true

    if anyChanged then
      if ctx.verbose then
        IO.eprintln "  Text substitution made changes, restarting"
      return { source, changed := true, action := .restart, newFailedChanges := allFailedKeys }
    else
      if ctx.verbose then
        IO.eprintln "  No text substitutions possible"
      return { source, changed := false, action := .continue, newFailedChanges := allFailedKeys }

end LeanMinimizer
