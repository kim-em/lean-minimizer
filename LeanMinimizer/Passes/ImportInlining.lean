/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass
import LeanMinimizer.Passes.ImportMinimization

/-!
# Import Inlining Pass

This pass inlines `import X.Y.Z` statements by replacing them with the module's content
wrapped in `section X.Y.Z ... end X.Y.Z`.

The pass:
1. Finds project-local module files
2. Extracts their content (stripping headers)
3. Merges their imports with the main file
4. Wraps the content in a section
5. Adds required `end` statements for any open scopes
6. Returns `.restart` to allow deletion/minimization of newly inlined code
-/

namespace LeanMinimizer

open Lean Elab Frontend Parser System

/-- Find the project root by searching upward for lakefile.toml -/
partial def findProjectRoot (startPath : FilePath) : IO (Option FilePath) := do
  let lakefile := startPath / "lakefile.toml"
  if ← lakefile.pathExists then
    return some startPath
  else
    match startPath.parent with
    | none => return none  -- Reached root without finding lakefile.toml
    | some parent => findProjectRoot parent

/-- Convert a Name to path components.
    Example: `Foo.Bar.Baz` → `["Foo", "Bar", "Baz"]` -/
def nameToPathComponents (name : Name) : List String :=
  let rec go (n : Name) (acc : List String) : List String :=
    match n with
    | Name.anonymous => acc
    | Name.str p s => go p (s :: acc)
    | Name.num p _ => go p acc  -- Skip numeric components
  go name []

/-- Build a file path from components -/
def buildModulePath (root : FilePath) (components : List String) : FilePath :=
  (components.foldl (· / ·) root).withExtension "lean"

/-- Resolve a module name to a file path.
    Searches both project-local modules and dependencies in .lake/packages/. -/
def resolveModulePath (modName : Name) (currentFile : String) : IO (Option FilePath) := do
  -- Convert name to path components
  let components := nameToPathComponents modName
  if components.isEmpty then
    return none

  -- Convert to absolute path if relative
  let currentFilePath := FilePath.mk currentFile
  let absolutePath ←
    if currentFilePath.isAbsolute then
      pure currentFilePath
    else
      -- Make it absolute relative to current working directory
      let cwd ← IO.currentDir
      pure (cwd / currentFilePath)

  -- Find project root
  let some parent := absolutePath.parent
    | return none
  let some root ← findProjectRoot parent
    | return none

  -- Try 1: Check in project root
  let projectPath := buildModulePath root components
  if ← projectPath.pathExists then
    return some projectPath

  -- Try 2: Check in .lake/packages/
  let packagesDir := root / ".lake" / "packages"
  if ← packagesDir.pathExists then
    -- List all package directories
    let entries ← packagesDir.readDir
    for entry in entries do
      if ← entry.path.isDir then
        let pkgPath := buildModulePath entry.path components
        if ← pkgPath.pathExists then
          return some pkgPath

  return none

/-- Merge imports: remove the inlined import, add the module's imports, deduplicate. -/
def mergeImports (original : Array ImportInfo) (toRemove : ImportInfo)
    (toAdd : Array ImportInfo) : Array ImportInfo := Id.run do
  let mut result := original.filter fun x => x.moduleName != toRemove.moduleName

  -- Add new imports, avoiding duplicates by module name
  -- Skip Init as it's always implicitly available
  for imp in toAdd do
    if imp.moduleName == `Init then
      continue
    let alreadyPresent := result.any fun x => x.moduleName == imp.moduleName
    if !alreadyPresent then
      result := result.push imp

  return result

/-- Track open scopes in an array of commands.
    Returns array of scope names that need end statements. -/
def trackOpenScopes (commands : Array Syntax) : Array String := Id.run do
  let mut scopeStack : Array String := #[]

  for cmd in commands do
    -- Check what kind of command this is
    if cmd.isOfKind `Lean.Parser.Command.namespace then
      -- namespace <ident>
      if cmd.getNumArgs > 1 then
        let identArg := cmd[1]!
        if identArg.isIdent then
          scopeStack := scopeStack.push identArg.getId.toString
    else if cmd.isOfKind `Lean.Parser.Command.section then
      -- section <ident>?
      if cmd.getNumArgs > 1 then
        let identArg := cmd[1]!
        if identArg.isIdent then
          scopeStack := scopeStack.push identArg.getId.toString
        else if identArg.isNone || identArg.isMissing then
          -- Anonymous section
          scopeStack := scopeStack.push ""
      else
        -- Anonymous section
        scopeStack := scopeStack.push ""
    else if cmd.isOfKind `Lean.Parser.Command.end then
      -- end <ident>?
      if !scopeStack.isEmpty then
        scopeStack := scopeStack.pop

  return scopeStack

/-- Find the index of the closing bracket `]` matching the opening bracket at position `start`.
    Returns `none` if no matching bracket is found. Handles nested brackets.
    Used for stripping attributes like @[expose]. -/
def findAttrClosingBracket (s : String) (start : Nat) : Option Nat := Id.run do
  let chars := s.toList
  if start >= chars.length then return none
  let mut depth := 1
  for i in [start + 1 : chars.length] do
    let c := chars[i]!
    if c == '[' then depth := depth + 1
    else if c == ']' then
      depth := depth - 1
      if depth == 0 then return some i
  return none

/-- Strip leading attributes (@[...]) and modifiers (public, private, protected, scoped)
    from a line of source code. Used to normalize lines before checking for section/namespace. -/
def stripAttributesAndModifiers (line : String) : String := Id.run do
  let mut s := line

  -- Strip leading attributes: @[...] (potentially nested brackets)
  while s.startsWith "@[" do
    if let some endIdx := findAttrClosingBracket s 1 then
      s := (s.drop (endIdx + 1)).trimAsciiStart.toString
    else
      break -- Malformed attribute, stop stripping

  -- Strip modifiers (can appear in sequence): visibility, scoped, noncomputable, partial, unsafe, meta
  let mut changed := true
  while changed do
    changed := false
    for modifier in ["public ", "private ", "protected ", "scoped ", "noncomputable ", "partial ", "unsafe ", "meta "] do
      if s.startsWith modifier then
        s := (s.drop modifier.length).trimAsciiStart.toString
        changed := true
        break

  return s

/-- Strip block comments, line comments, and string literals from source text,
    preserving newlines. Handles nested block comments (`/- /- ... -/ -/`).
    This ensures that scope keywords inside comments or strings are not
    incorrectly counted. -/
def stripComments (s : String) : String := Id.run do
  let chars := s.toList.toArray
  let mut result := ""
  let mut i := 0
  let mut depth : Nat := 0  -- Block comment nesting depth
  let mut inLineComment := false
  let mut inString := false  -- Inside a string literal
  while i < chars.size do
    let c := chars[i]!
    if inString then
      -- Inside string literal: look for closing quote or escape
      if c == '\\' && i + 1 < chars.size then
        -- Skip escaped character
        i := i + 2
      else if c == '"' then
        inString := false
        i := i + 1
      else
        if c == '\n' then result := result.push '\n'
        i := i + 1
    else if inLineComment then
      if c == '\n' then
        inLineComment := false
        result := result.push '\n'
      i := i + 1
    else if depth > 0 then
      -- Inside block comment: look for nested /- or closing -/
      if c == '/' && i + 1 < chars.size && chars[i + 1]! == '-' then
        depth := depth + 1
        i := i + 2
      else if c == '-' && i + 1 < chars.size && chars[i + 1]! == '/' then
        depth := depth - 1
        i := i + 2
      else
        -- Preserve newlines to maintain line structure
        if c == '\n' then result := result.push '\n'
        i := i + 1
    else
      -- Outside any comment or string
      if c == '"' then
        inString := true
        i := i + 1
      else if c == '/' && i + 1 < chars.size && chars[i + 1]! == '-' then
        depth := depth + 1
        i := i + 2
      else if c == '-' && i + 1 < chars.size && chars[i + 1]! == '-' then
        inLineComment := true
        i := i + 2
      else
        result := result.push c
        i := i + 1
  return result

/-- Sentinel value used internally to track `mutual` blocks on the scope stack,
    so that the `end` for a `mutual` block doesn't incorrectly consume a
    section/namespace entry. -/
private def mutualSentinel : String := "⟨mutual⟩"

/-- Track open scopes from source text (without parsing).
    Uses simple text matching for namespace/section/end keywords.
    Returns array of scope names that need end statements.

    Handles:
    - Block comments (nested) and line comments are stripped first
    - `mutual...end` blocks tracked so their `end` doesn't consume section/namespace -/
def trackOpenScopesFromText (body : String) : Array String := Id.run do
  -- Strip comments first to avoid false matches inside comments
  let cleanBody := stripComments body
  let mut scopeStack : Array String := #[]
  let lines := cleanBody.splitOn "\n"

  for line in lines do
    let trimmed := line.trimAsciiStart.toString
    -- Strip attributes and modifiers to handle lines like "@[expose] public section"
    let stripped := stripAttributesAndModifiers trimmed

    -- Check for namespace
    if stripped.startsWith "namespace " then
      let rest := (stripped.drop 10).trimAsciiStart.toString
      -- Extract identifier (first word)
      let ident := (rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '.')).toString
      if !ident.isEmpty then
        scopeStack := scopeStack.push ident
    -- Check for section (with or without name)
    -- Handle "section", "section ", "section Name"
    else if stripped == "section" then
      -- Anonymous section
      scopeStack := scopeStack.push ""
    else if stripped.startsWith "section " then
      -- "section " - extract name if present
      let rest := (stripped.drop 8).trimAsciiStart.toString
      let ident := (rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '.')).toString
      scopeStack := scopeStack.push ident
    -- Check for mutual (track so its 'end' doesn't consume section/namespace entries)
    -- Use trimAscii to handle trailing whitespace left after comment stripping
    else if stripped.trimAscii.toString == "mutual" then
      scopeStack := scopeStack.push mutualSentinel
    -- Check for end
    else if stripped.startsWith "end " || stripped == "end" then
      if !scopeStack.isEmpty then
        scopeStack := scopeStack.pop

  -- Filter out mutual sentinels - only return section/namespace scopes
  return scopeStack.filter (· != mutualSentinel)

/-- Analyze a module file for inlining WITHOUT elaboration.
    Returns: (header syntax, body content, open scopes at end) -/
def analyzeModuleForInlining (source : String) (fileName : String) :
    IO (Syntax × String × Array String) := do
  let inputCtx := Parser.mkInputContext source fileName

  -- Parse header only (no processHeader = no elaboration)
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  if messages.hasErrors then
    throw <| IO.userError "Module has header errors"

  -- Find where header ends (strip trailing whitespace/comments)
  let headerEndPos := findHeaderEnd source parserState.pos

  -- Extract body (everything after header)
  let body := String.Pos.Raw.extract source headerEndPos source.rawEndPos

  -- Track open scopes using text-based matching (no elaboration needed)
  let openScopes := trackOpenScopesFromText body

  return (header, body, openScopes)

/-- Remove `assert_not_exists` lines from module body.
    These assertions can fail after import merging when the asserted
    declaration becomes available via other imports. -/
def stripAssertNotExists (body : String) : String := Id.run do
  let lines := body.splitOn "\n"
  let filteredLines := lines.filter fun line =>
    let trimmed := line.trimAsciiStart.toString
    !trimmed.startsWith "assert_not_exists "
  "\n".intercalate filteredLines

/-- Build source with inlined import.
    Parameters:
    - usesModule: whether original file uses module system
    - hasPrelude: whether original file has prelude
    - newImports: merged import list
    - inlinedModuleName: name of module being inlined
    - moduleBody: body content from inlined module
    - openScopes: scopes that need to be closed
    - commandsPart: original file's commands (post-header)
    - stripModifiers: whether to strip import modifiers
-/
def buildInlinedSource
    (usesModule : Bool) (hasPrelude : Bool)
    (newImports : Array ImportInfo) (inlinedModuleName : Name)
    (moduleBody : String) (openScopes : Array String)
    (commandsPart : String) (stripModifiers : Bool) : String := Id.run do

  let mut result := ""

  -- 1. Reconstruct header with merged imports
  result := result ++ reconstructHeader usesModule hasPrelude newImports stripModifiers

  -- 2. Open section for inlined module
  result := result ++ s!"section {inlinedModuleName}\n"

  -- 3. Add module body
  result := result ++ moduleBody

  -- Ensure body ends with newline for proper formatting
  if !moduleBody.isEmpty && !moduleBody.back == '\n' then
    result := result ++ "\n"

  -- 4. Close open scopes from module (in reverse order)
  for scope in openScopes.reverse do
    if scope.isEmpty then
      result := result ++ "end\n"
    else
      result := result ++ s!"end {scope}\n"

  -- 5. Close inlined section
  result := result ++ s!"end {inlinedModuleName}\n\n"

  -- 6. Append original commands
  result := result ++ commandsPart

  return result

/-- Test if a source string compiles successfully (using subprocess for memory isolation). -/
def testSourceCompilesInline (source : String) (fileName : String) : IO Bool :=
  testCompilesSubprocess source fileName

/-- Check if a line starts a trivial command (open, variable, set_option, attribute, comment).
    These are skipped when finding the temp marker for parsimonious restarts. -/
def isTrivialCommandLine (line : String) : Bool :=
  let trimmed := line.trimAsciiStart.toString
  trimmed.isEmpty ||
  trimmed.startsWith "--" ||
  trimmed.startsWith "/-" ||
  trimmed.startsWith "open " ||
  trimmed == "open" ||
  trimmed.startsWith "variable " ||
  trimmed == "variable" ||
  trimmed.startsWith "set_option " ||
  trimmed.startsWith "attribute " ||
  trimmed.startsWith "universe " ||
  trimmed == "universe" ||
  trimmed.startsWith "noncomputable " ||
  trimmed == "noncomputable"

/-- Find the first non-trivial command line for use as temp marker.
    Skips: open, variable, set_option, attribute, universe, comments, blank lines.
    Returns the first line of the first non-trivial command, or none if all are trivial. -/
def findFirstNontrivialCommand (commandsPart : String) : Option String := Id.run do
  let lines := commandsPart.splitOn "\n"
  for line in lines do
    if !isTrivialCommandLine line then
      -- Return this line (trimmed) as the marker
      -- We return the whole line to maximize uniqueness
      let trimmed := line.trimAscii.toString
      if !trimmed.isEmpty then
        return some trimmed
  return none

/-! ## Inlined Block Error Recovery

When inlining an import's content produces compilation errors within the inlined block,
these functions attempt to recover by removing problematic declarations or fields. -/

/-- Parse error line numbers from lean compiler output.
    Error format: tempfile:line:col: error: ... -/
def parseInlineErrorLines (output : String) : Array Nat := Id.run do
  let mut resultSet : Std.HashSet Nat := {}
  for line in output.splitOn "\n" do
    if line.containsSubstr ": error:" then
      let parts := line.splitOn ":"
      if parts.length >= 2 then
        if let some lineNum := parts[1]?.bind (·.trimAscii.toString.toNat?) then
          resultSet := resultSet.insert lineNum
  return resultSet.toArray

/-- Find the line range of the inlined block (section Name ... end Name).
    Returns (startLine, endLine) as 1-indexed line numbers, inclusive. -/
def findInlinedBlockRange (source : String) (moduleName : Name) :
    Option (Nat × Nat) := Id.run do
  let sectionMarker := s!"section {moduleName}"
  let endMarker := s!"end {moduleName}"
  let lines := source.splitOn "\n"
  let mut startLine : Option Nat := none
  let mut endLine : Option Nat := none
  for i in [:lines.length] do
    let trimmed := lines[i]!.trimAscii.toString
    if startLine.isNone && trimmed == sectionMarker then
      startLine := some (i + 1)
    -- Keep updating endLine to find the *last* matching `end` marker,
    -- in case the module body itself closes an identically-named scope.
    else if startLine.isSome && trimmed == endMarker then
      endLine := some (i + 1)
  match startLine, endLine with
  | some s, some e => some (s, e)
  | _, _ => none

/-- Check if a line looks like a structure/instance field assignment or definition.
    Pattern: indented line starting with an identifier, followed by `:=` or `:`.
    Examples: `  one_mul := Submodule.one_mul`, `  __ := instNonUnitalSemiring`,
              `  bot_le _ := bot_le`, `  bar : Baz` -/
def isFieldLikeLine (line : String) : Bool := Id.run do
  if line.isEmpty then return false
  -- Must be indented (starts with whitespace)
  if line == line.trimAsciiStart.toString then return false
  let trimmed := line.trimAsciiStart.toString
  if trimmed.isEmpty then return false
  -- First token should be identifier-like
  let firstToken := (trimmed.takeWhile (fun c => c.isAlphanum || c == '_')).toString
  if firstToken.isEmpty then return false
  -- Exclude proof/program keywords that also match the identifier + `:=`/`:` pattern
  if firstToken ∈ ["have", "let", "show", "suffices", "calc", "match", "if", "do",
                    "where", "return", "fun", "intro", "apply", "exact", "simp",
                    "rw", "constructor", "cases", "induction", "obtain"] then
    return false
  -- Must have := or : after the identifier (possibly with patterns in between)
  let rest := (trimmed.drop firstToken.length).toString
  return rest.containsSubstr ":=" ||
    rest.trimAsciiStart.toString.startsWith ":"

/-- Check if a line is "top-level" within the inlined block body:
    non-empty, not indented, and not a comment. -/
def isBlockTopLevel (line : String) : Bool := Id.run do
  if line.isEmpty then return false
  if line != line.trimAsciiStart.toString then return false
  let trimmed := line.trimAsciiStart.toString
  if trimmed.startsWith "--" || trimmed.startsWith "/-" then return false
  -- Exclude continuation keywords that can appear flush-left but belong to previous decl
  for kw in ["| ", "where", "termination_by", "decreasing_by", "deriving ", "with"] do
    if trimmed.startsWith kw || trimmed == kw.trimAscii.toString then return false
  return true

/-- Find the line range of the declaration enclosing the given error line.
    Declarations are delimited by non-indented, non-comment lines ("top-level" lines).
    Returns (startLine, endLine) as 1-indexed line numbers, inclusive. -/
def findEnclosingDeclaration (lines : Array String) (errorLine : Nat)
    (blockStart blockEnd : Nat) : Nat × Nat := Id.run do
  -- Block body (excluding section/end markers) is blockStart+1 to blockEnd-1
  let bodyStart := blockStart + 1
  let bodyEnd := blockEnd - 1

  -- Scan backward from error line to find declaration start
  let mut declStart := bodyStart
  for j in [:errorLine - bodyStart + 1] do
    let lineNum := errorLine - j
    if lineNum < bodyStart then break
    if lineNum > 0 && lineNum <= lines.size then
      if isBlockTopLevel lines[lineNum - 1]! then
        declStart := lineNum
        break

  -- Scan forward from error line + 1 to find next top-level line
  let mut declEnd := bodyEnd
  for lineNum in [errorLine + 1 : bodyEnd + 1] do
    if lineNum > 0 && lineNum <= lines.size then
      if isBlockTopLevel lines[lineNum - 1]! then
        declEnd := lineNum - 1
        break

  return (declStart, declEnd)

/-- Try to fix an inlined block by removing declarations/fields with errors.
    Called when inlining produces compilation errors.

    Algorithm:
    1. Parse error locations from compiler output
    2. For errors in the inlined block: delete field-like lines individually,
       or delete entire declarations for other errors
    3. Test if the result compiles -/
def tryFixInlinedBlock (source : String) (errorOutput : String) (fileName : String)
    (moduleName : Name) (verbose : Bool) : IO (Option String) := do
  let mut currentSource := source
  let mut currentErrors := errorOutput
  -- Iterate: fix errors, recompile, fix new errors, until stable or we give up.
  -- Cap iterations to avoid unbounded loops.
  for _ in [:20] do
    -- Parse error line numbers
    let errorLines := parseInlineErrorLines currentErrors
    if errorLines.isEmpty then return none

    -- Find the inlined block range (recomputed each iteration since source changes)
    let some (blockStart, blockEnd) := findInlinedBlockRange currentSource moduleName
      | return none

    -- Filter to errors within the inlined block (between section and end markers)
    let blockErrors := errorLines.filter fun n => n > blockStart && n < blockEnd
    if blockErrors.isEmpty then
      if verbose then
        IO.eprintln s!"    No errors in inlined block (all {errorLines.size} errors are outside)"
      return none

    if verbose then
      IO.eprintln s!"    Found {blockErrors.size} errors in inlined block, attempting recovery..."

    -- Process each error - determine what to delete
    let lines := currentSource.splitOn "\n" |>.toArray
    let mut linesToDelete : Std.HashSet Nat := {}

    for errLine in blockErrors do
      -- Skip if this line is already marked for deletion
      if linesToDelete.contains errLine then continue
      if errLine == 0 || errLine > lines.size then continue
      let line := lines[errLine - 1]!
      if isFieldLikeLine line then
        -- Field-like line: delete just this line
        if verbose then
          IO.eprintln s!"      Line {errLine}: deleting field '{line.trimAscii.toString}'"
        linesToDelete := linesToDelete.insert errLine
      else
        -- Non-field: delete the enclosing declaration
        let (declStart, declEnd) := findEnclosingDeclaration lines errLine blockStart blockEnd
        if verbose then
          IO.eprintln s!"      Line {errLine}: deleting declaration (lines {declStart}-{declEnd})"
        for lineNum in [declStart : declEnd + 1] do
          linesToDelete := linesToDelete.insert lineNum

    if linesToDelete.isEmpty then return none

    -- Apply deletions
    let mut resultLines := #[]
    for i in [:lines.size] do
      if !linesToDelete.contains (i + 1) then
        resultLines := resultLines.push lines[i]!
    let fixedSource := "\n".intercalate resultLines.toList

    if verbose then
      IO.eprintln s!"    Deleted {linesToDelete.size} lines, testing compilation..."

    -- Test if it compiles now
    let (compiled, newErrors) ← testCompilesSubprocessWithError fixedSource fileName
    if compiled then
      if verbose then
        IO.eprintln s!"    Recovery successful!"
      return some fixedSource
    -- Not yet — loop with the new errors
    currentSource := fixedSource
    currentErrors := newErrors

  if verbose then
    IO.eprintln s!"    Recovery failed (errors remain after max iterations)"
  return none

/-- The import inlining pass.

    Iteratively tries to inline imports one at a time, returning `.restart` after each
    successful inlining to allow deletion and minimization of the newly inlined code.

    If inlining a particular import fails (compilation test fails), we try the next one.
    Only if ALL imports fail to inline do we report a fatal error. This handles cases
    where import order matters. -/
unsafe def importInliningPass : Pass where
  name := "Import Inlining"
  cliFlag := "import-inlining"
  run := fun ctx => do
    -- Use subprocess-provided flags when available, otherwise check syntax
    let usesModule := ctx.hasModule || headerUsesModuleSystem ctx.header
    let hasPrelude := ctx.hasPrelude || headerHasPrelude ctx.header
    -- Use subprocess-provided imports when available
    let imports := getImportsFromContext ctx

    if imports.isEmpty then
      if ctx.verbose then
        IO.eprintln "  No imports to inline"
      return { source := ctx.source, changed := false, action := .continue }

    if ctx.verbose then
      IO.eprintln s!"  Analyzing {imports.size} imports for inlining..."

    -- Get the commands part (everything after the header)
    -- Trim leading whitespace so we can control spacing consistently
    let commandsRaw := String.Pos.Raw.extract ctx.source ctx.headerEndPos ctx.source.rawEndPos
    let commandsPart := commandsRaw.trimAsciiStart.toString

    -- Whether to strip modifiers when generating imports
    let stripModifiers := !usesModule

    -- Track imports that failed compilation (not just couldn't be found/analyzed)
    let mut compilationFailures : Array (Name × String) := #[]

    -- Try to inline each import (using indexed loop to avoid ForIn issues)
    for i in [:imports.size] do
      let imp := imports[i]!
      if ctx.verbose then
        IO.eprintln s!"  Trying to inline import {imp.moduleName}..."

      -- Try to resolve module path
      let modulePathOpt ← resolveModulePath imp.moduleName ctx.fileName
      match modulePathOpt with
      | none =>
        if ctx.verbose then
          IO.eprintln s!"    Module file not found, skipping"
      | some modulePath =>
        try
          -- Read module file
          let moduleSource ← IO.FS.readFile modulePath

          -- Analyze module
          let (moduleHeader, moduleBody, openScopes) ←
            analyzeModuleForInlining moduleSource (modulePath.toString)

          -- Extract module imports
          let moduleImports := extractImports moduleHeader

          -- Build new import list
          let newImports := mergeImports imports imp moduleImports

          -- Strip assert_not_exists commands which can fail after import merging
          let cleanModuleBody := stripAssertNotExists moduleBody

          -- Build new source
          let newSource := buildInlinedSource usesModule hasPrelude newImports
                                              imp.moduleName cleanModuleBody openScopes
                                              commandsPart stripModifiers

          -- Test compilation (capture error output for recovery)
          let (compiled, errorOutput) ← testCompilesSubprocessWithError newSource ctx.fileName
          if compiled then
            if ctx.verbose then
              IO.eprintln s!"    Successfully inlined {imp.moduleName}"
            return { source := newSource, changed := true, action := .restart }
          else
            -- Compilation failed - try to fix by removing problematic declarations/fields
            if let some fixedSource ← tryFixInlinedBlock newSource errorOutput ctx.fileName
                                        imp.moduleName ctx.verbose then
              if ctx.verbose then
                IO.eprintln s!"    Successfully inlined {imp.moduleName} (with error recovery)"
              return { source := fixedSource, changed := true, action := .restart }
            -- Recovery also failed - record and try the next import
            -- (import order might matter in some cases)
            if ctx.verbose then
              IO.eprintln s!"    Compilation failed after inlining, trying next import"
            compilationFailures := compilationFailures.push (imp.moduleName, newSource)
        catch e =>
          if ctx.verbose then
            IO.eprintln s!"    Error analyzing module: {e}, skipping"

    -- Check if we had compilation failures but no successes
    if !compilationFailures.isEmpty then
      -- All attempted inlinings failed - this is fatal
      IO.eprintln s!"\n\nFATAL: All {compilationFailures.size} import inlining attempts failed."
      IO.eprintln s!"Failed imports: {compilationFailures.map (·.1)}"
      IO.eprintln s!"This should never happen - import inlining should always succeed."
      -- Write the last failed source to output for debugging
      if let some outPath := ctx.outputFile then
        if let some (_, lastSource) := compilationFailures.back? then
          IO.FS.writeFile outPath lastSource
          IO.eprintln s!"The last failed source has been written to the output file for debugging."
      IO.Process.exit 1

    -- No imports could be inlined (none found or all had analysis errors)
    if ctx.verbose then
      IO.eprintln "  No imports could be inlined"
    return { source := ctx.source, changed := false, action := .continue }

end LeanMinimizer
