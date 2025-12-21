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

  -- Strip modifiers (can appear in sequence): public, private, protected, scoped, meta
  let mut changed := true
  while changed do
    changed := false
    for modifier in ["public ", "private ", "protected ", "scoped ", "meta "] do
      if s.startsWith modifier then
        s := (s.drop modifier.length).trimAsciiStart.toString
        changed := true
        break

  return s

/-- Track open scopes from source text (without parsing).
    Uses simple text matching for namespace/section/end keywords.
    Returns array of scope names that need end statements. -/
def trackOpenScopesFromText (body : String) : Array String := Id.run do
  let mut scopeStack : Array String := #[]
  let lines := body.splitOn "\n"

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
    -- Check for end
    else if stripped.startsWith "end " || stripped == "end" then
      if !scopeStack.isEmpty then
        scopeStack := scopeStack.pop

  return scopeStack

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

/-- The import inlining pass.

    Iteratively tries to inline imports one at a time, returning `.restart` after each
    successful inlining to allow deletion and minimization of the newly inlined code. -/
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

          -- Build new source
          let newSource := buildInlinedSource usesModule hasPrelude newImports
                                              imp.moduleName moduleBody openScopes
                                              commandsPart stripModifiers

          -- Test compilation
          if ← testSourceCompilesInline newSource ctx.fileName then
            if ctx.verbose then
              IO.eprintln s!"    Successfully inlined {imp.moduleName}"
            return { source := newSource, changed := true, action := .restart }
          else
            -- Fatal error: import inlining should theoretically always succeed
            if let some outPath := ctx.outputFile then
              IO.FS.writeFile outPath newSource
            IO.eprintln s!"\n\nFATAL: Import inlining failed for {imp.moduleName}"
            IO.eprintln s!"This should never happen - import inlining should always succeed."
            IO.eprintln s!"The failed source has been written to the output file for debugging."
            IO.Process.exit 1
        catch e =>
          if ctx.verbose then
            IO.eprintln s!"    Error analyzing module: {e}, skipping"

    -- No imports could be inlined
    if ctx.verbose then
      IO.eprintln "  No imports could be inlined"
    return { source := ctx.source, changed := false, action := .continue }

end LeanMinimizer
