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

/-- Resolve a module name to a file path within the project.
    Only resolves project-local modules, not external libraries. -/
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

  -- Build file path
  let mut filePath := root
  for component in components do
    filePath := filePath / component
  filePath := filePath.withExtension "lean"

  -- Check if exists
  if ← filePath.pathExists then
    return some filePath
  else
    return none

/-- Merge imports: remove the inlined import, add the module's imports, deduplicate. -/
def mergeImports (original : Array ImportInfo) (toRemove : ImportInfo)
    (toAdd : Array ImportInfo) : Array ImportInfo := Id.run do
  let mut result := original.filter fun x => x.moduleName != toRemove.moduleName

  -- Add new imports, avoiding duplicates by module name
  for imp in toAdd do
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

/-- Track open scopes from source text (without parsing).
    Uses simple text matching for namespace/section/end keywords.
    Returns array of scope names that need end statements. -/
def trackOpenScopesFromText (body : String) : Array String := Id.run do
  let mut scopeStack : Array String := #[]
  let lines := body.splitOn "\n"

  for line in lines do
    let trimmed := line.trimAsciiStart.toString
    -- Check for namespace
    if trimmed.startsWith "namespace " then
      let rest := (trimmed.drop 10).trimAsciiStart.toString
      -- Extract identifier (first word)
      let ident := (rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '.')).toString
      if !ident.isEmpty then
        scopeStack := scopeStack.push ident
    -- Check for section
    else if trimmed.startsWith "section " then
      let rest := (trimmed.drop 8).trimAsciiStart.toString
      let ident := (rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '.')).toString
      if ident.isEmpty then
        scopeStack := scopeStack.push ""
      else
        scopeStack := scopeStack.push ident
    else if trimmed == "section" || trimmed.startsWith "section\n" || trimmed.startsWith "section " && (trimmed.drop 8).trimAsciiStart.toString.isEmpty then
      -- Anonymous section
      scopeStack := scopeStack.push ""
    -- Check for end
    else if trimmed.startsWith "end " || trimmed == "end" then
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
    let usesModule := headerUsesModuleSystem ctx.header
    let hasPrelude := headerHasPrelude ctx.header
    let imports := extractImports ctx.header

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
            if ctx.verbose then
              IO.eprintln s!"    Inlining breaks compilation, skipping"
        catch e =>
          if ctx.verbose then
            IO.eprintln s!"    Error analyzing module: {e}, skipping"

    -- No imports could be inlined
    if ctx.verbose then
      IO.eprintln "  No imports could be inlined"
    return { source := ctx.source, changed := false, action := .continue }

end LeanMinimizer
