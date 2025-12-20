/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Import Minimization Pass

This pass iteratively tries to remove or inline imports until a fixed point is reached.
For each import, it attempts:
1. Remove the import entirely
2. Replace the import with its own imports (from the environment)

When inlining imports, modifiers are stripped if the file is not using the module system.
-/

namespace LeanMinimizer

open Lean Elab Frontend Parser

/-- Information about a single import in the header -/
structure ImportInfo where
  /-- The module name being imported -/
  moduleName : Name
  /-- Whether this is a `public` import -/
  isPublic : Bool := false
  /-- Whether this is a `meta` import -/
  isMeta : Bool := false
  /-- Whether this is an `import all` -/
  isAll : Bool := false
  deriving Repr, BEq, Hashable, Inhabited

/-- Check if the header uses the module system (has `module` keyword) -/
def headerUsesModuleSystem (header : Syntax) : Bool :=
  if header.getNumArgs > 0 then
    let moduleOpt := header[0]!
    !moduleOpt.isNone && !moduleOpt.isMissing
  else
    false

/-- Check if the header has prelude -/
def headerHasPrelude (header : Syntax) : Bool :=
  if header.getNumArgs > 1 then
    let preludeOpt := header[1]!
    !preludeOpt.isNone && !preludeOpt.isMissing
  else
    false

/-- Check if syntax is a token with given value -/
def isTokenWithVal (stx : Syntax) (val : String) : Bool :=
  match stx with
  | .atom _ v => v == val
  | _ => false

/-- Extract import information from import syntax.
    Import syntax: `public? meta? import all? ident` -/
def parseImportSyntax (importStx : Syntax) : Option ImportInfo := do
  let mut isPublic := false
  let mut isMeta := false
  let mut isAll := false
  let mut modName : Option Name := none

  for i in [:importStx.getNumArgs] do
    let child := importStx[i]!
    -- Check for tokens
    if isTokenWithVal child "public" then isPublic := true
    else if isTokenWithVal child "meta" then isMeta := true
    else if isTokenWithVal child "all" then isAll := true
    else if isTokenWithVal child "import" then pure ()  -- skip the import keyword
    else if child.isIdent then
      modName := some child.getId
    else if !child.isNone && !child.isMissing then
      -- Check nested structure for optional modifiers or ident
      for j in [:child.getNumArgs] do
        let nested := child[j]!
        if isTokenWithVal nested "public" then isPublic := true
        else if isTokenWithVal nested "meta" then isMeta := true
        else if isTokenWithVal nested "all" then isAll := true
        else if nested.isIdent then
          modName := some nested.getId

  let name ← modName
  return { moduleName := name, isPublic, isMeta, isAll }

/-- Extract all imports from a header syntax -/
def extractImports (header : Syntax) : Array ImportInfo := Id.run do
  let mut result := #[]
  if header.getNumArgs > 2 then
    let imports := header[2]!
    for i in [:imports.getNumArgs] do
      let importStx := imports[i]!
      if let some info := parseImportSyntax importStx then
        result := result.push info
  return result

/-- Convert an Import from the environment to ImportInfo -/
def leanImportToInfo (imp : Import) : ImportInfo :=
  { moduleName := imp.module
    isPublic := imp.isExported  -- isExported=true means public
    isMeta := imp.isMeta
    isAll := imp.importAll }

/-- Render an ImportInfo as a string.
    If `stripModifiers` is true, all modifiers are removed. -/
def renderImport (info : ImportInfo) (stripModifiers : Bool) : String :=
  if stripModifiers then
    s!"import {info.moduleName}\n"
  else
    let pub := if info.isPublic then "public " else ""
    let met := if info.isMeta then "meta " else ""
    let all := if info.isAll then "all " else ""
    s!"{pub}{met}import {all}{info.moduleName}\n"

/-- Reconstruct header with given imports -/
def reconstructHeader (usesModule : Bool) (hasPrelude : Bool)
    (imports : Array ImportInfo) (stripModifiers : Bool) : String := Id.run do
  let mut result := ""
  if usesModule then
    result := result ++ "module\n\n"
  if hasPrelude then
    result := result ++ "prelude\n"
  for imp in imports do
    result := result ++ renderImport imp stripModifiers
  if !imports.isEmpty then
    result := result ++ "\n"
  return result

/-- Test if a source string compiles successfully (using subprocess for memory isolation). -/
def testSourceCompiles' (source : String) (fileName : String) : IO Bool :=
  testCompilesSubprocess source fileName

/-- Get the imports of a module from the environment.
    Returns none if the module is not found. -/
def getModuleImports (env : Environment) (modName : Name) : Option (Array Import) := do
  -- Search for module in moduleNames array
  let mut moduleIdx : Option Nat := none
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == modName then
      moduleIdx := some i
      break
  let idx ← moduleIdx
  let moduleData ← env.header.moduleData[idx]?
  return moduleData.imports

/-- The import minimization pass.

    Iteratively tries to remove or inline imports until no more changes can be made.
    Tracks which imports have been tried within this pass run to avoid redundant work. -/
unsafe def importMinimizationPass : Pass where
  name := "Import Minimization"
  cliFlag := "import-minimization"
  run := fun ctx => do
    let usesModule := headerUsesModuleSystem ctx.header
    let hasPrelude := headerHasPrelude ctx.header

    -- Track imports we've already tried and failed to remove/replace
    let mut triedAndFailed : Std.HashSet Name := {}
    let mut currentSource := ctx.source
    let mut anyChanges := false

    -- Get initial environment for looking up transitive imports
    let env ← match ctx.steps[0]? with
    | some step => pure step.before
    | none =>
      let inputCtx := Parser.mkInputContext ctx.source ctx.fileName
      let (header, _parserState, messages) ← Parser.parseHeader inputCtx
      if messages.hasErrors then
        return { source := ctx.source, changed := false, action := .continue }
      let (env, _msgs) ← processHeader header {} messages inputCtx
      pure env

    -- Whether to strip modifiers when generating imports
    let stripModifiers := !usesModule

    -- Loop until no more changes can be made
    let maxIterations := 1000
    for _ in [:maxIterations] do
      -- Re-parse header to get current imports
      let inputCtx := Parser.mkInputContext currentSource ctx.fileName
      let (header, parserState, _) ← Parser.parseHeader inputCtx
      let imports := extractImports header
      let headerEndPos := parserState.pos
      let commandsPart := String.Pos.Raw.extract currentSource headerEndPos currentSource.rawEndPos

      if imports.isEmpty then
        if ctx.verbose && !anyChanges then
          IO.eprintln "  No imports to minimize"
        break

      if ctx.verbose then
        IO.eprintln s!"  Analyzing {imports.size} imports ({triedAndFailed.size} already tried)..."

      -- Find an import we haven't tried yet
      let mut madeProgress := false
      for imp in imports do
        if triedAndFailed.contains imp.moduleName then
          continue

        if ctx.verbose then
          IO.eprintln s!"  Trying to remove import {imp.moduleName}..."

        -- Try 1: Remove this import entirely
        let remainingImports := imports.filter fun x => x != imp
        let newHeader := reconstructHeader usesModule hasPrelude remainingImports stripModifiers
        let newSource := newHeader ++ commandsPart

        if ← testSourceCompiles' newSource ctx.fileName then
          if ctx.verbose then
            IO.eprintln s!"    Removed import {imp.moduleName}"
          currentSource := newSource
          if let some outPath := ctx.outputFile then
            IO.FS.writeFile outPath currentSource
          anyChanges := true
          madeProgress := true
          break

        -- Try 2: Replace with its own imports
        if let some transitiveImports := getModuleImports env imp.moduleName then
          if !transitiveImports.isEmpty then
            if ctx.verbose then
              IO.eprintln s!"  Trying to replace import {imp.moduleName} with its {transitiveImports.size} imports..."

            -- Build new import list: remove current, add transitive (avoiding duplicates)
            let mut newImports := imports.filter fun x => x != imp
            for transImp in transitiveImports do
              let transInfo := leanImportToInfo transImp
              -- Skip Init - it's always implicitly available and causes infinite loops
              if transInfo.moduleName == `Init then
                continue
              let alreadyPresent := newImports.any fun existing =>
                existing.moduleName == transInfo.moduleName
              if !alreadyPresent then
                newImports := newImports.push transInfo

            let newHeader := reconstructHeader usesModule hasPrelude newImports stripModifiers
            let newSource := newHeader ++ commandsPart

            if ← testSourceCompiles' newSource ctx.fileName then
              if ctx.verbose then
                IO.eprintln s!"    Replaced import {imp.moduleName} with its imports"
              currentSource := newSource
              if let some outPath := ctx.outputFile then
                IO.FS.writeFile outPath currentSource
              anyChanges := true
              madeProgress := true
              break

        -- Mark this import as tried and failed
        triedAndFailed := triedAndFailed.insert imp.moduleName

      -- If no progress was made, we're done
      if !madeProgress then
        break

    if ctx.verbose && !anyChanges then
      IO.eprintln "  No imports could be removed or replaced"

    return { source := currentSource, changed := anyChanges, action := .continue }

end LeanMinimizer
