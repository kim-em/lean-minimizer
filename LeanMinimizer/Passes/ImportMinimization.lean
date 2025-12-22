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

/-- Convert SubprocessImportInfo to ImportInfo -/
def SubprocessImportInfo.toImportInfo (info : SubprocessImportInfo) : ImportInfo :=
  { moduleName := info.moduleName.toName
    isPublic := info.isPublic
    isMeta := info.isMeta
    isAll := info.isAll }

/-- Convert an array of SubprocessImportInfo to ImportInfo -/
def subprocessImportsToImportInfo (imports : Array SubprocessImportInfo) : Array ImportInfo :=
  imports.map (·.toImportInfo)

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

/-- Get imports from context, preferring subprocess data if available -/
def getImportsFromContext (ctx : PassContext) : Array ImportInfo :=
  if ctx.imports.isEmpty then
    extractImports ctx.header
  else
    subprocessImportsToImportInfo ctx.imports

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

/-! ## Delta debugging for imports -/

/-- State for import minimization with ddmin -/
structure ImportMinState where
  /-- Whether file uses module system -/
  usesModule : Bool
  /-- Whether file has prelude -/
  hasPrelude : Bool
  /-- Whether to strip modifiers from imports -/
  stripModifiers : Bool
  /-- The command portion of the source (after header) -/
  commandsPart : String
  /-- Full list of current imports -/
  allImports : Array ImportInfo
  /-- Imports that must be kept (already tried and failed to delete) -/
  required : Std.HashSet Name
  /-- File name for testing -/
  fileName : String
  /-- Whether to print verbose output -/
  verbose : Bool

/-- Test if keeping only the given indices (plus required imports) compiles -/
def testImportsCompile (state : ImportMinState) (keepIndices : Array Nat) : IO Bool := do
  -- Get the imports to keep: required ones plus the ones in keepIndices
  let mut keptImports : Array ImportInfo := #[]
  for i in [:state.allImports.size] do
    let imp := state.allImports[i]!
    if state.required.contains imp.moduleName || keepIndices.contains i then
      keptImports := keptImports.push imp
  let header := reconstructHeader state.usesModule state.hasPrelude keptImports state.stripModifiers
  let source := header ++ state.commandsPart
  testCompilesSubprocess source state.fileName

/-- Delta debugging core for imports. End-biased: tries removing later imports first.
    Returns indices (into the candidates array) that must be kept. -/
partial def ddminImportsCore (state : ImportMinState)
    (candidates : Array Nat) (currentlyKept : Array Nat) : IO (Array Nat) := do
  -- Base case: no candidates to try removing
  if candidates.size == 0 then
    return currentlyKept

  if candidates.size == 1 then
    -- Try removing this single import
    let idx := candidates[0]!
    let withoutThis := currentlyKept.filter (· != idx)
    if state.verbose then
      let imp := state.allImports[idx]!
      IO.eprintln s!"    ddmin: try remove [{imp.moduleName}]"
    if ← testImportsCompile state withoutThis then
      if state.verbose then
        IO.eprintln s!"      → Success"
      return withoutThis
    if state.verbose then
      IO.eprintln s!"      → Failed: must keep"
    return currentlyKept

  -- Binary split
  let n := candidates.size / 2
  let firstHalf := candidates[:n].toArray
  let secondHalf := candidates[n:].toArray

  -- End-biased: try removing second half (later imports) first
  let withoutSecond := currentlyKept.filter (!secondHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"    ddmin: try remove {secondHalf.size} imports (keep {firstHalf.size})"
  if ← testImportsCompile state withoutSecond then
    if state.verbose then
      IO.eprintln s!"      → Success, recursing on first half"
    return ← ddminImportsCore state firstHalf withoutSecond

  -- Try removing first half
  let withoutFirst := currentlyKept.filter (!firstHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"      → Failed, try remove {firstHalf.size} imports (keep {secondHalf.size})"
  if ← testImportsCompile state withoutFirst then
    if state.verbose then
      IO.eprintln s!"      → Success, recursing on second half"
    return ← ddminImportsCore state secondHalf withoutFirst

  -- Both halves needed; recurse on each
  if state.verbose then
    IO.eprintln s!"      → Failed: both halves needed, recursing on each"
  let afterSecond ← ddminImportsCore state secondHalf currentlyKept
  let afterFirst ← ddminImportsCore state firstHalf afterSecond
  return afterFirst

/-- Delta debugging entry point for imports.
    Takes indices of untried imports, returns indices that must be kept. -/
def ddminImports (state : ImportMinState) (candidates : Array Nat) : IO (Array Nat) := do
  ddminImportsCore state candidates candidates

/-- Greedy deletion: try removing each untried import one at a time.
    Returns the imports that couldn't be removed (should be added to required). -/
def greedyDeleteImports (state : ImportMinState) (untried : Array Nat) : IO (Array Nat) := do
  let mut mustKeep : Array Nat := #[]
  let mut currentKept := untried
  for idx in untried do
    let withoutThis := currentKept.filter (· != idx)
    if state.verbose then
      let imp := state.allImports[idx]!
      IO.eprintln s!"    Trying to remove {imp.moduleName}..."
    if ← testImportsCompile { state with } withoutThis then
      if state.verbose then
        IO.eprintln s!"      → Removed"
      currentKept := withoutThis
    else
      if state.verbose then
        IO.eprintln s!"      → Must keep"
      mustKeep := mustKeep.push idx
  return mustKeep

/-- The import minimization pass.

    Uses a two-phase approach in each iteration:
    1. Deletion sub-pass: Try to remove imports (using ddmin if >20 untried imports)
    2. Replacement sub-pass: Try to replace imports with their transitive imports

    Tracks `required` (imports we've tried and failed to delete) and `failedReplace`
    (imports we've tried and failed to replace). When replacement introduces new imports,
    they become candidates for deletion in the next iteration. -/
unsafe def importMinimizationPass : Pass where
  name := "Import Minimization"
  cliFlag := "import-minimization"
  needsSubprocess := true
  run := fun ctx => do
    -- Use subprocess-provided flags when available, otherwise check syntax
    let usesModule := ctx.hasModule || headerUsesModuleSystem ctx.header
    let hasPrelude := ctx.hasPrelude || headerHasPrelude ctx.header
    let stripModifiers := !usesModule

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

    -- Parse initial imports
    let inputCtx := Parser.mkInputContext ctx.source ctx.fileName
    let (header, parserState, _) ← Parser.parseHeader inputCtx
    let initialImports := extractImports header
    let commandsPart := String.Pos.Raw.extract ctx.source parserState.pos ctx.source.rawEndPos

    if initialImports.isEmpty then
      if ctx.verbose then
        IO.eprintln "  No imports to minimize"
      return { source := ctx.source, changed := false, action := .continue }

    -- Track state across iterations
    let mut required : Std.HashSet Name := {}       -- tried and failed to delete
    let mut failedReplace : Std.HashSet Name := {}  -- tried and failed to replace
    let mut currentImports := initialImports
    let mut anyChanges := false

    -- Loop until no more changes can be made
    let maxIterations := 1000
    for _ in [:maxIterations] do
      let mut madeProgress := false

      -- === Deletion sub-pass ===
      -- Find indices of untried imports (not in required set)
      let mut untried : Array Nat := #[]
      for i in [:currentImports.size] do
        if !required.contains currentImports[i]!.moduleName then
          untried := untried.push i

      if !untried.isEmpty then
        if ctx.verbose then
          IO.eprintln s!"  Deletion sub-pass: {untried.size} untried of {currentImports.size} imports"

        let state : ImportMinState := {
          usesModule, hasPrelude, stripModifiers, commandsPart
          allImports := currentImports
          required
          fileName := ctx.fileName
          verbose := ctx.verbose
        }

        -- Use ddmin for large sets, greedy for small
        let ddminThreshold := 20
        let keptIndices ← if untried.size > ddminThreshold then
          if ctx.verbose then
            IO.eprintln s!"    Using delta debugging ({untried.size} > {ddminThreshold})"
          ddminImports state untried
        else
          if ctx.verbose then
            IO.eprintln s!"    Using greedy deletion"
          greedyDeleteImports state untried

        -- Update required with imports that couldn't be deleted
        for idx in keptIndices do
          required := required.insert currentImports[idx]!.moduleName

        -- Check if any imports were removed
        let deletedCount := untried.size - keptIndices.size
        if deletedCount > 0 then
          if ctx.verbose then
            IO.eprintln s!"    Removed {deletedCount} imports"
          -- Rebuild currentImports: keep required + keptIndices
          let mut newImports : Array ImportInfo := #[]
          for i in [:currentImports.size] do
            let imp := currentImports[i]!
            if required.contains imp.moduleName || keptIndices.contains i then
              newImports := newImports.push imp
          currentImports := newImports
          anyChanges := true
          madeProgress := true
          -- Write progress
          if let some outPath := ctx.outputFile then
            let newHeader := reconstructHeader usesModule hasPrelude currentImports stripModifiers
            IO.FS.writeFile outPath (newHeader ++ commandsPart)

      -- === Replacement sub-pass ===
      -- Try to replace each import with its transitive imports
      for imp in currentImports do
        if failedReplace.contains imp.moduleName then
          continue

        if let some transitiveImports := getModuleImports env imp.moduleName then
          if !transitiveImports.isEmpty then
            if ctx.verbose then
              IO.eprintln s!"  Trying to replace {imp.moduleName} with its {transitiveImports.size} imports..."

            -- Build new import list: remove current, add transitive (avoiding duplicates)
            let mut newImports := currentImports.filter fun x => x.moduleName != imp.moduleName
            for transImp in transitiveImports do
              let transInfo := leanImportToInfo transImp
              -- Skip Init - it's always implicitly available
              if transInfo.moduleName == `Init then
                continue
              let alreadyPresent := newImports.any fun existing =>
                existing.moduleName == transInfo.moduleName
              if !alreadyPresent then
                newImports := newImports.push transInfo

            -- Test if replacement works
            let newHeader := reconstructHeader usesModule hasPrelude newImports stripModifiers
            let newSource := newHeader ++ commandsPart

            if ← testCompilesSubprocess newSource ctx.fileName then
              if ctx.verbose then
                IO.eprintln s!"    Replaced {imp.moduleName} with its imports"
              -- New imports are NOT in required, so they'll be tried for deletion
              -- Remove the replaced import from required if it was there
              required := required.erase imp.moduleName
              currentImports := newImports
              anyChanges := true
              madeProgress := true
              -- Write progress
              if let some outPath := ctx.outputFile then
                IO.FS.writeFile outPath newSource
              break
            else
              failedReplace := failedReplace.insert imp.moduleName
        else
          failedReplace := failedReplace.insert imp.moduleName

      -- If no progress was made in either sub-pass, we're done
      if !madeProgress then
        break

    if ctx.verbose && !anyChanges then
      IO.eprintln "  No imports could be removed or replaced"

    let finalHeader := reconstructHeader usesModule hasPrelude currentImports stripModifiers
    return { source := finalHeader ++ commandsPart, changed := anyChanges, action := .continue }

end LeanMinimizer
