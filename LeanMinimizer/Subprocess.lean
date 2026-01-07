/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Data.Json
import LeanMinimizer.Dependencies

/-!
# Subprocess-based Frontend Processing

This module provides infrastructure for running the Lean frontend in a subprocess.

## Why Subprocess?

Lean's environment is not designed to process different import headers in the same process.
When the minimizer (which imports its own dependencies) tries to elaborate user code
that uses different libraries with `[init]` declarations, conflicts occur.

By running elaboration in a subprocess, each elaboration gets a clean environment
where only the user file's imports are processed.

## Protocol

The subprocess reads a Lean source file, elaborates it, and outputs a JSON result with:
- Command positions and reprinted syntax
- Dependency information (defined/referenced constants)
- Header position
-/

namespace LeanMinimizer

open Lean

/-- Serializable info about a single import -/
structure SubprocessImportInfo where
  /-- The module name being imported -/
  moduleName : String
  /-- Whether this is a `public` import -/
  isPublic : Bool := false
  /-- Whether this is a `meta` import -/
  isMeta : Bool := false
  /-- Whether this is an `import all` -/
  isAll : Bool := false
  deriving ToJson, FromJson, Inhabited, Repr, BEq

/-- Serializable info about a single command -/
structure SubprocessCmdInfo where
  /-- Index of this command -/
  idx : Nat
  /-- Reprinted syntax as string -/
  stxRepr : String
  /-- The syntax kind (for isOfKind checks) -/
  stxKind : String
  /-- Start position in source -/
  startPos : Nat
  /-- End position in source -/
  endPos : Nat
  /-- Constants defined by this command -/
  definedConstants : Array String
  /-- Constants referenced by this command -/
  referencedConstants : Array String
  /-- For declarations: start position of body (for sorry replacement) -/
  declBodyStartPos : Option Nat := none
  /-- For declarations: end position of body (for sorry replacement) -/
  declBodyEndPos : Option Nat := none
  deriving ToJson, FromJson, Inhabited

/-- Serializable result from subprocess frontend processing -/
structure SubprocessFrontendResult where
  /-- End position of header -/
  headerEndPos : Nat
  /-- Whether the header has a `module` keyword -/
  hasModule : Bool
  /-- Whether the header has `prelude` -/
  hasPrelude : Bool
  /-- Header reprinted as string (for debugging) -/
  headerRepr : String
  /-- Header reconstructed without module keyword and import modifiers -/
  headerWithoutModule : String
  /-- Imports extracted from the header -/
  imports : Array SubprocessImportInfo
  /-- All commands with their info -/
  commands : Array SubprocessCmdInfo
  deriving ToJson, FromJson, Inhabited

/-- Serializable result from header-only parsing (no elaboration) -/
structure SubprocessHeaderResult where
  /-- End position of header -/
  headerEndPos : Nat
  /-- Whether the header has a `module` keyword -/
  hasModule : Bool
  /-- Whether the header has `prelude` -/
  hasPrelude : Bool
  /-- Header reprinted as string (for debugging) -/
  headerRepr : String
  /-- Header reconstructed without module keyword and import modifiers -/
  headerWithoutModule : String
  /-- Imports extracted from the header -/
  imports : Array SubprocessImportInfo
  deriving ToJson, FromJson, Inhabited

/-- Result from running a pass in subprocess mode -/
structure SubprocessPassResult where
  /-- The (possibly modified) source code -/
  source : String
  /-- Whether any changes were made -/
  changed : Bool
  /-- Action to take next: "restart", "repeat", or "continue" -/
  action : String
  /-- Failed changes to add to memory (keys are pass-specific strings) -/
  newFailedChanges : Array String := #[]
  /-- Whether to clear the failed changes memory -/
  clearMemory : Bool := false
  deriving ToJson, FromJson, Inhabited

/-! ## Subprocess data analysis -/

/-- Analyze subprocess command info to extract dependency information.
    This uses the pre-computed definedConstants/referencedConstants from the subprocess. -/
def analyzeSubprocessCommands (commands : Array SubprocessCmdInfo) : Array CommandAnalysis :=
  commands.map fun cmd => {
    idx := cmd.idx
    referencedConstants := cmd.referencedConstants.foldl (init := {}) fun acc s => acc.insert s.toName
    definedConstants := cmd.definedConstants.foldl (init := {}) fun acc s => acc.insert s.toName
  }

/-- Find which command indices define constants that are referenced by the invariant section.
    Uses subprocess command info with pre-computed constants. -/
def findInvariantDependenciesFromSubprocess
    (commandsBeforeMarker : Array SubprocessCmdInfo)
    (invariantCommands : Array SubprocessCmdInfo) : Array Nat := Id.run do
  -- Build map from constant name to defining command index
  let mut constantToCmd : Std.HashMap Name Nat := {}
  for cmd in commandsBeforeMarker do
    for name in cmd.definedConstants do
      constantToCmd := constantToCmd.insert name.toName cmd.idx

  -- Find all constants referenced by the invariant section
  let mut invariantRefs : NameSet := {}
  for cmd in invariantCommands do
    for name in cmd.referencedConstants do
      invariantRefs := invariantRefs.insert name.toName

  -- Find which commands before marker define constants used by invariant
  let mut result : Array Nat := #[]
  for name in invariantRefs do
    if let some idx := constantToCmd[name]? then
      if !result.contains idx then
        result := result.push idx

  return result

/-- Convert a CompilationStep to serializable SubprocessCmdInfo -/
def CompilationStep.toSubprocessInfo (step : CompilationStep) : SubprocessCmdInfo :=
  let bodyRange := getDeclBodyRange? step.stx
  { idx := step.idx
    stxRepr := step.stx.reprint.getD ""
    stxKind := step.stx.getKind.toString
    startPos := step.startPos.byteIdx
    endPos := step.endPos.byteIdx
    definedConstants := (getNewConstants step).toArray.map (·.toString)
    referencedConstants := (getReferencedConstants step).toArray.map (·.toString)
    declBodyStartPos := bodyRange.map (·.1.byteIdx)
    declBodyEndPos := bodyRange.map (·.2.byteIdx)
  }

/-- Check if the header uses the module system (has `module` keyword) -/
private def headerHasModuleImpl (header : Syntax) : Bool :=
  -- Header structure: optional(module) optional(prelude) many(import)
  -- The first child is the optional module token
  if header.getNumArgs > 0 then
    let moduleOpt := header[0]!
    -- Check if the optional module part is present (not null/missing)
    !moduleOpt.isNone && !moduleOpt.isMissing
  else
    false

/-- Extract the module name from an import syntax.
    Import syntax: `public? meta? import all? ident trailingDot?` -/
private def getImportModuleNameImpl (importStx : Syntax) : Option Name := Id.run do
  for i in [:importStx.getNumArgs] do
    let child := importStx[i]!
    if child.isIdent then
      return some child.getId
    -- Handle identWithPartialTrailingDot
    if !child.isNone && child.getNumArgs > 0 then
      let inner := child[0]!
      if inner.isIdent then
        return some inner.getId
  return none

/-- Check if the header has `prelude` -/
private def headerHasPreludeImpl (header : Syntax) : Bool :=
  if header.getNumArgs > 1 then
    let preludeOpt := header[1]!
    !preludeOpt.isNone && !preludeOpt.isMissing
  else
    false

/-- Check if syntax is a token with given value -/
private def isTokenWithValImpl (stx : Syntax) (val : String) : Bool :=
  match stx with
  | .atom _ v => v == val
  | _ => false

/-- Extract import info from import syntax -/
private def parseImportSyntaxImpl (importStx : Syntax) : Option SubprocessImportInfo := do
  let mut isPublic := false
  let mut isMeta := false
  let mut isAll := false
  let mut modName : Option Name := none

  for i in [:importStx.getNumArgs] do
    let child := importStx[i]!
    if isTokenWithValImpl child "public" then isPublic := true
    else if isTokenWithValImpl child "meta" then isMeta := true
    else if isTokenWithValImpl child "all" then isAll := true
    else if isTokenWithValImpl child "import" then pure ()
    else if child.isIdent then
      modName := some child.getId
    else if !child.isNone && !child.isMissing then
      for j in [:child.getNumArgs] do
        let nested := child[j]!
        if isTokenWithValImpl nested "public" then isPublic := true
        else if isTokenWithValImpl nested "meta" then isMeta := true
        else if isTokenWithValImpl nested "all" then isAll := true
        else if nested.isIdent then
          modName := some nested.getId

  let name ← modName
  return { moduleName := name.toString, isPublic, isMeta, isAll }

/-- Extract all imports from a header syntax -/
private def extractImportsImpl (header : Syntax) : Array SubprocessImportInfo := Id.run do
  let mut result := #[]
  if header.getNumArgs > 2 then
    let imports := header[2]!
    for i in [:imports.getNumArgs] do
      let importStx := imports[i]!
      if let some info := parseImportSyntaxImpl importStx then
        result := result.push info
  return result

/-- Reconstruct the header without `module` keyword and without import modifiers. -/
private def reconstructHeaderWithoutModuleImpl (header : Syntax) : String := Id.run do
  let mut result := ""

  -- Skip the module keyword (first optional child)
  -- Check for prelude (second optional child)
  if header.getNumArgs > 1 then
    let preludeOpt := header[1]!
    if !preludeOpt.isNone && !preludeOpt.isMissing then
      result := result ++ "prelude\n"

  -- Process imports (third child is the list of imports)
  if header.getNumArgs > 2 then
    let imports := header[2]!
    for i in [:imports.getNumArgs] do
      let importStx := imports[i]!
      if let some modName := getImportModuleNameImpl importStx then
        result := result ++ s!"import {modName}\n"

  return result

/-- Convert a FrontendResult to serializable SubprocessFrontendResult -/
def FrontendResult.toSubprocessResult (result : FrontendResult) : SubprocessFrontendResult :=
  { headerEndPos := result.headerEndPos.byteIdx
    hasModule := headerHasModuleImpl result.header
    hasPrelude := headerHasPreludeImpl result.header
    headerRepr := result.header.reprint.getD ""
    headerWithoutModule := reconstructHeaderWithoutModuleImpl result.header
    imports := extractImportsImpl result.header
    commands := result.steps.map (·.toSubprocessInfo)
  }

/-- Find the marker index in subprocess command info array.
    For #guard_msgs, also includes the preceding docstring if present. -/
def findMarkerIdxInSubprocessSteps (commands : Array SubprocessCmdInfo) (marker : String) : Option Nat := do
  let idx ← commands.findIdx? fun cmd =>
    cmd.stxRepr.containsSubstr marker

  -- For #guard_msgs, check if the previous command is a standalone docstring
  if marker == "#guard_msgs" && idx > 0 then
    if h : idx - 1 < commands.size then
      let prevCmd := commands[idx - 1]
      -- Only match if the previous step is a docstring command
      if prevCmd.stxKind == "Lean.Parser.Command.docComment" then
        return idx - 1

  return idx

/-- Convert SubprocessCmdInfo to CmdInfo.
    Creates a minimal Syntax that stores the reprinted text as an atom. -/
def SubprocessCmdInfo.toCmdInfo (cmd : SubprocessCmdInfo) : CmdInfo :=
  -- Create a synthetic syntax node with the kind and reprinted content
  -- The actual structure doesn't matter since we only use positions
  let syntheticStx := Syntax.node .none cmd.stxKind.toName #[Syntax.atom .none cmd.stxRepr]
  { idx := cmd.idx
    stx := syntheticStx
    startPos := ⟨cmd.startPos⟩
    endPos := ⟨cmd.endPos⟩
  }

/-- Convert SubprocessCmdInfo to a minimal CompilationStep.
    The Environment fields are set to empty since they're not needed for most passes. -/
unsafe def SubprocessCmdInfo.toCompilationStep (cmd : SubprocessCmdInfo) : IO CompilationStep := do
  let syntheticStx := Syntax.node .none cmd.stxKind.toName #[Syntax.atom .none cmd.stxRepr]
  -- Create a minimal empty environment - this won't be used by passes
  let emptyEnv ← mkEmptyEnvironment
  return {
    idx := cmd.idx
    stx := syntheticStx
    startPos := ⟨cmd.startPos⟩
    endPos := ⟨cmd.endPos⟩
    before := emptyEnv
    after := emptyEnv
    trees := []
  }

/-- Convert SubprocessFrontendResult to the structures needed by PassContext -/
unsafe def SubprocessFrontendResult.toPassContextData (result : SubprocessFrontendResult) :
    IO (Syntax × String.Pos.Raw × Array CompilationStep) := do
  -- Create a minimal header syntax
  let headerStx := Syntax.missing
  let headerEndPos : String.Pos.Raw := ⟨result.headerEndPos⟩
  -- Convert all commands to CompilationSteps
  let mut steps : Array CompilationStep := #[]
  for cmd in result.commands do
    steps := steps.push (← cmd.toCompilationStep)
  return (headerStx, headerEndPos, steps)

/-- Run frontend and output JSON result.
    This is the subprocess entry point for --analyze. -/
unsafe def elaborateAndOutputJson (source : String) (fileName : String) : IO Unit := do
  let result ← runFrontend source fileName
  let subprocessResult := result.toSubprocessResult
  IO.println (toJson subprocessResult).compress

/-- Parse header only (no elaboration) and output JSON result.
    This is the subprocess entry point for --header-info.
    Does NOT call processHeader, so there are no [init] conflicts. -/
def parseHeaderAndOutputJson (source : String) (fileName : String) : IO Unit := do
  let inputCtx := Parser.mkInputContext source fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  if messages.hasErrors then
    throw <| IO.userError "File has header errors"

  let headerResult : SubprocessHeaderResult := {
    headerEndPos := parserState.pos.byteIdx
    hasModule := headerHasModuleImpl header
    hasPrelude := headerHasPreludeImpl header
    headerRepr := (header : Syntax).reprint.getD ""
    headerWithoutModule := reconstructHeaderWithoutModuleImpl header
    imports := extractImportsImpl header
  }
  IO.println (toJson headerResult).compress

/-- Find the project root by searching upward for lakefile.toml -/
private partial def findProjectRootImpl (startPath : System.FilePath) : IO (Option System.FilePath) := do
  let lakefile := startPath / "lakefile.toml"
  if ← lakefile.pathExists then
    return some startPath
  else
    match startPath.parent with
    | none => return none
    | some parent => findProjectRootImpl parent

/-- Get the temp file path for subprocess execution.
    Uses a name derived from the input file and PID, so parallel processes don't conflict.
    If the process is interrupted, the file remains but next run with same PID overwrites it. -/
private def getTempSourcePath (fileName : String) : IO System.FilePath := do
  let fp := System.FilePath.mk fileName
  let fileDir := fp.parent.getD (System.FilePath.mk ".")
  let baseName := fp.fileName.getD "temp"
  let pid ← IO.Process.getPID
  return fileDir / s!".lean-minimize-{pid}-{baseName}"

/-- Find the project root for subprocess execution. -/
private def findProjectRoot (fileName : String) : IO System.FilePath := do
  let absoluteFilePath ← do
    let fp := System.FilePath.mk fileName
    if fp.isAbsolute then pure fp
    else do
      let cwd ← IO.currentDir
      pure (cwd / fp)

  match absoluteFilePath.parent with
  | none => pure (← IO.currentDir)
  | some parent =>
    match ← findProjectRootImpl parent with
    | some root => pure root
    | none => pure (← IO.currentDir)

/-- Write source to temp file and find project root for subprocess execution.
    Returns (tempFilePath, projectRoot). The caller should clean up the temp file. -/
private def setupSubprocessExecution (source : String) (fileName : String) :
    IO (System.FilePath × System.FilePath) := do
  let tempSource ← getTempSourcePath fileName
  IO.FS.writeFile tempSource source
  let projectRoot ← findProjectRoot fileName
  return (tempSource, projectRoot)

/-- Run `lean-minimizer --header-info` in a subprocess to parse header without elaboration.
    This avoids [init] conflicts since it doesn't call processHeader. -/
def runHeaderInfoSubprocess (source : String) (fileName : String) : IO SubprocessHeaderResult := do
  let (tempSource, projectRoot) ← setupSubprocessExecution source fileName

  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "minimize", "--header-info", tempSource.toString]
    cwd := some projectRoot
  }

  IO.FS.removeFile tempSource

  if result.exitCode != 0 then
    throw <| IO.userError s!"Header info subprocess failed:\n{result.stderr}"

  match Json.parse result.stdout with
  | .error err => throw <| IO.userError s!"Failed to parse header info output: {err}\nOutput: {result.stdout}"
  | .ok json =>
    match fromJson? json with
    | .error err => throw <| IO.userError s!"Failed to decode header info result: {err}"
    | .ok (result : SubprocessHeaderResult) => return result

/-- Run `lean-minimizer --analyze` in a subprocess to fully elaborate the file.
    This spawns a fresh process where processHeader is called exactly once. -/
def runAnalyzeSubprocess (source : String) (fileName : String) : IO SubprocessFrontendResult := do
  let (tempSource, projectRoot) ← setupSubprocessExecution source fileName

  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "minimize", "--analyze", tempSource.toString]
    cwd := some projectRoot
  }

  IO.FS.removeFile tempSource

  if result.exitCode != 0 then
    throw <| IO.userError s!"Analyze subprocess failed:\n{result.stderr}"

  match Json.parse result.stdout with
  | .error err => throw <| IO.userError s!"Failed to parse analyze output: {err}\nOutput: {result.stdout}"
  | .ok json =>
    match fromJson? json with
    | .error err => throw <| IO.userError s!"Failed to decode analyze result: {err}"
    | .ok (result : SubprocessFrontendResult) => return result

/-- Run a pass in a subprocess with full elaboration.
    This spawns a fresh process where processHeader is called exactly once,
    the pass runs with full Environment/InfoTrees, and returns JSON result.

    Stderr is inherited so verbose output appears in real-time.
    Only stdout is captured for the JSON result. -/
def runPassSubprocess (passName : String) (source : String) (fileName : String)
    (marker : String) (verbose : Bool)
    (failedChanges : Std.HashSet String := {})
    (stableSections : Std.HashSet String := {})
    (isCompleteSweep : Bool := true) : IO SubprocessPassResult := do
  let (tempSource, projectRoot) ← setupSubprocessExecution source fileName

  -- Write failedChanges to a temp file if non-empty
  let failedChangesFile := tempSource.toString ++ ".memory"
  if !failedChanges.isEmpty then
    let failedArray := failedChanges.toArray
    IO.FS.writeFile failedChangesFile (toJson failedArray).compress

  -- Write stableSections to a temp file if non-empty
  let stableSectionsFile := tempSource.toString ++ ".stable"
  if !stableSections.isEmpty then
    let stableArray := stableSections.toArray
    IO.FS.writeFile stableSectionsFile (toJson stableArray).compress

  let mut args := #["env", "minimize", "--run-pass", passName, tempSource.toString, "--marker", marker]
  if verbose then
    args := args.push "--verbose"
  if !failedChanges.isEmpty then
    args := args ++ #["--memory-file", failedChangesFile]
  if !stableSections.isEmpty then
    args := args ++ #["--stable-file", stableSectionsFile]
  if !isCompleteSweep then
    args := args.push "--unstable-only"

  let child ← IO.Process.spawn {
    cmd := "lake"
    args
    cwd := some projectRoot
    stdout := .piped
    stderr := .inherit
  }

  let stdout ← child.stdout.readToEnd
  let exitCode ← child.wait

  IO.FS.removeFile tempSource
  if !failedChanges.isEmpty then
    IO.FS.removeFile failedChangesFile
  if !stableSections.isEmpty then
    IO.FS.removeFile stableSectionsFile

  if exitCode != 0 then
    throw <| IO.userError s!"Run-pass subprocess failed with exit code {exitCode}"

  match Json.parse stdout with
  | .error err => throw <| IO.userError s!"Failed to parse run-pass output: {err}\nOutput: {stdout}"
  | .ok json =>
    match fromJson? json with
    | .error err => throw <| IO.userError s!"Failed to decode run-pass result: {err}"
    | .ok (result : SubprocessPassResult) => return result

end LeanMinimizer
