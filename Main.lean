import LeanMinimizer
import LeanMinimizer.Pass
import LeanMinimizer.Subprocess
import LeanMinimizer.Passes.ModuleRemoval
import LeanMinimizer.Passes.Deletion
import LeanMinimizer.Passes.EmptyScopeRemoval
import LeanMinimizer.Passes.SingletonNamespaceFlattening
import LeanMinimizer.Passes.PublicSectionRemoval
import LeanMinimizer.Passes.BodyReplacement
import LeanMinimizer.Passes.TextSubstitution
import LeanMinimizer.Passes.ExtendsSimplification
import LeanMinimizer.Passes.ImportMinimization
import LeanMinimizer.Passes.ImportInlining
import LeanMinimizer.Passes.AttributeExpansion

open Lean LeanMinimizer

/-- Handle --header-info subcommand (for subprocess invocation).
    This runs in a clean process to parse just the header and output JSON.
    Does NOT call processHeader, so there are no [init] conflicts. -/
def handleHeaderInfo (file : String) : IO UInt32 := do
  try
    let source ← IO.FS.readFile file
    parseHeaderAndOutputJson source file
    return 0
  catch e =>
    IO.eprintln s!"Header parsing error: {e}"
    return 1

/-- Handle --analyze subcommand (for subprocess invocation).
    This runs in a clean process to elaborate a file and output JSON.
    Calls processHeader ONCE, so must be run in a fresh subprocess. -/
unsafe def handleAnalyze (file : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  try
    let source ← IO.FS.readFile file
    elaborateAndOutputJson source file
    return 0
  catch e =>
    IO.eprintln s!"Elaboration error: {e}"
    return 1

/-- Registry of passes that run in subprocess mode with full elaboration. -/
unsafe def subprocessPassRegistry : Array (String × Pass) := #[
  ("body-replacement", bodyReplacementPass),
  ("extends", extendsSimplificationPass),
  ("attr-expansion", attributeExpansionPass),
  ("import-minimization", importMinimizationPass)
]

private unsafe def runPassInnerCore (pass : Pass) (file : String) (marker : String) (verbose : Bool)
    (failedChanges : Std.HashSet String := {})
    (stableSections : Std.HashSet String := {})
    (isCompleteSweep : Bool := true)
    (tempMarker : Option String := none)
    (tempMarkerSearchAfter : Option String := none) : IO Unit := do
  -- Read and elaborate
  let source ← IO.FS.readFile file
  let result ← runFrontend source file

  -- Find marker
  let some markerIdx := findMarkerIdxInSteps result.steps marker
    | throw <| IO.userError (markerNotFoundError marker)

  -- Convert steps to subprocess command format for temp marker lookup
  let subprocessCommands := result.steps.map (·.toSubprocessInfo)

  -- Compute temp marker index if we have a temp marker
  let tempMarkerIdx := tempMarker.bind fun tm =>
    findTempMarkerIdxInSubprocess subprocessCommands tm tempMarkerSearchAfter

  -- Build PassContext with full elaboration data
  let ctx : PassContext := {
    source
    fileName := file
    marker
    verbose
    header := result.header
    headerEndPos := result.headerEndPos
    hasModule := headerUsesModuleSystem result.header
    hasPrelude := headerHasPrelude result.header
    headerWithoutModule := reconstructHeader false false (extractImports result.header) false
    imports := (extractImports result.header).map fun imp =>
      { moduleName := imp.moduleName.toString, isPublic := false, isMeta := false, isAll := false }
    steps := result.steps
    subprocessCommands
    markerIdx
    outputFile := none
    failedChanges
    tempMarker
    tempMarkerIdx
    stableSections
    isCompleteSweep
  }

  -- Run the pass
  let passResult ← pass.run ctx

  -- Output JSON result
  let actionStr := match passResult.action with
    | .restart => "restart"
    | .repeat => "repeat"
    | .repeatThenRestart => "repeatThenRestart"
    | .continue => "continue"
    | .fatal => "fatal"
  let jsonResult : SubprocessPassResult := {
    source := passResult.source
    changed := passResult.changed
    action := actionStr
    newFailedChanges := passResult.newFailedChanges
    clearMemory := passResult.clearMemory
  }
  IO.println (toJson jsonResult).compress

private unsafe def runPassInner (pass : Pass) (file : String) (marker : String) (verbose : Bool)
    (failedChanges : Std.HashSet String := {})
    (stableSections : Std.HashSet String := {})
    (isCompleteSweep : Bool := true)
    (tempMarker : Option String := none)
    (tempMarkerSearchAfter : Option String := none) : IO UInt32 := do
  try
    runPassInnerCore pass file marker verbose failedChanges stableSections isCompleteSweep
        tempMarker tempMarkerSearchAfter
    return 0
  catch e =>
    IO.eprintln s!"Run-pass error: {e}"
    return 1

/-- Handle --run-pass subcommand (for subprocess invocation).
    This runs a specific pass with full elaboration data.
    Calls processHeader ONCE, runs the pass, outputs JSON result. -/
unsafe def handleRunPass (passName : String) (file : String) (marker : String) (verbose : Bool)
    (memoryFile : Option String := none)
    (stableFile : Option String := none)
    (isCompleteSweep : Bool := true)
    (tempMarkerFile : Option String := none) : IO UInt32 := do
  initSearchPath (← findSysroot)

  -- Read failedChanges from memory file if provided
  let failedChanges ← if let some memFile := memoryFile then
    let content ← IO.FS.readFile memFile
    match Json.parse content with
    | .error _ => pure ({} : Std.HashSet String)
    | .ok json =>
      match fromJson? json with
      | .error _ => pure ({} : Std.HashSet String)
      | .ok (arr : Array String) => pure (arr.foldl (init := {}) fun acc s => acc.insert s)
  else
    pure {}

  -- Read stableSections from stable file if provided
  let stableSections ← if let some stabFile := stableFile then
    let content ← IO.FS.readFile stabFile
    match Json.parse content with
    | .error _ => pure ({} : Std.HashSet String)
    | .ok json =>
      match fromJson? json with
      | .error _ => pure ({} : Std.HashSet String)
      | .ok (arr : Array String) => pure (arr.foldl (init := {}) fun acc s => acc.insert s)
  else
    pure {}

  -- Read tempMarker info from file if provided
  -- File format: JSON array [tempMarker, tempMarkerSearchAfter]
  let (tempMarker, tempMarkerSearchAfter) ← if let some tmFile := tempMarkerFile then
    let content ← IO.FS.readFile tmFile
    match Json.parse content with
    | .error _ => pure (none, none)
    | .ok json =>
      match fromJson? json with
      | .error _ => pure (none, none)
      | .ok (arr : Array String) =>
        if arr.size >= 2 then
          let tm := if arr[0]!.isEmpty then none else some arr[0]!
          let tmsa := if arr[1]!.isEmpty then none else some arr[1]!
          pure (tm, tmsa)
        else
          pure (none, none)
  else
    pure (none, none)

  -- Find the pass
  match subprocessPassRegistry.find? (·.1 == passName) with
  | none =>
    IO.eprintln s!"Unknown pass: {passName}"
    return 1
  | some (_, pass) =>
    runPassInner pass file marker verbose failedChanges stableSections isCompleteSweep
      tempMarker tempMarkerSearchAfter

/-- All available passes with their CLI flag names -/
unsafe def allPasses : Array (String × Pass) := #[
  ("module-removal", moduleRemovalPass),
  ("delete", deletionPass),
  ("empty-scope", emptyScopeRemovalPass),
  ("open-minimization", openMinimizationPass),
  ("singleton-ns", singletonNamespaceFlatteningPass),
  ("public-section", publicSectionRemovalPass),
  ("body-replacement", bodyReplacementPass),
  ("text-subst", textSubstitutionPass),
  ("extends", extendsSimplificationPass),
  ("attr-expansion", attributeExpansionPass),
  ("import-minimization", importMinimizationPass),
  ("import-inlining", importInliningPass),
  ("clear-memory", clearMemoryPass)
]

/-- Build the list of passes based on command line arguments.
    Pass order: Module Removal → Deletion → Empty Scope Removal → Open Minimization → Singleton Namespace Flattening → Public Section Removal → Body Replacement → Text Substitution → Extends Simplification → Attribute Expansion → Import Minimization → Import Inlining → Clear Memory -/
unsafe def buildPassList (args : Args) : Array Pass :=
  -- If --only-X is specified, run only that pass
  if let some passName := args.onlyPass then
    match allPasses.find? (·.1 == passName) with
    | some (_, pass) => #[pass]
    | none => #[]  -- Unknown pass name (shouldn't happen with proper arg parsing)
  else
    -- Normal mode: build pass list based on --no-X flags
    #[]
    |> (if args.noModuleRemoval then id else (·.push moduleRemovalPass))
    |> (if args.noDelete then id else (·.push deletionPass))
    |> (if args.noDelete then id else (·.push emptyScopeRemovalPass))  -- Only run if deletion is enabled
    |> (if args.noDelete then id else (·.push openMinimizationPass))  -- Only run if deletion is enabled
    |> (if args.noDelete then id else (·.push singletonNamespaceFlatteningPass))  -- Only run if deletion is enabled
    |> (·.push publicSectionRemovalPass)  -- Always run public section removal
    |> (if args.noSorry then id else (·.push bodyReplacementPass))
    |> (if args.noTextSubst then id else (·.push textSubstitutionPass))
    |> (if args.noExtendsSimplification then id else (·.push extendsSimplificationPass))
    |> (·.push attributeExpansionPass)  -- Always run attribute expansion
    |> (if args.noImportMinimization then id else (·.push importMinimizationPass))
    |> (if args.noImportInlining then id else (·.push importInliningPass))
    |> (·.push clearMemoryPass)  -- Always run clear memory pass at the end

/-- Parse --run-pass arguments flexibly (handles any order of optional flags) -/
def parseRunPassArgs (args : List String) :
    Option (String × String × String × Bool × Option String × Option String × Bool × Option String) := do
  match args with
  | "--run-pass" :: passName :: file :: rest =>
    let mut marker : Option String := none
    let mut verbose := false
    let mut memoryFile : Option String := none
    let mut stableFile : Option String := none
    let mut isCompleteSweep := true
    let mut tempMarkerFile : Option String := none
    let mut remaining := rest
    while !remaining.isEmpty do
      match remaining with
      | "--marker" :: m :: tail => marker := some m; remaining := tail
      | "--verbose" :: tail => verbose := true; remaining := tail
      | "--memory-file" :: mf :: tail => memoryFile := some mf; remaining := tail
      | "--stable-file" :: sf :: tail => stableFile := some sf; remaining := tail
      | "--unstable-only" :: tail => isCompleteSweep := false; remaining := tail
      | "--temp-marker-file" :: tf :: tail => tempMarkerFile := some tf; remaining := tail
      | _ => remaining := []  -- Unknown arg, stop parsing
    let m ← marker
    return (passName, file, m, verbose, memoryFile, stableFile, isCompleteSweep, tempMarkerFile)
  | _ => none

/-- Entry point -/
unsafe def main (args : List String) : IO UInt32 := do
  -- Handle subprocess subcommands early (before normal arg parsing)
  -- These are used when the minimizer spawns itself as a subprocess
  match args with
  | ["--header-info", file] => return ← handleHeaderInfo file
  | ["--analyze", file] => return ← handleAnalyze file
  | _ =>
    -- Try to parse as --run-pass command
    if let some (passName, file, marker, verbose, memoryFile, stableFile, isCompleteSweep, tempMarkerFile) :=
        parseRunPassArgs args then
      return ← handleRunPass passName file marker verbose memoryFile stableFile isCompleteSweep tempMarkerFile
    else
      pure ()

  initSearchPath (← findSysroot)
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"Error: {msg}"
    IO.eprintln ""
    IO.eprintln "Run with --help for usage information"
    return 1
  | .ok parsedArgs =>
    if parsedArgs.help then
      IO.println help
      return 0

    try
      let passes := buildPassList parsedArgs
      -- Default output file: replace .lean with .out.lean
      let outputFile := parsedArgs.outputFile.getD
        (if parsedArgs.file.endsWith ".lean" then
          (parsedArgs.file.dropEnd 5).toString ++ ".out.lean"
        else
          parsedArgs.file ++ ".out.lean")
      -- If --resume is set and output file exists, use it as input
      let inputFile ← if parsedArgs.resume then do
        if ← System.FilePath.pathExists outputFile then
          IO.eprintln s!"Resuming from {outputFile}"
          pure outputFile
        else
          IO.eprintln s!"Output file {outputFile} not found, starting fresh"
          pure parsedArgs.file
      else
        pure parsedArgs.file
      let isResuming := parsedArgs.resume && (← System.FilePath.pathExists outputFile)
      let input ← IO.FS.readFile inputFile

      -- When resuming, find the topmost section to focus on first
      let mut initialTempMarker : Option String := none
      let mut initialTempMarkerSearchAfter : Option String := none
      if isResuming then do
        -- Parse the file to find commands
        let subprocessResult ← runAnalyzeSubprocess input inputFile
        let some markerIdx := findMarkerIdxInSubprocessSteps subprocessResult.commands parsedArgs.marker
          | throw <| IO.userError (markerNotFoundError parsedArgs.marker)
        -- Find the topmost section
        match findTopmostSection subprocessResult.commands markerIdx with
        | some (sectionName, _endIdx, nextCmdText) =>
          if parsedArgs.verbose then
            IO.eprintln s!"  Found topmost section: {sectionName}"
          -- Use the next command's text as temp marker, or fall back to end marker
          initialTempMarker := some (nextCmdText.getD s!"end {sectionName}")
          initialTempMarkerSearchAfter := some s!"end {sectionName}"
        | none =>
          if parsedArgs.verbose then
            IO.eprintln s!"  No section found, processing entire file"

      let _ ← runPasses passes input inputFile parsedArgs.marker
                     parsedArgs.verbose (some outputFile) parsedArgs.fullRestarts
                     parsedArgs.completeSweepBudget initialTempMarker initialTempMarkerSearchAfter
      IO.eprintln s!"Output written to {outputFile}"
      return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
