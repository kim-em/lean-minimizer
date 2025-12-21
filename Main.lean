import LeanMinimizer
import LeanMinimizer.Pass
import LeanMinimizer.Subprocess
import LeanMinimizer.Passes.ModuleRemoval
import LeanMinimizer.Passes.Deletion
import LeanMinimizer.Passes.EmptyScopeRemoval
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

private unsafe def runPassInnerCore (pass : Pass) (file : String) (marker : String) (verbose : Bool) : IO Unit := do
  -- Read and elaborate
  let source ← IO.FS.readFile file
  let result ← runFrontend source file

  -- Find marker
  let some markerIdx := findMarkerIdxInSteps result.steps marker
    | throw <| IO.userError (markerNotFoundError marker)

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
    subprocessCommands := result.steps.map (·.toSubprocessInfo)
    markerIdx
    outputFile := none
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
  }
  IO.println (toJson jsonResult).compress

private unsafe def runPassInner (pass : Pass) (file : String) (marker : String) (verbose : Bool) : IO UInt32 := do
  try
    runPassInnerCore pass file marker verbose
    return 0
  catch e =>
    IO.eprintln s!"Run-pass error: {e}"
    return 1

/-- Handle --run-pass subcommand (for subprocess invocation).
    This runs a specific pass with full elaboration data.
    Calls processHeader ONCE, runs the pass, outputs JSON result. -/
unsafe def handleRunPass (passName : String) (file : String) (marker : String) (verbose : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)

  -- Find the pass
  match subprocessPassRegistry.find? (·.1 == passName) with
  | none =>
    IO.eprintln s!"Unknown pass: {passName}"
    return 1
  | some (_, pass) => runPassInner pass file marker verbose

/-- All available passes with their CLI flag names -/
unsafe def allPasses : Array (String × Pass) := #[
  ("module-removal", moduleRemovalPass),
  ("delete", deletionPass),
  ("empty-scope", emptyScopeRemovalPass),
  ("body-replacement", bodyReplacementPass),
  ("text-subst", textSubstitutionPass),
  ("extends", extendsSimplificationPass),
  ("attr-expansion", attributeExpansionPass),
  ("import-minimization", importMinimizationPass),
  ("import-inlining", importInliningPass)
]

/-- Build the list of passes based on command line arguments.
    Pass order: Module Removal → Deletion → Empty Scope Removal → Body Replacement → Text Substitution → Extends Simplification → Attribute Expansion → Import Minimization → Import Inlining -/
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
    |> (if args.noSorry then id else (·.push bodyReplacementPass))
    |> (if args.noTextSubst then id else (·.push textSubstitutionPass))
    |> (if args.noExtendsSimplification then id else (·.push extendsSimplificationPass))
    |> (·.push attributeExpansionPass)  -- Always run attribute expansion
    |> (if args.noImportMinimization then id else (·.push importMinimizationPass))
    |> (if args.noImportInlining then id else (·.push importInliningPass))

/-- Entry point -/
unsafe def main (args : List String) : IO UInt32 := do
  -- Handle subprocess subcommands early (before normal arg parsing)
  -- These are used when the minimizer spawns itself as a subprocess
  match args with
  | ["--header-info", file] => return ← handleHeaderInfo file
  | ["--analyze", file] => return ← handleAnalyze file
  | ["--run-pass", passName, file, "--marker", marker] =>
      return ← handleRunPass passName file marker false
  | ["--run-pass", passName, file, "--marker", marker, "--verbose"] =>
      return ← handleRunPass passName file marker true
  | _ => pure ()

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
      let input ← IO.FS.readFile parsedArgs.file
      let passes := buildPassList parsedArgs
      -- Default output file: replace .lean with .out.lean
      let outputFile := parsedArgs.outputFile.getD
        (if parsedArgs.file.endsWith ".lean" then
          (parsedArgs.file.dropEnd 5).toString ++ ".out.lean"
        else
          parsedArgs.file ++ ".out.lean")
      let _ ← runPasses passes input parsedArgs.file parsedArgs.marker
                     parsedArgs.verbose (some outputFile)
      IO.eprintln s!"Output written to {outputFile}"
      return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
