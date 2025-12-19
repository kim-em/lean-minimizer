import LeanMinimizer
import LeanMinimizer.Pass
import LeanMinimizer.Passes.ModuleRemoval
import LeanMinimizer.Passes.Deletion
import LeanMinimizer.Passes.ImportMinimization

open Lean LeanMinimizer

/-- Build the list of passes based on command line arguments.
    Pass order: Module Removal → Deletion → Import Minimization -/
unsafe def buildPassList (args : Args) : Array Pass :=
  #[]
  |> (if args.noModuleRemoval then id else (·.push moduleRemovalPass))
  |> (if args.noDelete then id else (·.push deletionPass))
  |> (if args.noImportMinimization then id else (·.push importMinimizationPass))

/-- Entry point -/
unsafe def main (args : List String) : IO UInt32 := do
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
      let result ← runPasses passes input parsedArgs.file parsedArgs.marker parsedArgs.verbose
      IO.print result
      return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
