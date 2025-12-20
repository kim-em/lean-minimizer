import LeanMinimizer
import LeanMinimizer.Pass
import LeanMinimizer.Passes.ModuleRemoval
import LeanMinimizer.Passes.Deletion
import LeanMinimizer.Passes.EmptyScopeRemoval
import LeanMinimizer.Passes.BodyReplacement
import LeanMinimizer.Passes.TextSubstitution
import LeanMinimizer.Passes.ExtendsSimplification
import LeanMinimizer.Passes.ImportMinimization
import LeanMinimizer.Passes.ImportInlining

open Lean LeanMinimizer

/-- Build the list of passes based on command line arguments.
    Pass order: Module Removal → Deletion → Empty Scope Removal → Body Replacement → Text Substitution → Extends Simplification → Import Minimization → Import Inlining -/
unsafe def buildPassList (args : Args) : Array Pass :=
  #[]
  |> (if args.noModuleRemoval then id else (·.push moduleRemovalPass))
  |> (if args.noDelete then id else (·.push deletionPass))
  |> (if args.noDelete then id else (·.push emptyScopeRemovalPass))  -- Only run if deletion is enabled
  |> (if args.noSorry then id else (·.push bodyReplacementPass))
  |> (if args.noTextSubst then id else (·.push textSubstitutionPass))
  |> (if args.noExtendsSimplification then id else (·.push extendsSimplificationPass))
  |> (if args.noImportMinimization then id else (·.push importMinimizationPass))
  |> (if args.noImportInlining then id else (·.push importInliningPass))

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
