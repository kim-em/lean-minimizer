import LeanMinimizer

open Lean LeanMinimizer

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
      let result ← minimize input parsedArgs.file parsedArgs.marker parsedArgs.verbose
      IO.print result
      return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
