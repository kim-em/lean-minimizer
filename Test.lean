import LeanMinimizer

open Lean LeanMinimizer

/-- Test input with unused definitions -/
def testInput : String := "def unused1 := 1
def unused2 := 2
def needed := 42
section invariant
#check needed
end invariant
"

/-- Expected output: only `needed` should remain -/
def expectedOutput : String := "def needed := 42
section invariant
#check needed
end invariant
"

/-- Run the minimizer test -/
unsafe def runTest : IO Bool := do
  initSearchPath (← findSysroot)
  let result ← minimize testInput "<test>" "invariant" false

  -- Normalize whitespace for comparison
  let resultLines := result.splitOn "\n" |>.filter (!·.isEmpty)
  let expectedLines := expectedOutput.splitOn "\n" |>.filter (!·.isEmpty)

  if resultLines == expectedLines then
    IO.println "✓ Test passed: minimizer correctly removed unused definitions"
    return true
  else
    IO.eprintln "✗ Test failed!"
    IO.eprintln s!"Expected:\n{expectedOutput}"
    IO.eprintln s!"Got:\n{result}"
    return false

/-- Entry point for `lake exe test` -/
unsafe def main : IO UInt32 := do
  IO.println "Running lean-minimizer tests..."
  IO.println ""

  let passed ← runTest

  if passed then
    IO.println ""
    IO.println "All tests passed!"
    return 0
  else
    return 1
