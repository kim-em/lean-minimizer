/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer
import LeanMinimizerTest.Component.RunFrontend
import LeanMinimizerTest.Component.GetNewConstants
import LeanMinimizerTest.Component.GetReferencedConstants
import LeanMinimizerTest.Component.BuildDependencyMap
import LeanMinimizerTest.Component.ComputeReachable
import LeanMinimizerTest.Component.DependencyHeuristic

open Lean System LeanMinimizer

/-- Base test directory -/
def testDir : FilePath := "LeanMinimizerTest"

/-- Golden tests directory -/
def goldenDir : FilePath := testDir / "Golden"

/-- CLI tests directory -/
def cliDir : FilePath := testDir / "CLI"

/-- Default marker pattern -/
def defaultMarker : String := "#guard_msgs"

/-- Find all .lean test files in a directory (excluding .out and .marker files) -/
def findTestFilesIn (dir : FilePath) : IO (Array FilePath) := do
  if !(← dir.pathExists) then
    return #[]
  let entries ← dir.readDir
  let leanFiles := entries.filterMap fun entry =>
    let path := entry.path
    let name := entry.fileName
    if name.endsWith ".lean" && !containsSubstr name ".expected" && !containsSubstr name ".produced" then
      some path
    else
      none
  return leanFiles.qsort (·.toString < ·.toString)

/-- Find CLI test files in a directory.
    CLI tests can be either:
    - X.lean files (where X.lean is the input)
    - X.lean.input files (where X.lean.input specifies the input path)
    Returns paths without the .input suffix. -/
def findCLITestFilesIn (dir : FilePath) : IO (Array FilePath) := do
  if !(← dir.pathExists) then
    return #[]
  let entries ← dir.readDir
  let mut tests : Array FilePath := #[]

  for entry in entries do
    let name := entry.fileName
    -- Direct .lean test files
    if name.endsWith ".lean" && !containsSubstr name ".expected" && !containsSubstr name ".produced" then
      tests := tests.push entry.path
    -- .lean.input files define tests with external input
    else if name.endsWith ".lean.input" then
      -- Extract test name (remove .input suffix)
      let testName := name.dropRight 6  -- drop ".input"
      let testPath := dir / testName
      -- Only add if there isn't already a .lean file for this test
      if !tests.contains testPath then
        tests := tests.push testPath

  return tests.qsort (·.toString < ·.toString)

/-- Get the marker for a test file (from .marker file or default) -/
def getMarker (testFile : FilePath) : IO String := do
  let markerFile : FilePath := testFile.toString ++ ".marker"
  if ← markerFile.pathExists then
    let marker ← IO.FS.readFile markerFile
    return marker.trim
  else
    return defaultMarker

/-- Result of running a single test -/
inductive TestResult
  | passed
  | failed (diff : String)
  | error (msg : String)
  | missingExpected

/-- Run minimizer on a test file and compare with expected output -/
unsafe def runGoldenTest (testFile : FilePath) : IO TestResult := do
  let expectedFile : FilePath := testFile.toString ++ ".expected.out"
  let producedFile : FilePath := testFile.toString ++ ".produced.out"

  -- Check expected file exists
  if !(← expectedFile.pathExists) then
    return .missingExpected

  -- Read input, expected, and marker
  let input ← IO.FS.readFile testFile
  let expected ← IO.FS.readFile expectedFile
  let marker ← getMarker testFile

  -- Run minimizer (using same code path as CLI)
  let produced ← try
    let passes := #[deletionPass]
    runPasses passes input testFile.toString marker false
  catch e =>
    return .error s!"Minimizer failed: {e}"

  -- Write produced output
  IO.FS.writeFile producedFile produced

  -- Compare (normalize trailing newlines)
  let expectedNorm := expected.trimRight ++ "\n"
  let producedNorm := produced.trimRight ++ "\n"

  if expectedNorm == producedNorm then
    return .passed
  else
    -- Generate diff
    let diffResult ← IO.Process.output {
      cmd := "diff"
      args := #["-u", "--label", "expected", "--label", "produced",
                expectedFile.toString, producedFile.toString]
    }
    return .failed diffResult.stdout

/-- Copy produced output to expected output for a test -/
def acceptGoldenTest (testFile : FilePath) : IO Unit := do
  let expectedFile : FilePath := testFile.toString ++ ".expected.out"
  let producedFile : FilePath := testFile.toString ++ ".produced.out"

  if ← producedFile.pathExists then
    let produced ← IO.FS.readFile producedFile
    IO.FS.writeFile expectedFile produced
    IO.println s!"  Updated: {expectedFile}"
  else
    IO.eprintln s!"  No produced output for {testFile}"

/-- Print test name from path -/
def testName (path : FilePath) : String :=
  path.fileName.getD path.toString

/-- Check if a test should be accepted -/
def shouldAccept (name : String) (acceptName : Option String) : Bool :=
  match acceptName with
  | none => true              -- accept all
  | some n => name == n       -- exact match only

/-! ## CLI Tests -/

/-- Get extra CLI args for a test file (from .args file or default) -/
def getCLIArgs (testFile : FilePath) : IO (Array String) := do
  let argsFile : FilePath := testFile.toString ++ ".args"
  if ← argsFile.pathExists then
    let content ← IO.FS.readFile argsFile
    return content.trim.splitOn " " |>.toArray
  else
    return #[]

/-- Get input file for a CLI test (from .input file or use test file itself) -/
def getCLIInput (testFile : FilePath) : IO FilePath := do
  let inputFile : FilePath := testFile.toString ++ ".input"
  if ← inputFile.pathExists then
    let content ← IO.FS.readFile inputFile
    return content.trim
  else
    return testFile

/-- Get expected exit code for a test file (from .expected.exit file or default 0) -/
def getExpectedExit (testFile : FilePath) : IO UInt32 := do
  let exitFile : FilePath := testFile.toString ++ ".expected.exit"
  if ← exitFile.pathExists then
    let content ← IO.FS.readFile exitFile
    return content.trim.toNat!.toUInt32
  else
    return 0

/-- Run a CLI test by executing the minimizer and comparing output -/
def runCLITest (testFile : FilePath) : IO TestResult := do
  let expectedOutFile : FilePath := testFile.toString ++ ".expected.out"
  let expectedErrFile : FilePath := testFile.toString ++ ".expected.err"
  let producedOutFile : FilePath := testFile.toString ++ ".produced.out"
  let producedErrFile : FilePath := testFile.toString ++ ".produced.err"

  let inputFile ← getCLIInput testFile
  let extraArgs ← getCLIArgs testFile
  let expectedExit ← getExpectedExit testFile

  -- Run minimizer from project root
  let cwd ← IO.currentDir
  let args := #[inputFile.toString] ++ extraArgs
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "minimize"] ++ args
    cwd := cwd
  }

  -- Write produced outputs
  IO.FS.writeFile producedOutFile result.stdout
  IO.FS.writeFile producedErrFile result.stderr

  -- Check expected files exist (after producing output so --accept works)
  if !(← expectedOutFile.pathExists) then
    return .missingExpected

  let expectedOut ← IO.FS.readFile expectedOutFile
  let expectedErr ← if ← expectedErrFile.pathExists then
    IO.FS.readFile expectedErrFile
  else
    pure ""

  -- Check exit code
  if result.exitCode != expectedExit then
    return .failed s!"Exit code mismatch: expected {expectedExit}, got {result.exitCode}\nstdout: {result.stdout}\nstderr: {result.stderr}"

  -- Compare stdout (normalize trailing newlines)
  let expectedOutNorm := expectedOut.trimRight ++ "\n"
  let producedOutNorm := result.stdout.trimRight ++ "\n"

  if expectedOutNorm != producedOutNorm then
    let diffResult ← IO.Process.output {
      cmd := "diff"
      args := #["-u", "--label", "expected.out", "--label", "produced.out",
                expectedOutFile.toString, producedOutFile.toString]
    }
    return .failed diffResult.stdout

  -- Compare stderr (normalize trailing newlines)
  let expectedErrNorm := expectedErr.trimRight ++ "\n"
  let producedErrNorm := result.stderr.trimRight ++ "\n"

  if expectedErrNorm != producedErrNorm then
    let diffResult ← IO.Process.output {
      cmd := "diff"
      args := #["-u", "--label", "expected.err", "--label", "produced.err",
                expectedErrFile.toString, producedErrFile.toString]
    }
    return .failed diffResult.stdout

  return .passed

/-- Copy produced output to expected output for a CLI test -/
def acceptCLITest (testFile : FilePath) : IO Unit := do
  let expectedOutFile : FilePath := testFile.toString ++ ".expected.out"
  let expectedErrFile : FilePath := testFile.toString ++ ".expected.err"
  let producedOutFile : FilePath := testFile.toString ++ ".produced.out"
  let producedErrFile : FilePath := testFile.toString ++ ".produced.err"

  if ← producedOutFile.pathExists then
    let produced ← IO.FS.readFile producedOutFile
    IO.FS.writeFile expectedOutFile produced
    IO.println s!"  Updated: {expectedOutFile}"
  else
    IO.eprintln s!"  No produced stdout for {testFile}"

  if ← producedErrFile.pathExists then
    let produced ← IO.FS.readFile producedErrFile
    -- Only write .expected.err if there's actual content
    if !produced.isEmpty then
      IO.FS.writeFile expectedErrFile produced
      IO.println s!"  Updated: {expectedErrFile}"

/-- Run all CLI tests. Returns (passed, failed).
    If acceptFilter is some, only accept tests matching the filter. -/
def runCLITests (acceptFilter : Option (Option String) := none) : IO (Nat × Nat) := do
  let cliFiles ← findCLITestFilesIn cliDir

  if cliFiles.isEmpty then
    IO.eprintln s!"Warning: No CLI test files found in {cliDir}"
    return (0, 0)

  let mut passed := 0
  let mut failed := 0

  for testFile in cliFiles do
    let name := testName testFile

    if let some acceptName := acceptFilter then
      if shouldAccept name acceptName then
        acceptCLITest testFile
      continue

    let result ← runCLITest testFile

    match result with
    | .passed =>
      IO.println s!"  ✓ {name}"
      passed := passed + 1
    | .failed diff =>
      IO.println s!"  ✗ {name}"
      IO.println ""
      IO.println diff
      failed := failed + 1
    | .error msg =>
      IO.println s!"  ✗ {name}: {msg}"
      failed := failed + 1
    | .missingExpected =>
      IO.println s!"  ? {name}: missing .expected.out (run and review, then --accept)"
      failed := failed + 1

  return (passed, failed)

/-! ## Component Tests -/

/-- Run all component tests. Returns (passed, failed). -/
unsafe def runComponentTests : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0

  let tests : List (IO Bool) := [
    LeanMinimizerTest.Component.RunFrontend.test,
    LeanMinimizerTest.Component.GetNewConstants.test,
    LeanMinimizerTest.Component.GetReferencedConstants.test,
    LeanMinimizerTest.Component.BuildDependencyMap.test,
    LeanMinimizerTest.Component.ComputeReachable.test,
    LeanMinimizerTest.Component.DependencyHeuristic.test
  ]

  for test in tests do
    if ← test then
      passed := passed + 1
    else
      failed := failed + 1

  return (passed, failed)

/-! ## Main Entry Point -/

/-- Parse --accept flag and optional test name.
    Returns: none (no --accept), some none (accept all), some (some name) (accept specific test) -/
def parseAcceptArg (args : List String) : Option (Option String) :=
  match args.dropWhile (· != "--accept") with
  | "--accept" :: next :: _ =>
    if next.startsWith "--" then some none  -- --accept followed by another flag
    else some (some next)                    -- --accept <test-name>
  | "--accept" :: [] => some none            -- --accept at end
  | _ => none                                 -- no --accept

/-- Entry point for `lake exe test` -/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)

  let acceptArg := parseAcceptArg args
  let accept := acceptArg.isSome
  let acceptFilter := acceptArg.join  -- Option (Option String) → Option String

  if accept then
    match acceptFilter with
    | none => IO.println "Accepting all test outputs..."
    | some f => IO.println s!"Accepting test '{f}'..."
    IO.println ""

  let mut passed := 0
  let mut failed := 0
  let mut errors := 0

  -- Run CLI tests
  IO.println "Running CLI tests..."
  IO.println ""

  let (cliPassed, cliFailed) ← runCLITests acceptArg
  passed := passed + cliPassed
  failed := failed + cliFailed

  -- Run component tests
  IO.println ""
  IO.println "Running component tests..."
  IO.println ""

  let (componentPassed, componentFailed) ← runComponentTests
  passed := passed + componentPassed
  failed := failed + componentFailed

  -- Run golden tests
  let goldenFiles ← findTestFilesIn goldenDir

  if goldenFiles.isEmpty then
    IO.eprintln s!"Warning: No golden test files found in {goldenDir}"
  else
    IO.println ""
    IO.println s!"Running {goldenFiles.size} golden tests from {goldenDir}/"
    IO.println ""

    for testFile in goldenFiles do
      let name := testName testFile

      if let some acceptName := acceptArg then
        if shouldAccept name acceptName then
          acceptGoldenTest testFile
        continue

      let result ← runGoldenTest testFile

      match result with
      | .passed =>
        IO.println s!"  ✓ {name}"
        passed := passed + 1
      | .failed diff =>
        IO.println s!"  ✗ {name}"
        IO.println ""
        IO.println diff
        failed := failed + 1
      | .error msg =>
        IO.println s!"  ✗ {name}: {msg}"
        errors := errors + 1
      | .missingExpected =>
        IO.println s!"  ? {name}: missing .expected.out (run minimizer and review, then --accept)"
        errors := errors + 1

  if accept then
    IO.println ""
    IO.println "Done. Review changes and commit."
    return 0

  -- Summary
  IO.println ""
  IO.println s!"Results: {passed} passed, {failed} failed, {errors} errors"

  if failed > 0 || errors > 0 then
    IO.println ""
    IO.println "To update expected outputs after review:"
    IO.println "  lake exe test --accept"
    return 1

  return 0
