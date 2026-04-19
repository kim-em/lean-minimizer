/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.Frontend
import Lean.Elab.Command
import Lean.Util.Path
import LeanMinimizer.LakefileOptions

/-!
# Minimize: A Lean test case minimizer

This tool finds commands in a Lean file that can be removed while preserving
compilation of a marked "invariant" section.

Usage:
  lake exe minimize <file.lean> [--marker <pattern>]

The tool finds a marker in the file (default: "invariant") and uses delta debugging
to find a minimal set of commands before the marker that are needed for the file
to compile.
-/

/-- Check if `needle` is a substring of `haystack`.
    Note: Lean's stdlib doesn't provide a substring search function as of v4.27,
    so we implement our own using splitOn. -/
def String.containsSubstr (haystack needle : String) : Bool :=
  -- Use splitOn: if needle is present, splitOn will return > 1 element
  needle.isEmpty || (haystack.splitOn needle).length > 1

namespace LeanMinimizer

open Lean Elab Frontend Parser

/-- Get the system temp directory in a cross-platform way.
    Checks TMPDIR (Unix), TEMP, TMP (Windows) environment variables,
    falling back to /tmp if none are set. -/
def getTempDir : IO System.FilePath := do
  -- Try Unix-style TMPDIR first
  if let some dir ← IO.getEnv "TMPDIR" then
    return System.FilePath.mk dir
  -- Try Windows-style TEMP
  if let some dir ← IO.getEnv "TEMP" then
    return System.FilePath.mk dir
  -- Try Windows-style TMP
  if let some dir ← IO.getEnv "TMP" then
    return System.FilePath.mk dir
  -- Fall back to /tmp
  return System.FilePath.mk "/tmp"

/-- Help string for the command line interface -/
def help : String := "Lean test case minimizer

Usage: lake exe minimize [OPTIONS] <FILE>

Arguments:
  <FILE>
    The Lean file to minimize.

Options:
  --marker <PATTERN>
    Pattern to search for in commands to identify the invariant section.
    Default: \"#guard_msgs\"

  -q, --quiet
    Suppress progress information during minimization.

  -o, --output <FILE>
    Write output to FILE. Defaults to <input>.out.lean if not specified.
    The file is updated after each successful minimization step,
    allowing you to follow along in an editor as the minimization progresses.

  --no-module-removal
    Disable the module system removal pass.

  --no-delete
    Disable the command deletion pass.

  --no-sorry
    Disable the body replacement pass (replacing bodies with sorry).

  --no-import-minimization
    Disable the import minimization pass.

  --no-import-inlining
    Disable the import inlining pass.

  --no-text-subst
    Disable the text substitution pass.

  --no-extends
    Disable the extends clause simplification pass.

  --resume
    Resume a previous minimization run. If the output file exists, use it
    as the input instead of the original file. This allows continuing an
    interrupted minimization.

  --cross-workspace <PATH>
    Cross-version minimization. Specifies a second, pre-built Lake
    workspace whose `lean-toolchain` pins a different Lean release. The
    file must compile successfully under BOTH the primary toolchain
    (the one `lake exe minimize` is itself running under) and the cross
    workspace's toolchain, after each minimization step.

    Cross-checks are performed by spawning `lake env lean` with the
    given path as the working directory, with inherited Lake/Lean/elan
    environment variables explicitly cleared so that the cross workspace
    controls toolchain and library resolution.

    Use #elab_if to conditionally elaborate code based on the Lean
    version, and #guard_msgs to capture version-specific error messages.
    This way the file encodes exactly what behavior is expected on each
    toolchain, and the minimizer just ensures both succeed.

    See the #elab_if section below for the definition and usage.

  --only-<PASS>
    Run only the specified pass once. Available passes:
      --only-module-removal    Module system removal
      --only-delete            Command deletion
      --only-empty-scope       Empty scope removal
      --only-sorry             Body replacement (sorry)
      --only-text-subst        Text substitution
      --only-field-removal     Structure field removal
      --only-extends           Extends simplification
      --only-attr-expansion    Attribute expansion
      --only-import-minimization  Import minimization
      --only-import-inlining   Import inlining

  --git
    Commit to git after each minimization step that makes a change.
    The workspace must already be a git repo. Each commit uses a message
    describing which pass made the change.

  --help
    Show this help message.

Example:
  lake exe minimize test.lean
  lake exe minimize test.lean --marker \"section invariant\"

The tool will find the first command containing the marker pattern and
remove as many commands before it as possible while keeping the file
compilable. It uses dependency analysis to identify which commands are
actually needed by the invariant section and removes unneeded commands first.

Tip: Use #guard_msgs to mark the section you want to preserve:

  /-- error: unknown identifier 'foo' -/
  #guard_msgs in
  #check foo

This captures the exact error message, making it ideal for bug reports
and regression tests.

Cross-version minimization:
  If a file behaves differently under two Lean versions, use #elab_if
  to conditionally elaborate version-specific code. Define #elab_if
  by adding this to the top of your file (after `import Lean`):

    open Lean Elab Command Term Meta in
    elab \"#elab_if \" cond:term \" in \" cmd:command : command => do
      if (← liftTermElabM do unsafe
        evalExpr Bool (mkConst ``Bool) (← elabTerm cond (some (mkConst ``Bool)))
      ) then elabCommand cmd

  Then use it to guard version-specific behavior:

    -- This theorem works on v4.28.0-rc1
    #elab_if Lean.versionString == \"4.28.0-rc1\" in
    theorem foo : ... := by some_tactic

    -- On v4.27.0, the tactic fails with a specific error
    #elab_if Lean.versionString == \"4.27.0\" in
    /-- error: tactic 'some_tactic' failed -/
    #guard_msgs in
    theorem foo : ... := by some_tactic

  Then minimize with:

    lake exe minimize test.lean --cross-workspace /path/to/cross-ws

  where `/path/to/cross-ws` is a pre-built Lake workspace with a
  `lean-toolchain` pinning the alternate toolchain (e.g. v4.27.0) and
  the same project dependencies as the primary workspace.

  The minimizer ensures the file compiles under BOTH toolchains.
"

/-- Parsed command line arguments -/
structure Args where
  file : String
  marker : String := "#guard_msgs"
  quiet : Bool := false
  help : Bool := false
  /-- Output file to write intermediate results to -/
  outputFile : Option String := none
  /-- Disable the module system removal pass -/
  noModuleRemoval : Bool := false
  /-- Disable the deletion pass -/
  noDelete : Bool := false
  /-- Disable the body replacement pass -/
  noSorry : Bool := false
  /-- Disable the import minimization pass -/
  noImportMinimization : Bool := false
  /-- Disable the import inlining pass -/
  noImportInlining : Bool := false
  /-- Disable the text substitution pass -/
  noTextSubst : Bool := false
  /-- Disable the structure field removal pass -/
  noFieldRemoval : Bool := false
  /-- Disable the extends clause simplification pass -/
  noExtendsSimplification : Bool := false
  /-- Run only a specific pass (by CLI flag name) -/
  onlyPass : Option String := none
  /-- Resume from output file if it exists -/
  resume : Bool := false
  /-- Budget for complete sweeps as fraction of runtime (0.0-1.0, default 0.20) -/
  completeSweepBudget : Float := 0.20
  /-- Cross-version minimization: a second toolchain where the file must also compile.
      Use with #elab_if to encode version-specific expectations in the file itself. -/
  crossWorkspace : Option String := none
  /-- Commit to git after each pass that makes a change -/
  gitCommit : Bool := false

/-- Check if verbose output is enabled (default is verbose, --quiet disables) -/
def Args.verbose (args : Args) : Bool := !args.quiet

/-- Parse command line arguments -/
def parseArgs (args : List String) : Except String Args := do
  let rec go (args : List String) (acc : Args) : Except String Args :=
    match args with
    | [] =>
      if acc.file.isEmpty && !acc.help then
        .error "No input file specified"
      else
        .ok acc
    | "--help" :: rest => go rest { acc with help := true }
    | "--quiet" :: rest => go rest { acc with quiet := true }
    | "-q" :: rest => go rest { acc with quiet := true }
    | "--marker" :: pattern :: rest => go rest { acc with marker := pattern }
    | "--marker" :: [] => .error "--marker requires an argument"
    | "-o" :: path :: rest => go rest { acc with outputFile := some path }
    | "--output" :: path :: rest => go rest { acc with outputFile := some path }
    | "-o" :: [] => .error "-o requires an argument"
    | "--output" :: [] => .error "--output requires an argument"
    | "--no-delete" :: rest => go rest { acc with noDelete := true }
    | "--no-module-removal" :: rest => go rest { acc with noModuleRemoval := true }
    | "--no-sorry" :: rest => go rest { acc with noSorry := true }
    | "--no-import-minimization" :: rest => go rest { acc with noImportMinimization := true }
    | "--no-import-inlining" :: rest => go rest { acc with noImportInlining := true }
    | "--no-text-subst" :: rest => go rest { acc with noTextSubst := true }
    | "--no-field-removal" :: rest => go rest { acc with noFieldRemoval := true }
    | "--no-extends" :: rest => go rest { acc with noExtendsSimplification := true }
    | "--only-delete" :: rest => go rest { acc with onlyPass := some "delete" }
    | "--only-module-removal" :: rest => go rest { acc with onlyPass := some "module-removal" }
    | "--only-sorry" :: rest => go rest { acc with onlyPass := some "body-replacement" }
    | "--only-import-minimization" :: rest => go rest { acc with onlyPass := some "import-minimization" }
    | "--only-import-inlining" :: rest => go rest { acc with onlyPass := some "import-inlining" }
    | "--only-text-subst" :: rest => go rest { acc with onlyPass := some "text-subst" }
    | "--only-field-removal" :: rest => go rest { acc with onlyPass := some "field-removal" }
    | "--only-extends" :: rest => go rest { acc with onlyPass := some "extends" }
    | "--only-attr-expansion" :: rest => go rest { acc with onlyPass := some "attr-expansion" }
    | "--only-empty-scope" :: rest => go rest { acc with onlyPass := some "empty-scope" }
    | "--git" :: rest => go rest { acc with gitCommit := true }
    | "--resume" :: rest => go rest { acc with resume := true }
    | "--cross-workspace" :: path :: rest => go rest { acc with crossWorkspace := some path }
    | "--cross-workspace" :: [] => .error "--cross-workspace requires an argument"
    | "--cross-toolchain" :: _ :: _ | "--cross-toolchain" :: [] =>
        .error "--cross-toolchain was replaced by --cross-workspace; see `--help`"
    | "--complete-sweep-budget" :: value :: rest =>
      -- Parse as percentage (0-100) and convert to fraction
      match value.toNat? with
      | some n =>
        if n > 100 then
          .error "--complete-sweep-budget must be between 0 and 100 (percentage)"
        else
          go rest { acc with completeSweepBudget := n.toFloat / 100.0 }
      | none => .error s!"--complete-sweep-budget requires an integer percentage (0-100, got '{value}')"
    | "--complete-sweep-budget" :: [] => .error "--complete-sweep-budget requires an argument"
    | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"Unknown option: {arg}"
      else if acc.file.isEmpty then
        go rest { acc with file := arg }
      else
        .error s!"Unexpected argument: {arg}"
  if args.isEmpty then
    .ok { file := "", help := true }
  else
    go args { file := "" }

/-- Error message when marker is not found in the file -/
def markerNotFoundError (marker : String) : String :=
  s!"Marker pattern '{marker}' not found in any command.

Add a marker to identify the section you want to preserve. The recommended
approach is to use #guard_msgs to capture the exact error:

  /-- error: unknown identifier 'foo' -/
  #guard_msgs in
  #check foo

Alternatively, use --marker to specify a different pattern."

/-- Information about a parsed command -/
structure CmdInfo where
  /-- Index in the command array -/
  idx : Nat
  /-- The parsed syntax -/
  stx : Syntax
  /-- Start position in the source file (includes leading whitespace/comments from previous) -/
  startPos : String.Pos.Raw
  /-- End position in the source file (including trailing whitespace) -/
  endPos : String.Pos.Raw
  deriving Inhabited

/-- State for the minimization process -/
structure MinState where
  /-- Original file content -/
  input : String
  /-- File name -/
  fileName : String
  /-- The header syntax -/
  header : Syntax
  /-- End position of header (including trailing whitespace) -/
  headerEndPos : String.Pos.Raw
  /-- All commands (before + invariant) -/
  allCommands : Array CmdInfo
  /-- Index of the marker command -/
  markerIdx : Nat
  /-- Whether to print verbose output -/
  verbose : Bool
  /-- Counter for compilation tests -/
  testCount : IO.Ref Nat
  /-- Output file to write intermediate results to (optional) -/
  outputFile : Option String := none
  /-- Cross-version minimization: a second toolchain where the file must also compile -/
  crossWorkspace : Option String := none

/-- A heuristic for splitting candidates during delta debugging.

    Given the minimization state and current candidate indices, returns a split
    `(tryRemoveFirst, tryRemoveSecond)` that partitions the candidates.

    The algorithm will:
    1. Try removing `tryRemoveFirst` (keeping `tryRemoveSecond`)
    2. If that fails, try removing `tryRemoveSecond` (keeping `tryRemoveFirst`)
    3. If both fail, recurse on each half

    A good heuristic puts commands likely to be removable in `tryRemoveFirst`.

    The heuristic has access to:
    - `state.allCommands` for command syntax and source positions
    - `state.input` for the original file content
    - `state.markerIdx` for the marker position
-/
def SplitHeuristic := MinState → Array Nat → IO (Array Nat × Array Nat)

/-- Default heuristic: split candidates in half by index.
    This is the standard delta debugging approach. -/
def defaultSplitHeuristic : SplitHeuristic := fun _ candidates => do
  let n := candidates.size / 2
  return (candidates[:n].toArray, candidates[n:].toArray)

/-! ## String Access Patterns

This codebase uses two main patterns for string access:

1. **`String.Pos.Raw.get`/`String.Pos.Raw.extract`**: For safe, position-aware character
   and substring access. Use this for general character iteration and extraction.

2. **Cached `toUTF8` byte array**: For byte-level scanning (e.g., detecting multi-byte
   Unicode sequences). Cache the array once at function start to avoid repeated allocations:
   ```
   let bytes := source.toUTF8
   let b := bytes[i]!
   ```

Prefer pattern 1 unless you specifically need byte-level access for UTF-8 sequence detection.
-/

/-- Get source text for a command from the original input (includes leading comments) -/
def CmdInfo.getSource (cmd : CmdInfo) (input : String) : String :=
  String.Pos.Raw.extract input cmd.startPos cmd.endPos

/-- Skip whitespace and line comments starting from a position -/
partial def skipWhitespaceAndComments (input : String) (startPos : String.Pos.Raw) (endPos : String.Pos.Raw) : String.Pos.Raw :=
  let endN := endPos.byteIdx
  let rec loop (pos : Nat) : Nat :=
    if pos >= endN then pos
    else
      let c := String.Pos.Raw.get input ⟨pos⟩
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
        loop (pos + 1)
      else if c == '-' && pos + 1 < endN && String.Pos.Raw.get input ⟨pos + 1⟩ == '-' then
        -- Line comment: skip to end of line
        let rec skipLine (p : Nat) : Nat :=
          if p >= endN then p
          else if String.Pos.Raw.get input ⟨p⟩ == '\n' then loop (p + 1)
          else skipLine (p + 1)
        skipLine (pos + 2)
      else
        pos
  ⟨loop startPos.byteIdx⟩

/-- Skip trailing whitespace and line comments, going backwards from endPos.
    Returns the position after the first newline following actual content.
    This preserves the newline separator between commands. -/
partial def skipTrailingWhitespaceAndComments (input : String) (startPos : String.Pos.Raw) (endPos : String.Pos.Raw) : String.Pos.Raw :=
  let startN := startPos.byteIdx
  -- First, find where trailing whitespace/comments start by going backwards
  let rec findContentEnd (pos : Nat) : Nat :=
    if pos <= startN then startN
    else
      let prevPos := pos - 1
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == ' ' || c == '\t' || c == '\r' then
        findContentEnd prevPos
      else if c == '\n' then
        -- Check if line before this is a comment
        let rec checkLineComment (p : Nat) : Option Nat :=
          if p <= startN then none
          else
            let pp := p - 1
            let cc := String.Pos.Raw.get input ⟨pp⟩
            if cc == '\n' then none  -- Reached previous line without finding --
            else if cc == '-' && pp > startN && String.Pos.Raw.get input ⟨pp - 1⟩ == '-' then
              some (pp - 1)  -- Found start of --
            else checkLineComment pp
        match checkLineComment prevPos with
        | some commentStart => findContentEnd commentStart
        | none => findContentEnd prevPos  -- Blank line, continue
      else
        pos  -- Found actual content
  let contentEnd := findContentEnd endPos.byteIdx
  -- Now find the first newline after contentEnd (to include it as separator)
  let rec findNewline (pos : Nat) : Nat :=
    if pos >= endPos.byteIdx then endPos.byteIdx
    else if String.Pos.Raw.get input ⟨pos⟩ == '\n' then pos + 1
    else findNewline (pos + 1)
  ⟨findNewline contentEnd⟩

/-- Get source text for just the syntax (excludes leading AND trailing comments) -/
def CmdInfo.getSyntaxSource (cmd : CmdInfo) (input : String) : String :=
  let actualStart := skipWhitespaceAndComments input cmd.startPos cmd.endPos
  let actualEnd := skipTrailingWhitespaceAndComments input cmd.startPos cmd.endPos
  String.Pos.Raw.extract input actualStart actualEnd

/-- Find where trailing whitespace and line comments end, going backwards from a position -/
partial def findHeaderEnd (input : String) (endPos : String.Pos.Raw) : String.Pos.Raw :=
  -- Go backwards from endPos to find where actual content ends
  -- We want to strip trailing whitespace and line comments
  let endN := endPos.byteIdx
  let rec loop (pos : Nat) : Nat :=
    if pos == 0 then 0
    else
      let prevPos := pos - 1
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == ' ' || c == '\t' || c == '\r' then
        loop prevPos
      else if c == '\n' then
        -- Check if the line before this newline is a comment
        let rec checkLineComment (p : Nat) : Option Nat :=
          if p == 0 then none
          else
            let pp := p - 1
            let cc := String.Pos.Raw.get input ⟨pp⟩
            if cc == '\n' then none  -- Reached previous line
            else if cc == '-' && pp > 0 && String.Pos.Raw.get input ⟨pp - 1⟩ == '-' then
              some (pp - 1)  -- Found start of --
            else checkLineComment pp
        match checkLineComment prevPos with
        | some commentStart => loop commentStart
        | none => pos  -- Not a comment line, keep newline
      else
        pos  -- Found actual content
  ⟨loop endN⟩

/-- Reconstruct source from header and selected command indices -/
def reconstructSource (state : MinState) (keepIndices : Array Nat) : String := Id.run do
  -- Include header, but strip trailing comments
  let headerEnd := findHeaderEnd state.input state.headerEndPos
  let mut result := String.Pos.Raw.extract state.input ⟨0⟩ headerEnd

  -- Track if we need to add separator
  let mut needsSep := false

  -- Add kept commands before marker (in sorted order to preserve original order)
  -- Use getSyntaxSource to strip leading comments - comments should be dropped with their command
  let sortedIndices := keepIndices.qsort (· < ·)
  for idx in sortedIndices do
    if idx < state.markerIdx then
      let cmd := state.allCommands[idx]!
      let src := cmd.getSyntaxSource state.input
      -- Add blank line between commands
      if needsSep then
        if !result.endsWith "\n" then
          result := result ++ "\n\n"
        else if !result.endsWith "\n\n" then
          result := result ++ "\n"
      result := result ++ src
      needsSep := true

  -- Always include marker and everything after (preserve full source including docstrings)
  for i in [state.markerIdx : state.allCommands.size] do
    let cmd := state.allCommands[i]!
    let src := cmd.getSyntaxSource state.input
    -- Add blank line between commands
    if needsSep then
      if !result.endsWith "\n" then
        result := result ++ "\n\n"
      else if !result.endsWith "\n\n" then
        result := result ++ "\n"
    result := result ++ src
    needsSep := true

  result

/-- Internal: run `lean` on `source` inside `crossWorkspace` under a hermetic
    allowlist environment. Returns `(success, combinedOutput)` where
    `combinedOutput` is the child's stdout+stderr (useful on failure).

    Two subtleties make this tricky:

    * `lake env` injects the PRIMARY toolchain's `bin/` ahead of
      `$ELAN_HOME/bin` on `PATH`. A bare `lake` inside a child process would
      therefore resolve to the primary toolchain's `lake` and bypass elan
      entirely — silently running the cross workspace under the primary
      toolchain. We invoke the elan shim by absolute path so cwd's
      `lean-toolchain` file wins.

    * The parent process also leaks loader and toolchain env vars
      (`LD_LIBRARY_PATH`, `DYLD_LIBRARY_PATH`, `DYLD_FALLBACK_LIBRARY_PATH`,
      `NIX_LD`, `NIX_LD_LIBRARY_PATH`, `LEAN_*`, `LAKE_*`, `ELAN_TOOLCHAIN`, …)
      — that is exactly the class of variable that caused the original bug.
      Trying to enumerate every dangerous var is a rearguard action; new
      ones keep showing up. We instead build the child's environment from
      an explicit **allowlist** by execing `env -i` with only the variables
      we know the subprocess needs, and let everything else drop on the
      floor. -/
private def runCrossLean (source : String) (fileName : String)
    (crossWorkspace : String) : IO (Bool × String) := do
  let baseName := (System.FilePath.mk fileName).fileName.getD "test"
  let pid ← IO.Process.getPID
  let tempDir ← getTempDir
  let tempFile := tempDir / s!".lean-minimize-{pid}-cross-{baseName}"
  IO.FS.writeFile tempFile source

  -- leanOptions come from the CROSS workspace's lakefile, not the primary's —
  -- options like `autoImplicit` can differ between toolchains.
  let leanOptions ← getLeanOptionsFromToml crossWorkspace

  -- Locate the elan `lake` shim. HOME fallback makes this portable across
  -- Linux, macOS, and nix/home-manager setups that don't always export
  -- ELAN_HOME into child processes.
  let elanHome ← match ← IO.getEnv "ELAN_HOME" with
    | some h => pure h
    | none =>
      match ← IO.getEnv "HOME" with
      | some h => pure (h ++ "/.elan")
      | none =>
        throw <| IO.userError "CROSS_WORKSPACE_SETUP_FAILED: neither ELAN_HOME nor HOME is set; cannot locate elan `lake` shim"
  let elanLakeShim := elanHome ++ "/bin/lake"

  -- Allowlist env: exec `env -i <KEY=VALUE> … <lake> env lean <file>`. `env -i`
  -- starts from an empty environment, so nothing the parent exported leaks
  -- unless we explicitly re-export it.
  --
  -- PATH deserves special treatment. The original hijack that motivated this
  -- whole subsystem came through `LD_LIBRARY_PATH`, not `PATH`. A maximally
  -- hermetic PATH (`$ELAN_HOME/bin:/usr/bin:/bin`) looks tidy but excludes
  -- `git` on platforms where git lives elsewhere (e.g. NixOS's
  -- `/run/current-system/sw/bin`), and Lake does reach for `git` during
  -- dep resolution. So we keep the parent's PATH and just prepend
  -- `$ELAN_HOME/bin` so the elan shim beats any primary-toolchain `lake`
  -- that `lake env` may have shoved onto the parent PATH. Loader variables
  -- remain scrubbed, which is the invariant that actually matters.
  let home := (← IO.getEnv "HOME").getD "/"
  let lang := (← IO.getEnv "LANG").getD "C.UTF-8"
  let tmpdir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let parentPath := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let allowlist : Array String := #[
    s!"HOME={home}",
    s!"ELAN_HOME={elanHome}",
    s!"PATH={elanHome}/bin:{parentPath}",
    s!"LANG={lang}",
    s!"TMPDIR={tmpdir}"
  ]

  try
    let result ← IO.Process.output {
      cmd := "env"
      args := #["-i"] ++ allowlist
              ++ #[elanLakeShim, "env", "lean"]
              ++ leanOptions
              ++ #[tempFile.toString]
      cwd := crossWorkspace
    }
    let success := result.exitCode == 0
    let out := if success then "" else (result.stdout ++ result.stderr)
    return (success, out)
  finally
    try IO.FS.removeFile tempFile catch _ => pure ()

/-- Test if `source` compiles under a second, independent Lake workspace.
    Used for cross-version minimization: verifies the file works under both the
    primary toolchain (driven by `testCompilesSubprocess`) and the toolchain
    pinned by `crossWorkspace/lean-toolchain`.

    The caller must have already built `crossWorkspace` (that is, its
    dependencies must be available under `<crossWorkspace>/.lake/build/`). This
    function does not run `lake build`; orchestrating that is the responsibility
    of the test harness or the Python `minimize` CLI. -/
def testSucceedsInCrossWorkspace (source : String) (fileName : String)
    (crossWorkspace : String) : IO Bool := do
  let (success, _) ← runCrossLean source fileName crossWorkspace
  return success

/-- As `testSucceedsInCrossWorkspace`, but on failure returns the cross
    compile's combined stdout+stderr so callers can surface it to the user
    in mid-minimization error messages. -/
def testSucceedsInCrossWorkspaceWithError (source : String) (fileName : String)
    (crossWorkspace : String) : IO (Bool × String) :=
  runCrossLean source fileName crossWorkspace

/-- Test if source compiles by running lean in a subprocess.
    This isolates memory usage - when the subprocess exits, all Lean caches are freed.
    When `crossWorkspace` is set, also verifies the file compiles under that toolchain. -/
def testCompilesSubprocess (source : String) (fileName : String)
    (crossWorkspace : Option String := none) : IO Bool := do
  -- Use a name based on input file and PID to avoid conflicts in parallel runs
  let baseName := (System.FilePath.mk fileName).fileName.getD "test"
  let pid ← IO.Process.getPID
  let tempDir ← getTempDir
  let tempFile := tempDir / s!".lean-minimize-{pid}-{baseName}"
  IO.FS.writeFile tempFile source

  -- Get environment variables for lean
  let leanPath ← IO.getEnv "LEAN_PATH"
  let leanSysroot ← IO.getEnv "LEAN_SYSROOT"
  let path ← IO.getEnv "PATH"

  let env : Array (String × Option String) := #[
    ("LEAN_PATH", leanPath),
    ("LEAN_SYSROOT", leanSysroot),
    ("PATH", path)
  ]

  -- Get leanOptions from the project's lakefile
  let leanOptions ← getLeanOptionsForFile fileName

  -- Run lean to check compilation, with try/finally for cleanup
  try
    let result ← IO.Process.output {
      cmd := "lean"
      args := leanOptions ++ #[tempFile.toString]
      env := env
    }
    if result.exitCode != 0 then
      return false
    -- Primary check passed. Now do cross-workspace check if configured.
    match crossWorkspace with
    | none => return true
    | some ws => testSucceedsInCrossWorkspace source fileName ws
  finally
    try IO.FS.removeFile tempFile catch _ => pure ()

/-- Check if source compiles using subprocess, returning error output if it fails.
    When `crossWorkspace` is set, also verifies the file compiles there. -/
def testCompilesSubprocessWithError (source : String) (fileName : String)
    (crossWorkspace : Option String := none) : IO (Bool × String) := do
  -- Use a name based on input file and PID to avoid conflicts in parallel runs
  let baseName := (System.FilePath.mk fileName).fileName.getD "test"
  let pid ← IO.Process.getPID
  let tempDir ← getTempDir
  let tempFile := tempDir / s!".lean-minimize-{pid}-{baseName}"
  IO.FS.writeFile tempFile source

  -- Get environment variables for lean
  let leanPath ← IO.getEnv "LEAN_PATH"
  let leanSysroot ← IO.getEnv "LEAN_SYSROOT"
  let path ← IO.getEnv "PATH"

  let env : Array (String × Option String) := #[
    ("LEAN_PATH", leanPath),
    ("LEAN_SYSROOT", leanSysroot),
    ("PATH", path)
  ]

  -- Get leanOptions from the project's lakefile
  let leanOptions ← getLeanOptionsForFile fileName

  -- Run lean to check compilation, with try/finally for cleanup
  try
    let result ← IO.Process.output {
      cmd := "lean"
      args := leanOptions ++ #[tempFile.toString]
      env := env
    }
    let success := result.exitCode == 0
    -- lean prints errors to stdout, so capture both
    let errorOutput := if success then "" else (result.stdout ++ result.stderr)
    if !success then
      return (false, errorOutput)
    -- Primary check passed. Now do cross-workspace check if configured.
    match crossWorkspace with
    | none => return (true, "")
    | some ws =>
      let (crossSucceeds, crossErr) ← testSucceedsInCrossWorkspaceWithError source fileName ws
      if crossSucceeds then
        return (true, "")
      else
        return (false, s!"Cross-workspace check failed in {ws}:\n{crossErr}")
  finally
    try IO.FS.removeFile tempFile catch _ => pure ()

/-- Check if reconstructed source compiles (using subprocess for memory isolation) -/
def testCompiles (state : MinState) (keepIndices : Array Nat) : IO Bool := do
  state.testCount.modify (· + 1)
  let source := reconstructSource state keepIndices
  testCompilesSubprocess source state.fileName state.crossWorkspace

/-- Write current progress to the output file if configured -/
def writeProgress (state : MinState) (keepIndices : Array Nat) : IO Unit := do
  if let some outPath := state.outputFile then
    let source := reconstructSource state keepIndices
    IO.FS.writeFile outPath source

/-- Delta debugging algorithm to find minimal required commands.

    The `heuristic` parameter controls how candidates are split at each step.
    Use `defaultSplitHeuristic` for standard binary splitting.

    This implementation is END-BIASED: it tries to remove later commands first,
    which works better for forward-declared code where later items depend on earlier ones.

    Parameters:
    - `candidates`: indices we're trying to remove
    - `currentlyKept`: all indices currently being kept (updated as we successfully remove items)

    Returns: the final set of indices that must be kept -/
unsafe def ddminCore (heuristic : SplitHeuristic) (state : MinState)
    (candidates : Array Nat) (currentlyKept : Array Nat) : IO (Array Nat) := do
  -- Base case: no candidates to try removing
  if candidates.size == 0 then
    return currentlyKept

  if candidates.size == 1 then
    -- Try removing this single command
    let idx := candidates[0]!
    let withoutThis := currentlyKept.filter (· != idx)
    if state.verbose then
      IO.eprintln s!"  Testing: try remove [{idx}]"
    if (← testCompiles state withoutThis) then
      if state.verbose then
        IO.eprintln s!"    → Success: removed [{idx}]"
      writeProgress state withoutThis
      return withoutThis
    if state.verbose then
      IO.eprintln s!"    → Failed: must keep [{idx}]"
    return currentlyKept

  -- Use heuristic to split candidates
  let (firstHalf, secondHalf) ← heuristic state candidates

  -- END-BIASED: Try removing second half (later indices) first!
  -- This works better for forward-declared code where later items depend on earlier ones.
  let withoutSecond := currentlyKept.filter (!secondHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"  Testing: try remove {secondHalf.toList} (keep {firstHalf.toList})"
  if (← testCompiles state withoutSecond) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {secondHalf.toList}, recursing on {firstHalf.toList}"
    writeProgress state withoutSecond
    return ← ddminCore heuristic state firstHalf withoutSecond

  -- Try removing first half
  let withoutFirst := currentlyKept.filter (!firstHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"    → Failed, trying: remove {firstHalf.toList} (keep {secondHalf.toList})"
  if (← testCompiles state withoutFirst) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {firstHalf.toList}, recursing on {secondHalf.toList}"
    writeProgress state withoutFirst
    return ← ddminCore heuristic state secondHalf withoutFirst

  -- Both halves are needed; recurse on each (but skip singletons - already tested)
  -- Process second half first (end-biased), then first half with updated kept set
  if state.verbose then
    IO.eprintln s!"    → Failed: both halves needed, recursing on each"

  -- Skip singleton halves - the failed half-tests already proved they're required
  let afterSecond ← if secondHalf.size == 1 then pure currentlyKept
                    else ddminCore heuristic state secondHalf currentlyKept
  let afterFirst ← if firstHalf.size == 1 then pure afterSecond
                   else ddminCore heuristic state firstHalf afterSecond
  return afterFirst

/-- Delta debugging algorithm to find minimal required commands.

    The `heuristic` parameter controls how candidates are split at each step.
    Use `defaultSplitHeuristic` for standard binary splitting.

    Returns: the indices that must be kept (subset of candidates) -/
unsafe def ddmin (heuristic : SplitHeuristic) (state : MinState) (candidates : Array Nat) :
    IO (Array Nat) := do
  -- Start with ALL indices before marker as currently kept (not just candidates).
  -- This ensures scope commands (section/namespace/end) that aren't in candidates
  -- are still included when testing compilation.
  let allIndices := Array.range state.markerIdx
  let finalKept ← ddminCore heuristic state candidates allIndices
  -- Return only the candidates that were kept (filter out non-candidate indices like scopes)
  return finalKept.filter (candidates.contains ·)

/-- Simpler binary deletion algorithm for command deletion.
    Unlike ddmin, this never tries removing the first half as an alternative.

    Algorithm:
    - Try deleting the second half (rounding up)
    - If that works, continue on the first half
    - If that didn't work and second half was a single declaration, continue on first half
    - Otherwise, recurse: first on second half, then on first half -/
unsafe def binaryDeleteCore (heuristic : SplitHeuristic) (state : MinState)
    (candidates : Array Nat) (currentlyKept : Array Nat) : IO (Array Nat) := do
  -- Base case: no candidates to try removing
  if candidates.size == 0 then
    return currentlyKept

  if candidates.size == 1 then
    -- Try removing this single command
    let idx := candidates[0]!
    let withoutThis := currentlyKept.filter (· != idx)
    if state.verbose then
      IO.eprintln s!"  Testing: try remove [{idx}]"
    if (← testCompiles state withoutThis) then
      if state.verbose then
        IO.eprintln s!"    → Success: removed [{idx}]"
      writeProgress state withoutThis
      return withoutThis
    if state.verbose then
      IO.eprintln s!"    → Failed: must keep [{idx}]"
    return currentlyKept

  -- Use heuristic to split candidates (secondHalf rounds up)
  let (firstHalf, secondHalf) ← heuristic state candidates

  -- Try removing second half
  let withoutSecond := currentlyKept.filter (!secondHalf.contains ·)
  if state.verbose then
    IO.eprintln s!"  Testing: try remove {secondHalf.toList} (keep {firstHalf.toList})"
  if (← testCompiles state withoutSecond) then
    if state.verbose then
      IO.eprintln s!"    → Success: removed {secondHalf.toList}, continuing on {firstHalf.toList}"
    writeProgress state withoutSecond
    return ← binaryDeleteCore heuristic state firstHalf withoutSecond

  -- Second half removal failed
  if state.verbose then
    IO.eprintln s!"    → Failed"

  if secondHalf.size == 1 then
    -- Single item can't be deleted, continue on first half only
    if state.verbose then
      IO.eprintln s!"    Single item in second half, continuing on first half"
    return ← binaryDeleteCore heuristic state firstHalf currentlyKept
  else
    -- Recurse: first on second half, then on first half
    if state.verbose then
      IO.eprintln s!"    Recursing into second half, then first half"
    let afterSecond ← binaryDeleteCore heuristic state secondHalf currentlyKept
    return ← binaryDeleteCore heuristic state firstHalf afterSecond

/-- Simpler binary deletion algorithm for command deletion.
    Entry point that sets up initial state.

    Returns: the indices that must be kept (subset of candidates) -/
unsafe def binaryDelete (heuristic : SplitHeuristic) (state : MinState) (candidates : Array Nat) :
    IO (Array Nat) := do
  -- Start with ALL indices before marker as currently kept (not just candidates).
  -- This ensures scope commands (section/namespace/end) that aren't in candidates
  -- are still included when testing compilation.
  let allIndices := Array.range state.markerIdx
  let finalKept ← binaryDeleteCore heuristic state candidates allIndices
  -- Return only the candidates that were kept (filter out non-candidate indices like scopes)
  return finalKept.filter (candidates.contains ·)

/-- Linear deletion: try removing each candidate one at a time.
    Simpler and more predictable than binary deletion — O(N) compile tests per pass.
    Better than binary deletion when most commands are needed (common after the
    initial binary pass has already removed the bulk). -/
unsafe def linearDeleteCore (state : MinState)
    (candidates : Array Nat) (currentlyKept : Array Nat) : IO (Array Nat) := do
  let mut kept := currentlyKept
  for idx in candidates do
    let withoutThis := kept.filter (· != idx)
    if state.verbose then
      IO.eprintln s!"  Testing: try remove [{idx}]"
    if (← testCompiles state withoutThis) then
      if state.verbose then
        IO.eprintln s!"    → Success: removed [{idx}]"
      writeProgress state withoutThis
      kept := withoutThis
    else
      if state.verbose then
        IO.eprintln s!"    → Failed: must keep [{idx}]"
  return kept

/-- Linear deletion: try removing each candidate one at a time.
    Entry point that sets up initial state.

    Returns: the indices that must be kept (subset of candidates) -/
unsafe def linearDelete (state : MinState) (candidates : Array Nat) :
    IO (Array Nat) := do
  let allIndices := Array.range state.markerIdx
  let finalKept ← linearDeleteCore state candidates allIndices
  return finalKept.filter (candidates.contains ·)

/-- Create a split heuristic that uses pre-computed reachability data.
    Commands not in `reachable` are tried for removal first.

    Since ddmin is end-biased (tries removing secondHalf first), we return
    (reachable, unreachable) so that unreachable commands are tried for removal first. -/
def precomputedDependencyHeuristic (reachable : Array Nat) : SplitHeuristic := fun state candidates => do
  let unreachable := candidates.filter fun idx => !reachable.contains idx
  let reachableInCandidates := candidates.filter fun idx => reachable.contains idx

  if state.verbose then
    IO.eprintln s!"  Pre-computed deps: {reachableInCandidates.size} reachable, {unreachable.size} likely removable"

  -- If we have both reachable and unreachable, split by reachability.
  -- Return (reachable, unreachable) so end-biased ddmin tries removing unreachable first.
  if unreachable.isEmpty || reachableInCandidates.isEmpty then
    defaultSplitHeuristic state candidates
  else
    return (reachableInCandidates, unreachable)

end LeanMinimizer
