# LeanMinimizer Tests

This directory contains tests for the lean-minimizer tool.

## Running Tests

```bash
lake test
```

To update expected outputs after reviewing changes:
```bash
lake test --accept
```

## Test Types

### Golden Tests (`Golden/`)

Golden tests verify the minimizer produces expected output for specific inputs.

Each test consists of:
- `X.lean` - Input file to minimize
- `X.lean.expected.out` - Expected minimized output
- `X.lean.marker` (optional) - Custom marker pattern (default: `#guard_msgs`)

**Adding a new golden test:**

1. Create `Golden/MyTest.lean` with input that should be minimized
2. Run `lake test` - it will report the test as missing expected output
3. Review `Golden/MyTest.lean.produced.out` to verify correctness
4. Run `lake test --accept` to copy produced output to expected

**Example golden test:**
```lean
-- Golden/MyTest.lean
def unused := 42
def needed := 1
/-- info: 1 -/
#guard_msgs in
#eval needed
```

The minimizer should remove `def unused` since it's not needed for the invariant.

### Component Tests (`Component/`)

Component tests verify individual functions work correctly.

Each test is a Lean file exporting an `unsafe def test : IO Bool` function.

**Adding a new component test:**

1. Create `Component/MyTest.lean`:
```lean
import LeanMinimizer

namespace LeanMinimizerTest.Component.MyTest

open Lean LeanMinimizer

unsafe def test : IO Bool := do
  -- Test logic here
  if someCondition then
    IO.println "  ✓ MyTest"
    return true
  else
    IO.println "  ✗ MyTest: explanation"
    return false

end LeanMinimizerTest.Component.MyTest
```

2. Add import to `Test.lean`:
```lean
import LeanMinimizerTest.Component.MyTest
```

3. Add to the test list in `runComponentTests`:
```lean
let tests : List (IO Bool) := [
  ...
  LeanMinimizerTest.Component.MyTest.test
]
```

### CLI Tests (`CLI/`)

CLI tests verify error handling and command-line behavior by running the minimizer
and comparing output.

Each test consists of:
- `X.lean` - Input file to run through the minimizer (or use `.input` to specify a different file)
- `X.lean.expected.out` - Expected output (stdout + stderr combined)
- `X.lean.expected.exit` (optional) - Expected exit code (default: 0)
- `X.lean.args` (optional) - Extra CLI arguments (space-separated)
- `X.lean.input` (optional) - Path to a different input file to run

**Adding a new CLI test:**

1. Create `CLI/MyTest.lean` with input that tests specific CLI behavior
2. Run `lake test` - it will report the test as missing expected output
3. Review `CLI/MyTest.lean.produced.out` to verify correctness
4. Run `lake test --accept` to copy produced output to expected

**Testing existing files with different options:**

To test the minimizer on an existing file (e.g., a golden test) with specific
CLI options, create only the metadata files:
- `CLI/MyTest.lean.input` - contains the path to the input file
- `CLI/MyTest.lean.args` - contains CLI arguments (e.g., `--verbose`)

Example: `VerboseDependencyHeuristic.lean.input` contains:
```
LeanMinimizerTest/Golden/DependencyHeuristic.lean
```

**Example CLI test:**
```lean
-- CLI/MissingMarker.lean
-- Test file with no #guard_msgs marker
def foo := 1
#check foo
```
With `MissingMarker.lean.expected.exit` containing `1` (for non-zero exit).

## Test Organization

```
LeanMinimizerTest/
├── README.md
├── Golden/           # End-to-end minimizer tests
│   ├── DependencyHeuristic.lean
│   └── CustomMarker.lean
├── Component/        # Unit tests for individual functions
│   ├── RunFrontend.lean
│   ├── BuildDependencyMap.lean
│   └── ...
└── CLI/              # Error handling and CLI behavior tests
    └── MissingMarker.lean
```
