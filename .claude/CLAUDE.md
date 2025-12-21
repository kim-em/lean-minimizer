# lean-minimizer Project Instructions

## Testing

**The full test suite takes a long time to run.** Always prefer running individual tests during development.

### Running a Single Golden Test

```bash
lake exe test LeanMinimizerTest/Golden/SomeTest.lean
```

### Running All Tests (slow)

```bash
lake exe test
```

Only run the full suite when you believe everything is working and want final verification.

### Running a Single Component Test

Create a temporary runner file:
```bash
cat > /tmp/run_test.lean << 'EOF'
import LeanMinimizerTest.Component.SomeTest
unsafe def main : IO Unit := do
  discard <| LeanMinimizerTest.Component.SomeTest.test
EOF
lake exe lean --run /tmp/run_test.lean
```

### Test Structure

- `LeanMinimizerTest/Golden/` - Golden tests comparing minimizer output to expected files
- `LeanMinimizerTest/CLI/` - CLI argument tests
- `LeanMinimizerTest/Component/` - Unit tests for internal components (these run as part of the full suite)

### Accepting Test Output

**Do NOT run `lake exe test --accept` yourself.** If test output has changed, suggest the accept command to the user for them to review and run.

To accept a specific test (works for both Golden and CLI tests):
```bash
lake exe test --accept LeanMinimizerTest/Golden/SomeTest.lean
lake exe test --accept LeanMinimizerTest/CLI/SomeTest.lean
```

To accept all changed test outputs:
```bash
lake exe test --accept
```

The user must review the diff and decide whether to accept the new output.

## Building

```bash
lake build           # Build everything
lake build minimize  # Build just the CLI binary
```

## Running the Minimizer

```bash
lake exe minimize <file.lean> --marker "#guard_msgs"
```
