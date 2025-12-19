# lean-minimizer

A Lean test case minimizer that uses delta debugging with dependency analysis to find a minimal set of commands needed for compilation.

## Usage

```bash
lake exe minimize <file.lean> [--marker <pattern>] [--verbose] [--no-delete]
```

### Options

- `--marker <PATTERN>`: Pattern to search for in commands to identify the invariant section (default: `#guard_msgs`)
- `--verbose`: Print progress information during minimization
- `--no-delete`: Disable the command deletion pass
- `--help`: Show help message

### Example

Given a file `test.lean`:
```lean
def unused1 := 1
def unused2 := 2
def needed := 42
/-- info: 42 -/
#guard_msgs in
#eval needed
```

Running:
```bash
lake exe minimize test.lean
```

Produces:
```lean
def needed := 42
/-- info: 42 -/
#guard_msgs in
#eval needed
```

## How it works

The tool runs a sequence of minimization passes:

### Command Deletion Pass

1. Parses the Lean file and fully elaborates it to extract dependency information
2. Finds the first command containing the marker pattern (the "invariant section")
3. Uses dependency analysis to identify which commands are reachable from the invariant
4. Applies delta debugging (ddmin algorithm) to find a minimal subset of commands needed for the file to compile
5. Outputs the minimized source

The dependency analysis makes minimization much faster by trying to remove unreachable commands first, rather than doing blind binary search.

### Pass Framework

The minimizer uses a multi-pass architecture where each pass can:
- **restart**: Go back to the first pass after making changes
- **repeat**: Run the same pass again
- **continue**: Move to the next pass

Currently only the deletion pass is implemented, but the framework supports adding future passes like:
- Import minimization
- Syntax simplification (replacing expressions with `sorry`)
- Tactic simplification

## Running tests

```bash
lake exe test
```
