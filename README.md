# lean-minimizer

A Lean test case minimizer that uses delta debugging to find a minimal set of commands needed for compilation.

## Usage

```bash
lake exe minimize <file.lean> [--marker <pattern>] [--verbose]
```

### Options

- `--marker <PATTERN>`: Pattern to search for in commands to identify the invariant section (default: "invariant")
- `--verbose`: Print progress information during minimization
- `--help`: Show help message

### Example

Given a file `test.lean`:
```lean
def unused1 := 1
def unused2 := 2
def needed := 42
section invariant
#check needed
end invariant
```

Running:
```bash
lake exe minimize test.lean
```

Produces:
```lean
def needed := 42
section invariant
#check needed
end invariant
```

## How it works

The tool:
1. Parses the Lean file into individual commands
2. Finds the first command containing the marker pattern
3. Uses delta debugging (ddmin algorithm) to find a minimal subset of commands before the marker that are required for the file to compile
4. Outputs the minimized source

## Running tests

```bash
lake exe test
```
