# lean-minimizer

A Lean test case minimizer that uses delta debugging with dependency analysis to produce minimal, self-contained test cases.

## Usage

```bash
lake exe minimize <file.lean> [options]
```

### Options

- `--marker <PATTERN>`: Pattern to search for in commands to identify the invariant section (default: `#guard_msgs`)
- `--verbose`: Print progress information during minimization
- `--no-module-removal`: Disable the module system removal pass
- `--no-delete`: Disable the command deletion pass
- `--no-import-minimization`: Disable the import minimization pass
- `--no-import-inlining`: Disable the import inlining pass
- `--no-sorry`: Disable the body replacement pass
- `--help`: Show help message

### Example

Given a file `test.lean`:
```lean
import SomeLibrary

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

Produces a minimal, self-contained file with the import inlined and unused definitions removed.

## How it works

The tool runs a sequence of minimization passes:

### Pass 1: Module System Removal

Attempts to remove the `module` keyword and strip import modifiers (`public`, `meta`, `all`) if the file still compiles without them.

### Pass 2: Command Deletion

1. Parses the Lean file and fully elaborates it to extract dependency information
2. Finds the first command containing the marker pattern (the "invariant section")
3. Uses dependency analysis to identify which commands are reachable from the invariant
4. Applies delta debugging (ddmin algorithm) to find a minimal subset of commands needed for the file to compile
5. Preserves `section`, `namespace`, and `end` commands to maintain scoping semantics

The dependency analysis makes minimization much faster by trying to remove unreachable commands first, rather than doing blind binary search.

### Pass 3: Empty Scope Removal

Removes adjacent empty scope pairs (`section X...end X` or `namespace X...end X`) that may remain after command deletion.

### Pass 4: Body Replacement

Replaces declaration bodies with `sorry` to simplify the test case:

1. Works declaration by declaration, starting from just above the invariant section and moving upward
2. For each declaration, tries replacing the entire body with `sorry`
3. For `where`-style structure definitions, tries replacing individual field values with `sorry`
4. Returns to the first pass after each successful replacement (since simplified bodies may enable further deletions)

### Pass 5: Import Minimization

1. Tries to remove each import entirely
2. For imports that can't be removed, tries to replace them with their transitive imports (useful when only a subset of a module's dependencies are needed)

### Pass 6: Import Inlining

Inlines project-local imports to create self-contained test files:

1. Resolves each import to its source file within the project
2. Wraps the imported content in `section ModuleName...end ModuleName`
3. Adds required `end` statements for any unclosed namespaces/sections
4. Moves the imported module's imports to the top of the file
5. Strips `module` keyword and import modifiers when needed

This pass only inlines imports from within the same project - external library imports are left as-is.

### Pass Framework

The minimizer uses a multi-pass architecture where each pass can:
- **restart**: Go back to the first pass after making changes (used by import inlining to allow deletion of newly inlined code)
- **repeat**: Run the same pass again (used by deletion when changes are made)
- **continue**: Move to the next pass

## Running tests

```bash
lake exe test
```

To accept updated test outputs after review:
```bash
lake exe test --accept
```
