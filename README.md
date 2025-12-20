# lean-minimizer

A Lean test case minimizer that uses delta debugging with dependency analysis to produce minimal, self-contained test cases.

## Usage

```bash
lake exe minimize <file.lean> [options]
```

### Options

- `--marker <PATTERN>`: Pattern to search for in commands to identify the invariant section (default: `#guard_msgs`)
- `-o, --output <FILE>`: Write output to FILE (default: `<input>.out.lean`)
- `-q, --quiet`: Suppress progress information during minimization
- `--no-module-removal`: Disable the module system removal pass
- `--no-delete`: Disable the command deletion pass
- `--no-import-minimization`: Disable the import minimization pass
- `--no-import-inlining`: Disable the import inlining pass
- `--no-sorry`: Disable the body replacement pass
- `--no-text-subst`: Disable the text substitution pass
- `--no-extends`: Disable the extends clause simplification pass
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
3. If that fails, identifies Prop-valued subexpressions (proofs) and tries replacing each with `sorry`
4. For `where`-style structure definitions, tries replacing individual field values with `sorry`
5. Returns to the first pass after each successful replacement (since simplified bodies may enable further deletions)

The Prop subexpression detection uses the InfoTree to find:
- Term expressions whose type is `Prop` (i.e., proofs)
- Tactic blocks (`by ...`) that represent proof terms

### Pass 5: Text Substitution

Performs textual replacements to simplify declarations:

1. **Keyword replacement**: `lemma` → `theorem`
2. **Type simplification**: `Type*` → `Type _`, then `Type _`/`Type u` → `Type`
3. **Unicode normalization**: `ℕ` → `Nat`, `ℤ` → `Int`, `ℚ` → `Rat`
4. **Attribute removal**: Removes `@[...]` attribute blocks
5. **Modifier removal**: Removes `unsafe`, `protected`, `private`, `noncomputable`
6. **Priority removal**: Removes priorities from attributes (`@[simp 100]` → `@[simp]`) and instances (`(priority := high)` → removed)

Each mini-pass tries all replacements at once first; if that fails, it applies them one-by-one from bottom to top. Comments and strings are preserved.

### Pass 6: Extends Simplification

Simplifies `extends` clauses in structure definitions:

1. For each structure with an extends clause, for each parent listed:
   - Tries to remove that parent entirely
   - If that fails, tries to replace it with the parent's own parents (grandparents)
2. When removing a parent causes errors on `sorry`-valued field lines, those lines are automatically deleted
3. Returns to the first pass after each successful change (since removing a parent may enable deletion of now-unused structures)

This is useful when a structure extends multiple parents but only needs fields from some of them.

### Pass 7: Import Minimization

1. Tries to remove each import entirely
2. For imports that can't be removed, tries to replace them with their transitive imports (useful when only a subset of a module's dependencies are needed)

### Pass 8: Import Inlining

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
