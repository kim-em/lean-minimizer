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
- `--resume`: Resume from the output file if it exists (useful for continuing interrupted runs)
- `--full-restarts`: Disable parsimonious restarts (for debugging)
- `--no-<PASS>`: Disable a specific pass:
  - `--no-module-removal`: Module system removal
  - `--no-delete`: Command deletion (also disables empty scope and singleton namespace passes)
  - `--no-sorry`: Body replacement (sorry)
  - `--no-text-subst`: Text substitution
  - `--no-extends`: Extends simplification
  - `--no-import-minimization`: Import minimization
  - `--no-import-inlining`: Import inlining
- `--only-<PASS>`: Run only a specific pass:
  - `--only-module-removal`: Module system removal
  - `--only-delete`: Command deletion
  - `--only-empty-scope`: Empty scope removal
  - `--only-sorry`: Body replacement (sorry)
  - `--only-text-subst`: Text substitution
  - `--only-extends`: Extends simplification
  - `--only-attr-expansion`: Attribute expansion
  - `--only-import-minimization`: Import minimization
  - `--only-import-inlining`: Import inlining
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

### Resuming Interrupted Runs

Minimization can take a while for large files. If you need to interrupt and resume later:

```bash
# Initial run (Ctrl-C to interrupt)
lake exe minimize test.lean

# Resume from where you left off
lake exe minimize test.lean --resume
```

The `--resume` flag checks if the output file (`test.out.lean`) exists and uses it as input instead of the original file.

### Minimizing Panics

If you're minimizing a test case that panics, use `#guard_panic` to catch the panic:

```lean
#guard_msgs in
#guard_panic in
some_command_that_panics
```

This allows the minimizer to verify the panic still occurs after each reduction step.

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

### Pass 4: Singleton Namespace Flattening

Simplifies namespace wrapping when a namespace contains only a single declaration. For example:
```lean
namespace Foo
def bar := 1
end Foo
```
becomes:
```lean
def Foo.bar := 1
```

### Pass 5: Public Section Removal

Removes `public section` wrappers when they're not needed, converting them to regular `section` blocks.

### Pass 6: Body Replacement

Replaces declaration bodies with `sorry` to simplify the test case:

1. Works declaration by declaration, starting from just above the invariant section and moving upward
2. For each declaration, tries replacing the entire body with `sorry`
3. If that fails, identifies Prop-valued subexpressions (proofs) and tries replacing each with `sorry`
4. For `where`-style structure definitions, tries replacing individual field values with `sorry`
5. Returns to the first pass after each successful replacement (since simplified bodies may enable further deletions)

The Prop subexpression detection uses the InfoTree to find:
- Term expressions whose type is `Prop` (i.e., proofs)
- Tactic blocks (`by ...`) that represent proof terms

### Pass 7: Text Substitution

Performs textual replacements to simplify declarations:

1. **Keyword replacement**: `lemma` → `theorem`
2. **Type simplification**: `Type*` → `Type _`, then `Type _`/`Type u` → `Type`
3. **Unicode normalization**: `ℕ` → `Nat`, `ℤ` → `Int`, `ℚ` → `Rat`
4. **Attribute removal**: Removes `@[...]` attribute blocks
5. **Modifier removal**: Removes `unsafe`, `protected`, `private`, `noncomputable`
6. **Priority removal**: Removes priorities from attributes (`@[simp 100]` → `@[simp]`) and instances (`(priority := high)` → removed)

Each mini-pass tries all replacements at once first; if that fails, it applies them one-by-one from bottom to top. Comments and strings are preserved.

### Pass 8: Extends Simplification

Simplifies `extends` clauses in structure definitions:

1. For each structure with an extends clause, for each parent listed:
   - Tries to remove that parent entirely
   - If that fails, tries to replace it with the parent's own parents (grandparents)
2. When removing a parent causes errors on `sorry`-valued field lines, those lines are automatically deleted
3. Returns to the first pass after each successful change (since removing a parent may enable deletion of now-unused structures)

This is useful when a structure extends multiple parents but only needs fields from some of them.

### Pass 9: Attribute Expansion

Expands certain attributes to their underlying form, which can enable further simplification.

### Pass 10: Import Minimization

1. Tries to remove each import entirely
2. For imports that can't be removed, tries to replace them with their transitive imports (useful when only a subset of a module's dependencies are needed)

### Pass 11: Import Inlining

Inlines imports to create self-contained test files:

1. Resolves each import to its source file (checking both project root and `.lake/packages/`)
2. Wraps the imported content in `section ModuleName...end ModuleName`
3. Adds required `end` statements for any unclosed namespaces/sections
4. Moves the imported module's imports to the top of the file
5. Strips `module` keyword and import modifiers when needed

This pass inlines any import whose source file can be found, including dependencies in `.lake/packages/`.

### Pass Framework

The minimizer uses a multi-pass architecture where each pass can:
- **restart**: Go back to the first pass after making changes (used by import inlining to allow deletion of newly inlined code)
- **repeat**: Run the same pass again (used by deletion when changes are made)
- **continue**: Move to the next pass

**Parsimonious restarts**: When import inlining restarts, it sets a "temp marker" at the boundary between inlined and original code. Subsequent passes only process commands before this marker, avoiding redundant work on already-minimized code. Use `--full-restarts` to disable this optimization.

## Running tests

```bash
lake exe test
```

To accept updated test outputs after review:
```bash
lake exe test --accept
```
