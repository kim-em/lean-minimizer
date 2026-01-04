# Future Pass Ideas

## Remove `_root_` Prefixes
Remove `_root_` prefixes from declaration names when they're not needed for disambiguation.

## Type Replacement
Try replacing `ℝ` with `ℚ`.

## Structure Field Removal
Remove a field from a structure, if all uses of that field below are `sorry` (and remove those uses).

## Generalize typeclass arguments/variables
e.g. try replacing `[CommRing A]` with `[Ring A]`

## Linter-Guided Argument Removal
Remove unused arguments flagged by the linter.

## Deriving Clause Removal
Remove `deriving` clauses from inductive/structure definitions.

## Default Argument Removal
Remove `opt_param` or `auto_param` default values from function signatures.

## Macro/Notation Inlining
Remove macros/notation by inlining their expansions at use sites.

# Other improvements

## More parsimonious restarts

**Import inlining**: ✅ Implemented. After inlining an import, the deletion pass only processes the newly inlined code, leaving the original commands as invariant. Uses a text-based "temp marker" to identify the boundary.

**Body replacement / Extends simplification**: Not yet implemented. When a body at index `i` is replaced with `sorry`, declarations at indices `< i` (helpers) may become deletable. Could use the same temp marker mechanism - set the marker to the simplified declaration, and deletion only processes commands before it.

## Only attempt some changes once.

✅ **Implemented** for TextSubstitution and ExtendsSimplification passes.

A memory system tracks failed transformations using string keys. When a change fails (e.g., removing a `noncomputable` modifier), it's recorded in memory and skipped on subsequent attempts. The `clearMemoryPass` at the end triggers one final sweep with empty memory to catch any changes that became possible due to context changes.

**Future**: Could extend to BodyReplacement (track by declaration name), ImportInlining (track by module name), etc.

## Extract Goal for Tactic Failures
**Complex pass involving invariant modification.** If the test case is showing that a tactic fails, but there are tactic steps *before* the interesting failure, we can use `extract_goal` before the failing tactic to get a simpler theorem where the tactic should also fail. This creates a new, smaller theorem that isolates the failure.
