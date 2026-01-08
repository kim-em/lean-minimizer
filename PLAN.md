# Future Pass Ideas

## Remove `_root_` Prefixes
Remove `_root_` prefixes from declaration names when they're not needed for disambiguation.

## Type Replacement
Try replacing `ℝ` with `ℚ`.

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

## Extract Goal for Tactic Failures
**Complex pass involving invariant modification.** If the test case is showing that a tactic fails, but there are tactic steps *before* the interesting failure, we can use `extract_goal` before the failing tactic to get a simpler theorem where the tactic should also fail. This creates a new, smaller theorem that isolates the failure.
