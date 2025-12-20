# Future Pass Ideas

## Type Replacement
Try replacing `ℝ` with `ℚ`.

## Attribute Expansion
Replace any surviving `@[simps]`, `@[to_additive]`, and `@[to_dual]` attributes with the definitions they produce. (Ideally by intercepting what they produce, either via `Environment` or `InfoTree`.)

## Structure Field Removal
Remove a field from a structure, if all uses of that field below are `sorry` (and remove those uses).

## Extends Clause Simplification
Remove parents from `extends` statements.

## Linter-Guided Argument Removal
Remove unused arguments flagged by the linter.

## Deriving Clause Removal
Remove `deriving` clauses from inductive/structure definitions.

## Default Argument Removal
Remove `opt_param` or `auto_param` default values from function signatures.

## Macro/Notation Inlining
Remove macros/notation by inlining their expansions at use sites.

## Singleton Namespace Flattening
If we have a namespace command with just one command inside, replace that by including the namespace in the declaration name directly.

## Extract Goal for Tactic Failures
**Complex pass involving invariant modification.** If the test case is showing that a tactic fails, but there are tactic steps *before* the interesting failure, we can use `extract_goal` before the failing tactic to get a simpler theorem where the tactic should also fail. This creates a new, smaller theorem that isolates the failure.
