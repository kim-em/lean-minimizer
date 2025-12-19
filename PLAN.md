# Future Pass Ideas

## Import Inlining
Inline an `import X.Y.Z`, wrap the inlined content in `section X.Y.Z`, move imports back to the top, and add any required `end` statements before the closing `end X.Y.Z`.

## Keyword Substitution
Replace all `lemma` with `theorem`.

## Body Replacement
Replace bodies of theorems/definitions with `sorry`, and otherwise replace Prop-valued subterms with `sorry`.

## Type Universe Simplification
Replace `Type*` with `Type _`. Then try replacing `Type _` or `Type u` with `Type`. (Starting from the bottom. No binary search, just linear.)

## Notation Replacement
- Replace `ℕ` with `Nat`, similarly for `ℤ` and `ℚ`
- Try replacing `ℝ` with `ℚ`

## Attribute Removal
Try removing attributes (work from the bottom up, no need to find a maximal subset).

## Attribute Expansion
Replace any surviving `@[simps]`, `@[to_additive]`, and `@[to_dual]` attributes with the definitions they produce. (Ideally by intercepting what they produce, either via `Environment` or `InfoTree`.)

## Structure Field Removal
Remove a field from a structure, if all uses of that field below are `sorry` (and remove those uses).

## Extends Clause Simplification
Remove parents from `extends` statements.

## Empty Section/Namespace Pair Deletion
Currently we can't delete an empty `section X; end X` pair, because neither is removable separately. Glom these together for the deletion pass. (Dynamically, as they become adjacent due to earlier deletions? Seems complicated.) Same for `namespace X; end X`.

## Linter-Guided Argument Removal
Remove unused arguments flagged by the linter.

## Deriving Clause Removal
Remove `deriving` clauses from inductive/structure definitions.

## Default Argument Removal
Remove `opt_param` or `auto_param` default values from function signatures.

## Macro/Notation Inlining
Remove macros/notation by inlining their expansions at use sites.

## Modifier Removal
Remove `unsafe`, `protected`, `private`, `noncomputable` modifiers.

## Priority Removal
Remove priorities from instances (`@[instance 100]`) or simp lemmas (`@[simp 500]`).

## Singleton Namespace Flattening
If we have a namespace command with just one command inside, replace that by including the namespace in the declaration name directly.

## Extract Goal for Tactic Failures
**Complex pass involving invariant modification.** If the test case is showing that a tactic fails, but there are tactic steps *before* the interesting failure, we can use `extract_goal` before the failing tactic to get a simpler theorem where the tactic should also fail. This creates a new, smaller theorem that isolates the failure.
