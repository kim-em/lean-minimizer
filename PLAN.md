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

Many of our current restarts are quite wasteful. Often, while we know that the changes made in a pass require re-running earlier passes, we can actually run those earlier passes just on some initial segment of the file (i.e. leaving a much longer tail of the file "invariant").

For example, after inlining an import, it shouldn't be necesssary to re-run the entire deletion pass; it should suffice to just run it on the newly inlined code.

We'd have to think carefully about each of the passes that causes a restart.

## Only attempt some changes once.

Many reductions don't really need to be attempted over and over again. For example, if we've tried removing a "protected" modifier and it didn't work, it not worth trying again. (I think all the text modification passes could benefit from this.)

Perhaps we can have a memory (e.g. in this case that could just include the proposed text change, i.e. the line before the change and the line after), and not reattempt things we've remembered that we've done before (perhaps different passes could use different parts of this "memory").

It's probably best that to be really sure that as a very final pass, we actually clear the memory (and restart if there was anything to clear, but continue if that memory was empty).

## Extract Goal for Tactic Failures
**Complex pass involving invariant modification.** If the test case is showing that a tactic fails, but there are tactic steps *before* the interesting failure, we can use `extract_goal` before the failing tactic to get a simpler theorem where the tactic should also fail. This creates a new, smaller theorem that isolates the failure.
