# Import Inlining Failure Example

This example demonstrates a case where import inlining fails with "Module file not found"
even though the Mathlib source files are present in `.lake/packages/mathlib/`.

## Setup

```bash
# From the root of the lean-minimizer repo:
echo "leanprover/lean4:nightly-2026-01-23" > lean-toolchain

# Add to lakefile.toml:
# [[require]]
# name = "mathlib"
# git = "https://github.com/leanprover-community/mathlib4-nightly-testing"
# rev = "nightly-testing"

lake update
lake exe cache get
lake build minimize
```

## Reproduce

```bash
lake exe minimize examples/import-inlining-failure/simp_test.lean
```

## Expected behavior

The minimizer should inline the `Mathlib.Algebra.Group.Torsion` import and produce
a self-contained Lean file with no external dependencies.

## Actual behavior

```
[Pass 12] Running: Import Inlining
  Analyzing 1 imports for inlining...
  Trying to inline import Mathlib.Algebra.Group.Torsion...
    Module file not found, skipping
  No imports could be inlined
```

The Mathlib source files ARE present at `.lake/packages/mathlib/Mathlib/Algebra/Group/Torsion.lean`.

## Context

This test case is for bisecting a simp perm lemma regression in Lean 4.
The goal is to produce a Mathlib-free file that demonstrates:
- `simp [zsmul_comm _ z]` succeeds (with explicit args)
- `simp [zsmul_comm]` fails (without explicit args, treated as perm lemma)

Once minimized, the file can be used with `lean-bisect` to find the exact
Lean 4 commit that caused the behavior change.
