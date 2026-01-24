/-
Test case for simp perm lemma regression.

On nightly-2026-01-23:
- `simp [zsmul_comm _ z]` succeeds (explicit args, not a perm lemma)
- `simp [zsmul_comm]` fails (perm lemma, AC ordering rejects)

This file demonstrates the bug. When minimized, import inlining fails with
"Module file not found" even though Mathlib source files are present in
.lake/packages/mathlib/.
-/
import Mathlib.Algebra.Group.Torsion

namespace SimpTest

variable {G : Type*} [AddCommGroup G] {a b p : G} {z : ℤ}

def ModEq (a b p : G) : Prop := ∃ m : ℤ, m • p = b - a
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq a b p
lemma modEq_iff_zsmul : a ≡ b [PMOD p] ↔ ∃ m : ℤ, m • p = b - a := Iff.rfl

-- SUCCESS: With explicit args, zsmul_comm is not a perm lemma
#guard_msgs in
theorem test_success [IsAddTorsionFree G] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm _ z, zsmul_right_inj hn]

-- FAILURE: Without explicit args, zsmul_comm becomes a perm lemma and is rejected
/--
error: unsolved goals
G : Type u_1
inst✝¹ : AddCommGroup G
a b p : G
z : ℤ
inst✝ : IsAddTorsionFree G
hn : z ≠ 0
⊢ (∃ m, m • z • p = z • (b - a)) ↔ ∃ m, m • p = b - a
---
warning: This simp argument is unused:
  zsmul_comm

Hint: Omit it from the simp argument list.
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_c̵o̵m̵m̵,̵ ̵z̵s̵m̵u̵l̵_̵right_inj hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
---
warning: This simp argument is unused:
  zsmul_right_inj hn

Hint: Omit it from the simp argument list.
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm,̵ ̵z̵s̵m̵u̵l̵_̵r̵i̵g̵h̵t̵_̵i̵n̵j̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
theorem test_failure [IsAddTorsionFree G] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm, zsmul_right_inj hn]

end SimpTest
