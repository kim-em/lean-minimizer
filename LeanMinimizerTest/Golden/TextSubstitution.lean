-- Test file for text substitution pass
-- Test that @[simp] and protected in comments are NOT removed

-- Macros for testing lemma→theorem and ℕ→Nat substitutions
-- (these should be deleted after the substitutions are made)
macro "lemma " n:ident sig:declSig val:declVal : command =>
  `(theorem $n $sig $val)

notation "ℕ" => Nat

-- @[simp] should be removed (but not from this comment!)
@[simp] def foo : Nat := 1

-- ℕ should become Nat (then notation can be deleted)
def myNat : ℕ := 42

namespace Baz
-- protected should be removed (not from this comment!)
protected def qux : Nat := 2
end Baz

-- private should be removed
private def quux : Nat := 3

-- Priority should be removed: @[simp 100] → @[simp] (then @[simp] removed)
@[simp 100] def withPrio : Nat := 4

-- Priority in instance should be removed
instance (priority := high) : Inhabited Bool := ⟨true⟩

-- lemma should become theorem; the macro then becomes unused and deletable
lemma myLemma : True := trivial

/-- info: 53 -/
#guard_msgs in
#eval foo + myNat + Baz.qux + quux + withPrio + (if (default : Bool) then 1 else 0)

/-- info: myLemma : True -/
#guard_msgs in
#check myLemma
