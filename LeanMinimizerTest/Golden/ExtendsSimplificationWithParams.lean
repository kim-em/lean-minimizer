-- Test: structure with type parameters should have extends simplified
-- This verifies that type arguments like "A R" are preserved when simplifying

structure A (R : Type) where
  a : R

structure B (R : Type) extends A R

structure C (R : Type) extends A R, B R where
  c : R

def foo : C Nat := { a := 1, c := 2 }

-- The marker only uses fields from A R, so B R should be removable
/-- info: 1 -/
#guard_msgs in
#eval foo.a
