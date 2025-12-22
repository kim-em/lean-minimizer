
structure A (R : Type) where
  a : R

structure B (R : Type) extends A R

structure C (R : Type)  extends B R where
  c : R

def foo : C Nat := { a := 1, c := 2 }

/-- info: 1 -/
#guard_msgs in
#eval foo.a
