
structure A where
  a : Nat

structure C  extends A where
  c : Nat

def foo : C := { a := 1, c := 2 }

/-- info: 1 -/
#guard_msgs in
#eval foo.a

