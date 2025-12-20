-- Test: structure C extends B should be simplified to extends A
-- since B only passes through fields from A

structure A where
  a : Nat

structure B extends A

structure C extends B where
  c : Nat

def foo : C := { a := 1, c := 2 }

/-- info: 1 -/
#guard_msgs in
#eval foo.a
