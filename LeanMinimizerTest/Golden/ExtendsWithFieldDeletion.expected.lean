structure A where
  a : Nat

structure C  extends A where
  c : Nat

def foo : C where
  a := 1
  c := sorry

#guard_msgs in
example : foo.a = 1 := rfl

