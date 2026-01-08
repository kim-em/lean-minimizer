structure A where
  a : Nat

structure C  extends A where

def foo : C where
  a := 1

#guard_msgs in
example : foo.a = 1 := rfl

