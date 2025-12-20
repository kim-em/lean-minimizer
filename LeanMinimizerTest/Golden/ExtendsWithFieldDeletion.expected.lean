structure A where
  a : Nat

structure C  extends A where
  c : Nat

def foo : C where
  a := 1
  -- This will be replaced with `h := sorry`,
  -- after which we can replace `B` with `A` in the `extends` clause for `C`
  c := sorry

#guard_msgs in
example : foo.a = 1 := rfl
