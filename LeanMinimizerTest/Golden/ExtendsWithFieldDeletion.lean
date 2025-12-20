structure A where
  a : Nat

structure B extends A where
  h : True

structure C extends B where
  c : Nat

def foo : C where
  a := 1
  -- This will be replaced with `h := sorry`,
  -- after which we can replace `B` with `A` in the `extends` clause for `C`
  h := trivial
  c := 2

#guard_msgs in
example : foo.a = 1 := rfl
