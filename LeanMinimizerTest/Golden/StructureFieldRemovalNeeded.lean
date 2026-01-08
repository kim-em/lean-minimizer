-- Test that field removal does NOT happen when removing would break compilation.
-- The field `h` should NOT be removed because `a.h` is accessed.

structure Foo where
  x : Nat
  h : x > 0  -- this field depends on x

def a : Foo where
  x := 1
  h := by decide

-- Uses the field - removing h would break this
example : a.x > 0 := a.h

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check a.x + "hello"
