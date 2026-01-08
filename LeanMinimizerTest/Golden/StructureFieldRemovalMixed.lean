-- Test that field removal does NOT happen when the field value isn't sorry.
-- The field `y` won't be removed because 42 isn't sorry.

structure Bar where
  x : Nat
  y : Nat  -- should NOT remove (used in error)

def a : Bar where
  x := 1
  y := 42

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check a.y + "hello"
