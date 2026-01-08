
structure Foo where
  x : Nat
def a : Foo where
  x := sorry

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check a.x + "hello"
