-- Test basic structure field removal.
-- The field `h` should be removed because its only assignment will be sorry
-- after body replacement.

structure A where
  a : Nat
  h : True  -- field to remove

def foo : A where
  a := 1
  h := trivial  -- will become sorry, then field should be removed

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check foo.a + "hello"
