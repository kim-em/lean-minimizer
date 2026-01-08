-- Test structure field removal with multiple instances.
-- The field `proof` should be removed because ALL its assignments will be sorry.

structure Foo where
  x : Nat
  proof : True  -- remove this

def a : Foo where
  x := 1
  proof := trivial

def b : Foo where
  x := 2
  proof := trivial

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check a.x + "hello"
