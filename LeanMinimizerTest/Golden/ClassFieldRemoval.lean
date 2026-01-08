-- Test class field removal.
-- The field `proof` should be removed because its only assignment will be sorry.

class MyClass (α : Type) where
  val : α
  proof : True  -- remove this

instance : MyClass Nat where
  val := 42
  proof := trivial

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check MyClass.val (α := Nat) + "hello"
