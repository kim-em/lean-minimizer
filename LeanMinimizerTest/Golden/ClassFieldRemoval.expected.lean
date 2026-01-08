
class MyClass (α : Type) where
  val : α
instance : MyClass Nat where
  val := sorry

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check MyClass.val (α := Nat) + "hello"
