def foo : Nat := 42
theorem bar : 1 + 1 = 2 := rfl

/-- info: foo : Nat -/
#guard_msgs in
#check foo
