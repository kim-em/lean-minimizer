structure Foo where
  x : Nat
  y : Nat

def bar : Foo where
  x := sorry
  y := sorry

/-- info: bar : Foo -/
#guard_msgs in
#check bar
