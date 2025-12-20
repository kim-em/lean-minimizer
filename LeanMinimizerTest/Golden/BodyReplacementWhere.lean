structure Foo where
  x : Nat
  y : Nat

def bar : Foo where
  x := 42
  y := 17

/-- info: bar : Foo -/
#guard_msgs in
#check bar
