def _root_.foo' : Nat := 42

def bar := 100

/-- info: (42, 100) -/
#guard_msgs in
#eval (foo', bar)

