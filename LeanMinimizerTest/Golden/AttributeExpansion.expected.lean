def _root_.foo' : Nat := 42

def bar := 100

theorem _root_.baz' : 1 + 1 = 2 := sorry

theorem _root_.qux' : 2 + 2 = 4 := sorry

/--
info: baz' : 1 + 1 = 2
-/
#guard_msgs in
#check baz'

/--
info: qux' : 2 + 2 = 4
-/
#guard_msgs in
#check qux'

/-- info: (42, 100) -/
#guard_msgs in
#eval (foo', bar)

