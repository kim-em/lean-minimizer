import LeanMinimizerTest.Golden.AttributeExpansion.MockToDual

@[to_dual] def foo := 42

def bar := 100

def baz := foo


@[to_dual] def qux := 7

/-- info: (42, 100) -/
#guard_msgs in
#eval (foo', bar)

/-- info: 7 -/
#guard_msgs in
#eval qux'

