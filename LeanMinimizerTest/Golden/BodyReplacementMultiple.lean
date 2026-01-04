-- Test that body replacement works correctly when multiple declarations
-- can have their bodies replaced in a single pass.
-- This tests for a bug where position offset tracking corrupted the source.

-- Three independent declarations that can all be replaced with sorry in one pass
def foo : Nat := 1 + 2 + 3

def bar : Nat := 4 + 5 + 6

def baz : Nat := 7 + 8 + 9

-- This references all three to make them non-removable
def qux : Nat := foo + bar + baz

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check qux + "hello"
