import LeanMinimizerTest.Golden.AttributeExpansion.MockToDual

-- This definition uses the mock @[to_dual] attribute
-- which creates a primed copy: foo'
@[to_dual] def foo := 42

-- Test that @[to_dual] works with other attributes
-- The other attributes should be preserved when both versions are used
@[simp, to_dual] def bar := 100

-- This definition is unused and should be deleted
def unused := 200

-- The invariant uses both foo' (generated) and bar (original)
-- This tests that:
-- 1. Attribute expansion adds foo' and bar' explicitly
-- 2. Deletion removes foo and bar' (not used) but keeps bar
-- 3. The @[simp] attribute is preserved on bar

/-- info: (42, 100) -/
#guard_msgs in
#eval (foo', bar)
