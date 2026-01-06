import LeanMinimizerTest.Golden.AttributeExpansion.MockToDual

-- This definition uses the mock @[to_dual] attribute
-- which creates a primed copy: foo'
@[to_dual] def foo := 42

-- Test that @[to_dual] works with other attributes
-- The other attributes should be preserved when both versions are used
@[simp, to_dual] def bar := 100

-- Test that theorem declarations are preserved as theorems (not converted to def)
-- We use baz' but NOT baz, forcing expansion
@[to_dual] theorem baz : 1 + 1 = 2 := rfl

-- This definition is unused and should be deleted
def unused := 200

-- The invariant uses foo' (generated), bar (original), and baz' (theorem)
-- This tests that:
-- 1. Attribute expansion adds foo', bar', baz' explicitly
-- 2. Deletion removes foo and bar' (not used) but keeps bar
-- 3. The @[simp] attribute is preserved on bar
-- 4. baz' is generated as a theorem, not a def

/--
info: baz' : 1 + 1 = 2
-/
#guard_msgs in
#check baz'

/-- info: (42, 100) -/
#guard_msgs in
#eval (foo', bar)
