import LeanMinimizerTest.Golden.AttributeExpansion.MockToDual

-- Test 1: Simple (attr := ...) stripping
@[to_dual (attr := simp)] def foo := 42

-- Test 2: Multi-attribute block — only strip args, keep both attrs
@[simp, to_dual (attr := simp)] def bar := 100

-- Test 3: deprecated with string argument containing special chars
@[deprecated "use foo instead"] def baz := foo

-- Test 4: Dotted attribute name (Lean.Elab.something-style)
-- (using to_dual as a stand-in since dotted attrs need registration)

-- Test 5: Nested parens in attribute args
@[to_dual (attr := simp)] def qux := 7

/-- info: (42, 100) -/
#guard_msgs in
#eval (foo', bar)

/-- info: 7 -/
#guard_msgs in
#eval qux'
