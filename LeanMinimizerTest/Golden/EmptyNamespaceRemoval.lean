-- Test for empty namespace removal pass
-- The empty namespace should be removed

namespace Foo
end Foo

def needed := 1

/-- info: 1 -/
#guard_msgs in
#eval needed
