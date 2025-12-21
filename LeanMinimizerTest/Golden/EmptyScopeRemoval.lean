-- Test for empty scope removal pass
-- The empty section should be removed after command deletion removes its contents

section Foo
end Foo

def needed := 1

/-- info: 1 -/
#guard_msgs in
#eval needed
