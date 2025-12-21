-- Test for header loss when multiple empty scope pairs are removed
-- This comment should be preserved in the output

section A
end A

section B
end B

def needed := 1

/-- info: 1 -/
#guard_msgs in
#eval needed
