-- Test for open argument minimization pass
-- The open command has two namespaces, but only one is needed

namespace Foo
def foo := 1
end Foo

namespace Bar
def bar := 2
end Bar

open Foo Bar

def needed := foo

/-- info: 1 -/
#guard_msgs in
#eval needed
