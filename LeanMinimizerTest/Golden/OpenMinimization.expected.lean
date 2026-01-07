
def Foo.foo := 1

open Foo

def needed := foo

/-- info: 1 -/
#guard_msgs in
#eval needed

