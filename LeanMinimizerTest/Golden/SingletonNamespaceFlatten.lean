namespace Foo
def bar := 42
end Foo

def needed := Foo.bar

/-- info: 42 -/
#guard_msgs in
#eval needed
