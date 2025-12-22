def Foo.bar := 42
def needed := Foo.bar

/-- info: 42 -/
#guard_msgs in
#eval needed
