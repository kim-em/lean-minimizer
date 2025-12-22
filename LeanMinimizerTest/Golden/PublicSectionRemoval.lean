-- Test: public section wrapper should be removed

section Wrapper
public section

def foo : Nat := 42

end
end Wrapper

#guard_msgs in
def bar : Nat := foo
