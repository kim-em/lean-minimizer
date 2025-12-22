
section Wrapper
def foo : Nat := sorry

end Wrapper

#guard_msgs in
def bar : Nat := foo
