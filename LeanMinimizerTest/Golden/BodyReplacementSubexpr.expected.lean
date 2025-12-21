
def bar : { x : Nat // x > 0 } := ⟨42, sorry⟩

#guard_msgs in
example : bar.1 = 42 := rfl
