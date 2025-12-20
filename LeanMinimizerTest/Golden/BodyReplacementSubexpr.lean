-- Test: Body replacement for Prop-valued subexpressions
-- The whole body can't be sorry (invariant needs bar.1 = 42)
-- But the proof `by omega` can become sorry

def bar : { x : Nat // x > 0 } := ⟨42, by omega⟩

#guard_msgs in
example : bar.1 = 42 := rfl
