section LeanMinimizerTest.Golden.BodyReplacementInlined.B
def f : { x : Nat // x = 37 } := ⟨37, sorry⟩
end LeanMinimizerTest.Golden.BodyReplacementInlined.B

#guard_msgs in
example : f.1 = 37 := rfl
