import LeanMinimizerTest.Golden.BodyReplacementInlined.B

-- The invariant only cares about the value, not the proof
#guard_msgs in
example : f.1 = 37 := rfl
