import LeanMinimizerTest.Golden.BodyReplacementInlined.C

-- B uses h from C to construct a subtype
def f : { x : Nat // x = 37 } := ⟨37, h⟩
