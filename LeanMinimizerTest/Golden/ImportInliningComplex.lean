import LeanMinimizerTest.Golden.ImportInliningComplex.A
import LeanMinimizerTest.Golden.ImportInliningComplex.B

-- Uses c (from C, via B) and d (from D, via B, which uses e1 from E)
#guard_msgs in
def foo : Nat := c + d
