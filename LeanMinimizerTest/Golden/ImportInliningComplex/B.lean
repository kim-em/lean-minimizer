import LeanMinimizerTest.Golden.ImportInliningComplex.C
import LeanMinimizerTest.Golden.ImportInliningComplex.D

-- B has an unused definition, but imports C and D which are needed
def b : Nat := 999
