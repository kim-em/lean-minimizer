import LeanMinimizerTest.Golden.ImportMinimization.B

-- We import B but only use aConstant from A
-- Import minimization should replace B with A
#guard_msgs in
def foo : Nat := aConstant
