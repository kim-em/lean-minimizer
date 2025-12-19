import LeanMinimizerTest.Golden.ImportRequired.Needed

-- This import is required and cannot be removed or replaced
-- (Needed has no imports of its own besides Init)
#guard_msgs in
def foo : Nat := neededConstant
