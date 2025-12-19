import LeanMinimizerTest.Golden.ImportRemoval.Unused

-- The import above is unused, so it should be removed
#guard_msgs in
def foo : Nat := 1
