import LeanMinimizerTest.Golden.ImportMinimization.A

-- Module B re-exports A and adds its own constant
def bConstant : Nat := aConstant + 1
