section LeanMinimizerTest.Golden.ImportInliningMutual.Module

section MutualSection

def mutualValue : Nat := 42

end MutualSection

end LeanMinimizerTest.Golden.ImportInliningMutual.Module

#guard_msgs in
def foo : Nat := mutualValue

