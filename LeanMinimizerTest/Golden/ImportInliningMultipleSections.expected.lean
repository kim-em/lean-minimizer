section LeanMinimizerTest.Golden.ImportInliningMultipleSections.Module
section

def someValue : Nat := sorry
end
end LeanMinimizerTest.Golden.ImportInliningMultipleSections.Module

#guard_msgs in
def foo : Nat := someValue
