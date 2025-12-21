section LeanMinimizerTest.Golden.ImportInliningPublicMetaSection.Module
public meta section

def metaValue : Nat := sorry
end
end LeanMinimizerTest.Golden.ImportInliningPublicMetaSection.Module

#guard_msgs in
def foo : Nat := metaValue
