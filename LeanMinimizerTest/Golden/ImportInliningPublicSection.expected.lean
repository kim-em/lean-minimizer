section LeanMinimizerTest.Golden.ImportInliningPublicSection.Module
public section

def publicValue : Nat := sorry

namespace Inner
def innerValue : Nat := sorry
end Inner
end
end LeanMinimizerTest.Golden.ImportInliningPublicSection.Module

#guard_msgs in
def foo : Nat := publicValue + Inner.innerValue
