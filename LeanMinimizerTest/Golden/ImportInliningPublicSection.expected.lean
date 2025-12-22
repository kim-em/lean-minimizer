section LeanMinimizerTest.Golden.ImportInliningPublicSection.Module
def publicValue : Nat := sorry

namespace Inner
def innerValue : Nat := sorry
end Inner
end LeanMinimizerTest.Golden.ImportInliningPublicSection.Module

#guard_msgs in
def foo : Nat := publicValue + Inner.innerValue
