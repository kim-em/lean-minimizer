import LeanMinimizerTest.Golden.ImportInliningPublicSection.Module

#guard_msgs in
def foo : Nat := publicValue + Inner.innerValue
