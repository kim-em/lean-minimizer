section LeanMinimizerTest.Golden.ImportInliningPublicSection.Module
-- Tests scope tracking with public section (module system syntax)
-- The public section is left unclosed, which is common in Mathlib
public section

def publicValue : Nat := sorry

namespace Inner
def innerValue : Nat := sorry
end Inner
end
end LeanMinimizerTest.Golden.ImportInliningPublicSection.Module

#guard_msgs in
def foo : Nat := publicValue + Inner.innerValue
