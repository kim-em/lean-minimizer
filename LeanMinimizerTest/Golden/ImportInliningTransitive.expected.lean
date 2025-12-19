section LeanMinimizerTest.Golden.ImportInliningTransitive.A
def aValue : Nat := 10
end LeanMinimizerTest.Golden.ImportInliningTransitive.A

section LeanMinimizerTest.Golden.ImportInliningTransitive.B
def bValue : Nat := aValue + 1
end LeanMinimizerTest.Golden.ImportInliningTransitive.B

#guard_msgs in
def foo : Nat := bValue
