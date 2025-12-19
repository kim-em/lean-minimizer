section LeanMinimizerTest.Golden.ImportInliningComplex.E
def e1 : Nat := 1
end LeanMinimizerTest.Golden.ImportInliningComplex.E

section LeanMinimizerTest.Golden.ImportInliningComplex.D
def d : Nat := e1 + 10
end LeanMinimizerTest.Golden.ImportInliningComplex.D

section LeanMinimizerTest.Golden.ImportInliningComplex.C
def c : Nat := 100
end LeanMinimizerTest.Golden.ImportInliningComplex.C

#guard_msgs in
def foo : Nat := c + d
