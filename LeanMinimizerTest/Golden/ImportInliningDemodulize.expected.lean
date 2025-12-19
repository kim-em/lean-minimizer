section LeanMinimizerTest.Golden.ImportInliningDemodulize.Dep
public def depValue : Nat := 1
end LeanMinimizerTest.Golden.ImportInliningDemodulize.Dep

section LeanMinimizerTest.Golden.ImportInliningDemodulize.ModFile
public def modValue : Nat := depValue + 50
end LeanMinimizerTest.Golden.ImportInliningDemodulize.ModFile

#guard_msgs in
def foo : Nat := modValue
