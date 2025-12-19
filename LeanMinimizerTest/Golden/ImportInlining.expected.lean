section LeanMinimizerTest.Golden.ImportInlining.Simple
def simpleValue : Nat := 42
end LeanMinimizerTest.Golden.ImportInlining.Simple

#guard_msgs in
def foo : Nat := simpleValue
