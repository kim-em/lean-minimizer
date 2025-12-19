section LeanMinimizerTest.Golden.ImportInliningNamespace.WithNS
namespace MyNS
def value : Nat := 100
end MyNS
end LeanMinimizerTest.Golden.ImportInliningNamespace.WithNS

#guard_msgs in
def foo : Nat := MyNS.value
