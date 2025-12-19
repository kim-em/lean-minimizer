section LeanMinimizerTest.Golden.ImportInliningNested.Multi
namespace Outer
namespace Inner
def nested : Nat := 7
end Inner
end Outer
end LeanMinimizerTest.Golden.ImportInliningNested.Multi

#guard_msgs in
def foo : Nat := Outer.Inner.nested
