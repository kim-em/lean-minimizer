section LeanMinimizerTest.Golden.ImportInliningBlockComment.Module
section RealSection

def blockCommentValue : Nat := 42
end RealSection
end LeanMinimizerTest.Golden.ImportInliningBlockComment.Module

#guard_msgs in
def foo : Nat := blockCommentValue
