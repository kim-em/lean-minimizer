module

import all LeanMinimizerTest.Golden.ModuleRemoval.Dep

-- File uses the module system with `import all` modifier
-- The module removal pass should strip the modifier
#guard_msgs in
def foo : Nat := depConstant
