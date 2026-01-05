import LeanMinimizerTest.Golden.ParsimoniousRestart.Lib

-- This definition uses neededValue from the imported module
def myValue : Nat := neededValue

-- Some more original content that depends on myValue
def anotherValue : Nat := myValue + 1

/-- info: 43 -/
#guard_msgs in
#eval anotherValue
