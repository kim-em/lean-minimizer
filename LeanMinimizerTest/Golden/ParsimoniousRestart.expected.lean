section LeanMinimizerTest.Golden.ParsimoniousRestart.Lib

def neededValue : Nat := 42

end LeanMinimizerTest.Golden.ParsimoniousRestart.Lib

def myValue : Nat := neededValue

def anotherValue : Nat := myValue + 1

/-- info: 43 -/
#guard_msgs in
#eval anotherValue
