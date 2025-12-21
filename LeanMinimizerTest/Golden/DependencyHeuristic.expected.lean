def base := 1

def helper1 := base + 1

def helper2 := base * 2

def result1 := helper1 + helper2

def result2 := helper2 + 10

/-- info: (4, 12) -/
#guard_msgs in
#eval (result1, result2)

