/-
Comprehensive test for the dependency heuristic.

Structure:
- 10 declarations before the marker
- Invariant depends on `result1` and `result2`
- These depend on helpers which depend on `base`
- 5 unreachable declarations with their own internal dependencies

Dependency graph:
  Reachable (5):
    base ← helper1 ← result1 → invariant
         ↖ helper2 ↙        ↗
              ↖ result2 ────┘

  Unreachable (5):
    unused1 ← unused2 ← unused3
    unrelated1 ← unrelated2
-/

-- Reachable declarations (will be kept)
def base := 1
def helper1 := base + 1
def helper2 := base * 2
def result1 := helper1 + helper2
def result2 := helper2 + 10

-- Unreachable chain 1
def unused1 := 100
def unused2 := unused1 + 1
def unused3 := unused2 + 2

-- Unreachable chain 2
def unrelated1 := 999
def unrelated2 := unrelated1 * 2

/-- info: (4, 12) -/
#guard_msgs in
#eval (result1, result2)
