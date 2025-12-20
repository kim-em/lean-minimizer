-- TODO: Run the minimizer on SimpleImport.lean and update this expected output
import Mathlib.Data.Nat.Basic

/-- A simple theorem using Mathlib -/
theorem foo : 1 + 1 = 2 := by
  #guard_msgs in
  decide

def bar : Nat := 42
