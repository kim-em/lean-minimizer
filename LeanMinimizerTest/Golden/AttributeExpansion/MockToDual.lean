/-
Mock @[to_dual] attribute for testing.

This creates a copy of the declaration with a prime suffix.
For example: @[to_dual] def foo := 42  creates  def foo' := 42
-/
import Lean

open Lean Meta Elab Command

/-- Append a prime to a name: `foo` -> `foo'` -/
def appendPrime : Name → Name
  | .str p s => .str p (s ++ "'")
  | n => n

/-- Copy a constant to a new name. -/
def copyConstant (src tgt : Name) : CoreM Unit := do
  let env ← getEnv
  let some srcInfo := env.find? src | throwError "constant {src} not found"

  -- Build the declaration based on the constant type
  let decl : Declaration := match srcInfo with
    | .defnInfo val =>
      .defnDecl { val with name := tgt }
    | .thmInfo val =>
      .thmDecl { val with name := tgt }
    | .axiomInfo val =>
      .axiomDecl { val with name := tgt }
    | .opaqueInfo val =>
      .opaqueDecl { val with name := tgt }
    | .quotInfo _ =>
      panic! "cannot copy quot"
    | .inductInfo _ =>
      panic! "cannot copy inductive"
    | .ctorInfo _ =>
      panic! "cannot copy constructor"
    | .recInfo _ =>
      panic! "cannot copy recursor"

  addAndCompile decl

initialize registerBuiltinAttribute {
  name := `to_dual
  descr := "Mock to_dual: creates a primed copy of the declaration"
  applicationTime := .afterCompilation
  add := fun src _stx _kind => do
    let tgt := appendPrime src
    copyConstant src tgt
}
