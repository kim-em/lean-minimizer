/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Passes.EmptyScopeRemoval

/-!
# Public Section Removal Pass

This pass removes `public section` / `public meta section` / `end` wrapper blocks.
These visibility modifiers are typically not needed in minimized examples.

After import inlining, modules containing `public section` blocks get their content
wrapped in named sections. The `public`/`meta` modifiers control visibility but are
unnecessary when the goal is minimizing for bug reproduction.

Example transformation:
```lean
section Module.Name
public section
def foo := sorry
end
end Module.Name
```
becomes:
```lean
section Module.Name
def foo := sorry
end Module.Name
```
-/

namespace LeanMinimizer

open Lean

/-- Check if a command is a `public section` or `public meta section` (anonymous).
    Returns `true` if it's a public anonymous section, `false` otherwise. -/
def isPublicAnonymousSection (stx : Syntax) : Bool :=
  if stx.isOfKind `Lean.Parser.Command.section then
    -- Check if it has public modifier by examining reprinted text
    match stx.reprint with
    | some repr =>
      let trimmed := repr.trimAscii.toString
      -- Must start with "public"
      if !trimmed.startsWith "public" then
        false
      else
        -- Extract what comes after "public " (with possible "meta " in between)
        let afterPublic := (trimmed.drop 6).trimAsciiStart.toString
        -- Check for "meta section" or just "section"
        let afterModifiers :=
          if afterPublic.startsWith "meta" then
            (afterPublic.drop 4).trimAsciiStart.toString
          else
            afterPublic
        -- Must be "section" followed by nothing or whitespace (anonymous)
        if afterModifiers == "section" then
          true
        else if afterModifiers.startsWith "section" then
          let rest := (afterModifiers.drop 7).toString
          -- Check that what follows is not an identifier (anonymous section)
          if rest.isEmpty then true
          else
            let c := rest.toList[0]!
            c == '\n' || c == ' ' || c == '-'
        else
          false
    | none => false
  else
    false

/-- Check if a command opens a new scope (section, namespace, or end closes one). -/
def scopeDelta (stx : Syntax) : Int :=
  if stx.isOfKind `Lean.Parser.Command.section then 1
  else if stx.isOfKind `Lean.Parser.Command.namespace then 1
  else if stx.isOfKind `Lean.Parser.Command.end then -1
  else 0

/-- Find one public section and its matching end, returning indices to remove.
    Returns `none` if no public section is found. -/
def findPublicSectionPair (steps : Array CompilationStep) :
    Option (Nat × Nat) := Id.run do
  for i in [:steps.size] do
    if h : i < steps.size then
      let stx := steps[i].stx
      if isPublicAnonymousSection stx then
        -- Found a public section, now find matching end
        let mut depth : Int := 1
        for j in [i + 1 : steps.size] do
          if hj : j < steps.size then
            let delta := scopeDelta steps[j].stx
            depth := depth + delta
            if depth == 0 then
              -- Found matching end
              return some (i, j)
        -- No matching end found (unclosed section)
        return none
  return none

/-- Remove one public section wrapper (section and matching end).
    Returns the new list of steps and whether a removal was made. -/
def removeOnePublicSectionWrapper (steps : Array CompilationStep) :
    Array CompilationStep × Bool := Id.run do
  match findPublicSectionPair steps with
  | none => (steps, false)
  | some (sectionIdx, endIdx) =>
    -- Remove end first (higher index), then section
    let newSteps := (steps.eraseIdx! endIdx).eraseIdx! sectionIdx
    (newSteps, true)

/-- Repeatedly remove public section wrappers until no more can be found. -/
def removeAllPublicSectionWrappers (steps : Array CompilationStep) :
    Array CompilationStep × Nat := Id.run do
  let mut currentSteps := steps
  let mut totalRemoved : Nat := 0
  let mut changed := true

  while changed do
    let (newSteps, removed) := removeOnePublicSectionWrapper currentSteps
    if removed then
      currentSteps := newSteps
      totalRemoved := totalRemoved + 2  -- Each pair is 2 commands
    else
      changed := false

  return (currentSteps, totalRemoved)

/-- The public section removal pass.

    Removes `public section` / `public meta section` wrapper blocks.
    These visibility modifiers are typically not needed in minimized examples.

    This pass runs after empty scope removal and handles the case where
    public sections have content between them and their matching end. -/
unsafe def publicSectionRemovalPass : Pass where
  name := "Public Section Removal"
  cliFlag := "public-section"
  run := fun ctx => do
    -- Only process steps before marker
    let stepsBeforeMarker := ctx.steps.filter (·.idx < ctx.markerIdx)
    let stepsFromMarker := ctx.steps.filter (·.idx ≥ ctx.markerIdx)

    let (newStepsBeforeMarker, removed) := removeAllPublicSectionWrappers stepsBeforeMarker

    if removed == 0 then
      return { source := ctx.source, changed := false, action := .continue }

    if ctx.verbose then
      IO.eprintln s!"  Removed {removed} public section commands ({removed / 2} wrappers)"

    -- Reconstruct source from remaining steps
    let allNewSteps := newStepsBeforeMarker ++ stepsFromMarker
    let newSource := reconstructSourceFromSteps ctx.source ctx.headerEndPos allNewSteps

    -- Use .repeat to run again in case there are now newly-removable wrappers
    return { source := newSource, changed := true, action := .repeat }

end LeanMinimizer
