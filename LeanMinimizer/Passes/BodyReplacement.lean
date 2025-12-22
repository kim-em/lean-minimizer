/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass
import LeanMinimizer.Dependencies
import Lean.Meta.InferType

/-!
# Body Replacement Pass

This pass replaces declaration bodies with `sorry` to simplify minimized files.

For each declaration (working upward from just above the invariant):
1. Try replacing the entire body with `sorry`
2. If that fails, try replacing Prop-valued subexpressions with `sorry`
3. If that fails and it's a where-structure, try replacing field values with `sorry`

When replacing subexpressions, we process them in reverse position order
to avoid invalidating source positions.
-/

namespace LeanMinimizer

open Lean Elab Frontend Parser Meta

/-- Check if a body is already just `sorry` -/
def bodyIsSorry (source : String) (startPos endPos : String.Pos.Raw) : Bool :=
  let body := String.Pos.Raw.extract source startPos endPos
  body.trimAscii == "sorry"

/-- Get field value ranges from whereStructInst for individual replacement.
    Returns array of (startPos, endPos) for each field value. -/
partial def getWhereFieldValueRanges (declVal : Syntax) : Array (String.Pos.Raw × String.Pos.Raw) :=
  if !declVal.isOfKind `Lean.Parser.Command.whereStructInst then
    #[]
  else
    -- whereStructInst has: "where" structInstFields
    -- structInstFields contains structInstField nodes
    -- Each structInstField has: structInstLVal, then a node containing structInstFieldDef
    -- structInstFieldDef has: ":=" val
    let rec collectFields (stx : Syntax) (acc : Array (String.Pos.Raw × String.Pos.Raw)) :
        Array (String.Pos.Raw × String.Pos.Raw) :=
      let acc' := if stx.isOfKind `Lean.Parser.Term.structInstFieldDef then
        -- structInstFieldDef has: ":=" optNewline val
        if stx.getNumArgs >= 3 then
          let val := stx.getArg 2
          match val.getPos?, val.getTailPos? with
          | some startPos, some endPos => acc.push (startPos, endPos)
          | _, _ => acc
        else acc
      else acc
      (List.range stx.getNumArgs).foldl (init := acc') fun a i => collectFields (stx.getArg i) a
    collectFields declVal #[]

/-! ## Prop subexpression extraction -/

/-- Extract Prop-valued subexpression ranges from InfoTrees.
    These are subexpressions whose type is a proposition (i.e., they are proofs).
    We only include subexpressions that fall within the given body range.

    This includes:
    1. TermInfo nodes whose type is Prop
    2. TacticInfo nodes (like `by ...`) that represent proof terms -/
def extractPropSubexprs (trees : List InfoTree) (bodyStartPos bodyEndPos : String.Pos.Raw) :
    IO (Array (String.Pos.Raw × String.Pos.Raw)) := do
  let mut result : Array (String.Pos.Raw × String.Pos.Raw) := #[]
  for tree in trees do
    let propRanges ← tree.foldInfoM (init := #[]) fun ctx info acc => do
      match info with
      | .ofTermInfo ti =>
        -- Get the source range of this term
        let some startPos := ti.stx.getPos? (canonicalOnly := true)
          | return acc
        let some endPos := ti.stx.getTailPos? (canonicalOnly := true)
          | return acc
        -- Check if this term is within the body range
        if startPos < bodyStartPos || endPos > bodyEndPos then
          return acc
        -- Check if this expression is a proof (its type is Prop)
        let isPropValued ← try
          ctx.runMetaM ti.lctx do
            let ty ← inferType ti.expr
            isProp ty
        catch _ =>
          pure false
        if isPropValued then
          return acc.push (startPos, endPos)
        else
          return acc
      | .ofTacticInfo ti =>
        -- Get the source range
        let some startPos := ti.stx.getPos? (canonicalOnly := true)
          | return acc
        let some endPos := ti.stx.getTailPos? (canonicalOnly := true)
          | return acc
        -- Check if within body range
        if startPos < bodyStartPos || endPos > bodyEndPos then
          return acc
        -- Tactics that represent proof terms (like `by ...`) are always Prop-valued
        -- Check if this is a `by` block - the whole thing can be replaced with sorry
        if ti.stx.getKind == `Lean.Parser.Term.byTactic then
          return acc.push (startPos, endPos)
        else
          return acc
      | _ => return acc
    result := result ++ propRanges
  return result

/-! ## Source manipulation -/

/-- Replace a source range with `sorry` -/
def replaceWithSorry (source : String) (startPos endPos : String.Pos.Raw) : String :=
  let before := String.Pos.Raw.extract source 0 startPos
  let after := String.Pos.Raw.extract source endPos source.rawEndPos
  before ++ "sorry" ++ after

/-! ## The pass -/

/-- The body replacement pass.

    For each declaration before the marker (working upward from just before marker):
    1. Try replacing the entire body with `sorry`
    2. If that fails, try replacing Prop-valued subexpressions with `sorry`
    3. If that fails and it's a where-structure, try replacing field values with `sorry`

    Returns `.repeatThenRestart` on success to continue replacing bodies until
    exhausted, then restart from pass 0 to allow other passes to run. -/
def bodyReplacementPass : Pass where
  name := "Body Replacement"
  cliFlag := "body-replacement"
  needsSubprocess := true
  run := fun ctx => do
    if ctx.verbose then
      IO.eprintln s!"  Processing {ctx.markerIdx} commands for body replacement..."

    -- Process declarations from just before marker going upward
    -- Use ctx.steps for full syntax and InfoTrees (available in subprocess mode)
    for i in (List.range ctx.markerIdx).reverse do
      let some step := ctx.steps[i]?
        | continue

      -- Check if this is a declaration with a body
      let some bodyRange := getDeclBodyRange? step.stx
        | continue

      -- Skip if body is already sorry
      if bodyIsSorry ctx.source bodyRange.1 bodyRange.2 then
        continue

      if ctx.verbose then
        IO.eprintln s!"    Trying declaration at index {i}..."

      -- Phase 1: Try replacing entire body with sorry
      let newSource := replaceWithSorry ctx.source bodyRange.1 bodyRange.2
      if ← testCompilesSubprocess newSource ctx.fileName then
        if ctx.verbose then
          IO.eprintln s!"    Success: replaced entire body with sorry"
        return { source := newSource, changed := true, action := .repeatThenRestart }

      -- Phase 2: Try replacing Prop-valued subexpressions with sorry
      -- These are subexpressions whose type is Prop (proofs)
      let propSubexprs ← extractPropSubexprs step.trees bodyRange.1 bodyRange.2
      -- Sort by end position descending to process from right to left
      let sortedPropSubexprs := propSubexprs.qsort (fun a b => a.2 > b.2)
      -- Filter to unique, non-nested ranges (keep largest containing range for each position)
      let mut uniquePropRanges : Array (String.Pos.Raw × String.Pos.Raw) := #[]
      for range in sortedPropSubexprs do
        -- Skip if this range is contained in a range we already have
        let isNested := uniquePropRanges.any fun r =>
          range.1 >= r.1 && range.2 <= r.2
        if !isNested then
          uniquePropRanges := uniquePropRanges.push range

      for (startPos, endPos) in uniquePropRanges do
        -- Skip if already sorry
        if bodyIsSorry ctx.source startPos endPos then
          continue
        let newSource := replaceWithSorry ctx.source startPos endPos
        if ← testCompilesSubprocess newSource ctx.fileName then
          if ctx.verbose then
            IO.eprintln s!"    Success: replaced Prop subexpression with sorry"
          return { source := newSource, changed := true, action := .repeatThenRestart }

      -- Phase 3: For where-structures, try replacing individual field values
      let inner := getInnerDecl? step.stx
      let declVal := inner.bind findDeclVal?
      if let some dv := declVal then
        if dv.isOfKind `Lean.Parser.Command.whereStructInst then
          let fieldRanges := getWhereFieldValueRanges dv
          -- Sort by end position descending to process from right to left
          let sortedFieldRanges := fieldRanges.qsort (fun a b => a.2 > b.2)
          for (startPos, endPos) in sortedFieldRanges do
            -- Skip if already sorry
            if bodyIsSorry ctx.source startPos endPos then
              continue
            let newSource := replaceWithSorry ctx.source startPos endPos
            if ← testCompilesSubprocess newSource ctx.fileName then
              if ctx.verbose then
                IO.eprintln s!"    Success: replaced where-structure field with sorry"
              return { source := newSource, changed := true, action := .repeatThenRestart }

    -- No changes possible
    if ctx.verbose then
      IO.eprintln s!"  No body replacements possible"
    return { source := ctx.source, changed := false, action := .continue }

end LeanMinimizer
