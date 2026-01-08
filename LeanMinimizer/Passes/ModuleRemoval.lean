/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanMinimizer.Pass

/-!
# Module System Removal Pass

This pass attempts to remove the `module` keyword and strip import modifiers
(`public`, `meta`, `all`) from a file that uses the Lean 4 module system.
-/

namespace LeanMinimizer

open Lean Elab Frontend Parser

/-- Reconstruct the header without `module` keyword and without import modifiers.
    Returns the new header string. -/
def reconstructHeaderWithoutModule (header : Syntax) : String := Id.run do
  let mut result := ""

  -- Skip the module keyword (first optional child)
  -- Check for prelude (second optional child)
  if header.getNumArgs > 1 then
    let preludeOpt := header[1]!
    if !preludeOpt.isNone && !preludeOpt.isMissing then
      result := result ++ "prelude\n"

  -- Process imports (third child is the list of imports)
  if header.getNumArgs > 2 then
    let imports := header[2]!
    for i in [:imports.getNumArgs] do
      let importStx := imports[i]!
      if let some modName := getImportModuleName importStx then
        result := result ++ s!"import {modName}\n"

  return result

/-- The module system removal pass.

    Removes the `module` keyword and strips import modifiers if the file
    still compiles without them. -/
unsafe def moduleRemovalPass : Pass where
  name := "Module System Removal"
  cliFlag := "module-removal"
  run := fun ctx => do
    -- Quick text check: if "module" doesn't appear at all, skip immediately
    if !ctx.source.containsSubstr "module" then
      if ctx.verbose then
        IO.eprintln "  File does not use module system, skipping"
      return { source := ctx.source, changed := false, action := .continue }

    -- Check if file uses module system
    -- Use the subprocess-provided flag if available, otherwise check syntax
    let hasModule := ctx.hasModule || headerHasModule ctx.header
    if !hasModule then
      if ctx.verbose then
        IO.eprintln "  File does not use module system, skipping"
      return { source := ctx.source, changed := false, action := .continue }

    if ctx.verbose then
      IO.eprintln "  File uses module system, attempting removal..."

    -- Use pre-computed header without module (from subprocess) if available
    let newHeader := if ctx.headerWithoutModule.isEmpty
      then reconstructHeaderWithoutModule ctx.header
      else ctx.headerWithoutModule

    -- Get the commands part (everything after the header)
    let commandsPart := String.Pos.Raw.extract ctx.source ctx.headerEndPos ctx.source.rawEndPos

    -- Build new source
    let newSource := newHeader ++ commandsPart

    -- Test if it compiles
    if !(← testCompilesSubprocess newSource ctx.fileName) then
      if ctx.verbose then
        IO.eprintln "  Module removal failed (does not compile), keeping original"
      return { source := ctx.source, changed := false, action := .continue }

    if ctx.verbose then
      IO.eprintln "  Module removal successful"
    return { source := newSource, changed := true, action := .continue }

end LeanMinimizer
