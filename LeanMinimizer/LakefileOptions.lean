/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

/-!
# Extract leanOptions from lakefile configuration

This module provides utilities to extract leanOptions from a project's lakefile
and convert them to command-line arguments for the `lean` command.
-/

namespace LeanMinimizer

open System (FilePath)

/-- Find the project root by searching upward for lakefile.toml or lakefile.lean -/
partial def findProjectRootForOptions (startPath : FilePath) : IO (Option FilePath) := do
  let lakefileToml := startPath / "lakefile.toml"
  let lakefileLean := startPath / "lakefile.lean"

  if (← lakefileToml.pathExists) || (← lakefileLean.pathExists) then
    return some startPath
  else
    match startPath.parent with
    | none => return none
    | some parent => findProjectRootForOptions parent

/-- Find the index of a character in a string, returns none if not found -/
def findCharInString (s : String) (c : Char) : Option Nat :=
  s.toList.findIdx? (· == c)

/-- Extract substring between start and end indices -/
def substringBetween (s : String) (startIdx endIdx : Nat) : String :=
  String.ofList (s.toList.drop (startIdx + 1) |>.take (endIdx - startIdx - 1))

/-- Parse lakefile.toml and extract leanOptions as an array of -D arguments.
    Returns command-line arguments like #["-DmaxSynthPendingDepth=3", "-DautoImplicit=false"]. -/
def getLeanOptionsFromToml (projectRoot : FilePath) : IO (Array String) := do
  let lakefilePath := projectRoot / "lakefile.toml"

  -- Check if lakefile.toml exists
  unless ← lakefilePath.pathExists do
    return #[]

  -- Read the TOML file
  let content ← IO.FS.readFile lakefilePath

  -- Parse TOML manually for leanOptions
  -- We'll look for lines like "leanOptions = {key = value, ...}"
  let mut leanArgs := #[]

  for line in content.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "leanOptions" then
      -- Extract the inline table: {key1 = val1, key2 = val2}
      if let some startIdx := findCharInString trimmed '{' then
        if let some endIdx := findCharInString trimmed '}' then
          let tableContent := (substringBetween trimmed startIdx endIdx).trimAscii.toString

          -- Split by commas to get individual key=value pairs
          for pair in tableContent.splitOn "," do
            let pair := pair.trimAscii.toString
            if let some eqIdx := findCharInString pair '=' then
              let key := (String.ofList (pair.toList.take eqIdx)).trimAscii.toString
              let value := (String.ofList (pair.toList.drop (eqIdx + 1))).trimAscii.toString
              -- Convert to -D argument
              leanArgs := leanArgs.push s!"-D{key}={value}"

  return leanArgs

/-- Get lean options for a file by finding its project root and extracting options.
    Returns an array of -D arguments to pass to the lean command. -/
def getLeanOptionsForFile (fileName : String) : IO (Array String) := do
  let fp := FilePath.mk fileName
  let absoluteFilePath ← do
    if fp.isAbsolute then pure fp
    else do
      let cwd ← IO.currentDir
      pure (cwd / fp)

  let startPath := absoluteFilePath.parent.getD (← IO.currentDir)

  match ← findProjectRootForOptions startPath with
  | none => return #[]
  | some root => getLeanOptionsFromToml root

end LeanMinimizer
