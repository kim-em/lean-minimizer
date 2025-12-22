-- This module serves as the root of the `LeanMinimizer` library.
-- Import modules here that should be built as part of the library.
import LeanMinimizer.Basic
import LeanMinimizer.Dependencies
import LeanMinimizer.Subprocess
import LeanMinimizer.Pass
import LeanMinimizer.Passes.ModuleRemoval
import LeanMinimizer.Passes.Deletion
import LeanMinimizer.Passes.EmptyScopeRemoval
import LeanMinimizer.Passes.SingletonNamespaceFlattening
import LeanMinimizer.Passes.PublicSectionRemoval
import LeanMinimizer.Passes.BodyReplacement
import LeanMinimizer.Passes.TextSubstitution
import LeanMinimizer.Passes.ExtendsSimplification
import LeanMinimizer.Passes.ImportMinimization
import LeanMinimizer.Passes.ImportInlining
import LeanMinimizer.Passes.AttributeExpansion
