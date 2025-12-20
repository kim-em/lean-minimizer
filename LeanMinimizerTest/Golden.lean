/-
This module imports all Golden test submodules to ensure they are built.
These modules are used as test inputs by the minimize tool.
-/
import LeanMinimizerTest.Golden.BodyReplacementInlined.B
import LeanMinimizerTest.Golden.BodyReplacementInlined.C
import LeanMinimizerTest.Golden.ImportInlining.Simple
import LeanMinimizerTest.Golden.ImportInliningComplex.A
import LeanMinimizerTest.Golden.ImportInliningComplex.B
import LeanMinimizerTest.Golden.ImportInliningComplex.C
import LeanMinimizerTest.Golden.ImportInliningComplex.D
import LeanMinimizerTest.Golden.ImportInliningComplex.E
import LeanMinimizerTest.Golden.ImportInliningDemodulize.Dep
import LeanMinimizerTest.Golden.ImportInliningDemodulize.ModFile
import LeanMinimizerTest.Golden.ImportInliningNamespace.WithNS
import LeanMinimizerTest.Golden.ImportInliningNested.Multi
import LeanMinimizerTest.Golden.ImportInliningTransitive.A
import LeanMinimizerTest.Golden.ImportInliningTransitive.B
import LeanMinimizerTest.Golden.ImportMinimization.A
import LeanMinimizerTest.Golden.ImportMinimization.B
import LeanMinimizerTest.Golden.ImportRemoval.Unused
import LeanMinimizerTest.Golden.ImportRequired.Needed
import LeanMinimizerTest.Golden.ModuleRemoval.Dep
