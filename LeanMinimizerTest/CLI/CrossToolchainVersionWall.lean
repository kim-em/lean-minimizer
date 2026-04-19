-- Regression test for the cross-toolchain feature.
--
-- This file contains a version-gated claim that elaborates under the primary
-- toolchain (4.28+) but fails to elaborate under any earlier toolchain.
-- With `--cross-toolchain leanprover/lean4:v4.27.0`, the initial validator in
-- `Main.lean` must reject this file with the tag
-- `CROSS_TOOLCHAIN_INITIAL_COMPILE_FAILED`.
--
-- Historical bug it catches: `lake env` injects `LD_LIBRARY_PATH` pointing at
-- the primary toolchain's `libleanshared.so`. The `lean` shim in each toolchain
-- dyn-loads `libleanshared.so` via `LD_LIBRARY_PATH`, so the 4.27 shim would
-- transparently execute 4.28 code — making every cross-toolchain check a no-op
-- that simply re-runs the primary toolchain. Bump the `"4.28"` literal below
-- whenever the project's primary toolchain crosses a major boundary.
example : Lean.versionString.startsWith "4.28" := by native_decide

/-- info: () -/
#guard_msgs in
#eval ()
