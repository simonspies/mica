import Lake
open System Lake DSL

package mica where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.30.0"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git"@"41eca5f0a4b6b38bfc5a53a7021182f1a5385863"/"Iris"

lean_lib Mica

lean_lib Exploration where globs := #[`Exploration.+]

@[default_target] lean_exe mica where root := `Main

lean_exe «testsuite-runner» where root := `Testsuite

lean_exe «dynamic-goal» where root := `Exploration.DynamicGoal

lean_exe «smt-query» where root := `Exploration.SMTQuery

def runFileSummaries (extraArgs : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["scripts/lean_outline.py", "--all"] ++ extraArgs
  }
  child.wait

def runOverviews : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["scripts/file_overview.py", "Mica"]
  }
  child.wait

script «generate-file-summaries» (args) := runFileSummaries args.toArray

script «generate-overviews» (_args) := runOverviews

script «generate-docs» (args) := do
  let rc ← runFileSummaries args.toArray
  if rc ≠ 0 then return rc
  runOverviews

/-- Build mica and the testsuite runner (`Testsuite.lean`), then forward the
    arguments to the runner. -/
script testsuite (args) := do
  let some mica ← Lake.findLeanExe? `mica
    | error "mica executable undefined"
  let some suite ← Lake.findLeanExe? `«testsuite-runner»
    | error "testsuite-runner executable undefined"
  let (micaFile, exeFile) ← runBuild do
    let micaJob ← mica.exe.fetch
    let suiteJob ← suite.exe.fetch
    return micaJob.zipWith (fun m s => (m, s)) suiteJob
  let child ← IO.Process.spawn {
    cmd := exeFile.toString
    args := #["--mica", micaFile.toString] ++ args.toArray
  }
  child.wait
