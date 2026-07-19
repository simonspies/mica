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

lean_lib Testsuite where globs := #[`Testsuite.+]

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

/-- Build mica and the testsuite runner (`Testsuite.lean`), ask the runner for
    the task list (`list` → `task,file` lines), and register one Lake job per
    task (`run-task`) so the build monitor shows live progress. Reports are
    printed once all jobs have finished; the summary is delegated back to the
    runner (`summarize`). -/
script testsuite (args) := do
  let some mica ← Lake.findLeanExe? `mica
    | error "mica executable undefined"
  let some suite ← Lake.findLeanExe? `«testsuite-runner»
    | error "testsuite-runner executable undefined"
  let (micaFile, exeFile) ← runBuild do
    let micaJob ← mica.exe.fetch
    let suiteJob ← suite.exe.fetch
    return micaJob.zipWith (fun m s => (m, s)) suiteJob
  let (flags, paths) := args.partition (·.startsWith "-")
  let listOut ← IO.Process.output {
    cmd := exeFile.toString
    args := #["list"] ++ paths.toArray
  }
  if listOut.exitCode != 0 then
    error s!"test discovery failed: {listOut.stderr}"
  let specs := listOut.stdout.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  let results ← runBuild do
    let jobs ← specs.mapM fun spec =>
      withRegisterJob (spec.replace "," " ") <| Job.async do
        let out ← IO.Process.output {
          cmd := exeFile.toString
          args := #["run-task", "--mica", micaFile.toString] ++ flags.toArray ++ #[spec]
        }
        return (spec, out)
    return Job.collectArray jobs "testsuite"
  let mut failed := #[]
  let mut prevTask := ""
  for (spec, out) in results do
    let task := (spec.splitOn ",").headD ""
    if task != prevTask && !prevTask.isEmpty then
      IO.println ""
    prevTask := task
    IO.print out.stdout
    IO.eprint out.stderr
    if out.exitCode != 0 then
      failed := failed.push spec
  let child ← IO.Process.spawn {
    cmd := exeFile.toString
    args := #["summarize"] ++ failed
  }
  child.wait
