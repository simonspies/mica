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

/-- Build mica and the testsuite runner (`Testsuite.lean`), ask the runner for
    the test list, and register one Lake job per test so the build monitor
    shows live progress. Reports and the summary are printed once all jobs
    have finished. -/
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
    args := #["--list"] ++ paths.toArray
  }
  if listOut.exitCode != 0 then
    error s!"test discovery failed: {listOut.stderr}"
  let files := listOut.stdout.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  let results ← runBuild do
    let jobs ← files.mapM fun file =>
      withRegisterJob s!"test {file}" <| Job.async do
        let out ← IO.Process.output {
          cmd := exeFile.toString
          args := #["--mica", micaFile.toString, "--single"] ++ flags.toArray ++ #[file]
        }
        return (file, out)
    return Job.collectArray jobs "testsuite"
  let mut failed := #[]
  for (file, out) in results do
    IO.print out.stdout
    IO.eprint out.stderr
    if out.exitCode != 0 then
      failed := failed.push file
  IO.println ""
  let bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"
  if failed.isEmpty then
    IO.println (bold "all tests passed")
    return 0
  else
    IO.println (bold s!"{failed.size} {if failed.size == 1 then "test" else "tests"} failed")
    for file in failed do
      IO.println s!"- {file}"
    return 1
