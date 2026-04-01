import Lake
open System Lake DSL

package mica where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"13214706190da5a7c4f634733c8895396cb0a121"

lean_lib Mica

lean_lib Exploration where globs := #[`Exploration.+]

@[default_target] lean_exe mica where root := `Main

lean_exe «dynamic-goal» where root := `Exploration.DynamicGoal

lean_exe «smt-query» where root := `Exploration.SMTQuery


def check (mica: LeanExe) (file : FilePath) : ScriptM UInt32 := do
  let process ← IO.Process.spawn {
    cmd := mica.file.toString
    args := #[file.toString]
    stdin := .null
    stdout := .null
    stderr := .null
  }
  return <- process.wait

script test := do
  let some mica <- Lake.findLeanExe? `mica
    | error "mica executable undefined"
  if not (<- mica.file.pathExists) then
    error "mica executable has not been built"
  IO.println "starting ..."
  let app <- IO.currentDir
  let examples_dir := app / "Examples"
  let examples <- examples_dir.readDir
  let stdout <- IO.getStdout
  let mut failed : List FilePath := []
  for file in examples do
    let filename := file.path.fileName.get!
    IO.print ("checking " ++ filename ++ " ...")
    stdout.flush
    let res <- check mica file.path
    if res != 0 then
      IO.println " ⨯"
      failed := file.path :: failed
    else
      IO.println " ✓"

  IO.println ""

  if List.isEmpty failed then
    IO.println "all tests pased"
    return 0
  else
      IO.println s!"{failed.length} {if failed.length = 1 then "test" else "tests"} failed"
    for test in failed do
      IO.println s!"- {test.fileName.get!}"
    return 1
