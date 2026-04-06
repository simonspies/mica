import Lake
open System Lake DSL

package mica where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"8f9d9cff6bd728b17a24e163c9402775d9e6a365"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git"@"2156ed266bcae27ab8fd00a1ecf0fa9209d4d330"

lean_lib Mica

lean_lib Exploration where globs := #[`Exploration.+]

@[default_target] lean_exe mica where root := `Main

lean_exe «dynamic-goal» where root := `Exploration.DynamicGoal

lean_exe «smt-query» where root := `Exploration.SMTQuery


structure ProcessOutput where
  exitCode : UInt32
  stdout : String
  stderr : String

inductive ProcessResult where
  | timeout (ms : UInt32)
  | terminated (output : ProcessOutput)

structure TestOutcome where
  path : FilePath
  result : ProcessResult

structure TestsuiteOptions where
  summaryOnly : Bool
  dir : FilePath

def testTimeoutMs : UInt32 := 300000

def pollIntervalMs : UInt32 := 300

def testsuiteUsage : String :=
  "usage: lake run testsuite [--summary-only] PATH"

partial def waitForExitOrTimeout {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg) (remainingMs : Nat) : IO (Option UInt32) := do
  match ← child.tryWait with
  | some exitCode => pure (some exitCode)
  | none =>
      if remainingMs <= 0 then
        pure none
      else
        let sleepMs := min pollIntervalMs.toNat remainingMs
        IO.sleep (UInt32.ofNat sleepMs)
        waitForExitOrTimeout child (remainingMs - sleepMs)

def runProcessWithTimeout (cmd : String) (args : Array String) (timeoutMs : UInt32) :
    IO ProcessResult := do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := args
    stdin := .null
    stdout := .piped
    stderr := .piped
  }
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let exitCode? ← waitForExitOrTimeout child timeoutMs.toNat
  match exitCode? with
  | none =>
      child.kill
      discard <| child.wait
      discard <| IO.ofExcept stdoutTask.get
      discard <| IO.ofExcept stderrTask.get
      pure (.timeout timeoutMs)
  | some exitCode =>
      let stdout ← IO.ofExcept stdoutTask.get
      let stderr ← IO.ofExcept stderrTask.get
      pure (.terminated { exitCode, stdout, stderr })

def runTest (mica : LeanExe) (file : FilePath) : ScriptM TestOutcome := do
  let result ← runProcessWithTimeout mica.file.toString #[file.toString] testTimeoutMs
  return { path := file, result := result }

def parseTestsuiteArgs (args : List String) : ScriptM TestsuiteOptions := do
  let mut summaryOnly := false
  let mut dir? : Option FilePath := none
  for arg in args do
    if arg == "--summary-only" then
      summaryOnly := true
    else if arg.startsWith "-" then
      error s!"unknown option '{arg}'"
    else
      match dir? with
      | none => dir? := some arg
      | some _ => error testsuiteUsage
  let some dir := dir?
    | error testsuiteUsage
  return {
    summaryOnly := summaryOnly
    dir := dir
  }

def resolveInputPath (path : FilePath) : ScriptM FilePath := do
  let cwd ← IO.currentDir
  let inputPath := if path.isAbsolute then path else cwd / path
  if !(← inputPath.pathExists) then
    error s!"test path does not exist: {inputPath}"
  pure inputPath

def isMlFile (path : FilePath) : IO Bool := do
  if path.extension != some "ml" then
    return false
  let metadata ← path.metadata
  return metadata.type == .file

partial def discoverTests (path : FilePath) : IO (Array FilePath) := do
  let metadata ← path.metadata
  match metadata.type with
  | .file =>
      if ← isMlFile path then
        pure #[path]
      else
        throw <| IO.userError s!"test file must end in .ml: {path}"
  | .dir =>
      let entries ← path.readDir
      let mut tests := #[]
      for entry in entries do
        let entryTests ← discoverTests entry.path
        tests := tests ++ entryTests
      pure <| tests.qsort (fun a b => a.toString < b.toString)
  | _ =>
      throw <| IO.userError s!"test path must be a .ml file or directory: {path}"

def printOutputBlock (output : String) : IO Unit := do
  unless output.isEmpty do
    IO.print output
    unless output.endsWith "\n" do IO.println ""

def printCapturedOutput (test : TestOutcome) : IO Unit := do
  match test.result with
  | .timeout _ => pure ()
  | .terminated output =>
      printOutputBlock output.stdout
      printOutputBlock output.stderr
      if !output.stdout.isEmpty || !output.stderr.isEmpty then
        IO.println ""

def isFailure (result : ProcessResult) : Bool :=
  match result with
  | .timeout _ => true
  | .terminated out => out.exitCode != 0

def resultSuffix (result : ProcessResult) : String :=
  match result with
  | .timeout ms => s!" timed out after {ms}ms"
  | .terminated output => if output.exitCode == 0 then " ✓" else " ⨯"

def recordFailure (failed : List TestOutcome) (test : TestOutcome) : List TestOutcome :=
  if isFailure test.result then test :: failed else failed

def printTestHeader (filename : String) : IO Unit := do
  IO.print s!"Checking {filename} ..."
  (← IO.getStdout).flush

private def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"

def printFailureSummary (failed : List TestOutcome) : IO Unit := do
  IO.println (bold s!"{failed.length} {if failed.length = 1 then "test" else "tests"} failed")
  for test in failed.reverse do
    let suffix := match test.result with
      | .timeout _ => " (timed out)"
      | .terminated _ => ""
    IO.println s!"- {test.path.fileName.getD test.path.toString}{suffix}"

script testsuite (args) := do
  let some mica <- Lake.findLeanExe? `mica
    | error "mica executable undefined"
  if not (<- mica.file.pathExists) then
    error "mica executable has not been built"
  let options ← parseTestsuiteArgs args
  let inputPath ← resolveInputPath options.dir
  let tests ← discoverTests inputPath
  let mut failed : List TestOutcome := []
  for file in tests do
    let filename := file.fileName.getD file.toString
    printTestHeader filename
    let test <- runTest mica file
    IO.println (resultSuffix test.result)
    failed := recordFailure failed test
    if !options.summaryOnly || isFailure test.result then
      printCapturedOutput test

  IO.println ""

  if List.isEmpty failed then
    IO.println (bold "all tests passed")
    return 0
  else
    printFailureSummary failed
    return 1
