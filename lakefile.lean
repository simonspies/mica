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
  elapsedMs : Nat

structure TestsuiteOutcomes where
  compile : Array TestOutcome
  check : Array TestOutcome

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

def runProcessWithTimeoutIn? (cmd : String) (args : Array String) (cwd? : Option FilePath)
    (timeoutMs : UInt32) : IO ProcessResult := do
  let child ← IO.Process.spawn {
    cmd := cmd
    args := args
    cwd := cwd?
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

def runProcessWithTimeout (cmd : String) (args : Array String) (timeoutMs : UInt32) :
    IO ProcessResult := do
  runProcessWithTimeoutIn? cmd args none timeoutMs

def measureTestOutcome (path : FilePath) (action : IO ProcessResult) : IO TestOutcome := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  return { path, result, elapsedMs := stop - start }

def runTest (mica : LeanExe) (file : FilePath) : IO TestOutcome := do
  measureTestOutcome file <|
    runProcessWithTimeout mica.file.toString #[file.toString] testTimeoutMs

def runStdlibCompileIn (tmpDir : FilePath) : IO TestOutcome := do
  let cwd ← IO.currentDir
  let path := cwd / "mica.ml"
  measureTestOutcome path <|
    try
      runProcessWithTimeoutIn? "ocamlopt" #["-c", path.toString, "-o", "mica.cmx"]
        (some tmpDir) testTimeoutMs
    catch e =>
      pure (.terminated {
        exitCode := 127
        stdout := ""
        stderr := s!"failed to run ocamlopt: {e}\n"
      })

def runOcamlExampleCompileIn (tmpDir : FilePath) (idx : Nat) (file : FilePath) : IO TestOutcome := do
  let out := tmpDir / s!"example_{idx}.cmx"
  measureTestOutcome file <|
    try
      runProcessWithTimeoutIn? "ocamlopt"
        #["-I", tmpDir.toString, "-c", file.toString, "-o", out.toString]
        (some tmpDir) testTimeoutMs
    catch e =>
      pure (.terminated {
        exitCode := 127
        stdout := ""
        stderr := s!"failed to run ocamlopt: {e}\n"
      })

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

def resultSuffix (test : TestOutcome) : String :=
  let elapsed := s!" ({test.elapsedMs}ms)"
  match test.result with
  | .timeout ms => s!" timed out after {ms}ms"
  | .terminated output => if output.exitCode == 0 then s!" ✓{elapsed}" else s!" ⨯{elapsed}"

def recordFailure (failed : List TestOutcome) (test : TestOutcome) : List TestOutcome :=
  if isFailure test.result then test :: failed else failed

def printTestHeader (verb filename : String) : IO Unit := do
  IO.print s!"{verb} {filename} ..."
  (← IO.getStdout).flush

private def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"

def printFailureSummary (failed : List TestOutcome) : IO Unit := do
  IO.println (bold s!"{failed.length} {if failed.length = 1 then "test" else "tests"} failed")
  for test in failed.reverse do
    let suffix := match test.result with
      | .timeout _ => " (timed out)"
      | .terminated _ => ""
    IO.println s!"- {test.path.fileName.getD test.path.toString}{suffix}"

def reportTestOutcome (options : TestsuiteOptions) (failed : List TestOutcome) (verb : String)
    (label : String) (test : TestOutcome) : IO (List TestOutcome) := do
  printTestHeader verb label
  IO.println (resultSuffix test)
  let failed := recordFailure failed test
  if !options.summaryOnly || isFailure test.result then
    printCapturedOutput test
  pure failed

def reportTestOutcomes (options : TestsuiteOptions) (failed : List TestOutcome) (verb : String)
    (tests : Array TestOutcome) : IO (List TestOutcome) := do
  let mut failed := failed
  for test in tests do
    let filename := test.path.fileName.getD test.path.toString
    failed ← reportTestOutcome options failed verb filename test
  pure failed

def runTestsuiteActions (mica : LeanExe) (tests : Array FilePath) : ScriptM TestsuiteOutcomes := do
  IO.FS.withTempDir fun tmpDir => do
    let stdlib ← runStdlibCompileIn tmpDir
    runBuild do
      let mut compileJobs := #[]
      if !isFailure stdlib.result then
        let mut idx := 0
        for file in tests do
          let compileIdx := idx
          let job ← withRegisterJob s!"compile {file.fileName.getD file.toString}" <|
            Job.async do
              runOcamlExampleCompileIn tmpDir compileIdx file
          compileJobs := compileJobs.push job
          idx := idx + 1
      let checkJobs ← tests.mapM fun file =>
        withRegisterJob s!"test {file.fileName.getD file.toString}" <|
          Job.async do
            runTest mica file
      let compileJob := Job.collectArray compileJobs "ocaml compile testsuite"
      let checkJob := Job.collectArray checkJobs "testsuite"
      return compileJob.zipWith
        (fun compile check => { compile := #[stdlib] ++ compile, check := check })
        checkJob

def printTestsuiteSummary (failed : List TestOutcome) : IO UInt32 := do
  IO.println ""
  if List.isEmpty failed then
    IO.println (bold "all tests passed")
    return 0
  else
    printFailureSummary failed
    return 1

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

script testsuite (args) := do
  let some mica <- Lake.findLeanExe? `mica
    | error "mica executable undefined"
  if not (<- mica.file.pathExists) then
    error "mica executable has not been built"
  let options ← parseTestsuiteArgs args
  let inputPath ← resolveInputPath options.dir
  let tests ← discoverTests inputPath
  let outcomes ← runTestsuiteActions mica tests
  let failed ← reportTestOutcomes options [] "Compiling" outcomes.compile
  unless outcomes.check.isEmpty do
    IO.println ""
  let failed ← reportTestOutcomes options failed "Checking" outcomes.check
  printTestsuiteSummary failed
