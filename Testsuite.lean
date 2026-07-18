/-!
# Testsuite runner

The testsuite driver, moved out of `lakefile.lean`. Invoked via
`lake run testsuite`, which builds this executable and forwards the
arguments, passing the mica executable via `--mica`.

Compared to the lakefile version, `ScriptM` becomes `IO` and Lake's job
machinery is replaced by a bounded worker pool; everything else is a
verbatim move.
-/

open System (FilePath)

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
  summaryOnly : Bool := false
  mica : Option FilePath := none
  dir : Option FilePath := none

def testTimeoutMs : UInt32 := 300000

def pollIntervalMs : UInt32 := 300

/-- Worker threads per parallel phase. -/
def poolSize : Nat := 8

def testsuiteUsage : String :=
  "usage: testsuite --mica PATH [--summary-only] TESTPATH"

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

def runTest (mica : FilePath) (file : FilePath) : IO TestOutcome := do
  measureTestOutcome file <|
    runProcessWithTimeout mica.toString #[file.toString] testTimeoutMs

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

def parseTestsuiteArgs : List String → TestsuiteOptions → Except String TestsuiteOptions
  | [], opts => .ok opts
  | "--summary-only" :: rest, opts =>
      parseTestsuiteArgs rest { opts with summaryOnly := true }
  | "--mica" :: path :: rest, opts =>
      parseTestsuiteArgs rest { opts with mica := some path }
  | arg :: rest, opts =>
      if arg.startsWith "-" then .error s!"unknown option '{arg}'"
      else match opts.dir with
        | none => parseTestsuiteArgs rest { opts with dir := some arg }
        | some _ => .error testsuiteUsage

def resolveInputPath (path : FilePath) : IO FilePath := do
  let cwd ← IO.currentDir
  let inputPath := if path.isAbsolute then path else cwd / path
  if !(← inputPath.pathExists) then
    throw <| IO.userError s!"test path does not exist: {inputPath}"
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

private partial def workerLoop (jobs : Array (IO TestOutcome)) (next : IO.Ref Nat)
    (results : IO.Ref (Array (Option TestOutcome))) : IO Unit := do
  let i ← next.modifyGet fun i => (i, i + 1)
  if h : i < jobs.size then
    let r ← jobs[i]
    results.modify (·.set! i (some r))
    workerLoop jobs next results

/-- Run all jobs on a bounded pool of dedicated threads, preserving order. -/
def runPool (jobs : Array (IO TestOutcome)) : IO (Array TestOutcome) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate jobs.size (none : Option TestOutcome))
  let workers := min poolSize (max jobs.size 1)
  let tasks ← (Array.range workers).mapM fun _ =>
    IO.asTask (workerLoop jobs next results) Task.Priority.dedicated
  for t in tasks do
    IO.ofExcept t.get
  (← results.get).mapM fun
    | some r => pure r
    | none => throw <| IO.userError "testsuite: worker pool lost a result"

def runTestsuiteActions (mica : FilePath) (tests : Array FilePath) : IO TestsuiteOutcomes := do
  IO.FS.withTempDir fun tmpDir => do
    let stdlib ← runStdlibCompileIn tmpDir
    let compile ←
      if isFailure stdlib.result then
        pure #[]
      else
        runPool (tests.mapIdx fun idx file => runOcamlExampleCompileIn tmpDir idx file)
    let check ← runPool (tests.map fun file => runTest mica file)
    return { compile := #[stdlib] ++ compile, check := check }

def printTestsuiteSummary (failed : List TestOutcome) : IO UInt32 := do
  IO.println ""
  if List.isEmpty failed then
    IO.println (bold "all tests passed")
    return 0
  else
    printFailureSummary failed
    return 1

def main (args : List String) : IO UInt32 := do
  let opts ← match parseTestsuiteArgs args {} with
    | .ok opts => pure opts
    | .error e => do
        IO.eprintln e
        return 1
  let (some mica, some dir) := (opts.mica, opts.dir)
    | do
        IO.eprintln testsuiteUsage
        return 1
  if !(← mica.pathExists) then
    IO.eprintln s!"mica executable not found at {mica}; run `lake build` first"
    return 1
  let inputPath ← resolveInputPath dir
  let tests ← discoverTests inputPath
  let outcomes ← runTestsuiteActions mica tests
  let failed ← reportTestOutcomes opts [] "Compiling" outcomes.compile
  unless outcomes.check.isEmpty do
    IO.println ""
  let failed ← reportTestOutcomes opts failed "Checking" outcomes.check
  printTestsuiteSummary failed
