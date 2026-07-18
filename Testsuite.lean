/-!
# Testsuite runner

Standalone driver for the mica test corpus, invoked via `lake run testsuite`.
The lake script builds this executable, asks it for the test list
(`--list`), and registers one Lake job per test (`--single FILE`) so the
build monitor shows live progress; this executable itself runs tests
sequentially.

A test is a single `.ml` file. An optional directive on its first line
configures the run:

  (* TEST: <token>* *)

where a token starting with `-` is passed to mica as a flag and the bare
tokens `no-compile` (skip the ocamlopt phase) and `roundtrip` (additionally
check the print∘parse fixpoint of `--print-ocaml`) toggle runner behavior.

Expectations: without a sibling `foo.out`, the mica run must exit 0. With
one, the captured output (stdout ++ stderr, ANSI-stripped, plus a trailing
`[<code>]` line for nonzero exits) must match it; `--promote` rewrites
existing `.out` files with the actual output instead of failing.
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
  label : String
  result : ProcessResult
  elapsedMs : Nat

/-- Per-test configuration from the `(* TEST: ... *)` directive. -/
structure Config where
  flags : Array String := #[]
  noCompile : Bool := false
  roundtrip : Bool := false

structure Test where
  path : FilePath
  label : String
  config : Config
  golden : Option FilePath

structure Options where
  summaryOnly : Bool := false
  promote : Bool := false
  /-- Per-test mode for use as a Lake job: quiet stdlib compile, no summary. -/
  single : Bool := false
  /-- Print the discovered test files and exit. -/
  list : Bool := false
  mica : Option FilePath := none
  paths : Array FilePath := #[]

def testTimeoutMs : UInt32 := 300000

def pollIntervalMs : UInt32 := 300

def usage : String :=
  "usage: testsuite --mica PATH [--summary-only] [--promote] [--single] [PATH ...]\n" ++
  "       testsuite --list [PATH ...]"

/-! ## Process execution -/

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

def measureTestOutcome (label : String) (action : IO ProcessResult) : IO TestOutcome := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  return { label, result, elapsedMs := stop - start }

/-! ## Test discovery -/

def parseDirective (path : FilePath) (line : String) : Except String Config := do
  let line := line.trimAscii.toString
  unless line.startsWith "(* TEST:" do return {}
  unless line.endsWith "*)" do
    throw s!"{path}: malformed TEST directive: {line}"
  let body := ((line.drop "(* TEST:".length).dropEnd "*)".length).toString
  let mut config : Config := {}
  for tok in body.split Char.isWhitespace do
    let tok := tok.toString
    if tok.isEmpty then
      continue
    else if tok.startsWith "-" then
      config := { config with flags := config.flags.push tok }
    else if tok == "no-compile" then
      config := { config with noCompile := true }
    else if tok == "roundtrip" then
      config := { config with roundtrip := true }
    else
      throw s!"{path}: unknown TEST directive token '{tok}'"
  return config

partial def discoverFiles (path : FilePath) (explicit : Bool) : IO (Array FilePath) := do
  let metadata ← path.metadata
  match metadata.type with
  | .file =>
      if path.extension == some "ml" then
        pure #[path]
      else if explicit then
        throw <| IO.userError s!"test file must end in .ml: {path}"
      else
        pure #[]
  | .dir =>
      let mut files := #[]
      for entry in (← path.readDir) do
        files := files ++ (← discoverFiles entry.path (explicit := false))
      pure files
  | _ =>
      if explicit then
        throw <| IO.userError s!"test path must be a .ml file or directory: {path}"
      else
        pure #[]

def relativeLabel (cwd : FilePath) (path : FilePath) : String :=
  let cwdPrefix := cwd.toString ++ FilePath.pathSeparator.toString
  if path.toString.startsWith cwdPrefix then
    (path.toString.drop cwdPrefix.length).toString
  else
    path.toString

def loadTest (cwd : FilePath) (path : FilePath) : IO Test := do
  let contents ← IO.FS.readFile path
  let firstLine := (contents.takeWhile (· != '\n')).toString
  let config ← match parseDirective path firstLine with
    | .ok config => pure config
    | .error e => throw <| IO.userError e
  let goldenPath := path.withExtension "out"
  let golden := if ← goldenPath.pathExists then some goldenPath else none
  return { path, label := relativeLabel cwd path, config, golden }

partial def stripTrailingSep (s : String) : String :=
  if s.length > 1 && s.endsWith FilePath.pathSeparator.toString then
    stripTrailingSep (s.dropEnd 1).toString
  else s

def discoverTests (cwd : FilePath) (paths : Array FilePath) : IO (Array Test) := do
  let mut files := #[]
  for path in paths do
    let path := FilePath.mk (stripTrailingSep path.toString)
    let inputPath := if path.isAbsolute then path else cwd / path
    if !(← inputPath.pathExists) then
      throw <| IO.userError s!"test path does not exist: {inputPath}"
    files := files ++ (← discoverFiles inputPath (explicit := true))
  let sorted := files.qsort (fun a b => a.toString < b.toString)
  sorted.mapM (loadTest cwd)

/-! ## Test actions -/

def runStdlibCompileIn (cwd tmpDir : FilePath) : IO TestOutcome := do
  let path := cwd / "mica.ml"
  measureTestOutcome (relativeLabel cwd path) <|
    try
      runProcessWithTimeoutIn? "ocamlopt" #["-c", path.toString, "-o", "mica.cmx"]
        (some tmpDir) testTimeoutMs
    catch e =>
      pure (.terminated {
        exitCode := 127
        stdout := ""
        stderr := s!"failed to run ocamlopt: {e}\n"
      })

def compileTest (tmpDir : FilePath) (idx : Nat) (test : Test) : IO TestOutcome := do
  let out := tmpDir / s!"example_{idx}.cmx"
  measureTestOutcome test.label <|
    try
      runProcessWithTimeoutIn? "ocamlopt"
        #["-I", tmpDir.toString, "-c", test.path.toString, "-o", out.toString]
        (some tmpDir) testTimeoutMs
    catch e =>
      pure (.terminated {
        exitCode := 127
        stdout := ""
        stderr := s!"failed to run ocamlopt: {e}\n"
      })

def stripAnsi (s : String) : String :=
  (s.replace "\x1b[1m" "").replace "\x1b[0m" ""

def ensureNewline (s : String) : String :=
  if s.isEmpty || s.endsWith "\n" then s else s ++ "\n"

/-- The text a golden `.out` file is compared against: stdout then stderr
    (ANSI-stripped), followed by a `[<code>]` line for nonzero exits. -/
def renderActual (out : ProcessOutput) : String :=
  let base := ensureNewline (stripAnsi out.stdout) ++ ensureNewline (stripAnsi out.stderr)
  if out.exitCode == 0 then base else base ++ s!"[{out.exitCode}]\n"

def diffStrings (tmpDir : FilePath) (tag : String) (expected actual : String) : IO String := do
  let expectedFile := tmpDir / s!"{tag}.expected"
  let actualFile := tmpDir / s!"{tag}.actual"
  IO.FS.writeFile expectedFile expected
  IO.FS.writeFile actualFile actual
  let out ← IO.Process.output {
    cmd := "diff"
    args := #["-u", "-L", "expected", "-L", "actual",
      expectedFile.toString, actualFile.toString]
  }
  pure out.stdout

def checkTest (mica : FilePath) (opts : Options) (tmpDir : FilePath) (idx : Nat) (test : Test) :
    IO TestOutcome := do
  -- Pass the cwd-relative path so file positions in golden output stay portable.
  let outcome ← measureTestOutcome test.label <|
    runProcessWithTimeout mica.toString
      (test.config.flags.push test.label) testTimeoutMs
  let some goldenPath := test.golden
    | return outcome
  match outcome.result with
  | .timeout _ => return outcome
  | .terminated out =>
      let actual := renderActual out
      let expected ← IO.FS.readFile goldenPath
      if actual == expected then
        return { outcome with result := .terminated { exitCode := 0, stdout := "", stderr := "" } }
      else if opts.promote then
        IO.FS.writeFile goldenPath actual
        let note := s!"promoted {goldenPath.fileName.getD goldenPath.toString}\n"
        return { outcome with result := .terminated { exitCode := 0, stdout := note, stderr := "" } }
      else
        let diff ← diffStrings tmpDir s!"golden_{idx}" expected actual
        return { outcome with result := .terminated { exitCode := 1, stdout := diff, stderr := "" } }

/-- Check that `--print-ocaml` output reparses to the same print (fixpoint). -/
def roundtripTest (mica : FilePath) (tmpDir : FilePath) (idx : Nat) (test : Test) :
    IO TestOutcome := do
  measureTestOutcome test.label do
    let args := fun (file : FilePath) => #["--print-ocaml", "--no-check", file.toString]
    let r1 ← runProcessWithTimeout mica.toString (args test.path) testTimeoutMs
    let .terminated out1 := r1
      | return r1
    if out1.exitCode != 0 then
      return .terminated { out1 with stdout := "roundtrip: initial print failed\n" ++ out1.stdout }
    let reprinted := tmpDir / s!"roundtrip_{idx}.ml"
    IO.FS.writeFile reprinted out1.stdout
    let r2 ← runProcessWithTimeout mica.toString (args reprinted) testTimeoutMs
    let .terminated out2 := r2
      | return r2
    if out2.exitCode != 0 then
      return .terminated
        { out2 with stdout := "roundtrip: reparse of printed output failed\n" ++ out2.stdout }
    if out2.stdout == out1.stdout then
      return .terminated { exitCode := 0, stdout := "", stderr := "" }
    else
      let diff ← diffStrings tmpDir s!"roundtrip_{idx}" out1.stdout out2.stdout
      return .terminated { exitCode := 1, stdout := "roundtrip: print is not a fixpoint\n" ++ diff, stderr := "" }

/-! ## Reporting -/

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

private def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"

def printFailureSummary (failed : List TestOutcome) : IO Unit := do
  IO.println (bold s!"{failed.length} {if failed.length = 1 then "test" else "tests"} failed")
  for test in failed.reverse do
    let suffix := match test.result with
      | .timeout _ => " (timed out)"
      | .terminated _ => ""
    IO.println s!"- {test.label}{suffix}"

def reportTestOutcomes (opts : Options) (failed : List TestOutcome) (verb : String)
    (tests : Array TestOutcome) : IO (List TestOutcome) := do
  let mut failed := failed
  for test in tests do
    IO.print s!"{verb} {test.label} ..."
    (← IO.getStdout).flush
    IO.println (resultSuffix test)
    if isFailure test.result then
      failed := test :: failed
    if !opts.summaryOnly || isFailure test.result then
      printCapturedOutput test
  pure failed

def printTestsuiteSummary (failed : List TestOutcome) : IO UInt32 := do
  IO.println ""
  if List.isEmpty failed then
    IO.println (bold "all tests passed")
    return 0
  else
    printFailureSummary failed
    return 1

/-! ## Entry point -/

def parseOptions : List String → Options → Except String Options
  | [], opts => .ok opts
  | "--summary-only" :: rest, opts => parseOptions rest { opts with summaryOnly := true }
  | "--promote" :: rest, opts => parseOptions rest { opts with promote := true }
  | "--single" :: rest, opts => parseOptions rest { opts with single := true }
  | "--list" :: rest, opts => parseOptions rest { opts with list := true }
  | "--mica" :: path :: rest, opts => parseOptions rest { opts with mica := some path }
  | ["--mica"], _ => .error usage
  | arg :: rest, opts =>
    if arg.startsWith "-" then .error s!"unknown option '{arg}'\n{usage}"
    else parseOptions rest { opts with paths := opts.paths.push arg }

def defaultPaths (cwd : FilePath) : IO (Array FilePath) := do
  let candidates := #[cwd / "Examples", cwd / "Tests"]
  let paths ← candidates.filterM (·.pathExists)
  if paths.isEmpty then
    throw <| IO.userError "no test paths given and neither Examples/ nor Tests/ exists"
  pure paths

def run (mica : FilePath) (opts : Options) : IO UInt32 := do
  let cwd ← IO.currentDir
  let paths ← if opts.paths.isEmpty then defaultPaths cwd else pure opts.paths
  let tests ← discoverTests cwd paths
  IO.FS.withTempDir fun tmpDir => do
    let stdlib ← runStdlibCompileIn cwd tmpDir
    let compileOutcomes ←
      if isFailure stdlib.result then
        pure #[]
      else
        let compileTests := tests.filter (!·.config.noCompile)
        compileTests.mapIdxM fun idx test => compileTest tmpDir idx test
    let checkOutcomes ← tests.mapIdxM fun idx test => checkTest mica opts tmpDir idx test
    let roundtripTests := tests.filter (·.config.roundtrip)
    let roundtripOutcomes ←
      roundtripTests.mapIdxM fun idx test => roundtripTest mica tmpDir idx test
    -- In single mode the stdlib stub compile is an implementation detail:
    -- report it only when it fails.
    let stdlibOutcomes := if opts.single && !isFailure stdlib.result then #[] else #[stdlib]
    let failed ← reportTestOutcomes opts [] "Compiling" (stdlibOutcomes ++ compileOutcomes)
    unless opts.single do
      IO.println ""
    let failed ← reportTestOutcomes opts failed "Checking" checkOutcomes
    unless opts.single || roundtripOutcomes.isEmpty do
      IO.println ""
    let failed ← reportTestOutcomes opts failed "Roundtrip" roundtripOutcomes
    if opts.single then
      return if failed.isEmpty then (0 : UInt32) else 1
    printTestsuiteSummary failed

def main (args : List String) : IO UInt32 := do
  let opts ← match parseOptions args {} with
    | .ok opts => pure opts
    | .error e => do
        IO.eprintln e
        return 1
  if opts.list then
    try
      let cwd ← IO.currentDir
      let paths ← if opts.paths.isEmpty then defaultPaths cwd else pure opts.paths
      let tests ← discoverTests cwd paths
      for test in tests do
        IO.println test.label
      return (0 : UInt32)
    catch e =>
      IO.eprintln s!"testsuite: {e}"
      return (1 : UInt32)
  let some mica := opts.mica
    | do
        IO.eprintln usage
        return 1
  if !(← mica.pathExists) then
    IO.eprintln s!"mica executable not found at {mica}; run `lake build` first"
    return 1
  try
    run mica opts
  catch e =>
    IO.eprintln s!"testsuite: {e}"
    return (1 : UInt32)
