-- SUMMARY: The per-test tasks (compile, check, roundtrip) and their execution.
import Testsuite.Process
import Testsuite.Test

open System (FilePath)

namespace Testsuite

/-- The kinds of per-test work the runner executes. -/
inductive TaskKind where
  | compile
  | check
  | roundtrip
deriving BEq

def TaskKind.name : TaskKind → String
  | .compile => "compile"
  | .check => "check"
  | .roundtrip => "roundtrip"

def TaskKind.verb : TaskKind → String
  | .compile => "Compiling"
  | .check => "Checking"
  | .roundtrip => "Roundtrip"

def TaskKind.parse : String → Option TaskKind
  | "compile" => some .compile
  | "check" => some .check
  | "roundtrip" => some .roundtrip
  | _ => none

/-- Expand tests into the phase-grouped list of tasks to run. -/
def plan (tests : Array Test) : Array (TaskKind × Test) :=
  (tests.filter (!·.config.noCompile)).map ((TaskKind.compile, ·))
    ++ tests.map ((TaskKind.check, ·))
    ++ (tests.filter (·.config.roundtrip)).map ((TaskKind.roundtrip, ·))

def ocamlopt (args : Array String) (cwd : FilePath) : IO ProcessResult := do
  try
    runProcess "ocamlopt" args (some cwd)
  catch e =>
    pure (.terminated {
      exitCode := 127
      stdout := ""
      stderr := s!"failed to run ocamlopt: {e}\n"
    })

/-- Compile the stdlib stub `mica.ml`, which the per-test compiles link against. -/
def compileStdlib (cwd tmpDir : FilePath) : IO Outcome := do
  let path := cwd / "mica.ml"
  measure (relativeLabel cwd path) <|
    ocamlopt #["-c", path.toString, "-o", "mica.cmx"] tmpDir

def compile (tmpDir : FilePath) (idx : Nat) (test : Test) : IO Outcome := do
  let out := tmpDir / s!"example_{idx}.cmx"
  measure test.label <|
    ocamlopt #["-I", tmpDir.toString, "-c", test.path.toString, "-o", out.toString] tmpDir

def ensureNewline (s : String) : String :=
  if s.isEmpty || s.endsWith "\n" then s else s ++ "\n"

/-- The text an expected `.out` file is compared against: stdout then stderr,
    followed by a `[<code>]` line for nonzero exits. Mica is always invoked
    with `--no-ansi`, so the captured output is plain text. -/
def renderActual (out : IO.Process.Output) : String :=
  let base := ensureNewline out.stdout ++ ensureNewline out.stderr
  if out.exitCode == 0 then base else base ++ s!"[{out.exitCode}]\n"

def diff (tmpDir : FilePath) (tag : String) (expected actual : String) : IO String := do
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

/-- Run mica on the test. Without an expected `.out` file the run must exit 0;
    with one, the rendered output must match it (or is rewritten under
    `promote`). Success is silent either way. -/
def check (mica : FilePath) (promote : Bool) (tmpDir : FilePath) (idx : Nat) (test : Test) :
    IO Outcome := do
  -- Pass the cwd-relative path so file positions in expected output stay portable.
  let outcome ← measure test.label <|
    runProcess mica.toString (#["--no-ansi"] ++ test.config.flags ++ #[test.label])
  let .terminated out := outcome.result
    | return outcome
  let some expectedPath := test.expected
    | if out.exitCode == 0 then
        return { outcome with result := .terminated { out with stdout := "", stderr := "" } }
      else
        return outcome
  let actual := renderActual out
  let expected ← IO.FS.readFile expectedPath
  if actual == expected then
    return { outcome with result := .terminated { exitCode := 0, stdout := "", stderr := "" } }
  else if promote then
    IO.FS.writeFile expectedPath actual
    let note := s!"promoted {expectedPath.fileName.getD expectedPath.toString}\n"
    return { outcome with result := .terminated { exitCode := 0, stdout := note, stderr := "" } }
  else
    let d ← diff tmpDir s!"check_{idx}" expected actual
    return { outcome with result := .terminated { exitCode := 1, stdout := d, stderr := "" } }

/-- Check that `--print-ocaml` output reparses to the same print (fixpoint). -/
def roundtrip (mica : FilePath) (tmpDir : FilePath) (idx : Nat) (test : Test) :
    IO Outcome := do
  measure test.label do
    let args := fun (file : FilePath) =>
      #["--no-ansi", "--print-ocaml", "--no-check", file.toString]
    let r1 ← runProcess mica.toString (args test.path)
    let .terminated out1 := r1
      | return r1
    if out1.exitCode != 0 then
      return .terminated { out1 with stdout := "roundtrip: initial print failed\n" ++ out1.stdout }
    let reprinted := tmpDir / s!"roundtrip_{idx}.ml"
    IO.FS.writeFile reprinted out1.stdout
    let r2 ← runProcess mica.toString (args reprinted)
    let .terminated out2 := r2
      | return r2
    if out2.exitCode != 0 then
      return .terminated
        { out2 with stdout := "roundtrip: reparse of printed output failed\n" ++ out2.stdout }
    if out2.stdout == out1.stdout then
      return .terminated { exitCode := 0, stdout := "", stderr := "" }
    else
      let d ← diff tmpDir s!"roundtrip_{idx}" out1.stdout out2.stdout
      return .terminated { exitCode := 1, stdout := "roundtrip: print is not a fixpoint\n" ++ d, stderr := "" }

/-- Dispatch one task. -/
def perform (mica : FilePath) (promote : Bool) (tmpDir : FilePath) (idx : Nat) :
    TaskKind × Test → IO Outcome
  | (.compile, test) => compile tmpDir idx test
  | (.check, test) => check mica promote tmpDir idx test
  | (.roundtrip, test) => roundtrip mica tmpDir idx test

end Testsuite
