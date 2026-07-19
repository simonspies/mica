import Testsuite.Process
import Testsuite.Test
import Testsuite.Task
import Testsuite.Report

/-!
# Testsuite runner

Standalone driver for the mica test corpus, invoked via `lake run testsuite`.
The unit of work is a *task*, written `task,file` where task is one of
`compile` (ocamlopt), `check` (run mica, compare against an optional expected
`.out` file), `roundtrip` (print∘parse fixpoint of `--print-ocaml`). The test
format itself (directive and `.out` expectations) is documented in
`Testsuite/Test.lean`.

Subcommands:

* `run [PATH ...]` — discover tests under the given paths (default:
  `Examples/` and `Tests/`) and run their tasks sequentially with a final
  summary.
* `list [PATH ...]` — print the discovered tasks as `task,file` lines.
* `run-task TASK,FILE ...` — run the given tasks; used by the lake script,
  which registers one Lake job per task so the build monitor shows live
  progress, and hands the failed tasks to `summarize`.
* `summarize [TASK,FILE ...]` — print the final summary for failed tasks.
-/

open System (FilePath)

namespace Testsuite

def usage : String :=
  "usage: testsuite run [--mica PATH] [--promote] [PATH ...]\n" ++
  "       testsuite list [PATH ...]\n" ++
  "       testsuite run-task [--mica PATH] [--promote] TASK,FILE ...\n" ++
  "       testsuite summarize [TASK,FILE ...]"

/-- Options shared by the `run` and `run-task` subcommands. -/
structure RunOptions where
  mica : Option FilePath := none
  promote : Bool := false
  args : Array String := #[]

def parseRunOptions : List String → RunOptions → Except String RunOptions
  | [], opts => .ok opts
  | "--promote" :: rest, opts => parseRunOptions rest { opts with promote := true }
  | "--mica" :: path :: rest, opts => parseRunOptions rest { opts with mica := some path }
  | ["--mica"], _ => .error s!"--mica requires a path\n{usage}"
  | arg :: rest, opts =>
    if arg.startsWith "-" then .error s!"unknown option '{arg}'\n{usage}"
    else parseRunOptions rest { opts with args := opts.args.push arg }

def rejectFlags (cmd : String) (args : List String) : Except String (Array String) :=
  match args.find? (·.startsWith "-") with
  | some flag => .error s!"unknown option '{flag}' for '{cmd}'\n{usage}"
  | none => .ok args.toArray

def resolveMica (mica? : Option FilePath) : IO FilePath := do
  let mica := mica?.getD (FilePath.mk ".lake" / "build" / "bin" / "mica")
  if !(← mica.pathExists) then
    throw <| IO.userError s!"mica executable not found at {mica}; run `lake build` first"
  pure mica

/-- Parse a `task,file` spec into a task against the working directory. -/
def parseSpec (cwd : FilePath) (spec : String) : IO (TaskKind × Test) := do
  let kindStr := (spec.takeWhile (· != ',')).toString
  let file := (spec.drop (kindStr.length + 1)).toString
  let some kind := TaskKind.parse kindStr
    | throw <| IO.userError s!"unknown task '{kindStr}' in '{spec}'"
  let path := FilePath.mk file
  let inputPath := if path.isAbsolute then path else cwd / path
  if !(← inputPath.pathExists) then
    throw <| IO.userError s!"test file does not exist: {inputPath}"
  let test ← loadTest cwd inputPath
  return (kind, test)

/-- Execute tasks in order. The stdlib stub (`mica.ml`) is compiled first
    whenever a compile task is present; if it fails, the per-test compiles
    are skipped. In standalone mode (`run`) the stub compile is always
    reported, kind changes are separated by blank lines, and a summary is
    printed; in `run-task` mode the stub compile is reported only on failure
    and the exit code carries the verdict. -/
def runTasks (mica : FilePath) (promote : Bool) (standalone : Bool)
    (tasks : Array (TaskKind × Test)) : IO UInt32 := do
  let cwd ← IO.currentDir
  IO.FS.withTempDir fun tmpDir => do
    let mut tasks := tasks
    let mut failed : List (TaskKind × Outcome) := []
    let mut prev? : Option TaskKind := none
    if tasks.any (·.1 == .compile) then
      let stdlib ← compileStdlib cwd tmpDir
      if stdlib.result.failed then
        -- Without the stdlib stub, compiling a test cannot succeed.
        tasks := tasks.filter (·.1 != .compile)
        failed := [(.compile, stdlib)]
      if standalone || stdlib.result.failed then
        report TaskKind.compile.verb stdlib
        prev? := some .compile
    let mut idx := 0
    for task in tasks do
      if standalone && prev?.any (· != task.1) then
        IO.println ""
      prev? := some task.1
      let outcome ← perform mica promote tmpDir idx task
      report task.1.verb outcome
      if outcome.result.failed then
        failed := (task.1, outcome) :: failed
      idx := idx + 1
    if standalone then
      summary (failed.reverse.map fun (kind, outcome) => failureLabel kind outcome)
    else
      pure (if failed.isEmpty then (0 : UInt32) else 1)

def runCommand (opts : RunOptions) : IO UInt32 := do
  let mica ← resolveMica opts.mica
  let cwd ← IO.currentDir
  let paths := opts.args.map FilePath.mk
  let paths ← if paths.isEmpty then defaultPaths cwd else pure paths
  let tests ← discoverTests cwd paths
  runTasks mica opts.promote (standalone := true) (plan tests)

def runTaskCommand (opts : RunOptions) : IO UInt32 := do
  if opts.args.isEmpty then
    throw <| IO.userError s!"run-task requires TASK,FILE arguments\n{usage}"
  let mica ← resolveMica opts.mica
  let cwd ← IO.currentDir
  let tasks ← opts.args.mapM (parseSpec cwd)
  runTasks mica opts.promote (standalone := false) tasks

def listCommand (pathArgs : Array String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let paths := pathArgs.map FilePath.mk
  let paths ← if paths.isEmpty then defaultPaths cwd else pure paths
  let tests ← discoverTests cwd paths
  for (kind, test) in plan tests do
    IO.println s!"{kind.name},{test.label}"
  return 0

def summarizeCommand (specs : Array String) : IO UInt32 :=
  summary (specs.map (·.replace "," " ")).toList

def dispatch : List String → IO UInt32
  | "run" :: rest => do runCommand (← IO.ofExcept (parseRunOptions rest {}))
  | "run-task" :: rest => do runTaskCommand (← IO.ofExcept (parseRunOptions rest {}))
  | "list" :: rest => do listCommand (← IO.ofExcept (rejectFlags "list" rest))
  | "summarize" :: rest => do summarizeCommand (← IO.ofExcept (rejectFlags "summarize" rest))
  | _ => do
      IO.eprintln usage
      return 1

end Testsuite

def main (args : List String) : IO UInt32 := do
  try
    Testsuite.dispatch args
  catch e =>
    IO.eprintln s!"testsuite: {e}"
    return (1 : UInt32)
