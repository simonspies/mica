-- SUMMARY: Run external processes with a timeout, capturing output and wall-clock time.

open System (FilePath)

namespace Testsuite

/-- Result of running an external process under the testsuite timeout. -/
inductive ProcessResult where
  | timeout (ms : UInt32)
  | terminated (output : IO.Process.Output)

/-- `true` if the result counts as a failure. -/
def ProcessResult.failed : ProcessResult → Bool
  | .timeout _ => true
  | .terminated out => out.exitCode != 0

def timeoutMs : UInt32 := 300000

def pollIntervalMs : UInt32 := 300

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

/-- Run `cmd` with `args` (in `cwd?` if given), killing it after `timeoutMs`. -/
def runProcess (cmd : String) (args : Array String) (cwd? : Option FilePath := none) :
    IO ProcessResult := do
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
  match ← waitForExitOrTimeout child timeoutMs.toNat with
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

/-- A finished run: its label, process result, and wall-clock time. -/
structure Outcome where
  label : String
  result : ProcessResult
  elapsedMs : Nat

def measure (label : String) (action : IO ProcessResult) : IO Outcome := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  return { label, result, elapsedMs := stop - start }

end Testsuite
