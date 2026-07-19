-- SUMMARY: Progress lines, captured-output blocks, and the final summary.
import Testsuite.Task

namespace Testsuite

private def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"

def printOutputBlock (output : String) : IO Unit := do
  unless output.isEmpty do
    IO.print output
    unless output.endsWith "\n" do IO.println ""

/-- Status suffix for the progress line: ✓/⨯ with timing, or the timeout notice. -/
def Outcome.status (outcome : Outcome) : String :=
  match outcome.result with
  | .timeout ms => s!" timed out after {ms}ms"
  | .terminated out =>
      s!" {if out.exitCode == 0 then "✓" else "⨯"} ({outcome.elapsedMs}ms)"

/-- Print the progress line for an outcome followed by its captured output. -/
def report (verb : String) (outcome : Outcome) : IO Unit := do
  IO.println s!"{verb} {outcome.label} ...{outcome.status}"
  if let .terminated out := outcome.result then
    printOutputBlock out.stdout
    printOutputBlock out.stderr
    if !out.stdout.isEmpty || !out.stderr.isEmpty then
      IO.println ""

/-- How a failed outcome appears in the summary. -/
def failureLabel (outcome : Outcome) : String :=
  match outcome.result with
  | .timeout _ => s!"{outcome.label} (timed out)"
  | .terminated _ => outcome.label

/-- Print the final summary; the exit code is 1 iff there are failures. -/
def summary (failed : List String) : IO UInt32 := do
  IO.println ""
  if failed.isEmpty then
    IO.println (bold "all tests passed")
    return 0
  IO.println (bold s!"{failed.length} {if failed.length == 1 then "test" else "tests"} failed")
  for label in failed do
    IO.println s!"- {label}"
  return 1

end Testsuite
