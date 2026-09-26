-- SUMMARY: Execution of SMT strategies against a live Z3 process.
import Mica.Engine.Strategy

/-! ## Session -/

namespace Smt

/-- How a session reports the commands it issues.
    - `quiet`: no output.
    - `trace`: `> command` / `< response` pairs on stderr (verbose debugging).
    - `script`: a replayable SMT-LIB script on stdout -/
inductive LogMode where
  | quiet
  | trace
  | script
  deriving BEq

/-- A persistent Z3 session. Keeps the subprocess alive for incremental queries. -/
structure Session where
  stdin  : IO.FS.Handle
  stdout : IO.FS.Handle
  child  : IO.Process.Child ⟨.piped, .piped, .piped⟩

namespace Session

/-- The SMT-LIB text every session starts with: the logic, the solver options,
    `SMTLIB.declarations`, and `SMTLIB.defaults`. -/
def preamble (timeout : Nat) : String := s!"
;; preamble
(set-logic ALL)
{String.intercalate "\n" (List.map Options.Settable.toSMTLIB (Options.Settable.initial timeout))}

{SMTLIB.declarations}
{String.intercalate "\n" (SMTLIB.defaults.map fun φ => (Command.assert φ).toSMTLIB)}

;; verification
"

/-- Start a new Z3 session with print-success enabled. -/
def create (log : LogMode) (timeout : Nat) : IO Session := do
  let child ← IO.Process.spawn {
    cmd := "z3"
    args := #["-in"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stdin := child.stdin
  stdin.putStr (preamble timeout)
  stdin.flush
  if log == .script then do
    IO.println "(set-option :print-success true)"
    IO.print (preamble timeout)
  -- Then we turn on interactive mode, and from here on parse the responses
  stdin.putStr "(set-option :print-success true)\n"
  stdin.flush
  let response ← child.stdout.getLine
  let response := response.trimAscii.toString
  if response != "success" then
    throw (IO.userError s!"Z3 init failed on set-option: {response}")
  return { stdin, stdout := child.stdout, child }

/-- Send a command and parse the response. Throws on unexpected output. -/
def send (s : Session) (cmd : Command α) (log : LogMode) : IO α := do
  let query := cmd.toSMTLIB
  match log with
  | .trace => IO.eprintln s!"  > {query}"
  | .script => IO.println query
  | .quiet => pure ()
  s.stdin.putStr (query ++ "\n")
  s.stdin.flush
  let line ← s.stdout.getLine
  let response := line.trimAscii.toString
  if log == .trace then IO.eprintln s!"  < {response}"
  match cmd.parse response with
  | some r => return r
  | none => throw (IO.userError s!"Unexpected Z3 response for `{query}`: {response}")

def close (s : Session) : IO Unit := do
  s.stdin.putStr "(exit)\n"
  s.stdin.flush
  -- The exit code carries no information after `(exit)`.
  discard s.child.wait

end Session

/-! ## Strategy.run and Strategy.execute -/

namespace Strategy

/-- Execute a strategy against a live Z3 session. -/
private def run (log : LogMode) : Strategy α → Session → IO α
  | .done a, _ => return a
  | .exec cmd k, session => do
    let response ← session.send cmd log
    run log (k response) session

/-- Run a strategy in a session of its own. Reporting the outcome is the
    caller's job. -/
def execute (s : Strategy α) (log : LogMode) (timeout : Nat) : IO α := do
  let session ← Session.create log timeout
  let result ← run log s session
  session.close
  return result

end Strategy

end Smt
