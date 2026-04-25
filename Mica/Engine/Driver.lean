-- SUMMARY: Execution of SMT strategies against a live Z3 process.
import Mica.Engine.Strategy

/-! ## Smt.Session (Z3 session) -/

namespace Smt

/-- A persistent Z3 session. Keeps the subprocess alive for incremental queries. -/
structure Session where
  stdin  : IO.FS.Handle
  stdout : IO.FS.Handle
  child  : IO.Process.Child ⟨.piped, .piped, .piped⟩

namespace Session

def preamble : String := s!"
;; preamble
(set-logic ALL)

(declare-sort Other 0)
(declare-sort Loc 0)
(declare-datatypes ((Value 0) (ValueList 0)) (
  ((of_int (to_int Int))
   (of_bool (to_bool Bool))
   (of_loc (to_loc Loc))
   (of_other (to_other Other))
   (of_tuple (to_tuple ValueList))
   (of_inj (tag_of Int) (arity_of Int) (payload_of Value)))
  ((vnil)
   (vcons (vhd Value) (vtl ValueList)))
))
(declare-const unit_val Other)

;; verification
"

/-- Start a new Z3 session with print-success enabled. -/
def create (z3Path : String := "z3") (log : Bool := false) : IO Session := do
  let child ← IO.Process.spawn {
    cmd := z3Path
    args := #["-in"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stdin := child.stdin
  -- We first define the preamble that introduces the value type
  stdin.putStr preamble
  stdin.flush
  if log then
    IO.println preamble
  -- Then we turn on interactive mode, and from here on parse the responses
  stdin.putStr "(set-option :print-success true)\n"
  stdin.flush
  let response ← child.stdout.getLine
  let response := response.trimAscii.toString
  if response != "success" then
    throw (IO.userError s!"Z3 init failed on set-option: {response}")
  return { stdin, stdout := child.stdout, child }

/-- Send a command and parse the response. Throws on unexpected output. -/
def send (s : Session) (cmd : Command α) (log : Bool := false) : IO α := do
  let query := cmd.toSMTLIB
  if log then IO.eprintln s!"  > {query}"
  s.stdin.putStr (query ++ "\n")
  s.stdin.flush
  let line ← s.stdout.getLine
  let response := line.trimAscii.toString
  if log then IO.eprintln s!"  < {response}"
  match cmd.parse response with
  | some r => return r
  | none => throw (IO.userError s!"Unexpected Z3 response for `{query}`: {response}")

/-- Close the session. -/
def close (s : Session) : IO Unit := do
  s.stdin.putStr "(exit)\n"
  s.stdin.flush

end Session

/-! ## Running Strategies -/

namespace Strategy

/-- Execute a strategy against a live Z3 session. -/
def run (log : Bool := false) : Strategy α → Session → IO α
  | .done a, _ => return a
  | .exec cmd k, session => do
    let response ← session.send cmd log
    run log (k response) session

/-- Top-level entry point: create session, run strategy, print result, close. -/
def execute (s : Strategy Outcome) (log : Bool := false) : IO Unit := do
  let session ← Session.create "z3" log
  let outcome ← run log s session
  session.close
  match outcome with
  | .ok () => IO.println "Successfully verified!"
  | .error msg => do
    IO.println "Verification failed. The following error was encountered."
    IO.println msg

end Strategy

end Smt
