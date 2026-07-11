-- SUMMARY: Execution of SMT strategies against a live Z3 process.
import Mica.Engine.Strategy

/-! ## Smt.Session (Z3 session) -/

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

-- `(set-option :smt.qi.eager_threshold 5.0)` Recursive functions are encoded
-- as quantified definitional axioms whose bodies reference the function again.
-- Z3's default eager instantiation easily falls into a matching loop. It even
-- does so _before_ a check-sat is reached when entering a new scope.
-- To avoid a severe performance penalty, we lower the default from 10.0 to 5.0.
def preamble : String := s!"
;; preamble
(set-logic ALL)
{String.intercalate "\n" (List.map Options.Settable.toSMTLIB Options.Settable.initial)}
(set-option :smt.qi.eager_threshold 5.0)

(declare-sort Other 0)
(declare-sort Loc 0)
(declare-sort Vec 0)
(declare-datatypes ((Value 0) (ValueList 0)) (
  ((of_int (to_int Int))
   (of_bool (to_bool Bool))
   (of_char (to_char (_ BitVec 8)))
   (of_string (to_string (Seq (_ BitVec 8))))
   (of_float (to_float (_ FloatingPoint 11 53)))
   (of_loc (to_loc Loc))
   (of_other (to_other Other))
   (of_tuple (to_tuple ValueList))
   (of_vec (to_vec Vec))
   (of_inj (tag_of Int) (arity_of Int) (payload_of Value)))
  ((vnil)
   (vcons (vhd Value) (vtl ValueList)))
))
(declare-const unit_val Other)

;; A `Value` constructor would need to expose both length and location
(declare-fun array_length (Value) Int)

;; Vector theory. Vectors are exposed as arrays to Z3, and via
;; the uninterpreted functions vec_get, ... to Mica
(declare-fun vec_to_array (Vec) (Array Int Value))
(declare-fun vec_of_array ((Array Int Value) Int) Vec)
(declare-fun vec_length (Vec) Int)
(assert (forall ((w Vec)) (! (<= 0 (vec_length w)) :pattern ((vec_length w)))))

(assert (forall ((w Vec))
  (! (= (vec_of_array (vec_to_array w) (vec_length w)) w)
     :pattern ((vec_to_array w)))))
(assert (forall ((a (Array Int Value)) (n Int))
  (! (=> (<= 0 n) (= (vec_length (vec_of_array a n)) n))
     :pattern ((vec_of_array a n)))))
(assert (forall ((a (Array Int Value)) (n Int) (i Int))
  (! (=> (and (<= 0 i) (< i n))
         (= (select (vec_to_array (vec_of_array a n)) i) (select a i)))
     :pattern ((select (vec_to_array (vec_of_array a n)) i)))))

(declare-fun vec_get (Vec Int) Value)
(declare-fun vec_set (Vec Int Value) Vec)
(declare-fun vec_make (Int Value) Vec)
(assert (forall ((w Vec) (i Int))
  (! (=> (and (<= 0 i) (< i (vec_length w)))
         (= (vec_get w i) (select (vec_to_array w) i)))
     :pattern ((vec_get w i)))))
(assert (forall ((w Vec) (i Int) (x Value))
  (! (=> (and (<= 0 i) (< i (vec_length w)))
         (= (vec_set w i x)
            (vec_of_array (store (vec_to_array w) i x) (vec_length w))))
     :pattern ((vec_set w i x)))))
(assert (forall ((n Int) (x Value))
  (! (=> (<= 0 n)
         (= (vec_make n x) (vec_of_array ((as const (Array Int Value)) x) n)))
     :pattern ((vec_make n x)))))

;; verification
"

/-- Start a new Z3 session with print-success enabled. -/
def create (z3Path : String := "z3") (log : LogMode := .quiet) : IO Session := do
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
  if log == .script then do
    IO.println "(set-option :print-success true)"
    IO.print preamble
  -- Then we turn on interactive mode, and from here on parse the responses
  stdin.putStr "(set-option :print-success true)\n"
  stdin.flush
  let response ← child.stdout.getLine
  let response := response.trimAscii.toString
  if response != "success" then
    throw (IO.userError s!"Z3 init failed on set-option: {response}")
  return { stdin, stdout := child.stdout, child }

/-- Send a command and parse the response. Throws on unexpected output. -/
def send (s : Session) (cmd : Command α) (log : LogMode := .quiet) : IO α := do
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

/-- Close the session. -/
def close (s : Session) : IO Unit := do
  s.stdin.putStr "(exit)\n"
  s.stdin.flush

end Session

/-! ## Running Strategies -/

namespace Strategy

/-- Execute a strategy against a live Z3 session. -/
def run (log : LogMode := .quiet) : Strategy α → Session → IO α
  | .done a, _ => return a
  | .exec cmd k, session => do
    let response ← session.send cmd log
    run log (k response) session

/-- Top-level entry point: create session, run strategy, print result, close. -/
def execute (s : Strategy Outcome) (log : LogMode := .quiet) : IO Unit := do
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
