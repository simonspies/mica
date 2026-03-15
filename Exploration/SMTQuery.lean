/-
  Experiment: calling Z3 from Lean via SMT-LIB2.

  Constructs SMT-LIB2 formulas as strings and invokes Z3 as a subprocess.
  This demonstrates using an external SMT solver for reasoning that Lean's
  built-in tactics don't handle well (e.g., bit vectors, nonlinear arithmetic).

  Supports both one-shot queries (runZ3) and interactive sessions (SmtSession)
  with push/pop for incremental solving.

  No certificate reconstruction — we trust the solver's answer.
-/

/-- An SMT-LIB2 sort. -/
inductive SmtSort
  | bool
  | int
  | bitVec (width : Nat)

/-- An SMT-LIB2 expression. -/
inductive SmtExpr
  | const (name : String)
  | litInt (n : Int)
  | litBV (val : Nat) (width : Nat)
  | litBool (b : Bool)
  | app (op : String) (args : List SmtExpr)
  | not (e : SmtExpr)
  | and (a b : SmtExpr)
  | or (a b : SmtExpr)
  | eq (a b : SmtExpr)
  | ite (c t e : SmtExpr)

/-- A declared constant with its sort. -/
structure SmtDecl where
  name : String
  sort : SmtSort

/-- An SMT query: declarations + assertions, check satisfiability. -/
structure SmtQuery where
  decls : List SmtDecl
  asserts : List SmtExpr

namespace SmtSort

def toSMTLIB : SmtSort → String
  | .bool => "Bool"
  | .int => "Int"
  | .bitVec w => s!"(_ BitVec {w})"

end SmtSort

namespace SmtExpr

partial def toSMTLIB : SmtExpr → String
  | .const name => name
  | .litInt n => if n ≥ 0 then s!"{n}" else s!"(- {-n})"
  | .litBV val width => s!"(_ bv{val} {width})"
  | .litBool true => "true"
  | .litBool false => "false"
  | .app op args => s!"({op} {" ".intercalate (args.map toSMTLIB)})"
  | .not e => s!"(not {e.toSMTLIB})"
  | .and a b => s!"(and {a.toSMTLIB} {b.toSMTLIB})"
  | .or a b => s!"(or {a.toSMTLIB} {b.toSMTLIB})"
  | .eq a b => s!"(= {a.toSMTLIB} {b.toSMTLIB})"
  | .ite c t e => s!"(ite {c.toSMTLIB} {t.toSMTLIB} {e.toSMTLIB})"

end SmtExpr

namespace SmtQuery

def toSMTLIB (q : SmtQuery) : String :=
  let header := "(set-logic ALL)\n"
  let decls := q.decls.map fun d =>
    s!"(declare-const {d.name} {d.sort.toSMTLIB})\n"
  let asserts := q.asserts.map fun e =>
    s!"(assert {e.toSMTLIB})\n"
  let footer := "(check-sat)\n"
  header ++ String.join decls ++ String.join asserts ++ footer

end SmtQuery

inductive SmtResult
  | sat
  | unsat
  | unknown (output : String)
  | error (msg : String)

deriving instance BEq for SmtResult

instance : ToString SmtResult where
  toString
    | .sat => "sat"
    | .unsat => "unsat"
    | .unknown s => s!"unknown: {s}"
    | .error s => s!"error: {s}"

def runZ3 (query : SmtQuery) (z3Path : String := "z3") : IO SmtResult := do
  let smtlib := query.toSMTLIB
  let child ← IO.Process.spawn {
    cmd := z3Path
    args := #["-in"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.putStr smtlib
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let stdout ← child.stdout.readToEnd
  let _ ← child.wait
  let output := stdout.trimAscii.toString
  if output == "sat" then return .sat
  else if output == "unsat" then return .unsat
  else return .unknown output

/-- A persistent Z3 session. Keeps the subprocess alive for incremental queries. -/
structure SmtSession where
  stdin  : IO.FS.Handle
  stdout : IO.FS.Handle
  child  : IO.Process.Child ⟨.null, .piped, .piped⟩

namespace SmtSession

/-- Start a new Z3 session. -/
def create (z3Path : String := "z3") : IO SmtSession := do
  let child ← IO.Process.spawn {
    cmd := z3Path
    args := #["-in"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stdin := child.stdin
  let (_, child) ← child.takeStdin
  stdin.putStr "(set-logic ALL)\n"
  stdin.flush
  return { stdin, stdout := child.stdout, child }

/-- Send a raw SMT-LIB2 command (no response expected). -/
def command (s : SmtSession) (cmd : String) : IO Unit := do
  s.stdin.putStr cmd
  s.stdin.putStr "\n"
  s.stdin.flush

/-- Declare a constant. -/
def declare (s : SmtSession) (name : String) (sort : SmtSort) : IO Unit :=
  s.command s!"(declare-const {name} {sort.toSMTLIB})"

/-- Assert a formula. -/
def assert (s : SmtSession) (e : SmtExpr) : IO Unit :=
  s.command s!"(assert {e.toSMTLIB})"

/-- Push a scope. -/
def push (s : SmtSession) : IO Unit := s.command "(push)"

/-- Pop a scope. -/
def pop (s : SmtSession) : IO Unit := s.command "(pop)"

/-- Check satisfiability and read the result. -/
def checkSat (s : SmtSession) : IO SmtResult := do
  s.command "(check-sat)"
  let line ← s.stdout.getLine
  let output := line.trimAscii.toString
  if output == "sat" then return .sat
  else if output == "unsat" then return .unsat
  else return .unknown output

/-- Close the session. -/
def close (s : SmtSession) : IO Unit := do
  s.command "(exit)"

end SmtSession

def main : IO Unit := do
  let s ← SmtSession.create
  -- n is the candidate square root, x = n * n is the perfect square
  s.declare "n" .int
  s.declare "x" .int
  s.assert (.eq (.const "x") (.app "*" [.const "n", .const "n"]))
  s.assert (.app ">=" [.const "n", .litInt 0])

  IO.println "Perfect square finder (backed by Z3)"
  IO.println "Enter lower and upper bounds, or 'q' to quit."
  IO.println ""

  let stdin ← IO.getStdin
  repeat do
    IO.print "Lower bound A: "
    let lineA ← stdin.getLine
    let lineA := lineA.trimAscii.toString
    if lineA == "q" then break
    IO.print "Upper bound B: "
    let lineB ← stdin.getLine
    let lineB := lineB.trimAscii.toString
    if lineB == "q" then break

    match lineA.toInt?, lineB.toInt? with
    | some a, some b =>
      s.push
      s.assert (.app ">=" [.const "x", .litInt a])
      s.assert (.app "<=" [.const "x", .litInt b])
      let r ← s.checkSat
      match r with
      | .sat => IO.println s!"sat: there is a perfect square in [{a}, {b}]"
      | .unsat => IO.println s!"unsat: no perfect square in [{a}, {b}]"
      | other => IO.println s!"Z3 says: {other}"
      s.pop
    | _, _ => IO.println "Invalid input, please enter integers."
    IO.println ""

  s.close
