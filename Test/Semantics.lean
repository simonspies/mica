import Mica.Verifier.Monad
import Mica.Engine.Driver

/-! ## Semantic agreement tests

Checks that Lean's evaluation of FOL operations agrees with Z3's.
For each operation and test input, we use `VerifM.check` to ask Z3
whether `op(a, b) = lean_result`. -/

structure IntBinOpTest where
  name : String
  op   : BinOp .int .int .int
  cases : List (Int × Int)

def intBinOpTests : List IntBinOpTest := [
  { name := "add", op := .add,
    cases := [(0, 0), (1, 0), (0, 1), (3, 5), (-3, 5), (3, -5), (-3, -5)] },
  { name := "sub", op := .sub,
    cases := [(0, 0), (1, 0), (0, 1), (3, 5), (-3, 5), (3, -5), (-3, -5)] },
  { name := "mul", op := .mul,
    cases := [(0, 0), (1, 0), (0, 1), (3, 5), (-3, 5), (3, -5), (-3, -5)] },
  { name := "div", op := .div,
    cases := [(7, 3), (7, -3), (-7, 3), (-7, -3),
              (0, 3), (0, -3), (6, 3), (6, -3), (-6, 3), (-6, -3),
              (1, 1), (-1, 1), (1, -1), (-1, -1),
              (1, 0), (-1, 0), (0, 0)] },
  { name := "mod", op := .mod,
    cases := [(7, 3), (7, -3), (-7, 3), (-7, -3),
              (0, 3), (0, -3), (6, 3), (6, -3), (-6, 3), (-6, -3),
              (1, 1), (-1, 1), (1, -1), (-1, -1),
              (1, 0), (-1, 0), (0, 0)] }
]

/-- Check a single int binary op case. -/
def checkIntBinOp (name : String) (op : BinOp .int .int .int) (a b : Int)
    : VerifM (String × Bool) := do
  let lhs := Term.binop op (.const (.i a)) (.const (.i b))
  let rhs : Term .int := .const (.i (op.eval a b))
  let ok ← VerifM.check (Formula.eq .int lhs rhs)
  return (s!"{name}({a}, {b})", ok)

/-- Build all tests, collecting (label, passed) pairs. The results are
    accumulated via `VerifM.assume` of a dummy formula so that `VerifM`
    stays in `Unit`-land for `strategy`. We print results in `IO` by
    running each test individually. -/

def runTest (session : SmtSession) (_name : String) (op : BinOp .int .int .int)
    (a b : Int) : IO Bool := do
  let lhs := Term.binop op (.const (.i a)) (.const (.i b))
  let rhs : Term .int := .const (.i (op.eval a b))
  let m : VerifM Unit := do
    let ok ← VerifM.check (Formula.eq .int lhs rhs)
    if !ok then VerifM.failed "disagree"
  let strategy := VerifM.strategy m
  let outcome ← run (log := false) strategy session
  match outcome with
  | Except.ok () => return true
  | Except.error _ => return false

def main : IO Unit := do
  let session ← SmtSession.create
  let mut anyFail := false
  for test in intBinOpTests do
    for (a, b) in test.cases do
      let ok ← runTest session test.name test.op a b
      let mark := if ok then "✓" else "✗"
      IO.println s!"{mark} {test.name}({a}, {b})"
      if !ok then anyFail := true
  session.close
  if anyFail then
    IO.Process.exit 1
