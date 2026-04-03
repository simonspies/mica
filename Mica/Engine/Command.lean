import Mica.Engine.State

/-! ## Smt.Command

An SMT command, indexed by its response type -- Unit for no meaningful response
- push, pop, assert: Unit
- declareConst, declareUnary, declareBinary : Unit
- checkSat: returns sat/unsat/unknown — Smt.Result -/

namespace Smt

inductive Command : Type → Type where
  | push : Command Unit
  | pop : Command Unit
  | declareConst (name : String) (sort : Srt) : Command Unit
  | declareUnary (name : String) (arg ret : Srt) : Command Unit
  | declareBinary (name : String) (arg1 arg2 ret : Srt) : Command Unit
  | assert (expr : Formula) : Command Unit
  | checkSat : Command Result

/-! ## Serialization -/

namespace Command

/-- Serialize a command to its SMT-LIB2 string. -/
def toSMTLIB : Command α → String
  | .push => "(push)"
  | .pop => "(pop)"
  | .declareConst n s => s!"(declare-const {n} {s.toSMTLIB})"
  | .declareUnary n a r => s!"(declare-fun {n} ({a.toSMTLIB}) {r.toSMTLIB})"
  | .declareBinary n a1 a2 r => s!"(declare-fun {n} ({a1.toSMTLIB} {a2.toSMTLIB}) {r.toSMTLIB})"
  | .assert e => s!"(assert {e.toSMTLIB})"
  | .checkSat => "(check-sat)"

/-- Parse the solver's response string for a given command. Returns `none` on unexpected output. -/
def parse : (cmd : Command α) → String → Option α
  | .push, s => if s == "success" then some () else none
  | .pop, s => if s == "success" then some () else none
  | .declareConst _ _, s => if s == "success" then some () else none
  | .declareUnary _ _ _, s => if s == "success" then some () else none
  | .declareBinary _ _ _ _, s => if s == "success" then some () else none
  | .assert _, s => if s == "success" then some () else none
  | .checkSat, s =>
    if s == "sat" then some .sat
    else if s == "unsat" then some .unsat
    else if s == "unknown" then some .unknown
    else none

end Command

/-! ## Smt.State.step -/

namespace State

/-- Advance the state by one command. -/
def step : Command β → β → State → State
  | .push, (), s => s.push
  | .pop, (), s => s.pop
  | .declareConst n sort, (), s => s.addConst ⟨n, sort⟩
  | .declareUnary n arg ret, (), s => s.addUnary ⟨n, arg, ret⟩
  | .declareBinary n arg1 arg2 ret, (), s => s.addBinary ⟨n, arg1, arg2, ret⟩
  | .assert e, (), s => s.addAssert e
  | .checkSat, _, s => s

end State

end Smt
