-- SUMMARY: SMT commands, their responses, and their effect on the abstract solver state.
import Mica.Engine.State
import Mica.FOL.Printing

/-! ## Smt.Command

An SMT command, indexed by its response type. -/

namespace Smt

namespace Options

/-- A solver option together with the value to set it to. Options are
    soundness-irrelevant; `Trace.isSound` imposes nothing on them. -/
inductive Settable where
  | timeout (ms : Nat)
  | eagerThreshold (bound : Float)
  | mbqi (on : Bool)

/-- A solver option to read back, indexed by the type parsed from Z3's response. -/
inductive Gettable : Type → Type where
  | timeout : Gettable Nat

-- Recursive functions are encoded as quantified definitional axioms whose
-- bodies reference the function again.
-- Z3's default eager instantiation easily falls into a matching loop. It even
-- does so _before_ a check-sat is reached when entering a new scope.
-- To avoid a severe performance penalty, we lower the default from 10.0 to 5.0.
-- The verifier's quantified axioms are designed for E-matching (with explicit
-- or Z3-inferred triggers), so model-based quantifier instantiation adds a
-- second, less predictable search path without being needed by the examples.
/-- The settings every session starts with. -/
def Settable.initial : List Settable :=
  [.timeout 10000, .eagerThreshold 5.0, .mbqi false]

def Settable.toSMTLIB : Settable → String
  | .timeout ms => s!"(set-option :timeout {ms})"
  | .eagerThreshold bound => s!"(set-option :smt.qi.eager_threshold {bound})"
  | .mbqi on => s!"(set-option :smt.mbqi {on})"

def Gettable.toSMTLIB : Gettable α → String
  | .timeout => "(get-option :timeout)"

/-- Parse the solver's response for an option read. -/
def Gettable.parse : Gettable α → String → Option α
  | .timeout, s => s.toNat?

end Options

inductive Command : Type → Type 1 where
  | push : Command Unit
  | pop : Command Unit
  | declareConst (name : String) (sort : Srt) : Command Unit
  | declareUnary (name : String) (arg ret : Srt) : Command Unit
  | declareBinary (name : String) (arg1 arg2 ret : Srt) : Command Unit
  | declareTernary (name : String) (arg1 arg2 arg3 ret : Srt) : Command Unit
  | declareUnaryRel (name : String) (arg : Srt) : Command Unit
  | declareBinaryRel (name : String) (arg1 arg2 : Srt) : Command Unit
  | assert (expr : Formula) : Command Unit
  | checkSat : Command Result
  | setOption (s : Options.Settable) : Command Unit
  | getOption (g : Options.Gettable α) : Command α

/-! ## Serialization -/

namespace Command

def toSMTLIB : Command α → String
  | .push => "(push)"
  | .pop => "(pop)"
  | .declareConst n sort => s!"(declare-const {n} {sort.toSMTLIB})"
  | .declareUnary n arg ret => s!"(declare-fun {n} ({arg.toSMTLIB}) {ret.toSMTLIB})"
  | .declareBinary n arg1 arg2 ret =>
      s!"(declare-fun {n} ({arg1.toSMTLIB} {arg2.toSMTLIB}) {ret.toSMTLIB})"
  | .declareTernary n arg1 arg2 arg3 ret =>
      s!"(declare-fun {n} ({arg1.toSMTLIB} {arg2.toSMTLIB} {arg3.toSMTLIB}) {ret.toSMTLIB})"
  | .declareUnaryRel n arg => s!"(declare-fun {n} ({arg.toSMTLIB}) Bool)"
  | .declareBinaryRel n arg1 arg2 => s!"(declare-fun {n} ({arg1.toSMTLIB} {arg2.toSMTLIB}) Bool)"
  | .assert e => s!"(assert {e.toSMTLIB})"
  | .checkSat => "(check-sat)"
  | .setOption opt => opt.toSMTLIB
  | .getOption g => g.toSMTLIB

/-- The acknowledgement `print-success` sends for a command with no response. -/
private def ack (s : String) : Option Unit := if s == "success" then some () else none

/-- Parse the solver's response string for a given command. Returns `none` on unexpected output. -/
def parse : (cmd : Command α) → String → Option α
  | .push, s => ack s
  | .pop, s => ack s
  | .declareConst _ _, s => ack s
  | .declareUnary _ _ _, s => ack s
  | .declareBinary _ _ _ _, s => ack s
  | .declareTernary _ _ _ _ _, s => ack s
  | .declareUnaryRel _ _, s => ack s
  | .declareBinaryRel _ _ _, s => ack s
  | .assert _, s => ack s
  | .checkSat, s =>
    if s == "sat" then some .sat
    else if s == "unsat" then some .unsat
    else if s == "unknown" then some .unknown
    else none
  | .setOption _, s => ack s
  | .getOption g, s => g.parse s

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
  | .declareTernary n arg1 arg2 arg3 ret, (), s => s.addTernary ⟨n, arg1, arg2, arg3, ret⟩
  | .declareUnaryRel n arg, (), s => s.addUnaryRel ⟨n, arg⟩
  | .declareBinaryRel n arg1 arg2, (), s => s.addBinaryRel ⟨n, arg1, arg2⟩
  | .assert e, (), s => s.addAssert e
  | .checkSat, _, s => s
  | .setOption _, (), s => s
  | .getOption _, _, s => s

end State

end Smt
