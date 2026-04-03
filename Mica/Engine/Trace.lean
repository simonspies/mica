import Mica.Engine.Command

/-! ## Smt.Trace

A trace is a linear record of one execution: a sequence of command-response
pairs, ending in a result. -/

namespace Smt

inductive Trace (α : Type) where
  | done (result : α) : Trace α
  | step {β : Type} (cmd : Command β) (response : β) (rest : Trace α) : Trace α

namespace Trace

def result : Trace α → α
  | .done a => a
  | .step _ _ rest => rest.result

/-! ## Trace.finalState

Walk a trace, advancing the Smt.State at each step. -/

def finalState (st : State) : Trace α → State
  | .done _ => st
  | .step cmd r rest => rest.finalState (st.step cmd r)

/-! ## Trace.isSound

A trace is sound if every `unsat` response is truthful: the active assertions
at that point are genuinely unsatisfiable.

We do not require anything of `sat` or `unknown` responses — the checker must
handle those conservatively. -/

/-- Walk a trace maintaining the SMT state, verifying that every `unsat` is justified. -/
def isSound : State → Trace α → Prop
  | _, .done _ => True
  | s, .step .push () rest => isSound s.push rest
  | s, .step .pop () rest => isSound s.pop rest
  | s, .step (.declareConst n sort) () rest => isSound (s.addConst ⟨n, sort⟩) rest
  | s, .step (.declareUnary n arg ret) () rest => isSound (s.addUnary ⟨n, arg, ret⟩) rest
  | s, .step (.declareBinary n arg1 arg2 ret) () rest => isSound (s.addBinary ⟨n, arg1, arg2, ret⟩) rest
  | s, .step (.assert e) () rest => isSound (s.addAssert e) rest
  | s, .step .checkSat .unsat rest =>
      ¬ State.satisfiable s.allDecls s.allAsserts ∧ isSound s rest
  | s, .step .checkSat _ rest => isSound s rest

/-! ## isSound step lemmas -/

/-- Peeling one step off isSound: the rest is sound from the stepped state. -/
theorem isSound.step_rest {cmd : Command β} {r : β} {rest : Trace α} {st : State}
    (h : isSound st (.step cmd r rest)) : isSound (st.step cmd r) rest := by
  cases cmd with
  | push => exact h
  | pop => exact h
  | declareConst n sort => cases r; exact h
  | declareUnary n arg ret => cases r; exact h
  | declareBinary n arg1 arg2 ret => cases r; exact h
  | assert e => cases r; exact h
  | checkSat => cases r with | sat => exact h | unsat => exact h.2 | unknown => exact h

/-- Reconstructing isSound for one step from the step obligation and the rest. -/
theorem isSound.step_cons {cmd : Command β} {r : β} {rest : Trace α} {st : State}
    (hrest : isSound (st.step cmd r) rest)
    (hstep : match cmd, r with
      | .checkSat, .unsat => ¬ State.satisfiable st.allDecls st.allAsserts
      | _, _ => True) :
    isSound st (.step cmd r rest) := by
  cases cmd with
  | push => exact hrest
  | pop => exact hrest
  | declareConst n sort => cases r; exact hrest
  | declareUnary n arg ret => cases r; exact hrest
  | declareBinary n arg1 arg2 ret => cases r; exact hrest
  | assert e => cases r; exact hrest
  | checkSat => cases r with | sat => exact hrest | unsat => exact ⟨hstep, hrest⟩ | unknown => exact hrest

end Trace

end Smt
