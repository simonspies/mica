-- SUMMARY: Execution traces and the soundness condition imposed on solver replies.
import Mica.Engine.Command

/-! ## Trace

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

/-! ## Trace.finalState -/

def finalState (st : State) : Trace α → State
  | .done _ => st
  | .step cmd r rest => rest.finalState (st.step cmd r)

/-! ## Trace.isSound

A trace is sound if every `unsat` response is truthful: the active assertions
at that point are genuinely unsatisfiable.

We do not require anything of `sat` or `unknown` responses — the checker must
handle those conservatively. -/

/-- What one reply must justify. Only `unsat` carries an obligation. -/
def obligation : Command β → β → State → Prop
  | .checkSat, .unsat, s => ¬ State.satisfiable s.allDecls s.allAsserts
  | _, _, _ => True

def isSound : State → Trace α → Prop
  | _, .done _ => True
  | s, .step cmd r rest => obligation cmd r s ∧ isSound (s.step cmd r) rest

/-! ## Trace.isSound step lemmas -/

theorem isSound.step_obligation {cmd : Command β} {r : β} {rest : Trace α} {st : State}
    (h : isSound st (.step cmd r rest)) : obligation cmd r st := h.left

theorem isSound.step_rest {cmd : Command β} {r : β} {rest : Trace α} {st : State}
    (h : isSound st (.step cmd r rest)) : isSound (st.step cmd r) rest := h.right

theorem isSound.step_cons {cmd : Command β} {r : β} {rest : Trace α} {st : State}
    (hrest : isSound (st.step cmd r) rest) (hstep : obligation cmd r st) :
    isSound st (.step cmd r rest) := ⟨hstep, hrest⟩

end Trace

end Smt
