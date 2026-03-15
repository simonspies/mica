import Mica.Engine.Command

/-! ## Strategies (Interaction Trees)

A strategy is a tree where each node executes a command and branches on the
response. The only interesting branching is at checkSat (since other commands
return Unit, their continuation is effectively linear). -/

inductive Strategy (α : Type) where
  | done (result : α) : Strategy α
  | exec {β : Type} (cmd : Command β) (k : β → Strategy α) : Strategy α

/-! ## Traces

A trace is a linear record of one execution: a sequence of command-response
pairs, ending in a result. Like a cons-list but terminated by a result. -/

inductive Trace (α : Type) where
  | done (result : α) : Trace α
  | step {β : Type} (cmd : Command β) (response : β) (rest : Trace α) : Trace α

namespace Trace

def result : Trace α → α
  | .done a => a
  | .step _ _ rest => rest.result

end Trace

/-! ## Trace Generation

`Generates strategy trace` means that `trace` is a possible execution of `strategy`.
Purely structural — no semantics of push/pop here. -/

inductive Generates : Strategy α → Trace α → Prop where
  | done : Generates (.done a) (.done a)
  | exec {cmd : Command β} {f : β → Strategy α} {r : β} {t : Trace α} :
      Generates (f r) t →
      Generates (.exec cmd f) (.step cmd r t)

/-! ## Strategy.bind -/

def Strategy.bind : Strategy α → (α → Strategy β) → Strategy β
  | .done a, k => k a
  | .exec cmd f, k => .exec cmd (fun r => (f r).bind k)

theorem Strategy.bind_assoc {s : Strategy α} {f : α → Strategy β} {g : β → Strategy γ} :
    (s.bind f).bind g = s.bind (fun a => (f a).bind g) := by
  induction s with
  | done a => rfl
  | exec cmd k ih => simp [Strategy.bind]; funext r; exact ih r

/-! ## Trace.finalState

Walk a trace, advancing the SmtState at each step. -/

def Trace.finalState (st : SmtState) : Trace α → SmtState
  | .done _ => st
  | .step cmd r rest => rest.finalState (st.step cmd r)

/-! ## Trace Soundness

A trace is sound if every `unsat` response is truthful: the active assertions
at that point are genuinely unsatisfiable.

We do not require anything of `sat` or `unknown` responses — the checker must
handle those conservatively. -/

/-- Walk a trace maintaining the SMT state, verifying that every `unsat` is justified. -/
def TraceSound : SmtState → Trace α → Prop
  | _, .done _ => True
  | s, .step .push () rest => TraceSound s.push rest
  | s, .step .pop () rest => TraceSound s.pop rest
  | s, .step (.declareConst n sort) () rest => TraceSound (s.addDecl ⟨n, sort⟩) rest
  | s, .step (.assert e) () rest => TraceSound (s.addAssert e) rest
  | s, .step .checkSat .unsat rest =>
      ¬ Satisfiable s.allDecls s.allAsserts ∧ TraceSound s rest
  | s, .step .checkSat _ rest => TraceSound s rest

/-- Trace soundness starting from the initial state. -/
def TraceSound' (t : Trace α) : Prop := TraceSound .initial t

/-! ## TraceSound step lemmas -/

/-- Peeling one step off TraceSound: the rest is sound from the stepped state. -/
theorem TraceSound.step_rest {cmd : Command β} {r : β} {rest : Trace α} {st : SmtState}
    (h : TraceSound st (.step cmd r rest)) : TraceSound (st.step cmd r) rest := by
  cases cmd with
  | push => exact h
  | pop => exact h
  | declareConst n sort => cases r; exact h
  | assert e => cases r; exact h
  | checkSat => cases r with | sat => exact h | unsat => exact h.2 | unknown => exact h

/-- Reconstructing TraceSound for one step from the step obligation and the rest. -/
theorem TraceSound.step_cons {cmd : Command β} {r : β} {rest : Trace α} {st : SmtState}
    (hrest : TraceSound (st.step cmd r) rest)
    (hstep : match cmd, r with
      | .checkSat, .unsat => ¬ Satisfiable st.allDecls st.allAsserts
      | _, _ => True) :
    TraceSound st (.step cmd r rest) := by
  cases cmd with
  | push => exact hrest
  | pop => exact hrest
  | declareConst n sort => cases r; exact hrest
  | assert e => cases r; exact hrest
  | checkSat => cases r with | sat => exact hrest | unsat => exact ⟨hstep, hrest⟩ | unknown => exact hrest

/-! ## Bind decomposition -/

/-- Any trace of `s.bind k` decomposes into a trace of `s` followed by a trace of `k`. -/
theorem Strategy.bind_generates_decompose {s : Strategy α} {k : α → Strategy β}
    {t : Trace β} (hgen : Generates (s.bind k) t) :
    ∃ a ts tk,
      Generates s ts ∧ Generates (k a) tk ∧ (ts : Trace α).result = a ∧
      (∀ st, t.finalState st = tk.finalState (ts.finalState st)) ∧
      t.result = tk.result := by
  induction s generalizing t with
  | done a =>
    simp [Strategy.bind] at hgen
    exact ⟨a, .done a, t, .done, hgen, rfl, fun _ => rfl, rfl⟩
  | exec cmd f ih =>
    simp [Strategy.bind] at hgen
    cases hgen
    rename_i rest r hrest
    obtain ⟨a, ts, tk, hgens, hgenk, hres, hfin, hresult⟩ := ih r hrest
    exact ⟨a, .step cmd r ts, tk, .exec hgens, hgenk, hres,
      fun st => by simp [Trace.finalState]; exact hfin _, hresult⟩

/-- TraceSound decomposes through Strategy.bind. -/
theorem Strategy.bind_traceSound {s : Strategy α} {k : α → Strategy β}
    {t : Trace β} (hgen : Generates (s.bind k) t) {st : SmtState}
    (hsound : TraceSound st t) :
    ∃ a ts tk,
      Generates s ts ∧ Generates (k a) tk ∧ ts.result = a ∧
      TraceSound st ts ∧ TraceSound (ts.finalState st) tk ∧
      (∀ st', t.finalState st' = tk.finalState (ts.finalState st')) ∧
      t.result = tk.result := by
  induction s generalizing t st with
  | done a =>
    simp [Strategy.bind] at hgen
    exact ⟨a, .done a, t, .done, hgen, rfl, trivial, hsound, fun _ => rfl, rfl⟩
  | exec cmd f ih =>
    simp [Strategy.bind] at hgen
    cases hgen; rename_i rest r hrest
    dsimp only at hrest
    obtain ⟨a, ts, tk, hgens, hgenk, hres, hsound_ts, hsound_tk, hfin, hresult⟩ :=
      ih r hrest (hsound.step_rest)
    refine ⟨a, .step cmd r ts, tk, .exec hgens, hgenk, hres, ?_, ?_, fun st' => ?_, hresult⟩
    · exact TraceSound.step_cons hsound_ts (by
        cases cmd with
        | push => trivial | pop => trivial
        | declareConst => cases r; trivial
        | assert => cases r; trivial
        | checkSat => cases r with
          | sat => trivial
          | unsat => cases hsound; assumption
          | unknown => trivial)
    · simp [Trace.finalState]; exact hsound_tk
    · simp [Trace.finalState]; exact hfin _

/-! ## Strategy.eval: Extensional Semantics

`Strategy.eval s st ret st'` means: there exists a sound execution of `s` starting
from `st` that results in `ret` with final state `st'`. -/

def Strategy.eval (s : Strategy α) (st : SmtState) (ret: α) (st' : SmtState) : Prop :=
  ∃ t, Generates s t ∧ TraceSound st t ∧ st' = t.finalState st ∧ ret = t.result

theorem Strategy.eval_done {a : α} {st : SmtState} {ret : α} {st' : SmtState} :
    Strategy.eval (.done a) st ret st' ↔ (ret = a ∧ st' = st) := by
  constructor
  · rintro ⟨t, hgen, hsound, hst, hret⟩
    cases hgen
    simp [Trace.finalState, Trace.result] at hst hret
    exact ⟨hret, hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨.done ret, .done, trivial, rfl, rfl⟩

def Outcome := Except String Unit

def Strategy.checks (s : Strategy Outcome) (φ : Prop) :=
  ∀ st', Strategy.eval s SmtState.initial (.ok ()) st' → φ
