import Mica.Engine.Trace

/-! ## Smt.Strategy (Interaction Trees)

A strategy is an interaction tree, a tree where each node executes a command and
branches on the response. The only interesting branching is at checkSat. (Since
other commands return Unit, their continuation is effectively linear.) -/

namespace Smt

inductive Strategy (α : Type) where
  | done (result : α) : Strategy α
  | exec {β : Type} (cmd : Command β) (k : β → Strategy α) : Strategy α

namespace Strategy

/-! ## Strategy.bind -/

def bind : Strategy α → (α → Strategy β) → Strategy β
  | .done a, k => k a
  | .exec cmd f, k => .exec cmd (fun r => (f r).bind k)

theorem bind_assoc {s : Strategy α} {f : α → Strategy β} {g : β → Strategy γ} :
    (s.bind f).bind g = s.bind (fun a => (f a).bind g) := by
  induction s with
  | done a => rfl
  | exec cmd k ih => simp [bind]; funext r; exact ih r

/-! ## Smt.Strategy.generates

`generates strategy trace` means that `trace` is a possible execution of `strategy`. -/

inductive generates : Strategy α → Trace α → Prop where
  | done : generates (.done a) (.done a)
  | exec {cmd : Command β} {f : β → Strategy α} {r : β} {t : Trace α} :
      generates (f r) t →
      generates (.exec cmd f) (.step cmd r t)

/-! ## Bind decomposition -/

/-- Any trace of `s.bind k` decomposes into a trace of `s` followed by a trace of `k`. -/
theorem bind_generates_decompose {s : Strategy α} {k : α → Strategy β}
    {t : Trace β} (hgen : generates (s.bind k) t) :
    ∃ a ts tk,
      generates s ts ∧ generates (k a) tk ∧ (ts : Trace α).result = a ∧
      (∀ st, t.finalState st = tk.finalState (ts.finalState st)) ∧
      t.result = tk.result := by
  induction s generalizing t with
  | done a =>
    simp [bind] at hgen
    exact ⟨a, .done a, t, .done, hgen, rfl, fun _ => rfl, rfl⟩
  | exec cmd f ih =>
    simp [bind] at hgen
    cases hgen
    rename_i rest r hrest
    obtain ⟨a, ts, tk, hgens, hgenk, hres, hfin, hresult⟩ := ih r hrest
    exact ⟨a, .step cmd r ts, tk, .exec hgens, hgenk, hres,
      fun st => by simp [Trace.finalState]; exact hfin _, hresult⟩

/-- isSound decomposes through bind. -/
theorem bind_traceSound {s : Strategy α} {k : α → Strategy β}
    {t : Trace β} (hgen : generates (s.bind k) t) {st : State}
    (hsound : Trace.isSound st t) :
    ∃ a ts tk,
      generates s ts ∧ generates (k a) tk ∧ ts.result = a ∧
      Trace.isSound st ts ∧ Trace.isSound (ts.finalState st) tk ∧
      (∀ st', t.finalState st' = tk.finalState (ts.finalState st')) ∧
      t.result = tk.result := by
  induction s generalizing t st with
  | done a =>
    simp [bind] at hgen
    exact ⟨a, .done a, t, .done, hgen, rfl, trivial, hsound, fun _ => rfl, rfl⟩
  | exec cmd f ih =>
    simp [bind] at hgen
    cases hgen; rename_i rest r hrest
    dsimp only at hrest
    obtain ⟨a, ts, tk, hgens, hgenk, hres, hsound_ts, hsound_tk, hfin, hresult⟩ :=
      ih r hrest (hsound.step_rest)
    refine ⟨a, .step cmd r ts, tk, .exec hgens, hgenk, hres, ?_, ?_, fun st' => ?_, hresult⟩
    · exact Trace.isSound.step_cons hsound_ts (by
        cases cmd with
        | push => trivial | pop => trivial
        | declareConst => cases r; trivial
        | declareUnary => cases r; trivial
        | declareBinary => cases r; trivial
        | assert => cases r; trivial
        | checkSat => cases r with
          | sat => trivial
          | unsat => cases hsound; assumption
          | unknown => trivial)
    · simp [Trace.finalState]; exact hsound_tk
    · simp [Trace.finalState]; exact hfin _

/-! ## Strategy.eval: Extensional Semantics

`eval s st ret st'` means: there exists a sound execution of `s` starting
from `st` that results in `ret` with final state `st'`. -/

def eval (s : Strategy α) (st : State) (ret : α) (st' : State) : Prop :=
  ∃ t, generates s t ∧ Trace.isSound st t ∧ st' = t.finalState st ∧ ret = t.result

theorem eval_done {a : α} {st : State} {ret : α} {st' : State} :
    eval (.done a) st ret st' ↔ (ret = a ∧ st' = st) := by
  constructor
  · rintro ⟨t, hgen, hsound, hst, hret⟩
    cases hgen
    simp [Trace.finalState, Trace.result] at hst hret
    exact ⟨hret, hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨.done ret, .done, trivial, rfl, rfl⟩

/-! ## Smt.Strategy.Outcome and checks -/

def Outcome := Except String Unit

def checks (s : Strategy Outcome) (φ : Prop) :=
  ∀ st', eval s State.initial (.ok ()) st' → φ

end Strategy

end Smt
