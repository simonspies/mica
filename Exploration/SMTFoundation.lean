import Mica.Verifier.Scoped

/-! ## Example: classifying the sign of an integer

Declares a constant `n`, asserts `n = k`, then uses bracket to test:
is `n ≥ 0` unsatisfiable (meaning k < 0)? -/

inductive SignResult where
  | negative
  | inconclusive
  deriving BEq, Repr

def smtEqInt (name : String) (k : Int) : Formula :=
  .eq .int (.var .int name) (.const (.i k))

def smtGeq0 (name : String) : Formula :=
  .binpred .le (.const (.i 0)) (.var .int name)

/-- Classify whether integer `k` is negative by querying an SMT solver. -/
def classifySign (k : Int) : ScopedM SignResult :=
  .declareConst "n" .int fun () =>
    .assert (smtEqInt "n" k) fun () =>
      .bracket
        (.assert (smtGeq0 "n") fun () =>
          .checkSat fun r => .ret r)
        fun
          | .unsat => .ret .negative
          | _ => .ret .inconclusive

axiom unsat_geq0_means_negative (k : Int) :
    ¬ Satisfiable [⟨"n", .int⟩] [smtGeq0 "n", smtEqInt "n" k] → k < 0

theorem classifySign_negative (k : Int) st' :
    Strategy.eval (ScopedM.translate (classifySign k)) .initial .negative st' →
    k < 0 := by
  intro heval
  have h := ScopedM.strategy_eval_initial_implies_ScopedM_eval heval; simp only [classifySign] at h
  -- declareConst "n" : Int
  have h := ScopedM.eval_declareConst h
  -- assert (n = k)
  have h := ScopedM.eval_assert h
  -- bracket: decompose into body and continuation
  obtain ⟨b, ctx_body, hbody, hk⟩ := ScopedM.eval_bracket h
  -- case-split on the SMT result b to determine which branch of the continuation fires
  match b with
  | .unsat =>
    -- continuation: .ret .negative — consistent with goal ret = .negative
    -- body: assert (n ≥ 0) → checkSat → ret .unsat
    have hbody := ScopedM.eval_assert hbody
    rcases ScopedM.eval_checkSat hbody with ⟨hunsat, _⟩ | h | h
    · exact unsat_geq0_means_negative k hunsat
    all_goals (simp only [ScopedM.eval_ret] at h; exact absurd h.1 (by simp))
  | .sat | .unknown =>
    -- continuation: .ret .inconclusive — contradicts ret = .negative
    simp only [ScopedM.eval_ret] at hk
    exact absurd hk.1 (by simp)
