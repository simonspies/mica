-- SUMMARY: Integer induction for total definedness of specification functions.
import Mica.Verifier.RelationalEncoding.Axioms
import Mica.Verifier.Monad

/-!
# Termination of a specification function

Without a measure, `Axioms` states definedness of a `[@@fn]` declaration in both
directions: the encoded body is defined at `x` exactly when `f_def(x)` holds.
The solver then has to reach `f_def(x)` by unfolding one recursive call at a
time, and never reaches it for an input whose recursion is unbounded.

`[@@decreases m]` establishes definedness once instead. One query asks whether
the body is defined at every input whose measure is `rank`, given that `f` is
already defined at every input of smaller nonnegative measure. If it succeeds,
`total` — definedness at every input — is assumed and the two definedness
axioms are not emitted. For `countdown n = if n <= 0 then 0 else
countdown (n - 1)` under `[@@decreases n]`, writing `D` for `countdown_def` and
`V` for `countdown_func`, the permanent context holds

```text
D(n) -> V(n) = (if n <= 0 then 0 else V(n - 1))
D(n)
```

instead of that value axiom together with `(n <= 0 or D(n - 1)) -> D(n)` and its
converse. The induction query itself is enclosed in `push`/`pop` and leaves
nothing behind.

A ghost declaration ranks its recursion differently: `Verifier.Ghost` gives each
self-call a rank constant to lower, because what it checks is a proof rather
than a definition. Both read the same `[@@decreases]` measure.
-/

namespace Verifier.RelationalEncoding.Termination

/-- Negative ranks have no predecessors. Recursive calls must have a
nonnegative rank strictly below the current rank. -/
private theorem induction (m : α → Int) (P : α → Prop)
    (step : ∀ x, (∀ y, 0 ≤ m y → m y < m x → P y) → P x) : ∀ x, P x := by
  intro x
  generalize hn : (m x).toNat = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    apply step x
    intro y hzero hlt
    exact ih (m y).toNat (by omega) y rfl

/-- Definedness of `fn` at every input: the assertion a successful termination
check adds. -/
def total (fn : SpecFn) (x : String) : Formula :=
  .all x .value (fn.isDefined (.var .value x))

/-- The rank binder encloses two separate input scopes, so the measure and
body use their original argument name without substitution. -/
private def obligation (fn : SpecFn) (x rank : String) (m : Typed.Measure)
    (body : Skolemize.DefVal) : Formula :=
  .all rank .int
    (.implies
      (.forall_ x .value [.unpred (.uninterpreted fn.defName .value) (.var .value x)]
        (.implies
          (.and (.binpred .le (.const (.i 0)) m.term)
            (.binpred .lt m.term (.var .int rank)))
          (fn.isDefined (.var .value x))))
      (.all x .value
        (.implies (.eq .int m.term (.var .int rank))
          (.and m.defined body.defined))))

private theorem obligation_correct {fn : SpecFn} {x rank : String}
    {m : Typed.Measure} {body : Skolemize.DefVal} {Δ : Signature} {ρ : Env}
    (hfresh : rank ∉ Δ.allNames) (hne : rank ≠ x)
    (hm : m.term.wfIn (Δ.declVar ⟨x, .value⟩))
    (hb : body.defined.wfIn (Δ.declVar ⟨x, .value⟩))
    (hclose : ∀ v, body.defined.eval (ρ.updateConst .value x v) →
      (fn.isDefined (.var .value x)).eval (ρ.updateConst .value x v))
    (h : (obligation fn x rank m body).eval ρ) : (total fn x).eval ρ := by
  have hag (r : Int) (v : Srt.value.denote) :=
    Env.agreeOn_declVar (τ := Srt.value) (x := x) (v := v)
      (Env.agreeOn_update_fresh_const (ρ := ρ) (c := ⟨rank, .int⟩) (u := r) hfresh)
  have hm' (r : Int) (v : Srt.value.denote) := Term.eval_env_agree hm (hag r v)
  have hb' (r : Int) (v : Srt.value.denote) := Formula.eval_env_agree hb (hag r v)
  simp only [obligation, Formula.all, Formula.eval] at h
  change ∀ v, (fn.isDefined (.var .value x)).eval (ρ.updateConst .value x v)
  apply induction (fun v => m.term.eval (ρ.updateConst .value x v))
  intro v ih
  apply hclose v
  apply (hb' _ v).mpr
  apply (h (m.term.eval (ρ.updateConst .value x v)) ?_ v ?_).2
  · intro y hy
    have hy' : 0 ≤ m.term.eval (ρ.updateConst .value x y) ∧
        m.term.eval (ρ.updateConst .value x y) < m.term.eval (ρ.updateConst .value x v) := by
      simpa only [Formula.eval, BinPred.eval, Term.eval, Const.denote,
        Env.lookupConst_updateConst_ne' (Or.inl hne), Env.lookupConst_updateConst_same,
        ← hm'] using hy
    have hd := ih y hy'.1 hy'.2
    simpa only [SpecFn.isDefined, Formula.eval, UnPred.eval, Term.eval,
      Env.lookupConst_updateConst_same, Env.updateConst_unaryRel] using hd
  · simpa only [Term.eval, Env.lookupConst_updateConst_ne' (Or.inl hne),
      Env.lookupConst_updateConst_same] using (hm' _ v).symm

/-- Prove total definedness from the body, without recursive definedness
axioms. The quantified induction hypothesis belongs only to this query. -/
def check (fn : SpecFn) (x : String) (m : Typed.Measure)
    (body : Skolemize.DefVal) : VerifM Unit := do
  let Δ ← VerifM.decls
  let rank := Fresh.freshName (x :: Δ.allNames) "rank"
  let φ := obligation fn x rank m body
  match m.term.checkWf (Δ.declVar ⟨x, .value⟩),
      body.defined.checkWf (Δ.declVar ⟨x, .value⟩), φ.checkWf Δ, (total fn x).checkWf Δ with
  | .ok (), .ok (), .ok (), .ok () => do
    if ← VerifM.check .high φ then
      VerifM.assume (.pure (total fn x))
    else VerifM.failed s!"termination check failed for {fn}"
  | .error msg, _, _, _ | _, .error msg, _, _ | _, _, .error msg, _ | _, _, _, .error msg =>
    VerifM.fatal msg

theorem check_correct {fn : SpecFn} {x : String} {m : Typed.Measure}
    {body : Skolemize.DefVal} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop}
    (hclose : ∀ v, body.defined.eval (ρ.updateConst .value x v) →
      (fn.isDefined (.var .value x)).eval (ρ.updateConst .value x v))
    (h : VerifM.eval (check fn x m body) st ρ Q) :
    Q () { st with asserts := total fn x :: st.asserts } ρ := by
  simp only [check] at h
  have h := VerifM.eval_decls (VerifM.eval_bind h)
  split at h
  · rename_i hm hb hφ ht
    obtain ⟨b, hb', h⟩ := VerifM.eval_check (VerifM.eval_bind h) (Formula.checkWf_ok hφ)
    cases b with
    | false => exact (VerifM.eval_failed h).elim
    | true =>
      have hfresh := Fresh.freshName_not_in_avoid (x :: st.decls.allNames) "rank"
      simp only [List.mem_cons, not_or] at hfresh
      apply VerifM.eval_assumePure h (Formula.checkWf_ok ht)
      exact obligation_correct hfresh.2 hfresh.1 (Term.checkWf_ok hm)
        (Formula.checkWf_ok hb) hclose (hb' rfl)
  all_goals exact (VerifM.eval_fatal h).elim

end Verifier.RelationalEncoding.Termination
