import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.SeparationLogic
import Mica.Verifier.Monad

open Iris Iris.BI

/-!
# Atoms

Defines `Atom`, a sort predicate that asserts a value-sorted term has a specific sort
and extracts the underlying typed value.
-/


-- ---------------------------------------------------------------------------
-- Atom inductive
-- ---------------------------------------------------------------------------

/-- A sort predicate: asserts that a value-sorted term has a specific sort,
    and extracts the underlying typed value. -/
inductive Atom : Srt → Type where
  | isint  : Term .value → Atom .int
  | isbool : Term .value → Atom .bool
  | isinj  (tag : Nat) (arity : Nat) : Term .value → Atom .value


def Atom.pure {τ: Srt} (a : Atom τ) : Bool :=
  match a with
  | isint _ => true
  | isbool _ => true
  | isinj _ _ _ => true


-- ---------------------------------------------------------------------------
-- Substitution
-- ---------------------------------------------------------------------------

def Atom.subst (σ : Subst) : Atom τ → Atom τ
  | .isint t  => .isint (t.subst σ)
  | .isbool t => .isbool (t.subst σ)
  | .isinj tag arity t => .isinj tag arity (t.subst σ)


-- ---------------------------------------------------------------------------
-- Conversion to context items
-- ---------------------------------------------------------------------------

/-- Convert an atom applied to a typed term into a formula. -/
def Atom.toFormula : Atom τ → Term τ → Formula
  | .isint  v, t => .eq .value v (.unop .ofInt t)
  | .isbool v, t => .eq .value v (.unop .ofBool t)
  | .isinj tag arity v, t => .eq .value v (.unop (.mkInj tag arity) t)

namespace CtxItem

/-- Semantic interpretation of a verifier context item. -/
def interp (ρ : Env) : CtxItem → iProp
  | .pure φ => ⌜φ.eval ρ⌝
  | .spatial a => a.interp ρ

def purePart (i : CtxItem) (ρ : Env) : Prop :=
  match i with
  | .pure φ => φ.eval ρ
  | .spatial _ => True

end CtxItem

/-- Convert an instantiated atom into the corresponding verifier context item. -/
def Atom.toItem (a : Atom τ) (t : Term τ) : CtxItem :=
  .pure (a.toFormula t)

-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def Atom.eval {τ : Srt} (p : Atom τ) (ρ : Env) : τ.denote → iProp :=
  match p with
  | isint t  => λ v => ⌜.int v = t.eval ρ⌝
  | isbool t => λ v => ⌜.bool v = t.eval ρ⌝
  | isinj tag arity t => λ v => ⌜.inj tag arity v = t.eval ρ⌝


/-- Try to match a formula against an atom, returning the extracted term if it matches. -/
def Formula.matchAtom (φ : Formula) (a : Atom τ) : Option (Term τ) :=
  match a with
  | .isint v =>
    match φ with
    | .eq .value v' (.unop .ofInt t) => if v' = v then some t else none
    | _ => none
  | .isbool v =>
    match φ with
    | .eq .value v' (.unop .ofBool t) => if v' = v then some t else none
    | _ => none
  | .isinj tag arity v =>
    match φ with
    | .eq .value v' (.unop (.mkInj tag' arity') t) =>
      if v' = v ∧ tag = tag' ∧ arity = arity' then some t else none
    | _ => none

theorem Formula.matchAtom_wfIn {φ : Formula} {a : Atom τ} {t : Term τ} {Δ : Signature}
    (h : φ.matchAtom a = some t) (hφ : φ.wfIn Δ) : t.wfIn Δ := by
  cases a with
  | isint v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all [Formula.wfIn, Term.wfIn]
  | isbool v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all [Formula.wfIn, Term.wfIn]
  | isinj tag arity v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all [Formula.wfIn, Term.wfIn]


theorem Formula.matchAtom_correct {φ : Formula} {a : Atom τ} {t : Term τ}
    (h : φ.matchAtom a = some t) : φ = a.toFormula t := by
  cases a with
  | isint v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all; obtain ⟨rfl, rfl⟩ := h; rfl
  | isbool v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all; obtain ⟨rfl, rfl⟩ := h; rfl
  | isinj tag arity v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h; rfl


-- ---------------------------------------------------------------------------
-- Resolution
-- ---------------------------------------------------------------------------

/-- Resolve an atom against a list of formulas. -/
def Atom.resolve (a : Atom τ) (C : List Formula) : Option (Term τ) :=
  C.findSome? (·.matchAtom a)

theorem Atom.resolve_correct {a : Atom τ} {C : List Formula} {t : Term τ}
    (h : a.resolve C = some t) (ρ : Env) (hC : ∀ φ ∈ C, φ.eval ρ) :
    (a.toFormula t).eval ρ := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  have heq := Formula.matchAtom_correct hφ_match
  subst heq
  exact hC _ hφ_mem

theorem Atom.resolve_wfIn {a : Atom τ} {C : List Formula} {t : Term τ} {Δ : Signature}
    (h : a.resolve C = some t) (hwf : ∀ φ ∈ C, φ.wfIn Δ) :
    t.wfIn Δ := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  exact Formula.matchAtom_wfIn hφ_match (hwf _ hφ_mem)


-- ---------------------------------------------------------------------------
-- Printer
-- ---------------------------------------------------------------------------

def Atom.toStringHum : {τ : Srt} → Atom τ → String
  | _, .isint  t => s!"isint {t.toStringHum}"
  | _, .isbool t => s!"isbool {t.toStringHum}"
  | _, .isinj tag arity t => s!"isinj {tag}/{arity} {t.toStringHum}"

-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- An atom is well-formed in a signature. -/
def Atom.wfIn (Δ : Signature) : Atom τ → Prop
  | .isint t  => t.wfIn Δ
  | .isbool t => t.wfIn Δ
  | .isinj _ _ t => t.wfIn Δ

def Atom.checkWf (p : Atom τ) (Δ : Signature) : Except String Unit :=
  match p with
  | .isint t  => t.checkWf Δ
  | .isbool t => t.checkWf Δ
  | .isinj _ _ t => t.checkWf Δ

theorem Atom.checkWf_ok {p : Atom τ} {Δ : Signature} (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | isint t  => exact Term.checkWf_ok h
  | isbool t => exact Term.checkWf_ok h
  | isinj tag arity t => exact Term.checkWf_ok h

theorem Atom.wfIn_mono {p : Atom τ} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hmono : Δ.Subset Δ') (hwf : Δ'.wf) : p.wfIn Δ' := by
  cases p with
  | isint t  => exact Term.wfIn_mono t h hmono hwf
  | isbool t => exact Term.wfIn_mono t h hmono hwf
  | isinj tag arity t => exact Term.wfIn_mono t h hmono hwf

theorem Atom.eval_env_agree {p : Atom τ} {ρ ρ' : Env} {Δ : Signature}
    (hwf : p.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') : p.eval ρ = p.eval ρ' := by
  cases p with
  | isint t  => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | isbool t => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | isinj tag arity t => simp [Atom.eval, Term.eval_env_agree hwf hagree]

theorem Atom.toItem_wfIn {p : Atom τ} {t : Term τ} {Δ : Signature}
    (hp : p.wfIn Δ) (ht : t.wfIn Δ) :
    (p.toItem t).wfIn Δ := by
  cases p with
  | isint v =>
    simp only [Atom.toItem, CtxItem.wfIn]
    exact ⟨hp, trivial, ht⟩
  | isbool v =>
    simp only [Atom.toItem, CtxItem.wfIn]
    exact ⟨hp, trivial, ht⟩
  | isinj tag arity v =>
    simp only [Atom.toItem, CtxItem.wfIn]
    exact ⟨hp, trivial, ht⟩

theorem Atom.toFormula_wfIn {p : Atom τ} {t : Term τ} {Δ : Signature}
    (hp : p.wfIn Δ) (ht : t.wfIn Δ) :
    (p.toFormula t).wfIn Δ := by
  cases p with
  | isint v =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn]
    exact ⟨hp, trivial, ht⟩
  | isbool v =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn]
    exact ⟨hp, trivial, ht⟩
  | isinj tag arity v =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn]
    exact ⟨hp, trivial, ht⟩

theorem Atom.eval_pure {p : Atom τ} {t : Term τ} {ρ : Env} :
    p.eval ρ (t.eval ρ) ⊣⊢ ⌜(p.toFormula t).eval ρ⌝ := by
  cases p with
  | isint v  => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]
  | isbool v => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]
  | isinj tag arity v => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]

/-- If `p.eval ρ u` holds and `p` is wfIn fresh decls, then `p.toFormula (.var τ x)` holds
    after updating `ρ` with `x ↦ u`. -/
theorem Atom.toFormula_eval_1 {p : Atom τ} {t : Term τ} {ρ : Env} :
     p.eval ρ (t.eval ρ) ⊢ ⌜(p.toFormula t).eval ρ⌝ := by
  exact Atom.eval_pure.1

/-- If `(p.toFormula t).eval ρ` holds, then `p.eval ρ (t.eval ρ)`. -/
theorem Atom.toFormula_eval_2 {p : Atom τ} {t : Term τ} {ρ : Env}
    : ⌜(p.toFormula t).eval ρ⌝ ⊢ p.eval ρ (t.eval ρ) := by
  exact Atom.eval_pure.2

theorem Atom.eval_toItem {p : Atom τ} {t : Term τ} {ρ : Env} :
    p.eval ρ (t.eval ρ) ⊢ CtxItem.interp ρ (p.toItem t) := by
  cases p with
  | isint v  => simp [Atom.eval, Atom.toFormula, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | isbool v => simp [Atom.eval, Atom.toFormula, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | isinj tag arity v => simp [Atom.eval, Atom.toFormula, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]

theorem Atom.eval_purePart {p : Atom τ} {t : Term τ} {ρ : Env} :
    p.eval ρ (t.eval ρ) ⊢ ⌜(p.toItem t).purePart ρ⌝ := by
  cases p with
  | isint v =>
    simp [Atom.eval, CtxItem.purePart, Atom.toFormula, Atom.toItem, Formula.eval, Term.eval, eq_comm]
  | isbool v =>
    simp [Atom.eval, CtxItem.purePart, Atom.toFormula, Atom.toItem, Formula.eval, Term.eval, eq_comm]
  | isinj tag arity v =>
    simp [Atom.eval, CtxItem.purePart, Atom.toFormula, Atom.toItem, Formula.eval, Term.eval, eq_comm]


-- ---------------------------------------------------------------------------
-- Substitution lemmas
-- ---------------------------------------------------------------------------

-- @agent: change eval_subst to a bi-entailment in the future.
theorem Atom.eval_subst {p : Atom τ} {σ : Subst} {ρ : Env} {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    (p.subst σ).eval ρ = p.eval (σ.eval ρ) := by
  cases p with
  | isint t =>
    funext v
    simp only [Atom.subst, Atom.eval]
    rw [Term.eval_subst hp hσ hwfΔ']
  | isbool t =>
    funext v
    simp only [Atom.subst, Atom.eval]
    rw [Term.eval_subst hp hσ hwfΔ']
  | isinj tag arity t =>
    funext v
    simp only [Atom.subst, Atom.eval]
    rw [Term.eval_subst hp hσ hwfΔ']

theorem Atom.subst_wfIn {p : Atom τ} {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (p.subst σ).wfIn Δ' := by
  cases p with
  | isint t  => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isbool t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isinj tag arity t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf


-- ---------------------------------------------------------------------------
-- Candidates: guarded resolution alternatives
-- ---------------------------------------------------------------------------

/-- Candidate resolutions for an atom, each guarded by a provability condition.
    Each pair `(φ, t)` means: if `φ` is provable, then `t` resolves the atom. -/
def Atom.candidates : Atom τ → List (Formula × Term τ)
  | .isint  v => [(.unpred .isInt v, .unop .toInt v)]
  | .isbool v => [(.unpred .isBool v, .unop .toBool v)]
  | .isinj tag arity v => [(.unpred (.isInj tag arity) v, .unop .payloadOf v)]

theorem Atom.candidates_correct {a : Atom τ} {φ : Formula} {t : Term τ} {ρ : Env}
    (hmem : (φ, t) ∈ a.candidates) (h : φ.eval ρ) : (a.toFormula t).eval ρ := by
  cases a with
  | isint v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toFormula, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all
  | isbool v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toFormula, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all
  | isinj tag arity v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toFormula, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all

theorem Atom.candidates_wfIn {a : Atom τ} {φ : Formula} {t : Term τ} {Δ : Signature}
    (hmem : (φ, t) ∈ a.candidates) (h : a.wfIn Δ) : φ.wfIn Δ ∧ t.wfIn Δ := by
  cases a with
  | isint v  => simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem; exact ⟨h, trivial, h⟩
  | isbool v => simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem; exact ⟨h, trivial, h⟩
  | isinj tag arity v => simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem; exact ⟨h, trivial, h⟩


-- ---------------------------------------------------------------------------
-- VerifM integration
-- ---------------------------------------------------------------------------

/-- Try candidate resolutions in order, checking each guard via the SMT solver. -/
def VerifM.tryCandidates : List (Formula × Term τ) → VerifM (Option (Term τ))
  | [] => pure none
  | (φ, t) :: rest => do
    if ← VerifM.check φ then pure (some t)
    else VerifM.tryCandidates rest

private theorem VerifM.eval_tryCandidates
    {candidates : List (Formula × Term τ)} {a : Atom τ}
    {st : TransState} {ρ : Env} {Q : Option (Term τ) → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.tryCandidates candidates) st ρ Q)
    (hcands : ∀ p ∈ candidates, p ∈ a.candidates)
    (hpwf : a.wfIn st.decls) :
    ∃ result : Option (Term τ),
      Q result st ρ
      ∧ (∀ t, result = some t → (a.toFormula t).eval ρ)
      ∧ (∀ t, result = some t → t.wfIn st.decls) := by
  induction candidates with
  | nil =>
    simp [tryCandidates] at h
    exact ⟨none, VerifM.eval_ret h,
           fun _ ht => absurd ht (by simp), fun _ ht => absurd ht (by simp)⟩
  | cons c rest ih =>
    obtain ⟨φ, t⟩ := c
    simp [tryCandidates] at h
    have hb := VerifM.eval_bind _ _ _ _ h
    have hmem := hcands (φ, t) (List.mem_cons_self ..)
    have ⟨φwf, twf⟩ := Atom.candidates_wfIn hmem hpwf
    have ⟨b, hb_sound, hq⟩ := VerifM.eval_check hb φwf
    cases b with
    | true =>
      simp at hq
      exact ⟨some t, VerifM.eval_ret hq,
             fun t' ht' => by cases ht'; exact Atom.candidates_correct hmem (hb_sound rfl),
             fun t' ht' => by cases ht'; exact twf⟩
    | false =>
      simp at hq
      exact ih hq (fun p hp => hcands p (List.mem_cons_of_mem _ hp))


-- ---------------------------------------------------------------------------
-- Spatial resolution (linear search over st.owns)
-- ---------------------------------------------------------------------------

namespace SpatialAtom

/-- Two points-to atoms with semantically equal locations have equal Iris
    interpretations. -/
theorem interp_pointsTo_loc_congr {ρ : Env} {l l' v : Term .value}
    (h : Term.eval ρ l = Term.eval ρ l') :
    interp ρ (.pointsTo l v) ⊣⊢ interp ρ (.pointsTo l' v) := by
  simp only [interp, h]
  exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩

end SpatialAtom

/-- Walk a spatial context and return the index and stored value at the first
    `pointsTo` whose location the SMT solver can prove equal to `lq`. The
    returned index is into the input list; consumption is the caller's job. -/
def VerifM.findMatchIn (lq : Term .value) :
    SpatialContext → VerifM (Option (Nat × Term .value))
  | [] => pure none
  | .pointsTo l v :: rest => do
      if ← VerifM.check (.eq .value lq l) then
        pure (some (0, v))
      else
        return (← VerifM.findMatchIn lq rest).map fun (n, v') => (n + 1, v')

/-- Search the current ownership context for a `pointsTo` at location `lq`,
    returning the stored value and consuming the matched entry from `st.owns`. -/
def VerifM.findMatch (lq : Term .value) : VerifM (Option (Term .value)) := do
  let owns ← VerifM.ctx (fun st => (st.owns, st.owns))
  match ← VerifM.findMatchIn lq owns with
  | none => pure none
  | some (n, v) =>
      match SpatialContext.remove owns n with
      | none => VerifM.fatal "findMatch: returned index out of range"
      | some (_, rest) => do
          let _ ← VerifM.ctx (fun _ => ((), rest))
          pure (some v)

/-- Correctness of `findMatchIn`: on a `some (n, v)` result, `remove ctx n`
    extracts a points-to whose location the solver has proved equal to `lq`. -/
theorem VerifM.eval_findMatchIn {lq : Term .value} {ctx : SpatialContext}
    {st : TransState} {ρ : Env}
    {Q : Option (Nat × Term .value) → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.findMatchIn lq ctx) st ρ Q)
    (hlq : lq.wfIn st.decls) (hctx : ctx.wfIn st.decls) :
    ∃ result,
      Q result st ρ ∧
      (∀ n v, result = some (n, v) →
        ∃ l rest,
          SpatialContext.remove ctx n = some (.pointsTo l v, rest) ∧
          Term.eval ρ lq = Term.eval ρ l) := by
  induction ctx generalizing Q with
  | nil =>
    simp only [VerifM.findMatchIn] at h
    refine ⟨none, VerifM.eval_ret h, ?_⟩
    intros n v hvr; simp at hvr
  | cons a ctx ih =>
    cases a with
    | pointsTo l v =>
      simp only [VerifM.findMatchIn] at h
      have hb := VerifM.eval_bind _ _ _ _ h
      have hcons := (SpatialContext.wfIn_cons _ _ _).1 hctx
      have hatom := hcons.1
      have hrest := hcons.2
      have hwfeq : (Formula.eq .value lq l).wfIn st.decls := ⟨hlq, hatom.1⟩
      obtain ⟨b, hb_sound, hq⟩ := VerifM.eval_check hb hwfeq
      cases b with
      | true =>
        simp at hq
        refine ⟨some (0, v), VerifM.eval_ret hq, ?_⟩
        intros n' v' hnv
        simp at hnv
        obtain ⟨rfl, rfl⟩ := hnv
        have heq : Term.eval ρ lq = Term.eval ρ l := by
          have := hb_sound rfl
          simpa [Formula.eval] using this
        exact ⟨l, ctx, rfl, heq⟩
      | false =>
        simp at hq
        have hb' := VerifM.eval_bind _ _ _ _ hq
        obtain ⟨result', hres', hsome'⟩ := ih hb' hrest
        cases result' with
        | none =>
          simp at hres'
          refine ⟨none, VerifM.eval_ret hres', ?_⟩
          intros n' v' hnv; simp at hnv
        | some pair =>
          obtain ⟨n₀, v₀⟩ := pair
          simp at hres'
          refine ⟨some (n₀ + 1, v₀), VerifM.eval_ret hres', ?_⟩
          intros n' v' hnv
          simp at hnv
          obtain ⟨rfl, rfl⟩ := hnv
          obtain ⟨l', rest', hrem, heq⟩ := hsome' n₀ v₀ rfl
          refine ⟨l', .pointsTo l v :: rest', ?_, heq⟩
          simp [SpatialContext.remove, hrem]

/-- Correctness of `findMatch` in CPS style: the caller supplies Iris-level
    continuations for the `some` and `none` branches. On `some v`, the
    postcondition state has the matched points-to consumed from `st.owns`, and
    the caller receives separate ownership of `lq ↦ v`. -/
theorem VerifM.eval_findMatch {lq : Term .value}
    {st : TransState} {ρ : Env}
    {Q : Option (Term .value) → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.findMatch lq) st ρ Q)
    (hlq : lq.wfIn st.decls)
    (hsome : ∀ v st', Q (some v) st' ρ →
        st'.decls = st.decls → v.wfIn st.decls →
        SpatialAtom.interp ρ (.pointsTo lq v) ∗ SpatialContext.interp ρ st'.owns ∗ R ⊢ Φ)
    (hnone : Q none st ρ → SpatialContext.interp ρ st.owns ∗ R ⊢ Φ) :
    SpatialContext.interp ρ st.owns ∗ R ⊢ Φ := by
  unfold VerifM.findMatch at h
  have hb := VerifM.eval_bind _ _ _ _ h
  have ⟨hk, howns, _, _⟩ := VerifM.eval_ctx hb
  have hst_eq : ({ st with owns := st.owns } : TransState) = st := rfl
  rw [hst_eq] at hk
  have hk' := hk howns
  have hb2 := VerifM.eval_bind _ _ _ _ hk'
  obtain ⟨result, hres, hprop⟩ := eval_findMatchIn hb2 hlq howns
  cases result with
  | none =>
    simp at hres
    exact hnone (VerifM.eval_ret hres)
  | some pair =>
    obtain ⟨n, v⟩ := pair
    obtain ⟨l, rest, hrem, heq⟩ := hprop n v rfl
    have hrest_wf : SpatialContext.wfIn rest st.decls :=
      (SpatialContext.wfIn_remove howns hrem).2
    have hatom_wf : SpatialAtom.wfIn (.pointsTo l v) st.decls :=
      (SpatialContext.wfIn_remove howns hrem).1
    have hv_wf : v.wfIn st.decls := hatom_wf.2
    simp [hrem] at hres
    -- hres : (VerifM.ctx (fun _ => ((), rest)) >>= fun _ => pure (some v)).eval st ρ Q
    have hb3 := VerifM.eval_bind _ _ _ _ hres
    have ⟨hk3, _, _, _⟩ := VerifM.eval_ctx hb3
    have hk3' := hk3 hrest_wf
    have hQ : Q (some v) { st with owns := rest } ρ := VerifM.eval_ret hk3'
    have hsplit := SpatialContext.interp_remove ρ st.owns n _ _ hrem
    have hcong := SpatialAtom.interp_pointsTo_loc_congr (v := v) heq.symm
    -- goal: st.owns.interp ρ ∗ R ⊢ Φ
    -- st.owns.interp ρ ⊣⊢ (pointsTo l v).interp ρ ∗ rest.interp ρ
    --                ⊣⊢ (pointsTo lq v).interp ρ ∗ rest.interp ρ
    refine (Iris.BI.sep_mono hsplit.1 BIBase.Entails.rfl).trans ?_
    refine (Iris.BI.sep_mono (Iris.BI.sep_mono hcong.1 BIBase.Entails.rfl) BIBase.Entails.rfl).trans ?_
    refine Iris.BI.sep_assoc.1.trans ?_
    exact hsome v { st with owns := rest } hQ rfl hv_wf

/-- Like `findMatch`, but aborts with a fatal error if no matching points-to
    is found in the current ownership context. -/
def VerifM.findMatchForce (lq : Term .value) : VerifM (Term .value) := do
  match ← VerifM.findMatch lq with
  | some v => pure v
  | none => VerifM.fatal s!"no matching points-to for location"

/-- CPS correctness for `findMatchForce`: only a `some`-style continuation is
    required, since the `none` branch is discharged by the fatal error. -/
theorem VerifM.eval_findMatchForce {lq : Term .value}
    {st : TransState} {ρ : Env}
    {Q : Term .value → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.findMatchForce lq) st ρ Q)
    (hlq : lq.wfIn st.decls)
    (hsome : ∀ v st', Q v st' ρ →
        st'.decls = st.decls → v.wfIn st.decls →
        SpatialAtom.interp ρ (.pointsTo lq v) ∗ SpatialContext.interp ρ st'.owns ∗ R ⊢ Φ) :
    SpatialContext.interp ρ st.owns ∗ R ⊢ Φ := by
  unfold VerifM.findMatchForce at h
  have hb := VerifM.eval_bind _ _ _ _ h
  refine eval_findMatch (R := R) (Φ := Φ) hb hlq ?_ ?_
  · intros v st' hQ hdecls hv
    simp at hQ
    exact hsome v st' (VerifM.eval_ret hQ) hdecls hv
  · intro hQ
    simp at hQ
    exact (VerifM.eval_fatal hQ).elim


/-- Look up an atom in the assertion context.
    Tier 1: syntactic search through the context.
    Tier 2: try candidate resolutions via the SMT solver. -/
def VerifM.resolve (a : Atom τ) : VerifM (Option (Term τ)) := do
  if a.pure then
    match ← VerifM.ctxPure (a.resolve ·) with
    | some t => pure (some t)
    | none => VerifM.tryCandidates a.candidates
  else
    VerifM.fatal "here will be the points-to case"

theorem VerifM.eval_resolve {pred : Atom τ} {st : TransState} {ρ : Env}
    {Q : Option (Term τ) → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.resolve pred) st ρ Q)
    (hwf : pred.wfIn st.decls)
    (hnone : ∀ st', Q .none st' ρ → st'.decls = st.decls → SpatialContext.interp ρ st'.owns ∗ R ⊢ Φ)
    (hsome : ∀ v st', Q (.some v) st' ρ → st'.decls = st.decls → v.wfIn st.decls →
      Atom.eval pred ρ (v.eval ρ) ∗ SpatialContext.interp ρ st'.owns ∗ R ⊢ Φ) :
    SpatialContext.interp ρ st.owns ∗ R ⊢ Φ := by
  unfold VerifM.resolve at h
  cases hpure : pred.pure with
  | false =>
    simp [hpure] at h
    exact (VerifM.eval_fatal h).elim
  | true =>
    simp [hpure] at h
    have hb1 := VerifM.eval_bind _ _ _ _ h
    have ⟨hctx_q, hholds, hwfAsserts⟩ := VerifM.eval_ctxPure hb1
    cases hres : pred.resolve st.asserts with
    | some t =>
      simp [hres] at hctx_q
      have hq := VerifM.eval_ret hctx_q
      have htwf : t.wfIn st.decls := Atom.resolve_wfIn hres hwfAsserts
      have hpred : ⊢ Atom.eval pred ρ (t.eval ρ) := by
        iapply Atom.toFormula_eval_2
        ipure_intro
        exact Atom.resolve_correct hres ρ hholds
      have hframe : SpatialContext.interp ρ st.owns ∗ R ⊢
          Atom.eval pred ρ (t.eval ρ) ∗ SpatialContext.interp ρ st.owns ∗ R := by
        istart
        iintro H
        isplitr [H]
        · iapply hpred
        · iexact H
      exact hframe.trans (hsome t st hq rfl htwf)
    | none =>
      simp [hres] at hctx_q
      obtain ⟨result, hq, hresult_eval, hresult_wf⟩ :=
        eval_tryCandidates hctx_q (fun p hp => hp) hwf
      cases hr : result with
      | none =>
        have hqnone : Q .none st ρ := by simpa [hr] using hq
        exact hnone st hqnone rfl
      | some t =>
        have htwf : t.wfIn st.decls := hresult_wf t hr
        have hqsome : Q (.some t) st ρ := by simpa [hr] using hq
        have hpred : ⊢ Atom.eval pred ρ (t.eval ρ) := by
          iapply Atom.toFormula_eval_2
          ipure_intro
          exact hresult_eval t hr
        have hframe : SpatialContext.interp ρ st.owns ∗ R ⊢
            Atom.eval pred ρ (t.eval ρ) ∗ SpatialContext.interp ρ st.owns ∗ R := by
          istart
          iintro H
          isplitr [H]
          · iapply hpred
          · iexact H
        exact hframe.trans (hsome t st hqsome rfl htwf)
