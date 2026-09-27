-- SUMMARY: Verifier operations on atoms: context items, resolution procedures, well-formedness, and correctness lemmas.
import Mica.SourceTinyML.Semantics
import Mica.Engine.SMTLIB
import Mica.FirstOrderLogic.Subst
import Mica.Verifier.SpatialAtom
import Mica.Verifier.Ownership
import Mica.Verifier.RelationalEncoding.Skolemize

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Verifier.RelationalEncoding

/-!
# Atoms

Verifier-side operations on `Atom`: substitution, the corresponding context
item, resolution against the pure context, well-formedness, and the lemmas
relating `Atom.eval` to the spatial interpretation. The syntax lives in
`Mica/SourceTinyML/Assertions.lean` and the semantics in
`Mica/SourceTinyML/Semantics.lean`.
-/


-- ---------------------------------------------------------------------------
-- Substitution
-- ---------------------------------------------------------------------------

def Atom.subst (σ : Subst) : Atom TinyML.Typ τ → Atom TinyML.Typ τ
  | .isint t  => .isint (t.subst σ)
  | .isbool t => .isbool (t.subst σ)
  | .isinj tag arity t => .isinj tag arity (t.subst σ)
  | .own t ty => .own (t.subst σ) ty
  | .arr t ty => .arr (t.subst σ) ty
  | .rel name t => .rel name (t.subst σ)


/-- Convert an instantiated atom into the corresponding verifier context item. -/
def Atom.toItem (a : Atom TinyML.Typ τ) (t : Term τ) : CtxItem :=
  match a with
  | .isint v => .pure (.eq .value v (.unop .ofInt t))
  | .isbool v => .pure (.eq .value v (.unop .ofBool t))
  | .isinj tag arity v => .pure (.eq .value v (.unop (.ofInj tag arity) t))
  | .own l ty => .spatial (.pointsTo l t ty)
  | .arr a ty => .spatial (.arrayPointsTo a t ty)
  | .rel name arg => .pure (.and (SpecFn.isDefined name arg) (.eq .value (SpecFn.call name arg) t))

/-- Try to match a formula against an atom, returning the extracted term if it matches. -/
def Formula.matchAtom (φ : Formula) (a : Atom TinyML.Typ τ) : Option (Term τ) :=
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
    | .eq .value v' (.unop (.ofInj tag' arity') t) =>
      if v' = v ∧ tag = tag' ∧ arity = arity' then some t else none
    | _ => none
  | .own _ _ => none
  | .arr _ _ => none
  | .rel _ _ => none

omit [MicaGS HasLC.hasLC Sig] in
theorem Formula.matchAtom_wfIn {φ : Formula} {a : Atom TinyML.Typ τ} {t : Term τ} {Δ : Signature}
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
  | own l ty => simp only [Formula.matchAtom] at h; cases h
  | arr a ty => simp only [Formula.matchAtom] at h; cases h
  | rel name arg => simp only [Formula.matchAtom] at h; cases h


omit [MicaGS HasLC.hasLC Sig] in
theorem Formula.matchAtom_correct {φ : Formula} {a : Atom TinyML.Typ τ} {t : Term τ}
    (h : φ.matchAtom a = some t) : a.toItem t = .pure φ := by
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
  | own l ty => simp only [Formula.matchAtom] at h; cases h
  | arr a ty => simp only [Formula.matchAtom] at h; cases h
  | rel name arg => simp only [Formula.matchAtom] at h; cases h


-- ---------------------------------------------------------------------------
-- Resolution
-- ---------------------------------------------------------------------------

/-- Resolve an atom against a list of formulas. -/
def Atom.resolve (a : Atom TinyML.Typ τ) (C : List Formula) : Option (Term τ) :=
  C.findSome? (·.matchAtom a)

theorem Atom.resolve_correct (W : TinyML.World) {a : Atom TinyML.Typ τ} {C : List Formula} {t : Term τ}
    (h : a.resolve C = some t) (ρ : Env) (hC : ∀ φ ∈ C, φ.eval ρ) :
    ⊢ (a.toItem t).interp W ρ := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  rw [Formula.matchAtom_correct hφ_match]
  simpa [CtxItem.interp, hC _ hφ_mem] using (pure_intro (PROP := iProp) trivial)

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.resolve_wfIn {a : Atom TinyML.Typ τ} {C : List Formula} {t : Term τ} {Δ : Signature}
    (h : a.resolve C = some t) (hwf : ∀ φ ∈ C, φ.wfIn Δ) :
    t.wfIn Δ := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  exact Formula.matchAtom_wfIn hφ_match (hwf _ hφ_mem)


-- ---------------------------------------------------------------------------
-- Printer
-- ---------------------------------------------------------------------------

def Atom.toString : {τ : Srt} → Atom TinyML.Typ τ → String
  | _, .isint  t => s!"isint {t.toSMTLIB}"
  | _, .isbool t => s!"isbool {t.toSMTLIB}"
  | _, .isinj tag arity t => s!"isinj {tag}/{arity} {t.toSMTLIB}"
  | _, .own t ty => s!"own {t.toSMTLIB} : {reprStr ty}"
  | _, .arr t ty => s!"arr {t.toSMTLIB} : {reprStr ty}"
  | _, .rel name t => s!"call {name} {t.toSMTLIB}"

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.toItem_wfIn {p : Atom TinyML.Typ τ} {t : Term τ} {Δ : Signature}
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
  | own l ty =>
    simp only [Atom.toItem, CtxItem.wfIn, SpatialAtom.wfIn]
    exact ⟨hp, ht⟩
  | arr a ty =>
    simp only [Atom.toItem, CtxItem.wfIn, SpatialAtom.wfIn]
    exact ⟨hp, ht⟩
  | rel name arg =>
    simp only [Atom.toItem, CtxItem.wfIn, Formula.wfIn]
    exact ⟨hp.1, hp.2, ht⟩

theorem Atom.toItem_eval (W : TinyML.World) {p : Atom TinyML.Typ τ} {t : Term τ} {ρ : Env} :
    CtxItem.interp W ρ (p.toItem t) ⊣⊢ p.eval (TinyML.ValHasType W) ρ (t.eval ρ) := by
  cases p with
  | isint v  => simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | isbool v => simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | isinj tag arity v => simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | own l ty =>
    simp only [Atom.eval, Atom.toItem, CtxItem.interp, SpatialAtom.interp]
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩
  | arr a ty =>
    simp only [Atom.eval, Atom.toItem, CtxItem.interp, SpatialAtom.interp]
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩
  | rel name arg =>
    simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval]

theorem Atom.eval_purePart {V : TinyML.ValueRelation} {p : Atom TinyML.Typ τ} {t : Term τ}
    {ρ : Env} :
    p.eval V ρ (t.eval ρ) ⊢ ⌜(p.toItem t).purePart ρ⌝ := by
  cases p with
  | isint v =>
    simp [Atom.eval, CtxItem.purePart, Atom.toItem, Formula.eval, Term.eval, eq_comm]
  | isbool v =>
    simp [Atom.eval, CtxItem.purePart, Atom.toItem, Formula.eval, Term.eval, eq_comm]
  | isinj tag arity v =>
    simp [Atom.eval, CtxItem.purePart, Atom.toItem, Formula.eval, Term.eval, eq_comm]
  | own l ty =>
    simp only [Atom.toItem, CtxItem.purePart]
    exact pure_intro trivial
  | arr a ty =>
    simp only [Atom.toItem, CtxItem.purePart]
    exact pure_intro trivial
  | rel name arg =>
    simp [Atom.eval, CtxItem.purePart, Atom.toItem, Formula.eval]


-- ---------------------------------------------------------------------------
-- Substitution lemmas
-- ---------------------------------------------------------------------------

theorem Atom.eval_subst {V : TinyML.ValueRelation} {p : Atom TinyML.Typ τ} {σ : Subst}
    {ρ : Env} {Δ Δ' : Signature} (v : τ.denote)
    (hp : p.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    (p.subst σ).eval V ρ v ⊣⊢ p.eval V ((σ.eval ρ)) v := by
  cases p with
  | isint t =>
    simp only [Atom.subst, Atom.eval, ]
    rw [Term.eval_subst hp hσ hwfΔ']
    exact .rfl
  | isbool t =>
    simp only [Atom.subst, Atom.eval, ]
    rw [Term.eval_subst hp hσ hwfΔ']
    exact .rfl
  | isinj tag arity t =>
    simp only [Atom.subst, Atom.eval, ]
    rw [Term.eval_subst hp hσ hwfΔ']
    exact .rfl
  | own l ty =>
    simp only [Atom.subst, Atom.eval, ]
    rw [Term.eval_subst hp hσ hwfΔ']
    exact .rfl
  | arr a ty =>
    simp only [Atom.subst, Atom.eval, ]
    rw [Term.eval_subst hp hσ hwfΔ']
    exact .rfl
  | rel name t =>
    simp only [Atom.subst, Atom.eval, SpecFn.isDefined,
      SpecFn.call, Formula.eval, Term.eval, UnPred.eval]
    rw [Term.eval_subst hp.2.2 hσ hwfΔ']
    simp only [Subst.eval]
    exact .rfl

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.subst_wfIn {p : Atom TinyML.Typ τ} {σ : Subst} {dom : List Var} {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (p.subst σ).wfIn Δ' := by
  cases p with
  | isint t  => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isbool t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isinj tag arity t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | own t ty => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | arr t ty => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | rel name t =>
    refine ⟨?_, ?_⟩
    · exact SpecFn.isDefined_wfIn (hsymbols.unaryRel _ hp.1.1.1) hwf
        (Term.subst_wfIn hp.1.2 hσ hdom hsymbols hwf)
    · exact SpecFn.call_wfIn (hsymbols.unary _ hp.2.1.1) hwf
        (Term.subst_wfIn hp.2.2 hσ hdom hsymbols hwf)


-- ---------------------------------------------------------------------------
-- Candidates: guarded resolution alternatives
-- ---------------------------------------------------------------------------

/-- Candidate resolutions for an atom, each guarded by a provability condition.
    Each pair `(φ, t)` means: if `φ` is provable, then `t` resolves the atom. -/
def Atom.candidates : Atom TinyML.Typ τ → List (Formula × Term τ)
  | .isint  v => [(.unpred .isInt v, .unop .toInt v)]
  | .isbool v => [(.unpred .isBool v, .unop .toBool v)]
  | .isinj tag arity v =>
      [(.and
          (.unpred .isOfInj v)
          (.and
            (.eq .int (.unop .tagOf v) (.const (.i tag)))
            (.eq .int (.unop .arityOf v) (.const (.i arity)))),
        .unop .payloadOf v)]
  | .own _ _ => []
  | .arr _ _ => []
  | .rel _ _ => []

theorem Atom.candidates_correct (W : TinyML.World) {a : Atom TinyML.Typ τ} {φ : Formula} {t : Term τ} {ρ : Env}
    (hmem : (φ, t) ∈ a.candidates) (h : φ.eval ρ) : ⊢ (a.toItem t).interp W ρ := by
  cases a with
  | isint v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toItem, CtxItem.interp, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all
    · exact (pure_intro (PROP := iProp) trivial).trans true_emp.1
  | isbool v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toItem, CtxItem.interp, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all
    · exact (pure_intro (PROP := iProp) trivial).trans true_emp.1
  | isinj tag arity v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval, Term.eval, UnOp.eval, Const.eval] at h
    simp [toItem, CtxItem.interp, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all
    exact (pure_intro (PROP := iProp) trivial).trans true_emp.1
  | own l ty => simp [candidates] at hmem
  | arr a ty => simp [candidates] at hmem
  | rel name arg => simp [candidates] at hmem

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.candidates_wfIn {a : Atom TinyML.Typ τ} {φ : Formula} {t : Term τ} {Δ : Signature}
    (hmem : (φ, t) ∈ a.candidates) (h : a.wfIn Δ) : φ.wfIn Δ ∧ t.wfIn Δ := by
  cases a with
  | isint v =>
    simp [candidates] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨⟨trivial, h⟩, ⟨trivial, h⟩⟩
  | isbool v =>
    simp [candidates] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨⟨trivial, h⟩, ⟨trivial, h⟩⟩
  | isinj tag arity v =>
    simp [candidates] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    refine ⟨⟨⟨trivial, h⟩, ?_⟩, ⟨trivial, h⟩⟩
    exact ⟨⟨⟨trivial, h⟩, trivial⟩, ⟨⟨trivial, h⟩, trivial⟩⟩
  | own l ty => simp [candidates] at hmem
  | arr a ty => simp [candidates] at hmem
  | rel name arg => simp [candidates] at hmem


-- ---------------------------------------------------------------------------
-- VerifM integration
-- ---------------------------------------------------------------------------

/-- Try candidate resolutions in order, checking each guard via the SMT solver. -/
def VerifM.tryCandidates : List (Formula × Term τ) → VerifM (Option (Term τ))
  | [] => pure none
  | (φ, t) :: rest => do
    if ← VerifM.check .high φ then pure (some t)
    else VerifM.tryCandidates rest

private theorem VerifM.eval_tryCandidates (W : TinyML.World)
    {candidates : List (Formula × Term τ)} {a : Atom TinyML.Typ τ}
    {st : TransState} {ρ : Env} {Q : Option (Term τ) → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.tryCandidates candidates) st ρ Q)
    (hcands : ∀ p ∈ candidates, p ∈ a.candidates)
    (hpwf : a.wfIn st.decls) :
    ∃ result : Option (Term τ),
      Q result st ρ
      ∧ (∀ t, result = some t → ⊢ (a.toItem t).interp W ρ)
      ∧ (∀ t, result = some t → t.wfIn st.decls) := by
  induction candidates with
  | nil =>
    simp [tryCandidates] at h
    exact ⟨none, VerifM.eval_ret h,
           fun _ ht => absurd ht (by simp), fun _ ht => absurd ht (by simp)⟩
  | cons c rest ih =>
    obtain ⟨φ, t⟩ := c
    simp [tryCandidates] at h
    have hb := VerifM.eval_bind h
    have hmem := hcands (φ, t) (List.mem_cons_self ..)
    have ⟨φwf, twf⟩ := Atom.candidates_wfIn hmem hpwf
    have ⟨b, hb_sound, hq⟩ := VerifM.eval_check hb φwf
    cases b with
    | true =>
      simp at hq
      exact ⟨some t, VerifM.eval_ret hq,
             fun t' ht' => by cases ht'; exact Atom.candidates_correct W hmem (hb_sound rfl),
             fun t' ht' => by cases ht'; exact twf⟩
    | false =>
      simp at hq
      exact ih hq (fun p hp => hcands p (List.mem_cons_of_mem _ hp))


omit [MicaGS HasLC.hasLC Sig] in
/-- A valid proposition can be introduced on the left of any separating conjunction. -/
private theorem sep_intro_valid_left {P Q : iProp} (h : ⊢ P) : Q ⊢ P ∗ Q :=
  emp_sep.2.trans (sep_mono_left h)

/-- Look up an atom in the assertion context.
    Tier 1: syntactic search through the context.
    Tier 2: try candidate resolutions via the SMT solver. -/
def VerifM.resolve : {τ : Srt} → Atom TinyML.Typ τ → VerifM (Option (Term τ))
  | _, .own l ty => do
      VerifM.findMatch .ref l ty
  | _, .arr a ty => do
      VerifM.findMatch .array a ty
  | _, .rel name arg => do
      if ← VerifM.check .high (SpecFn.isDefined name arg) then
        pure (some (SpecFn.call name arg))
      else
        pure none
  | _, a => do
      match ← VerifM.ctxPure (a.resolve ·) with
      | some t => pure (some t)
      | none => VerifM.tryCandidates a.candidates

/-- Helper: resolution of a pure atom via formula matching or SMT candidates. -/
private theorem VerifM.eval_resolve_pure (W : TinyML.World) {pred : Atom TinyML.Typ τ} {st : TransState} {ρ : Env}
    {Q : Option (Term τ) → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (do
      match ← VerifM.ctxPure (pred.resolve ·) with
      | some t => pure (some t)
      | none => VerifM.tryCandidates pred.candidates) st ρ Q)
    (hwf : pred.wfIn st.decls)
    (hnone : ∀ st' ρ', Q .none st' ρ' → st.decls.Subset st'.decls →
      Env.agreeOn st.decls ρ ρ' → st'.sl W ρ' ∗ R ⊢ Φ)
    (hsome : ∀ v st' ρ', Q (.some v) st' ρ' → st.decls.Subset st'.decls →
      Env.agreeOn st.decls ρ ρ' → v.wfIn st'.decls →
      Atom.eval (TinyML.ValHasType W) pred ρ' (v.eval ρ') ∗ st'.sl W ρ' ∗ R ⊢ Φ) :
    st.sl W ρ ∗ R ⊢ Φ := by
    have hb1 := VerifM.eval_bind h
    have ⟨hctx_q, hholds, hwfAsserts⟩ := VerifM.eval_ctxPure hb1
    cases hres : pred.resolve st.asserts with
    | some t =>
      simp [hres] at hctx_q
      have hq := VerifM.eval_ret hctx_q
      have htwf : t.wfIn st.decls := Atom.resolve_wfIn hres hwfAsserts
      have hpred : ⊢ Atom.eval (TinyML.ValHasType W) pred ρ (t.eval ρ) :=
        (Atom.resolve_correct W hres ρ hholds.asserts).trans (Atom.toItem_eval W).1
      exact (sep_intro_valid_left hpred).trans
        (hsome t st ρ hq (Signature.Subset.refl _) Env.agreeOn_refl htwf)
    | none =>
      simp [hres] at hctx_q
      obtain ⟨result, hq, hresult_eval, hresult_wf⟩ :=
        eval_tryCandidates W hctx_q (fun p hp => hp) hwf
      cases hr : result with
      | none =>
        have hqnone : Q .none st ρ := by simpa [hr] using hq
        exact hnone st ρ hqnone (Signature.Subset.refl _) Env.agreeOn_refl
      | some t =>
        have htwf : t.wfIn st.decls := hresult_wf t hr
        have hqsome : Q (.some t) st ρ := by simpa [hr] using hq
        have hpred : ⊢ Atom.eval (TinyML.ValHasType W) pred ρ (t.eval ρ) :=
          (hresult_eval t hr).trans (Atom.toItem_eval W).1
        exact (sep_intro_valid_left hpred).trans
          (hsome t st ρ hqsome (Signature.Subset.refl _) Env.agreeOn_refl htwf)

private theorem VerifM.eval_resolve_spatial (W : TinyML.World) {k : SpatialAtom.Kind}
    {pred : Atom TinyML.Typ .value} {tq : Term .value} {ty : TinyML.Typ}
    {st : TransState} {ρ : Env} {Q : Option (Term .value) → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.findMatch k tq ty) st ρ Q)
    (hwf : tq.wfIn st.decls)
    (hinterp : ∀ v : Term .value, SpatialAtom.interp W ρ (k.atom tq v ty) ⊢
      Atom.eval (TinyML.ValHasType W) pred ρ (v.eval ρ))
    (hnone : ∀ st' ρ', Q .none st' ρ' → st.decls.Subset st'.decls →
      Env.agreeOn st.decls ρ ρ' → st'.sl W ρ' ∗ R ⊢ Φ)
    (hsome : ∀ v st' ρ', Q (.some v) st' ρ' → st.decls.Subset st'.decls →
      Env.agreeOn st.decls ρ ρ' → v.wfIn st'.decls →
      Atom.eval (TinyML.ValHasType W) pred ρ' (v.eval ρ') ∗ st'.sl W ρ' ∗ R ⊢ Φ) :
    st.sl W ρ ∗ R ⊢ Φ := by
  refine VerifM.eval_findMatch W (R := R) (Φ := Φ) h hwf ?_ ?_
  · intros v st' hqsome hdecls hvwf
    have hsub : st.decls.Subset st'.decls := by rw [hdecls]; exact Signature.Subset.refl _
    have hvwf' : v.wfIn st'.decls := by rw [hdecls]; exact hvwf
    exact (sep_mono (hinterp v) BIBase.Entails.rfl).trans
      (hsome v st' ρ hqsome hsub Env.agreeOn_refl hvwf')
  · intros hqnone
    exact hnone st ρ hqnone (Signature.Subset.refl _) Env.agreeOn_refl

theorem VerifM.eval_resolve (W : TinyML.World) {pred : Atom TinyML.Typ τ} {st : TransState} {ρ : Env}
    {Q : Option (Term τ) → TransState → Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.resolve pred) st ρ Q)
    (hwf : pred.wfIn st.decls)
    (hnone : ∀ st' ρ', Q .none st' ρ' → st.decls.Subset st'.decls →
      Env.agreeOn st.decls ρ ρ' → st'.sl W ρ' ∗ R ⊢ Φ)
    (hsome : ∀ v st' ρ', Q (.some v) st' ρ' → st.decls.Subset st'.decls →
      Env.agreeOn st.decls ρ ρ' → v.wfIn st'.decls →
      Atom.eval (TinyML.ValHasType W) pred ρ' (v.eval ρ') ∗ st'.sl W ρ' ∗ R ⊢ Φ) :
    st.sl W ρ ∗ R ⊢ Φ := by
  match pred, hwf, hsome, h with
  | .own l ty, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    refine VerifM.eval_resolve_spatial W h hwf (fun v => ?_) hnone hsome
    simp only [SpatialAtom.Kind.atom, Atom.eval, SpatialAtom.interp]
    exact BIBase.Entails.rfl
  | .arr a ty, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    refine VerifM.eval_resolve_spatial W h hwf (fun v => ?_) hnone hsome
    simp only [SpatialAtom.Kind.atom, Atom.eval, SpatialAtom.interp]
    exact BIBase.Entails.rfl
  | .isint t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    exact VerifM.eval_resolve_pure W (pred := .isint t) h hwf hnone hsome
  | .isbool t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    exact VerifM.eval_resolve_pure W (pred := .isbool t) h hwf hnone hsome
  | .isinj tag arity t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    exact VerifM.eval_resolve_pure W (pred := .isinj tag arity t) h hwf hnone hsome
  | .rel name t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    have hb := VerifM.eval_bind h
    obtain ⟨ok, hok_sound, hafter⟩ := VerifM.eval_check hb hwf.1
    cases ok with
    | false =>
      simp at hafter
      exact hnone st ρ (VerifM.eval_ret hafter)
        (Signature.Subset.refl _) Env.agreeOn_refl
    | true =>
      simp at hafter
      have hdef : (SpecFn.isDefined name t).eval ρ := hok_sound rfl
      have hqsome : Q (some (SpecFn.call name t)) st ρ := VerifM.eval_ret hafter
      have hpred : ⊢ Atom.eval (TinyML.ValHasType W) (Atom.rel name t) ρ ((SpecFn.call name t).eval ρ) :=
        pure_intro (PROP := iProp) ⟨hdef, rfl⟩
      exact (sep_intro_valid_left hpred).trans (hsome (SpecFn.call name t) st ρ hqsome
        (Signature.Subset.refl _) Env.agreeOn_refl hwf.2)
