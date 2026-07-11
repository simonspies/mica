-- SUMMARY: Verifier atoms for pure and spatial facts, together with their interpretations, resolution procedures, and correctness lemmas.
import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.SeparationLogic
import Mica.Verifier.Monad
import Mica.Verifier.RelationalEncoding.SkolemizeCompleteness

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Verifier.RelationalEncoding

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
  | own    : Term .value → TinyML.Typ → Atom .value
  | rel    (name : String) : Term .value → Atom .value


def Atom.pure {τ: Srt} (a : Atom τ) : Bool :=
  match a with
  | isint _ => true
  | isbool _ => true
  | isinj _ _ _ => true
  | own _ _ => false
  | rel _ _ => true


-- ---------------------------------------------------------------------------
-- Substitution
-- ---------------------------------------------------------------------------

def Atom.subst (σ : Subst) : Atom τ → Atom τ
  | .isint t  => .isint (t.subst σ)
  | .isbool t => .isbool (t.subst σ)
  | .isinj tag arity t => .isinj tag arity (t.subst σ)
  | .own t ty => .own (t.subst σ) ty
  | .rel name t => .rel name (t.subst σ)


/-- Convert an instantiated atom into the corresponding verifier context item. -/
def Atom.toItem (a : Atom τ) (t : Term τ) : CtxItem :=
  match a with
  | .isint v => .pure (.eq .value v (.unop .ofInt t))
  | .isbool v => .pure (.eq .value v (.unop .ofBool t))
  | .isinj tag arity v => .pure (.eq .value v (.unop (.ofInj tag arity) t))
  | .own l ty => .spatial (.pointsTo l t ty)
  | .rel name arg => .pure (.and (SpecFn.isDefined name arg) (.eq .value (SpecFn.call name arg) t))

-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def Atom.eval (Θ : TinyML.TypeEnv) {τ : Srt} (p : Atom τ) (ρ : VerifM.Env) : τ.denote → iProp :=
  match p with
  | isint t  => λ v => ⌜.int v = t.eval ρ.env⌝
  | isbool t => λ v => ⌜.bool v = t.eval ρ.env⌝
  | isinj tag arity t => λ v => ⌜.inj tag arity v = t.eval ρ.env⌝
  | own l ty => λ v => ∃ loc : Runtime.Location,
      ⌜l.eval ρ.env = .loc loc⌝ ∗ loc ↦ [v] ∗ TinyML.ValHasType Θ v ty
  | rel name arg => λ v =>
    ⌜(SpecFn.isDefined name arg).eval ρ.env ∧ (SpecFn.call name arg).eval ρ.env = v⌝


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
    | .eq .value v' (.unop (.ofInj tag' arity') t) =>
      if v' = v ∧ tag = tag' ∧ arity = arity' then some t else none
    | _ => none
  | .own _ _ => none
  | .rel _ _ => none

omit [MicaGS HasLC.hasLC Sig] in
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
  | own l ty => simp only [Formula.matchAtom] at h; cases h
  | rel name arg => simp only [Formula.matchAtom] at h; cases h


omit [MicaGS HasLC.hasLC Sig] in
theorem Formula.matchAtom_correct {φ : Formula} {a : Atom τ} {t : Term τ}
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
  | rel name arg => simp only [Formula.matchAtom] at h; cases h


-- ---------------------------------------------------------------------------
-- Resolution
-- ---------------------------------------------------------------------------

/-- Resolve an atom against a list of formulas. -/
def Atom.resolve (a : Atom τ) (C : List Formula) : Option (Term τ) :=
  C.findSome? (·.matchAtom a)

theorem Atom.resolve_correct (Θ : TinyML.TypeEnv) {a : Atom τ} {C : List Formula} {t : Term τ}
    (h : a.resolve C = some t) (ρ : VerifM.Env) (hC : ∀ φ ∈ C, φ.eval ρ.env) :
    ⊢ (a.toItem t).interp Θ ρ := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  rw [Formula.matchAtom_correct hφ_match]
  simpa [CtxItem.interp, hC _ hφ_mem] using (pure_intro (PROP := iProp) trivial)

omit [MicaGS HasLC.hasLC Sig] in
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
  | _, .own t ty => s!"own {t.toStringHum} : {reprStr ty}"
  | _, .rel name t => s!"call {name} {t.toStringHum}"

-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- An atom is well-formed in a signature. -/
def Atom.wfIn (Δ : Signature) : Atom τ → Prop
  | .isint t  => t.wfIn Δ
  | .isbool t => t.wfIn Δ
  | .isinj _ _ t => t.wfIn Δ
  | .own t _  => t.wfIn Δ
  | .rel name t => (SpecFn.isDefined name t).wfIn Δ ∧ (SpecFn.call name t).wfIn Δ

def Atom.checkWf (p : Atom τ) (Δ : Signature) : Except String Unit :=
  match p with
  | .isint t  => t.checkWf Δ
  | .isbool t => t.checkWf Δ
  | .isinj _ _ t => t.checkWf Δ
  | .own t _  => t.checkWf Δ
  | .rel name t => do
      (SpecFn.isDefined name t).checkWf Δ
      (SpecFn.call name t).checkWf Δ

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.checkWf_ok {p : Atom τ} {Δ : Signature} (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | isint t  => exact Term.checkWf_ok h
  | isbool t => exact Term.checkWf_ok h
  | isinj tag arity t => exact Term.checkWf_ok h
  | own t ty => exact Term.checkWf_ok h
  | rel name t =>
    have ⟨w, hd, hv⟩ := Except.bind_ok h
    exact ⟨Formula.checkWf_ok hd, Term.checkWf_ok hv⟩

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.wfIn_mono {p : Atom τ} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hmono : Δ.Subset Δ') (hwf : Δ'.wf) : p.wfIn Δ' := by
  cases p with
  | isint t  => exact Term.wfIn_mono t h hmono hwf
  | isbool t => exact Term.wfIn_mono t h hmono hwf
  | isinj tag arity t => exact Term.wfIn_mono t h hmono hwf
  | own t ty => exact Term.wfIn_mono t h hmono hwf
  | rel name t =>
    exact ⟨Formula.wfIn_mono _ h.1 hmono hwf, Term.wfIn_mono _ h.2 hmono hwf⟩

theorem Atom.eval_env_agree (Θ : TinyML.TypeEnv) {p : Atom τ} {ρ ρ' : VerifM.Env} {Δ : Signature}
    (hwf : p.wfIn Δ) (hagree : VerifM.Env.agreeOn Δ ρ ρ') : p.eval Θ ρ = p.eval Θ ρ' := by
  cases p with
  | isint t  => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | isbool t => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | isinj tag arity t => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | own l ty => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | rel name t =>
    simp only [Atom.eval]
    funext v
    rw [(Formula.eval_env_agree hwf.1 hagree),
        Term.eval_env_agree hwf.2 hagree]

omit [MicaGS HasLC.hasLC Sig] in
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
  | own l ty =>
    simp only [Atom.toItem, CtxItem.wfIn, SpatialAtom.wfIn]
    exact ⟨hp, ht⟩
  | rel name arg =>
    simp only [Atom.toItem, CtxItem.wfIn, Formula.wfIn]
    exact ⟨hp.1, hp.2, ht⟩

theorem Atom.toItem_eval (Θ : TinyML.TypeEnv) {p : Atom τ} {t : Term τ} {ρ : VerifM.Env} :
    CtxItem.interp Θ ρ (p.toItem t) ⊣⊢ p.eval Θ ρ (t.eval ρ.env) := by
  cases p with
  | isint v  => simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | isbool v => simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | isinj tag arity v => simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval, Term.eval, eq_comm]
  | own l ty =>
    simp only [Atom.eval, Atom.toItem, CtxItem.interp, SpatialAtom.interp]
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩
  | rel name arg =>
    simp [Atom.eval, Atom.toItem, CtxItem.interp, Formula.eval]

theorem Atom.eval_purePart (Θ : TinyML.TypeEnv) {p : Atom τ} {t : Term τ} {ρ : VerifM.Env} :
    p.eval Θ ρ (t.eval ρ.env) ⊢ ⌜(p.toItem t).purePart ρ⌝ := by
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
  | rel name arg =>
    simp [Atom.eval, CtxItem.purePart, Atom.toItem, Formula.eval]


-- ---------------------------------------------------------------------------
-- Substitution lemmas
-- ---------------------------------------------------------------------------

-- @agent: change eval_subst to a bi-entailment in the future.
theorem Atom.eval_subst (Θ : TinyML.TypeEnv) {p : Atom τ} {σ : Subst} {ρ : VerifM.Env} {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    (p.subst σ).eval Θ ρ = p.eval Θ (ρ.withEnv (σ.eval ρ.env)) := by
  cases p with
  | isint t =>
    funext v
    simp only [Atom.subst, Atom.eval, VerifM.Env.withEnv_env]
    rw [Term.eval_subst hp hσ hwfΔ']
  | isbool t =>
    funext v
    simp only [Atom.subst, Atom.eval, VerifM.Env.withEnv_env]
    rw [Term.eval_subst hp hσ hwfΔ']
  | isinj tag arity t =>
    funext v
    simp only [Atom.subst, Atom.eval, VerifM.Env.withEnv_env]
    rw [Term.eval_subst hp hσ hwfΔ']
  | own l ty =>
    funext v
    simp only [Atom.subst, Atom.eval, VerifM.Env.withEnv_env]
    rw [Term.eval_subst hp hσ hwfΔ']
  | rel name t =>
    funext v
    simp only [Atom.subst, Atom.eval, VerifM.Env.withEnv_env, SpecFn.isDefined,
      SpecFn.call, Formula.eval, Term.eval, UnPred.eval]
    rw [Term.eval_subst hp.2.2 hσ hwfΔ']
    simp [Subst.eval]

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.subst_wfIn {p : Atom τ} {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (p.subst σ).wfIn Δ' := by
  cases p with
  | isint t  => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isbool t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isinj tag arity t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | own t ty => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
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
def Atom.candidates : Atom τ → List (Formula × Term τ)
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
  | .rel _ _ => []

theorem Atom.candidates_correct (Θ : TinyML.TypeEnv) {a : Atom τ} {φ : Formula} {t : Term τ} {ρ : VerifM.Env}
    (hmem : (φ, t) ∈ a.candidates) (h : φ.eval ρ.env) : ⊢ (a.toItem t).interp Θ ρ := by
  cases a with
  | isint v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toItem, CtxItem.interp, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ.env <;> simp_all
    · exact (pure_intro (PROP := iProp) trivial).trans true_emp.1
  | isbool v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toItem, CtxItem.interp, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ.env <;> simp_all
    · exact (pure_intro (PROP := iProp) trivial).trans true_emp.1
  | isinj tag arity v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval, Term.eval, UnOp.eval, Const.denote] at h
    simp [toItem, CtxItem.interp, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ.env <;> simp_all
    exact (pure_intro (PROP := iProp) trivial).trans true_emp.1
  | own l ty => simp [candidates] at hmem
  | rel name arg => simp [candidates] at hmem

omit [MicaGS HasLC.hasLC Sig] in
theorem Atom.candidates_wfIn {a : Atom τ} {φ : Formula} {t : Term τ} {Δ : Signature}
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

private theorem VerifM.eval_tryCandidates (Θ : TinyML.TypeEnv)
    {candidates : List (Formula × Term τ)} {a : Atom τ}
    {st : TransState} {ρ : VerifM.Env} {Q : Option (Term τ) → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.tryCandidates candidates) st ρ Q)
    (hcands : ∀ p ∈ candidates, p ∈ a.candidates)
    (hpwf : a.wfIn st.decls) :
    ∃ result : Option (Term τ),
      Q result st ρ
      ∧ (∀ t, result = some t → ⊢ (a.toItem t).interp Θ ρ)
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
             fun t' ht' => by cases ht'; exact Atom.candidates_correct Θ hmem (hb_sound rfl),
             fun t' ht' => by cases ht'; exact twf⟩
    | false =>
      simp at hq
      exact ih hq (fun p hp => hcands p (List.mem_cons_of_mem _ hp))


-- ---------------------------------------------------------------------------
-- Spatial resolution (linear search over st.owns)
-- ---------------------------------------------------------------------------

/-- Walk a spatial context and return the index and stored value at the first
    `pointsTo` whose location the SMT solver can prove equal to `lq`. The
    returned index is into the input list; consumption is the caller's job. -/
def VerifM.findMatchIn (lq : Term .value) (ty : TinyML.Typ) :
    SpatialContext → VerifM (Option (Nat × Term .value))
  | [] => pure none
  | .pointsTo l v ty' :: rest => do
      if ty' == ty then
        if ← VerifM.test (.eq .value lq l) then
          pure (some (0, v))
        else
          return (← VerifM.findMatchIn lq ty rest).map fun (n, v') => (n + 1, v')
      else
        return (← VerifM.findMatchIn lq ty rest).map fun (n, v') => (n + 1, v')
  | .arrayPointsTo _ _ _ :: rest => do
      return (← VerifM.findMatchIn lq ty rest).map fun (n, v') => (n + 1, v')

/-- Search the current ownership context for a `pointsTo` at location `lq`,
    returning the stored value and consuming the matched entry from `st.owns`. -/
def VerifM.findMatch (lq : Term .value) (ty : TinyML.Typ) : VerifM (Option (Term .value)) := do
  let owns ← VerifM.ctx (fun st => (st.owns, st.owns))
  match ← VerifM.findMatchIn lq ty owns with
  | none => pure none
  | some (n, v) =>
      match SpatialContext.remove owns n with
      | none => VerifM.fatal "findMatch: returned index out of range"
      | some (_, rest) => do
          let _ ← VerifM.ctx (fun _ => ((), rest))
          pure (some v)

omit [MicaGS HasLC.hasLC Sig] in
/-- Correctness of `findMatchIn`: on a `some (n, v)` result, `remove ctx n`
    extracts a points-to whose location the solver has proved equal to `lq`. -/
theorem VerifM.eval_findMatchIn {lq : Term .value} {ty : TinyML.Typ} {ctx : SpatialContext}
    {st : TransState} {ρ : VerifM.Env}
    {Q : Option (Nat × Term .value) → TransState → VerifM.Env → Prop}
    (h : VerifM.eval (VerifM.findMatchIn lq ty ctx) st ρ Q)
    (hlq : lq.wfIn st.decls) (hctx : ctx.wfIn st.decls) :
    ∃ result,
      Q result st ρ ∧
      (∀ n v, result = some (n, v) →
        ∃ l rest,
          SpatialContext.remove ctx n = some (.pointsTo l v ty, rest) ∧
          Term.eval ρ.env lq = Term.eval ρ.env l) := by
  induction ctx generalizing Q with
  | nil =>
    simp only [VerifM.findMatchIn] at h
    refine ⟨none, VerifM.eval_ret h, ?_⟩
    intros n v hvr; simp at hvr
  | cons a ctx ih =>
    cases a with
    | pointsTo l v ty' =>
      simp only [VerifM.findMatchIn] at h
      have hcons := (SpatialContext.wfIn_cons _ _ _).1 hctx
      have hwfeq : (Formula.eq .value lq l).wfIn st.decls := ⟨hlq, hcons.1.1⟩
      have hrecurse :
          VerifM.eval
            (return (← VerifM.findMatchIn lq ty ctx).map fun (n, v') => (n + 1, v'))
            st ρ Q →
          ∃ result,
            Q result st ρ ∧
            (∀ n v', result = some (n, v') →
              ∃ l' rest',
                SpatialContext.remove (.pointsTo l v ty' :: ctx) n =
                  some (.pointsTo l' v' ty, rest') ∧
                Term.eval ρ.env lq = Term.eval ρ.env l') := by
        intro hrec
        have hb' := VerifM.eval_bind _ _ _ _ hrec
        obtain ⟨result', hres', hsome'⟩ := ih hb' hcons.2
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
          refine ⟨l', .pointsTo l v ty' :: rest', ?_, heq⟩
          simp [SpatialContext.remove, hrem]
      split at h
      · -- the type matches, so ask the solver whether the locations are equal
        rename_i hty
        have hb := VerifM.eval_bind _ _ _ _ h
        obtain ⟨b, hb_sound, hq⟩ := VerifM.eval_check hb hwfeq
        split at hq
        · -- the solver proved the locations equal
          rename_i hbtrue
          refine ⟨some (0, v), VerifM.eval_ret hq, ?_⟩
          intros n' v' hnv
          simp at hnv
          obtain ⟨rfl, rfl⟩ := hnv
          have heq : Term.eval ρ.env lq = Term.eval ρ.env l := by
            simpa [Formula.eval] using hb_sound hbtrue
          exact ⟨l, ctx, by simp [beq_iff_eq.mp hty], heq⟩
        · exact hrecurse hq
      · -- the type does not match, so skip the solver and keep searching
        exact hrecurse h
    | arrayPointsTo a v elemTy =>
      simp only [VerifM.findMatchIn] at h
      have hcons := (SpatialContext.wfIn_cons _ _ _).1 hctx
      have hb := VerifM.eval_bind _ _ _ _ h
      obtain ⟨result, hres, hsome⟩ := ih hb hcons.2
      cases result with
      | none =>
        simp at hres
        refine ⟨none, VerifM.eval_ret hres, ?_⟩
        intros n' v' hnv
        simp at hnv
      | some pair =>
        obtain ⟨n₀, v₀⟩ := pair
        simp at hres
        refine ⟨some (n₀ + 1, v₀), VerifM.eval_ret hres, ?_⟩
        intros n' v' hnv
        simp at hnv
        obtain ⟨rfl, rfl⟩ := hnv
        obtain ⟨l', rest', hrem, heq⟩ := hsome n₀ v₀ rfl
        refine ⟨l', .arrayPointsTo a v elemTy :: rest', ?_, heq⟩
        simp [SpatialContext.remove, hrem]

/-- Correctness of `findMatch` in CPS style: the caller supplies Iris-level
    continuations for the `some` and `none` branches. On `some v`, the
    postcondition state has the matched points-to consumed from `st.owns`, and
    the caller receives separate ownership of `lq ↦ v`. -/
theorem VerifM.eval_findMatch (Θ : TinyML.TypeEnv) {lq : Term .value} {ty : TinyML.Typ}
    {st : TransState} {ρ : VerifM.Env}
    {Q : Option (Term .value) → TransState → VerifM.Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.findMatch lq ty) st ρ Q)
    (hlq : lq.wfIn st.decls)
    (hsome : ∀ v st', Q (some v) st' ρ →
        st'.decls = st.decls → v.wfIn st.decls →
        SpatialAtom.interp Θ ρ.env (.pointsTo lq v ty) ∗ st'.sl Θ ρ ∗ R ⊢ Φ)
    (hnone : Q none st ρ → st.sl Θ ρ ∗ R ⊢ Φ) :
    st.sl Θ ρ ∗ R ⊢ Φ := by
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
    have hatom_wf : SpatialAtom.wfIn (.pointsTo l v ty) st.decls :=
      (SpatialContext.wfIn_remove howns hrem).1
    have hv_wf : v.wfIn st.decls := hatom_wf.2
    simp [hrem] at hres
    -- hres : (VerifM.ctx (fun _ => ((), rest)) >>= fun _ => pure (some v)).eval st ρ Q
    have hb3 := VerifM.eval_bind _ _ _ _ hres
    have ⟨hk3, _, _, _⟩ := VerifM.eval_ctx hb3
    have hk3' := hk3 hrest_wf
    have hQ : Q (some v) { st with owns := rest } ρ := VerifM.eval_ret hk3'
    have hsplit := SpatialContext.interp_remove Θ ρ.env st.owns n _ _ hrem
    have hcong := SpatialAtom.pointsTo_congr Θ (l := l) (l' := lq) (v := v) (v' := v)
      (ty := ty) heq.symm rfl
    -- goal: st.owns.interp ρ ∗ R ⊢ Φ
    -- st.owns.interp ρ ⊣⊢ (pointsTo l v ty).interp ρ ∗ rest.interp ρ
    --                ⊣⊢ (pointsTo lq v ty).interp ρ ∗ rest.interp ρ
    refine (Iris.BI.sep_mono hsplit.1 BIBase.Entails.rfl).trans ?_
    refine (Iris.BI.sep_mono (Iris.BI.sep_mono hcong.1 BIBase.Entails.rfl) BIBase.Entails.rfl).trans ?_
    refine Iris.BI.sep_assoc.1.trans ?_
    exact hsome v { st with owns := rest } hQ rfl hv_wf

/-- Like `findMatch`, but aborts with a fatal error if no matching points-to
    is found in the current ownership context. -/
def VerifM.findMatchForce (lq : Term .value) (ty : TinyML.Typ) : VerifM (Term .value) := do
  match ← VerifM.findMatch lq ty with
  | some v => pure v
  | none => VerifM.fatal s!"no matching points-to for location"

/-- CPS correctness for `findMatchForce`: only a `some`-style continuation is
    required, since the `none` branch is discharged by the fatal error. -/
theorem VerifM.eval_findMatchForce (Θ : TinyML.TypeEnv) {lq : Term .value} {ty : TinyML.Typ}
    {st : TransState} {ρ : VerifM.Env}
    {Q : Term .value → TransState → VerifM.Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.findMatchForce lq ty) st ρ Q)
    (hlq : lq.wfIn st.decls)
    (hsome : ∀ v st', Q v st' ρ →
        st'.decls = st.decls → v.wfIn st.decls →
        SpatialAtom.interp Θ ρ.env (.pointsTo lq v ty) ∗ st'.sl Θ ρ ∗ R ⊢ Φ) :
    st.sl Θ ρ ∗ R ⊢ Φ := by
  unfold VerifM.findMatchForce at h
  have hb := VerifM.eval_bind _ _ _ _ h
  refine eval_findMatch Θ (R := R) (Φ := Φ) hb hlq ?_ ?_
  · intros v st' hQ hdecls hv
    simp at hQ
    exact hsome v st' (VerifM.eval_ret hQ) hdecls hv
  · intro hQ
    simp at hQ
    exact (VerifM.eval_fatal hQ).elim


/-- Look up an atom in the assertion context.
    Tier 1: syntactic search through the context.
    Tier 2: try candidate resolutions via the SMT solver. -/
def VerifM.resolve : {τ : Srt} → Atom τ → VerifM (Option (Term τ))
  | _, .own l ty => do
      VerifM.findMatch l ty
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
private theorem VerifM.eval_resolve_pure (Θ : TinyML.TypeEnv) {pred : Atom τ} {st : TransState} {ρ : VerifM.Env}
    {Q : Option (Term τ) → TransState → VerifM.Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (do
      match ← VerifM.ctxPure (pred.resolve ·) with
      | some t => pure (some t)
      | none => VerifM.tryCandidates pred.candidates) st ρ Q)
    (hwf : pred.wfIn st.decls)
    (hnone : ∀ st' ρ', Q .none st' ρ' → st.decls.Subset st'.decls →
      VerifM.Env.agreeOn st.decls ρ ρ' → st'.sl Θ ρ' ∗ R ⊢ Φ)
    (hsome : ∀ v st' ρ', Q (.some v) st' ρ' → st.decls.Subset st'.decls →
      VerifM.Env.agreeOn st.decls ρ ρ' → v.wfIn st'.decls →
      Atom.eval Θ pred ρ' (v.eval ρ'.env) ∗ st'.sl Θ ρ' ∗ R ⊢ Φ) :
    st.sl Θ ρ ∗ R ⊢ Φ := by
    have hb1 := VerifM.eval_bind _ _ _ _ h
    have ⟨hctx_q, hholds, hwfAsserts⟩ := VerifM.eval_ctxPure hb1
    cases hres : pred.resolve st.asserts with
    | some t =>
      simp [hres] at hctx_q
      have hq := VerifM.eval_ret hctx_q
      have htwf : t.wfIn st.decls := Atom.resolve_wfIn hres hwfAsserts
      have hpred : ⊢ Atom.eval Θ pred ρ (t.eval ρ.env) := by
        exact (Atom.resolve_correct Θ hres ρ hholds.asserts).trans (Atom.toItem_eval Θ).1
      have hframe : st.sl Θ ρ ∗ R ⊢
          Atom.eval Θ pred ρ (t.eval ρ.env) ∗ st.sl Θ ρ ∗ R := by
        istart
        iintro H
        isplitr [H]
        · iapply hpred
        · iexact H
      exact hframe.trans (hsome t st ρ hq (Signature.Subset.refl _) VerifM.Env.agreeOn_refl htwf)
    | none =>
      simp [hres] at hctx_q
      obtain ⟨result, hq, hresult_eval, hresult_wf⟩ :=
        eval_tryCandidates Θ hctx_q (fun p hp => hp) hwf
      cases hr : result with
      | none =>
        have hqnone : Q .none st ρ := by simpa [hr] using hq
        exact hnone st ρ hqnone (Signature.Subset.refl _) VerifM.Env.agreeOn_refl
      | some t =>
        have htwf : t.wfIn st.decls := hresult_wf t hr
        have hqsome : Q (.some t) st ρ := by simpa [hr] using hq
        have hpred : ⊢ Atom.eval Θ pred ρ (t.eval ρ.env) := by
          exact (hresult_eval t hr).trans (Atom.toItem_eval Θ).1
        have hframe : st.sl Θ ρ ∗ R ⊢
            Atom.eval Θ pred ρ (t.eval ρ.env) ∗ st.sl Θ ρ ∗ R := by
          istart
          iintro H
          isplitr [H]
          · iapply hpred
          · iexact H
        exact hframe.trans (hsome t st ρ hqsome (Signature.Subset.refl _) VerifM.Env.agreeOn_refl htwf)

theorem VerifM.eval_resolve (Θ : TinyML.TypeEnv) {pred : Atom τ} {st : TransState} {ρ : VerifM.Env}
    {Q : Option (Term τ) → TransState → VerifM.Env → Prop}
    {R Φ : iProp}
    (h : VerifM.eval (VerifM.resolve pred) st ρ Q)
    (hwf : pred.wfIn st.decls)
    (hnone : ∀ st' ρ', Q .none st' ρ' → st.decls.Subset st'.decls →
      VerifM.Env.agreeOn st.decls ρ ρ' → st'.sl Θ ρ' ∗ R ⊢ Φ)
    (hsome : ∀ v st' ρ', Q (.some v) st' ρ' → st.decls.Subset st'.decls →
      VerifM.Env.agreeOn st.decls ρ ρ' → v.wfIn st'.decls →
      Atom.eval Θ pred ρ' (v.eval ρ'.env) ∗ st'.sl Θ ρ' ∗ R ⊢ Φ) :
    st.sl Θ ρ ∗ R ⊢ Φ := by
  match pred, hwf, hsome, h with
  | .own l ty, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    refine VerifM.eval_findMatch Θ (R := R) (Φ := Φ) h hwf ?_ ?_
    · intros v st' hqsome hdecls hvwf
      have hsub : st.decls.Subset st'.decls := by rw [hdecls]; exact Signature.Subset.refl _
      have hvwf' : v.wfIn st'.decls := by rw [hdecls]; exact hvwf
      have hsome' := hsome v st' ρ hqsome hsub VerifM.Env.agreeOn_refl hvwf'
      have heq : SpatialAtom.interp Θ ρ.env (.pointsTo l v ty) ⊢ Atom.eval Θ (Atom.own l ty) ρ (v.eval ρ.env) := by
        simp only [Atom.eval, SpatialAtom.interp]
        exact BIBase.Entails.rfl
      exact (sep_mono heq BIBase.Entails.rfl).trans hsome'
    · intros hqnone
      exact hnone st ρ hqnone (Signature.Subset.refl _) VerifM.Env.agreeOn_refl
  | .isint t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    exact VerifM.eval_resolve_pure Θ (pred := .isint t) h hwf hnone hsome
  | .isbool t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    exact VerifM.eval_resolve_pure Θ (pred := .isbool t) h hwf hnone hsome
  | .isinj tag arity t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    exact VerifM.eval_resolve_pure Θ (pred := .isinj tag arity t) h hwf hnone hsome
  | .rel name t, hwf, hsome, h =>
    simp only [VerifM.resolve] at h
    have hb := VerifM.eval_bind _ _ _ _ h
    obtain ⟨ok, hok_sound, hafter⟩ := VerifM.eval_check hb hwf.1
    cases ok with
    | false =>
      simp at hafter
      exact hnone st ρ (VerifM.eval_ret hafter)
        (Signature.Subset.refl _) VerifM.Env.agreeOn_refl
    | true =>
      simp at hafter
      have hdef : (SpecFn.isDefined name t).eval ρ.env := hok_sound rfl
      have hqsome : Q (some (SpecFn.call name t)) st ρ := VerifM.eval_ret hafter
      have hpred : ⊢ Atom.eval Θ (Atom.rel name t) ρ ((SpecFn.call name t).eval ρ.env) :=
        pure_intro (PROP := iProp) ⟨hdef, rfl⟩
      have hframe : st.sl Θ ρ ∗ R ⊢
          Atom.eval Θ (Atom.rel name t) ρ ((SpecFn.call name t).eval ρ.env) ∗ st.sl Θ ρ ∗ R := by
        istart
        iintro H
        isplitr [H]
        · iapply hpred
        · iexact H
      exact hframe.trans (hsome (SpecFn.call name t) st ρ hqsome
        (Signature.Subset.refl _) VerifM.Env.agreeOn_refl hwf.2)
