-- SUMMARY: Assertion language for specifications, together with its semantics, well-formedness conditions, and verifier operations.
import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.SeparationLogic
import Mica.FOL.Printing
import Mica.Verifier.Utils
import Mica.Verifier.Monad
import Mica.Verifier.Atoms
import Mica.Base.Fresh
import Mica.Base.Except

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-!
# Assertions

Defines `Assertion` (formerly `PropM`), along with its semantic interpretations
and VerifM-level operations `Assertion.assume` and `Assertion.prove`.
-/


-- ---------------------------------------------------------------------------
-- Core types
-- ---------------------------------------------------------------------------

inductive Assertion : Type → Type where
  | ret    : α → Assertion α
  | assert : Formula → Assertion α → Assertion α
  | let_   : (v : Var) → Term v.sort → Assertion α → Assertion α
  | pred   : (v : Var) → Atom v.sort → Assertion α → Assertion α
  | ite    : Formula → Assertion α → Assertion α → Assertion α


-- ---------------------------------------------------------------------------
-- Printers
-- ---------------------------------------------------------------------------

def Assertion.toStringHum {α : Type} (showA : α → String) : Assertion α → String
  | .ret a        => showA a
  | .assert φ k   => s!"assert {φ.toStringHum};\n{k.toStringHum showA}"
  | .let_ v t k   => s!"let {v.name} = {t.toStringHum} in\n{k.toStringHum showA}"
  | .pred v p k   => s!"let {v.name} <- {p.toStringHum} in\n{k.toStringHum showA}"
  | .ite φ kt ke  =>
    s!"if {φ.toStringHum} then\n{kt.toStringHum showA}\nelse\n{ke.toStringHum showA}"


-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def Assertion.pre (Θ : TinyML.TypeEnv) (Φ : α → VerifM.Env → iProp) (m : Assertion α) (ρ : VerifM.Env) : iProp :=
  (match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ.env⌝ ∗ Assertion.pre Θ Φ k ρ
  | .let_ x t k   => let v := t.eval ρ.env; Assertion.pre Θ Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => ∃ (v : x.sort.denote), p.eval Θ ρ v ∗ Assertion.pre Θ Φ k (ρ.updateConst x.sort x.name v)
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ.env⌝ -∗ Assertion.pre Θ Φ kt ρ) ∧
            (⌜¬ φ.eval ρ.env⌝ -∗ Assertion.pre Θ Φ ke ρ)))

def Assertion.post (Θ : TinyML.TypeEnv) {α} (Φ : α → VerifM.Env → iProp) (m : Assertion α) (ρ : VerifM.Env) : iProp :=
  match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ.env⌝ -∗ Assertion.post Θ Φ k ρ
  | .let_ x t k   => let v := t.eval ρ.env; Assertion.post Θ Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => iprop(∀ (v : x.sort.denote),
      p.eval Θ ρ v -∗ Assertion.post Θ Φ k (ρ.updateConst x.sort x.name v))
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ.env⌝ -∗ Assertion.post Θ Φ kt ρ) ∧
            (⌜¬ φ.eval ρ.env⌝ -∗ Assertion.post Θ Φ ke ρ))


-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- An assertion is well-formed in a signature when every formula
    and term it mentions only refers to variables/symbols from `Δ` (extended by its own
    let-bindings). The `retWf` predicate specifies an additional well-formedness
    condition on the return value; by default it is trivially true. -/
def Assertion.wfIn (retWf : α → Signature → Prop) (Δ : Signature) : Assertion α → Prop
  | .ret a       => retWf a Δ
  | .assert φ k  => φ.wfIn Δ ∧ k.wfIn retWf Δ
  | .let_ v t k  => t.wfIn Δ ∧ k.wfIn retWf (Δ.declVar v)
  | .pred v p k  => p.wfIn Δ ∧ k.wfIn retWf (Δ.declVar v)
  | .ite φ kt ke => φ.wfIn Δ ∧ kt.wfIn retWf Δ ∧ ke.wfIn retWf Δ


def Assertion.checkWf (retCheck : α → Signature → Except String Unit)
    (Δ : Signature) : Assertion α → Except String Unit
  | .ret a       => retCheck a Δ
  | .assert φ k  => do φ.checkWf Δ; k.checkWf retCheck Δ
  | .let_ v t k  => do t.checkWf Δ; k.checkWf retCheck (Δ.declVar v)
  | .pred v p k  => do p.checkWf Δ; k.checkWf retCheck (Δ.declVar v)
  | .ite φ kt ke => do φ.checkWf Δ; kt.checkWf retCheck Δ; ke.checkWf retCheck Δ

omit [MicaGS HasLC.hasLC Sig] in
theorem Assertion.checkWf_ok {m : Assertion α} {retCheck : α → Signature → Except String Unit}
    {retWf : α → Signature → Prop} {Δ : Signature}
    (hret : ∀ a Δ', retCheck a Δ' = .ok () → retWf a Δ')
    (h : m.checkWf retCheck Δ = .ok ()) : m.wfIn retWf Δ := by
  induction m generalizing Δ with
  | ret a => exact hret a Δ h
  | assert φ k ih =>
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨Formula.checkWf_ok h1, ih h2⟩
  | let_ v t k ih =>
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨Term.checkWf_ok h1, ih h2⟩
  | pred v p k ih =>
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨Atom.checkWf_ok h1, ih h2⟩
  | ite φ kt ke iht ihe =>
    have ⟨_, h1, h23⟩ := Except.bind_ok h
    have ⟨_, h2, h3⟩ := Except.bind_ok h23
    exact ⟨Formula.checkWf_ok h1, iht h2, ihe h3⟩

omit [MicaGS HasLC.hasLC Sig] in
theorem Assertion.wfIn_mono (m : Assertion α) (retWf : α → Signature → Prop)
    (hret : ∀ a Δ Δ', Δ.Subset Δ' → Δ'.wf → retWf a Δ → retWf a Δ')
    {Δ Δ' : Signature}
    (h : m.wfIn retWf Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : m.wfIn retWf Δ' := by
  induction m generalizing Δ Δ' with
  | ret a => exact hret a Δ Δ' hsub hwf h
  | assert φ k ih => exact ⟨Formula.wfIn_mono φ h.1 hsub hwf, ih h.2 hsub hwf⟩
  | let_ v t k ih =>
    exact ⟨Term.wfIn_mono t h.1 hsub hwf,
      ih h.2 (Signature.Subset.declVar hsub v) (Signature.wf_declVar hwf)⟩
  | pred v p k ih =>
    exact ⟨Atom.wfIn_mono h.1 hsub hwf,
      ih h.2 (Signature.Subset.declVar hsub v) (Signature.wf_declVar hwf)⟩
  | ite φ kt ke iht ihe =>
    exact ⟨Formula.wfIn_mono φ h.1 hsub hwf, iht h.2.1 hsub hwf, ihe h.2.2 hsub hwf⟩

-- ---------------------------------------------------------------------------
-- Environment agreement
-- ---------------------------------------------------------------------------

theorem Assertion.pre_env_agree (Θ : TinyML.TypeEnv) {m : Assertion α} {retWf : α → Signature → Prop}
    {Φ : α → VerifM.Env → iProp} {ρ ρ' : VerifM.Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : VerifM.Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    Assertion.pre Θ Φ m ρ ⊢ Assertion.pre Θ Φ m ρ' := by
  induction m generalizing Δ ρ ρ' with
  | ret a => exact hΦ a Δ ρ ρ' hwf hagree
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.pre]
    istart
    iintro ⟨%hφ, Hk⟩
    isplitr
    · ipureintro
      exact (Formula.eval_env_agree hφwf hagree).mp hφ
    · iapply (ih hkwf hagree)
      iexact Hk
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.pre]
    rw [← Term.eval_env_agree htwf hagree]
    exact ih hkwf (VerifM.Env.agreeOn_declVar hagree)
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.pre]
    istart
    iintro ⟨%w, Hsep⟩
    iexists w
    iapply (sep_mono
      (show p.eval Θ ρ w ⊢ p.eval Θ ρ' w by
        simp [(Atom.eval_env_agree Θ hpwf hagree)])
      (ih hkwf (VerifM.Env.agreeOn_declVar hagree)))
    iexact Hsep
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.pre]
    apply BI.and_intro
    · apply BI.and_elim_l.trans
      iintro Hkt
      iintro Hφ
      have hφ : BIBase.Entails (⌜φ.eval ρ'.env⌝ : iProp) ⌜φ.eval ρ.env⌝ := by
        iintro %hφ
        ipureintro
        exact (Formula.eval_env_agree hφwf hagree).mpr hφ
      iapply (iht hktwf hagree)
      iapply Hkt
      iapply hφ
      iapply Hφ
    · apply BI.and_elim_r.trans
      iintro Hke
      iintro Hnφ
      have hnφ : BIBase.Entails (⌜¬ φ.eval ρ'.env⌝ : iProp) ⌜¬ φ.eval ρ.env⌝ := by
        iintro %hnφ
        ipureintro
        exact mt (Formula.eval_env_agree hφwf hagree).mp hnφ
      iapply (ihe hkewf hagree)
      iapply Hke
      iapply hnφ
      iapply Hnφ

theorem Assertion.post_env_agree (Θ : TinyML.TypeEnv) {m : Assertion α} {retWf : α → Signature → Prop}
    {Φ : α → VerifM.Env → iProp} {ρ ρ' : VerifM.Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : VerifM.Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    Assertion.post Θ Φ m ρ ⊢ Assertion.post Θ Φ m ρ' := by
  induction m generalizing Δ ρ ρ' with
  | ret a => exact hΦ a Δ ρ ρ' hwf hagree
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    iintro H
    iintro %hφ
    have hφ' : φ.eval ρ.env := (Formula.eval_env_agree hφwf hagree).mpr hφ
    iapply (ih hkwf hagree)
    iapply H
    ipureintro
    exact hφ'
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    rw [← Term.eval_env_agree htwf hagree]
    exact ih hkwf (VerifM.Env.agreeOn_declVar hagree)
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    iintro H
    iintro %w Hw
    iapply (ih hkwf (VerifM.Env.agreeOn_declVar hagree))
    iapply H
    iapply (show p.eval Θ ρ' w ⊢ p.eval Θ ρ w by simp [(Atom.eval_env_agree Θ hpwf hagree)])
    iexact Hw
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.post]
    apply BI.and_intro
    · apply BI.and_elim_l.trans
      iintro Hkt
      iintro %hφ
      have hφ' : φ.eval ρ.env := (Formula.eval_env_agree hφwf hagree).mpr hφ
      iapply (iht hktwf hagree)
      iapply Hkt
      ipureintro
      exact hφ'
    · apply BI.and_elim_r.trans
      iintro Hke
      iintro %hnφ
      have hnφ' : ¬ φ.eval ρ.env := mt (Formula.eval_env_agree hφwf hagree).mp hnφ
      iapply (ihe hkewf hagree)
      iapply Hke
      ipureintro
      exact hnφ'

/-- Combining caller-side `pre` with verifier-side `post`. -/
theorem Assertion.pre_post_combine (Θ : TinyML.TypeEnv) {α : Type}
    {m : Assertion α}
    {Φ : α → VerifM.Env → iProp} {Ψ : α → VerifM.Env → iProp}
    {ρ : VerifM.Env}
    {R : iProp}
    (hR : ∀ (a : α) (ρ0 : VerifM.Env), Φ a ρ0 ∗ Ψ a ρ0 ⊢ R)
    : (Assertion.pre Θ Φ m ρ ∗ Assertion.post Θ Ψ m ρ) ⊢ R := by
  induction m generalizing ρ R with
  | ret a =>
    simpa [Assertion.pre, Assertion.post] using hR a ρ
  | assert φ k ih =>
    simp only [Assertion.pre, Assertion.post]
    istart
    iintro ⟨Hpre, Hpost⟩
    icases Hpre with ⟨%hφ, Hpre⟩
    iapply (ih (ρ := ρ) (R := R) hR)
    isplitl [Hpre]
    · iexact Hpre
    · iapply Hpost
      ipureintro
      exact hφ
  | let_ v t k ih =>
    simp only [Assertion.pre, Assertion.post]
    simpa using ih (ρ := ρ.updateConst v.sort v.name (t.eval ρ.env)) (R := R) hR
  | pred v p k ih =>
    simp only [Assertion.pre, Assertion.post]
    istart
    iintro ⟨Hex, Hpost⟩
    icases Hex with ⟨%u, Hpre1, Hpre2⟩
    iapply (ih (ρ := ρ.updateConst v.sort v.name u) (R := R) hR)
    isplitl [Hpre2]
    · iexact Hpre2
    · iapply Hpost
      iexact Hpre1
  | ite φ kt ke iht ihe =>
    simp only [Assertion.pre, Assertion.post]
    by_cases hφ : φ.eval ρ.env
    · istart
      iintro ⟨Hpre, Hpost⟩
      iapply (iht (ρ := ρ) (R := R) hR)
      isplitl [Hpre]
      · iapply Hpre
        ipureintro
        exact hφ
      · iapply Hpost
        ipureintro
        exact hφ
    · istart
      iintro ⟨Hpre, Hpost⟩
      iapply (ihe (ρ := ρ) (R := R) hR)
      isplitl [Hpre]
      · iapply Hpre
        ipureintro
        exact hφ
      · iapply Hpost
        ipureintro
        exact hφ

-- ---------------------------------------------------------------------------
-- VerifM helpers
-- ---------------------------------------------------------------------------

/-- Introduce preconditions: assume formulas, declare and bind let-variables.
    Threads a `FiniteSubst` that maps assertion-level names to fresh SMT-level names. -/
def Assertion.assume (σ : FiniteSubst) : Assertion α → VerifM (FiniteSubst × α)
  | .ret a => pure (σ, a)
  | .assert φ k => do
    VerifM.assume (.pure (φ.subst σ.subst σ.range.allNames))
    Assertion.assume σ k
  | .let_ v t k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.assume (.pure (.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)))
    Assertion.assume σ' k
  | .pred v p k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.acquire ((p.subst σ.subst).toItem (.const (.uninterpreted v'.name v.sort)))
    Assertion.assume σ' k
  | .ite φ kt ke => do
    let branch ← VerifM.all [true, false]
    if branch then do
      VerifM.assume (.pure (φ.subst σ.subst σ.range.allNames))
      Assertion.assume σ kt
    else do
      VerifM.assume (.pure (.not (φ.subst σ.subst σ.range.allNames)))
      Assertion.assume σ ke

/-- Assert postconditions: assert formulas, declare and bind let-variables.
    Threads a `FiniteSubst` that maps assertion-level names to fresh SMT-level names. -/
def Assertion.prove (σ : FiniteSubst) : Assertion α → VerifM (FiniteSubst × α)
  | .ret a => pure (σ, a)
  | .assert φ k => do
    VerifM.assert (φ.subst σ.subst σ.range.allNames)
    Assertion.prove σ k
  | .let_ v t k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.assume (.pure (.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)))
    Assertion.prove σ' k
  | .pred v p k => do
    match ← VerifM.resolve (p.subst σ.subst) with
    | some t =>
      let v' ← VerifM.decl (some v.name) v.sort
      let σ' := σ.rename v v'.name
      VerifM.assume (.pure (.eq v.sort (.const (.uninterpreted v'.name v.sort)) t))
      Assertion.prove σ' k
    | none => VerifM.fatal s!"could not resolve predicate `{p.toStringHum}` for {v.name}"
  | .ite φ kt ke => do
    let branch ← VerifM.all [true, false]
    if branch then do
      VerifM.assume (.pure (φ.subst σ.subst σ.range.allNames))
      Assertion.prove σ kt
    else do
      VerifM.assume (.pure (.not (φ.subst σ.subst σ.range.allNames)))
      Assertion.prove σ ke


-- ---------------------------------------------------------------------------
-- Correctness theorems
-- ---------------------------------------------------------------------------

theorem Assertion.assume_correct (Θ : TinyML.TypeEnv) (m : Assertion α) (Δ_base : Signature) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : (FiniteSubst × α) → TransState → VerifM.Env → Prop) (Φ : α → VerifM.Env → iProp) (R : iProp)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    σ.wfIn Δ_base st.decls →
    m.wfIn retWf (Δ_base.declVars σ.dom) →
    VerifM.eval (Assertion.assume σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wfIn Δ_base st'.decls →
      retWf a (Δ_base.declVars σ'.dom) →
      st'.sl Θ ρ' ∗ R ⊢ Φ a (ρ'.withEnv (σ'.subst.eval ρ'.env))) →
    st.sl Θ ρ ∗ R ⊢ Assertion.post Θ Φ m (ρ.withEnv (σ.subst.eval ρ.env)) := by
  intro hσwf hwf heval hpost
  induction m generalizing Δ_base σ st ρ Ψ with
  | ret a =>
      exact hpost _ _ _ _ (VerifM.eval_ret heval) hσwf hwf
  | assert φ k ih =>
      obtain ⟨hφwf, hkwf⟩ := hwf
      simp only [Assertion.assume] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      simp only [Assertion.post]
      iintro Howns %hφ
      have hsubst_wf_range : (φ.subst σ.subst σ.range.allNames).wfIn σ.range :=
        FiniteSubst.subst_wfIn_formula_range hσwf hφwf
      have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
        Formula.wfIn_mono _ hsubst_wf_range huse hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hσwf hφwf).mpr hφ
      have hassume := VerifM.eval_assumePure hb hsubst_wf hsubst_eval
      iapply (ih Δ_base σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hkwf hassume hpost)
      simp [TransState.sl]
  | let_ v t k ih =>
      obtain ⟨htwf, hkwf⟩ := hwf
      simp only [Assertion.assume] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hdecl := VerifM.eval_decl hb
      simp only [Assertion.post]
      set v' := st.freshConst (some v.name) v.sort
      have hv'_fresh_decls : v'.name ∉ st.decls.allNames :=
        Fresh.freshNumbers_not_mem v.name st.decls.allNames
      have hv'_fresh_range : v'.name ∉ σ.range.allNames :=
        fun h => hv'_fresh_decls (Signature.allNames_subset huse _ h)
      set u := t.eval (σ.subst.eval ρ.env)
      specialize hdecl u
      have hb2 := VerifM.eval_bind _ _ _ _ hdecl
      have ht_subst_wf : (t.subst σ.subst).wfIn st.decls :=
        FiniteSubst.subst_wfIn_term hσwf htwf
      have heq_wf : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)).wfIn
          (st.decls.addConst v') := by
        refine ⟨?_, ?_⟩
        · simp only [Term.wfIn, Const.wfIn, Signature.addConst]
          have hwf_add : (st.decls.addConst v').wf := Signature.wf_addConst hwfst hv'_fresh_decls
          refine ⟨List.Mem.head _, ?_, ?_⟩
          · intro τ' hvar
            exact hv'_fresh_decls (Signature.mem_allNames_of_var hvar)
          · intro τ' hc'
            exact Signature.wf_unique_const hwf_add (List.Mem.head _) hc'
        · exact Term.wfIn_mono _ ht_subst_wf (Signature.Subset.subset_addConst _ _)
            (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
      have heq_holds : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)).eval
          (ρ.updateConst v.sort v'.name u).env := by
        rw [Formula.eval, Term.eval, Const.denote]
        rw [FiniteSubst.eval_subst_term hσwf htwf]
        simpa [u, Env.lookupConst, Env.updateConst] using
          (Term.eval_env_agree htwf
            (FiniteSubst.eval_update_fresh (σ := σ) (ρ := ρ.env)
              (τ := v.sort) (name' := v'.name) (u := u) hσwf hv'_fresh_range))
      have hassume := VerifM.eval_assumePure hb2 heq_wf heq_holds
      set σ' := σ.rename v v'.name
      have hσ'wf : σ'.wfIn Δ_base (st.decls.addConst v') := by
        simpa [σ'] using
          (FiniteSubst.rename_wfIn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
            (v := v) (name' := v'.name) hσwf hv'_fresh_range hv'_fresh_decls)
      have hkwf' : k.wfIn retWf (Δ_base.declVars σ'.dom) := by
        simpa [σ', FiniteSubst.rename_source_eq] using hkwf
      have hih := ih Δ_base σ' { st with decls := st.decls.addConst v', asserts := _ :: st.asserts }
        (ρ.updateConst v.sort v'.name u) Ψ hσ'wf hkwf' hassume hpost
      have hinterp_bi : st.sl Θ ρ ⊣⊢ st.sl Θ (ρ.updateConst v.sort v'.name u) :=
        SpatialContext.interp_env_agree Θ (VerifM.eval.wf heval).ownsWf
          (Env.agreeOn_update_fresh_const (c := v') hv'_fresh_decls)
      exact (sep_mono hinterp_bi.1 (by
        iintro HR
        iexact HR)).trans <| hih.trans <| Assertion.post_env_agree Θ hkwf'
        (by
          simpa [σ', VerifM.Env.agreeOn, VerifM.Env.withEnv_env, VerifM.Env.updateConst] using
            (FiniteSubst.rename_agreeOn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
              (v := v) (name' := v'.name) (ρ := ρ.env) (u := u) hσwf hv'_fresh_range))
        hΦ
  | pred v p k ih =>
      obtain ⟨hpwf, hkwf⟩ := hwf
      simp only [Assertion.post]
      apply forall_intro; intro u
      iintro Howns
      iintro Hpu
      simp only [Assertion.assume] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hdecl := VerifM.eval_decl hb
      set v' := st.freshConst (some v.name) v.sort
      have hv'_fresh_decls : v'.name ∉ st.decls.allNames :=
        Fresh.freshNumbers_not_mem v.name st.decls.allNames
      have hv'_fresh_range : v'.name ∉ σ.range.allNames :=
        fun h => hv'_fresh_decls (Signature.allNames_subset huse _ h)
      specialize hdecl u
      have hb2 := VerifM.eval_bind _ _ _ _ hdecl
      have hsymbols : (Δ_base.declVars σ.dom).SymbolSubset σ.range :=
        Signature.SymbolSubset.trans declVars_symbolSubset hbase
      have hp_subst_wf_range : (p.subst σ.subst).wfIn σ.range :=
        Atom.subst_wfIn hpwf hsubst (by intro x hx; exact hx) hsymbols hrangewf
      have hp_subst_wf : (p.subst σ.subst).wfIn st.decls :=
        Atom.wfIn_mono hp_subst_wf_range huse hwfst
      have hvar_wf : (Term.const (.uninterpreted v'.name v.sort)).wfIn (st.decls.addConst v') := by
        simp only [Term.wfIn, Const.wfIn, Signature.addConst]
        have hwf_add : (st.decls.addConst v').wf := Signature.wf_addConst hwfst hv'_fresh_decls
        refine ⟨List.Mem.head _, ?_, ?_⟩
        · intro τ' hvar
          exact hv'_fresh_decls (Signature.mem_allNames_of_var hvar)
        · intro τ' hc'
          exact Signature.wf_unique_const hwf_add (List.Mem.head _) hc'
      have hitem_wf : ((p.subst σ.subst).toItem (.const (.uninterpreted v'.name v.sort))).wfIn
          (st.decls.addConst v') :=
        Atom.toItem_wfIn
          (Atom.wfIn_mono hp_subst_wf (Signature.Subset.subset_addConst _ _)
            (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint) hvar_wf
      have hpu' : p.eval Θ (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
          (p.subst σ.subst).eval Θ (ρ.updateConst v.sort v'.name u)
            ((.const (.uninterpreted v'.name v.sort) : Term v.sort).eval
              (ρ.updateConst v.sort v'.name u).env) := by
        have hconst : ((.const (.uninterpreted v'.name v.sort) : Term v.sort).eval
            (ρ.updateConst v.sort v'.name u).env) = u := by
          simp [Term.eval, Const.denote, Env.updateConst]
        rw [hconst]
        rw [Atom.eval_subst Θ hpwf hsubst hrangewf]
        have hagree := FiniteSubst.eval_update_fresh (σ := σ) (ρ := ρ.env)
          (τ := v.sort) (name' := v'.name) (u := u) hσwf hv'_fresh_range
        have heval_agree :
            p.eval Θ (ρ.withEnv (σ.subst.eval ρ.env)) =
              p.eval Θ ((ρ.updateConst v.sort v'.name u).withEnv
                (σ.subst.eval (ρ.updateConst v.sort v'.name u).env)) :=
          Atom.eval_env_agree Θ (p := p)
            (ρ := ρ.withEnv (σ.subst.eval ρ.env))
            (ρ' := (ρ.updateConst v.sort v'.name u).withEnv
              (σ.subst.eval (ρ.updateConst v.sort v'.name u).env))
            (Δ := Δ_base.declVars σ.dom) hpwf (by
              simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv_env] using hagree)
        rw [heval_agree]
        exact .rfl
      set item := (p.subst σ.subst).toItem (.const (.uninterpreted v'.name v.sort))
      set σ' := σ.rename v v'.name
      have hσ'wf : σ'.wfIn Δ_base (st.decls.addConst v') := by
        simpa [σ'] using
          (FiniteSubst.rename_wfIn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
            (v := v) (name' := v'.name) hσwf hv'_fresh_range hv'_fresh_decls)
      have hkwf' : k.wfIn retWf (Δ_base.declVars σ'.dom) := by
        simpa [σ', FiniteSubst.rename_source_eq] using hkwf
      cases hitem : item with
      | pure φ =>
        have hφ_entail : p.eval Θ (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
            ⌜φ.eval (ρ.updateConst v.sort v'.name u).env⌝ := by
          simpa [item, hitem] using
            (hpu'.trans (Atom.eval_purePart Θ (p := p.subst σ.subst)
              (t := .const (.uninterpreted v'.name v.sort))
              (ρ := (ρ.updateConst v.sort v'.name u))))
        ihave Hφ : ⌜φ.eval (ρ.updateConst v.sort v'.name u).env⌝ $$ [Hpu]
        · iapply hφ_entail
          simp [VerifM.Env.withEnv]
        icases Hφ with %hφ
        have hb2' : (VerifM.acquire (.pure φ)).eval
            { st with decls := st.decls.addConst v' } (ρ.updateConst v.sort v'.name u)
            (fun r st' ρ' => (Assertion.assume σ' k).eval st' ρ' Ψ) := by
          simpa [item, hitem] using hb2
        have hitem_wf' : (.pure φ : CtxItem).wfIn (st.decls.addConst v') := by
          simpa [item, hitem] using hitem_wf
        obtain ⟨st'', hdecls'', howns'', hassume⟩ :=
          VerifM.eval_acquire hb2' hitem_wf' hφ (by simp [CtxItem.facts])
        have hσ''wf : σ'.wfIn Δ_base st''.decls := by rw [hdecls'']; exact hσ'wf
        have hih := ih Δ_base σ' st''
          (ρ.updateConst v.sort v'.name u) Ψ hσ''wf hkwf' hassume hpost
        have hframe :
            st.sl Θ ρ ∗ R ⊢
              st''.sl Θ (ρ.updateConst v.sort v'.name u) ∗ R := by
          simp only [TransState.sl_eq, howns'', TransState.addItem]
          exact sep_mono
            (SpatialContext.interp_env_agree Θ (VerifM.eval.wf heval).ownsWf
              (Env.agreeOn_update_fresh_const (c := v') hv'_fresh_decls)).1
            (by
              iintro HR
              iexact HR)
        iapply (hframe.trans <| hih.trans <| Assertion.post_env_agree Θ hkwf'
          (by
            simpa [σ', VerifM.Env.agreeOn, VerifM.Env.withEnv_env, VerifM.Env.updateConst] using
              (FiniteSubst.rename_agreeOn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
                (v := v) (name' := v'.name) (ρ := ρ.env) (u := u) hσwf hv'_fresh_range))
          hΦ)
        iexact Howns
      | spatial a =>
        have hb2' : (VerifM.acquire (.spatial a)).eval
            { st with decls := st.decls.addConst v' } (ρ.updateConst v.sort v'.name u)
            (fun r st' ρ' => (Assertion.assume σ' k).eval st' ρ' Ψ) := by
          simpa [item, hitem] using hb2
        have hitem_wf' : (.spatial a : CtxItem).wfIn (st.decls.addConst v') := by
          simpa [item, hitem] using hitem_wf
        have hitem_interp :
            p.eval Θ (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
              CtxItem.interp Θ (ρ.updateConst v.sort v'.name u) item := by
          simpa [item] using
            (hpu'.trans (Atom.toItem_eval Θ (p := p.subst σ.subst)
              (t := .const (.uninterpreted v'.name v.sort))
              (ρ := (ρ.updateConst v.sort v'.name u))).2)
        have hspatial_interp :
            p.eval Θ (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
              SpatialAtom.interp Θ (ρ.updateConst v.sort v'.name u).env a := by
          simpa [item, hitem, CtxItem.interp] using hitem_interp
        ihave Ha : SpatialAtom.interp Θ (ρ.updateConst v.sort v'.name u).env a $$ [Hpu]
        · iapply hspatial_interp
          simp [VerifM.Env.withEnv]
        ihave Hfacts := SpatialAtom.interp_facts Θ a $$ Ha
        icases Hfacts with ⟨%hfacts, Ha⟩
        obtain ⟨st'', hdecls'', howns'', hassume⟩ :=
          VerifM.eval_acquire hb2' hitem_wf' trivial (by simpa [CtxItem.facts] using hfacts)
        have hσ''wf : σ'.wfIn Δ_base st''.decls := by rw [hdecls'']; exact hσ'wf
        have hih := ih Δ_base σ' st''
          (ρ.updateConst v.sort v'.name u) Ψ hσ''wf hkwf' hassume hpost
        have howns_agree :
            st.sl Θ ρ ⊢
              st.sl Θ (ρ.updateConst v.sort v'.name u) :=
          (SpatialContext.interp_env_agree Θ (VerifM.eval.wf heval).ownsWf
            (Env.agreeOn_update_fresh_const (c := v') hv'_fresh_decls)).1
        iapply (hih.trans <| Assertion.post_env_agree Θ hkwf'
          (by
            simpa [σ', VerifM.Env.agreeOn, VerifM.Env.withEnv_env, VerifM.Env.updateConst] using
              (FiniteSubst.rename_agreeOn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
                (v := v) (name' := v'.name) (ρ := ρ.env) (u := u) hσwf hv'_fresh_range))
          hΦ)
        simp only [TransState.sl_eq, howns'', TransState.addItem, SpatialContext.interp]
        icases Howns with ⟨HS, HR⟩
        isplitr [HR]
        · isplitl [Ha]
          · iexact Ha
          · simp only [← TransState.sl_eq]
            iapply howns_agree
            simp [TransState.sl]
        · iexact HR
  | ite φ kt ke iht ihe =>
      obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
      simp only [Assertion.assume] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hall := VerifM.eval_all hb
      simp only [Assertion.post]
      apply and_intro
      · iintro Howns %hφ
        have htrue := hall true (List.mem_cons_self ..)
        simp at htrue
        have hb2 := VerifM.eval_bind _ _ _ _ htrue
        have hsubst_wf_range : (φ.subst σ.subst σ.range.allNames).wfIn σ.range :=
          FiniteSubst.subst_wfIn_formula_range hσwf hφwf
        have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
          Formula.wfIn_mono _ hsubst_wf_range huse hwfst
        have hsubst_eval := (FiniteSubst.eval_subst_formula hσwf hφwf).mpr hφ
        have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
        iapply (iht Δ_base σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hktwf hassume hpost)
        simp [TransState.sl]
      · iintro Howns %hnφ
        have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
        simp at hfalse
        have hb2 := VerifM.eval_bind _ _ _ _ hfalse
        have hnot_wf : (Formula.not φ).wfIn (Δ_base.declVars σ.dom) := by
          simp only [Formula.wfIn]; exact hφwf
        have hsubst_wf_range : (φ.not.subst σ.subst σ.range.allNames).wfIn σ.range :=
          FiniteSubst.subst_wfIn_formula_range hσwf hnot_wf
        have hsubst_wf : (φ.not.subst σ.subst σ.range.allNames).wfIn st.decls :=
          Formula.wfIn_mono _ hsubst_wf_range huse hwfst
        have hsubst_eval := (FiniteSubst.eval_subst_formula hσwf hnot_wf).mpr hnφ
        have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
        iapply (ihe Δ_base σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hkewf hassume hpost)
        simp [TransState.sl]

theorem Assertion.prove_correct (Θ : TinyML.TypeEnv) (m : Assertion α) (Δ_base : Signature) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : (FiniteSubst × α) → TransState → VerifM.Env → Prop) (Φ : α → VerifM.Env → iProp) (R : iProp)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    σ.wfIn Δ_base st.decls →
    m.wfIn retWf (Δ_base.declVars σ.dom) →
    VerifM.eval (Assertion.prove σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wfIn Δ_base st'.decls →
      retWf a (Δ_base.declVars σ'.dom) →
      st'.sl Θ ρ' ∗ R ⊢ Φ a (ρ'.withEnv (σ'.subst.eval ρ'.env))) →
    st.sl Θ ρ ∗ R ⊢ Assertion.pre Θ Φ m (ρ.withEnv (σ.subst.eval ρ.env)) := by
  intro hσwf hwf heval hpost
  induction m generalizing Δ_base σ st ρ Ψ with
  | ret a =>
      exact hpost _ _ _ _ (VerifM.eval_ret heval) hσwf hwf
  | assert φ k ih =>
      obtain ⟨hφwf, hkwf⟩ := hwf
      simp only [Assertion.prove] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hsubst_wf_range : (φ.subst σ.subst σ.range.allNames).wfIn σ.range :=
        FiniteSubst.subst_wfIn_formula_range hσwf hφwf
      have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
        Formula.wfIn_mono _ hsubst_wf_range huse hwfst
      have hassert := VerifM.eval_assert hb hsubst_wf
      have hφ_holds := (FiniteSubst.eval_subst_formula hσwf hφwf).mp hassert.1
      show st.sl Θ ρ ∗ R ⊢
        (⌜φ.eval (σ.subst.eval ρ.env)⌝ ∗ Assertion.pre Θ Φ k (ρ.withEnv (σ.subst.eval ρ.env)) : iProp)
      istart
      iintro ⟨Howns, HR⟩
      isplitr [Howns HR]
      · ipureintro
        exact hφ_holds
      · iapply (ih Δ_base σ st ρ Ψ hσwf hkwf hassert.2 hpost)
        isplitl [Howns]
        · iexact Howns
        · iexact HR
  | let_ v t k ih =>
      obtain ⟨htwf, hkwf⟩ := hwf
      simp only [Assertion.prove] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hdecl := VerifM.eval_decl hb
      simp only [Assertion.pre]
      set v' := st.freshConst (some v.name) v.sort
      have hv'_fresh_decls : v'.name ∉ st.decls.allNames :=
        Fresh.freshNumbers_not_mem v.name st.decls.allNames
      have hv'_fresh_range : v'.name ∉ σ.range.allNames :=
        fun h => hv'_fresh_decls (Signature.allNames_subset huse _ h)
      set u := t.eval (σ.subst.eval ρ.env)
      specialize hdecl u
      have hb2 := VerifM.eval_bind _ _ _ _ hdecl
      have ht_subst_wf : (t.subst σ.subst).wfIn st.decls :=
        FiniteSubst.subst_wfIn_term hσwf htwf
      have heq_wf : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)).wfIn
          (st.decls.addConst v') := by
        refine ⟨?_, ?_⟩
        · simp only [Term.wfIn, Const.wfIn, Signature.addConst]
          have hwf_add : (st.decls.addConst v').wf := Signature.wf_addConst hwfst hv'_fresh_decls
          refine ⟨List.Mem.head _, ?_, ?_⟩
          · intro τ' hvar
            exact hv'_fresh_decls (Signature.mem_allNames_of_var hvar)
          · intro τ' hc'
            exact Signature.wf_unique_const hwf_add (List.Mem.head _) hc'
        · exact Term.wfIn_mono _ ht_subst_wf (Signature.Subset.subset_addConst _ _)
            (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
      have heq_holds : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)).eval
          (ρ.updateConst v.sort v'.name u).env := by
        rw [Formula.eval, Term.eval, Const.denote]
        rw [FiniteSubst.eval_subst_term hσwf htwf]
        simpa [u, Env.lookupConst, Env.updateConst] using
          (Term.eval_env_agree htwf
            (FiniteSubst.eval_update_fresh (σ := σ) (ρ := ρ.env)
              (τ := v.sort) (name' := v'.name) (u := u) hσwf hv'_fresh_range))
      have hassume := VerifM.eval_assumePure hb2 heq_wf heq_holds
      set σ' := σ.rename v v'.name
      have hσ'wf : σ'.wfIn Δ_base (st.decls.addConst v') := by
        simpa [σ'] using
          (FiniteSubst.rename_wfIn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
            (v := v) (name' := v'.name) hσwf hv'_fresh_range hv'_fresh_decls)
      have hkwf' : k.wfIn retWf (Δ_base.declVars σ'.dom) := by
        simpa [σ', FiniteSubst.rename_source_eq] using hkwf
      have hih := ih Δ_base σ' { st with decls := st.decls.addConst v', asserts := _ :: st.asserts }
        (ρ.updateConst v.sort v'.name u) Ψ hσ'wf hkwf' hassume hpost
      have hinterp_bi : st.sl Θ ρ ⊣⊢ st.sl Θ (ρ.updateConst v.sort v'.name u) :=
        SpatialContext.interp_env_agree Θ (VerifM.eval.wf heval).ownsWf
          (Env.agreeOn_update_fresh_const (c := v') hv'_fresh_decls)
      exact (sep_mono hinterp_bi.1 (by
        iintro HR
        iexact HR)).trans <| hih.trans <| Assertion.pre_env_agree Θ hkwf'
        (by
          simpa [σ', VerifM.Env.agreeOn, VerifM.Env.withEnv_env, VerifM.Env.updateConst] using
            (FiniteSubst.rename_agreeOn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
              (v := v) (name' := v'.name) (ρ := ρ.env) (u := u) hσwf hv'_fresh_range))
        hΦ
  | pred v p k ih =>
      obtain ⟨hpwf, hkwf⟩ := hwf
      simp only [Assertion.prove] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hsymbols : (Δ_base.declVars σ.dom).SymbolSubset σ.range :=
        Signature.SymbolSubset.trans declVars_symbolSubset hbase
      have hpwf_range : (p.subst σ.subst).wfIn σ.range :=
        Atom.subst_wfIn hpwf hsubst (by intro x hx; exact hx) hsymbols hrangewf
      have hpwf_decls : (p.subst σ.subst).wfIn st.decls :=
        Atom.wfIn_mono hpwf_range huse hwfst
      exact VerifM.eval_resolve Θ hb hpwf_decls
        (fun st' ρ' hq hsub hagree => by
          exact (VerifM.eval_fatal hq).elim)
        (fun t st' ρ' hq hsub hagree htwf => by
          simp [Assertion.pre]
          have hwfst' : st'.decls.wf := (VerifM.eval.wf hq).namesDisjoint
          have hσwf_st' : σ.wfIn Δ_base st'.decls := by
            rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
            exact ⟨hsubst, hbase, huse.trans hsub, hsrcwf, hrangewf, hwfst', hbasevars⟩
          istart
          iintro H
          icases H with ⟨Hpred, Howns, HR⟩
          iexists (t.eval ρ'.env)
          isplitr [Howns HR]
          · have hpred_subst :
                (p.subst σ.subst).eval Θ ρ' (t.eval ρ'.env) ⊢
                  p.eval Θ (ρ'.withEnv (σ.subst.eval ρ'.env)) (t.eval ρ'.env) := by
              simpa [VerifM.Env.withEnv] using
                (show (p.subst σ.subst).eval Θ ρ' (t.eval ρ'.env) ⊢
                    p.eval Θ (ρ'.withEnv (σ.subst.eval ρ'.env)) (t.eval ρ'.env) by
                  rw [Atom.eval_subst Θ hpwf hsubst hrangewf]
                  exact BIBase.Entails.rfl)
            have hagree_subst :
                VerifM.Env.agreeOn (Δ_base.declVars σ.dom)
                  (ρ.withEnv (σ.subst.eval ρ.env))
                  (ρ'.withEnv (σ.subst.eval ρ'.env)) := by
              exact FiniteSubst.eval_agreeOn hσwf hagree
            have hpred_transport :
                p.eval Θ (ρ'.withEnv (σ.subst.eval ρ'.env)) (t.eval ρ'.env) ⊢
                  p.eval Θ (ρ.withEnv (σ.subst.eval ρ.env)) (t.eval ρ'.env) := by
              rw [Atom.eval_env_agree Θ hpwf (VerifM.Env.agreeOn_symm hagree_subst)]
              exact BIBase.Entails.rfl
            iapply hpred_transport
            iapply hpred_subst
            iexact Hpred
          · have hb2 := VerifM.eval_bind _ _ _ _ hq
            have hdecl := VerifM.eval_decl hb2
            set v' := st'.freshConst (some v.name) v.sort
            have hv'_fresh_decls : v'.name ∉ st'.decls.allNames :=
              Fresh.freshNumbers_not_mem v.name st'.decls.allNames
            have hv'_fresh_range : v'.name ∉ σ.range.allNames := by
              intro h
              apply hv'_fresh_decls
              exact Signature.allNames_subset (huse.trans hsub) _ h
            specialize hdecl (t.eval ρ'.env)
            have hb3 := VerifM.eval_bind _ _ _ _ hdecl
            have heq_wf : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) t).wfIn
                (st'.decls.addConst v') := by
              refine ⟨?_, ?_⟩
              · simp only [Term.wfIn, Const.wfIn, Signature.addConst]
                have hwf_add : (st'.decls.addConst v').wf := Signature.wf_addConst hwfst' hv'_fresh_decls
                refine ⟨List.Mem.head _, ?_, ?_⟩
                · intro τ' hvar
                  exact hv'_fresh_decls (Signature.mem_allNames_of_var hvar)
                · intro τ' hc'
                  exact Signature.wf_unique_const hwf_add (List.Mem.head _) hc'
              · exact Term.wfIn_mono _ htwf (Signature.Subset.subset_addConst _ _)
                  (TransState.freshConst.wf _ (VerifM.eval.wf hq)).namesDisjoint
            have heq_holds : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) t).eval
                (ρ'.updateConst v.sort v'.name (t.eval ρ'.env)).env := by
              simp only [Formula.eval, Term.eval, Const.denote]
              simpa [Env.lookupConst, Env.updateConst] using
                (Term.eval_env_agree htwf
                  (Env.agreeOn_update_fresh_const (c := v') hv'_fresh_decls))
            have hassume := VerifM.eval_assumePure hb3 heq_wf heq_holds
            set σ' := σ.rename v v'.name
            have hσ'wf : σ'.wfIn Δ_base (st'.decls.addConst v') := by
              simpa [σ'] using
                (FiniteSubst.rename_wfIn (σ := σ) (Δ_base := Δ_base) (Δ_use := st'.decls)
                  (v := v) (name' := v'.name) hσwf_st' hv'_fresh_range hv'_fresh_decls)
            have hkwf' : k.wfIn retWf (Δ_base.declVars σ'.dom) := by
              simpa [σ', FiniteSubst.rename_source_eq] using hkwf
            have hih := ih Δ_base σ' { st' with decls := st'.decls.addConst v', asserts := _ :: st'.asserts }
              (ρ'.updateConst v.sort v'.name (t.eval ρ'.env)) Ψ hσ'wf hkwf' hassume hpost
            have hinterp_bi : st'.sl Θ ρ' ⊣⊢ st'.sl Θ (ρ'.updateConst v.sort v'.name (t.eval ρ'.env)) :=
              SpatialContext.interp_env_agree Θ (VerifM.eval.wf hq).ownsWf
                (Env.agreeOn_update_fresh_const (c := v') hv'_fresh_decls)
            have hframe : st'.sl Θ ρ' ∗ R ⊢
                st'.sl Θ (ρ'.updateConst v.sort v'.name (t.eval ρ'.env)) ∗ R := by
              exact sep_mono hinterp_bi.1 (by
                iintro HR
                iexact HR)
            iapply (hframe.trans <| hih.trans <| Assertion.pre_env_agree Θ hkwf'
              (by
                have hrename := (FiniteSubst.rename_agreeOn (σ := σ) (Δ_base := Δ_base) (Δ_use := st'.decls)
                    (v := v) (name' := v'.name) (ρ := ρ'.env) (u := t.eval ρ'.env)
                    hσwf_st' hv'_fresh_range)
                have hsubst_agree : _root_.Env.agreeOn (Δ_base.declVars σ.dom)
                    (σ.subst.eval ρ'.env) (σ.subst.eval ρ.env) := by
                  exact _root_.Env.agreeOn_symm (FiniteSubst.eval_agreeOn hσwf (by
                    simpa [VerifM.Env.agreeOn] using hagree))
                have hsubst_update : _root_.Env.agreeOn ((Δ_base.declVars σ.dom).declVar v)
                    ((σ.subst.eval ρ'.env).updateConst v.sort v.name (t.eval ρ'.env))
                    ((σ.subst.eval ρ.env).updateConst v.sort v.name (t.eval ρ'.env)) :=
                  _root_.Env.agreeOn_declVar hsubst_agree
                have hsubst_update' : _root_.Env.agreeOn (Δ_base.declVars (σ.rename v v'.name).dom)
                    ((σ.subst.eval ρ'.env).updateConst v.sort v.name (t.eval ρ'.env))
                    ((σ.subst.eval ρ.env).updateConst v.sort v.name (t.eval ρ'.env)) :=
                  _root_.Env.agreeOn_mono
                    (FiniteSubst.rename_source_subset_rev σ Δ_base v v'.name) hsubst_update
                have htrans := _root_.Env.agreeOn_trans hrename hsubst_update'
                simpa [σ', VerifM.Env.agreeOn, VerifM.Env.withEnv_env, VerifM.Env.updateConst] using htrans)
              hΦ)
            isplitl [Howns]
            · simp [TransState.sl]
            · iexact HR)
  | ite φ kt ke iht ihe =>
      obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
      simp only [Assertion.prove] at heval
      rcases hσwf with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hσwf : σ.wfIn Δ_base st.decls := ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
      have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hall := VerifM.eval_all hb
      simp only [Assertion.pre]
      iintro Howns
      apply BI.and_intro
      · apply wand_intro
        iintro H
        icases H with ⟨Howns, %hφ⟩
        have htrue := hall true (List.mem_cons_self ..)
        simp at htrue
        have hb2 := VerifM.eval_bind _ _ _ _ htrue
        have hsubst_wf_range : (φ.subst σ.subst σ.range.allNames).wfIn σ.range :=
          FiniteSubst.subst_wfIn_formula_range hσwf hφwf
        have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
          Formula.wfIn_mono _ hsubst_wf_range huse hwfst
        have hsubst_eval := (FiniteSubst.eval_subst_formula hσwf hφwf).mpr hφ
        have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
        iapply (iht Δ_base σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hktwf hassume hpost)
        simp [TransState.sl]
      · apply wand_intro
        iintro H
        icases H with ⟨Howns, %hnφ⟩
        have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
        simp at hfalse
        have hb2 := VerifM.eval_bind _ _ _ _ hfalse
        have hnot_wf : (Formula.not φ).wfIn (Δ_base.declVars σ.dom) := by
          simp only [Formula.wfIn]; exact hφwf
        have hsubst_wf_range : (φ.not.subst σ.subst σ.range.allNames).wfIn σ.range :=
          FiniteSubst.subst_wfIn_formula_range hσwf hnot_wf
        have hsubst_wf : (φ.not.subst σ.subst σ.range.allNames).wfIn st.decls :=
          Formula.wfIn_mono _ hsubst_wf_range huse hwfst
        have hsubst_eval := (FiniteSubst.eval_subst_formula hσwf hnot_wf).mpr hnφ
        have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
        iapply (ihe Δ_base σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hkewf hassume hpost)
        simp [TransState.sl]
