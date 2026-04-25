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

def Assertion.pre (Φ : α → VerifM.Env → iProp) (m : Assertion α) (ρ : VerifM.Env) : iProp :=
  (match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ.env⌝ ∗ Assertion.pre Φ k ρ
  | .let_ x t k   => let v := t.eval ρ.env; Assertion.pre Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => ∃ (v : x.sort.denote), p.eval ρ v ∗ Assertion.pre Φ k (ρ.updateConst x.sort x.name v)
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ.env⌝ -∗ Assertion.pre Φ kt ρ) ∧
            (⌜¬ φ.eval ρ.env⌝ -∗ Assertion.pre Φ ke ρ)))

def Assertion.post {α} (Φ : α → VerifM.Env → iProp) (m : Assertion α) (ρ : VerifM.Env) : iProp :=
  match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ.env⌝ -∗ Assertion.post Φ k ρ
  | .let_ x t k   => let v := t.eval ρ.env; Assertion.post Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => iprop(∀ (v : x.sort.denote),
      p.eval ρ v -∗ Assertion.post Φ k (ρ.updateConst x.sort x.name v))
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ.env⌝ -∗ Assertion.post Φ kt ρ) ∧
            (⌜¬ φ.eval ρ.env⌝ -∗ Assertion.post Φ ke ρ))


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

theorem Assertion.checkWf_ok {m : Assertion α} {retCheck : α → Signature → Except String Unit}
    {retWf : α → Signature → Prop} {Δ : Signature}
    (hret : ∀ a Δ', retCheck a Δ' = .ok () → retWf a Δ')
    (h : m.checkWf retCheck Δ = .ok ()) : m.wfIn retWf Δ := by
  induction m generalizing Δ with
  | ret a => exact hret a Δ h
  | assert φ k ih =>
    have ⟨h1, h2⟩ := bind_ok h
    exact ⟨Formula.checkWf_ok h1, ih h2⟩
  | let_ v t k ih =>
    have ⟨h1, h2⟩ := bind_ok h
    exact ⟨Term.checkWf_ok h1, ih h2⟩
  | pred v p k ih =>
    have ⟨h1, h2⟩ := bind_ok h
    exact ⟨Atom.checkWf_ok h1, ih h2⟩
  | ite φ kt ke iht ihe =>
    have ⟨h1, h23⟩ := bind_ok h
    have ⟨h2, h3⟩ := bind_ok h23
    exact ⟨Formula.checkWf_ok h1, iht h2, ihe h3⟩

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

theorem Assertion.pre_env_agree {m : Assertion α} {retWf : α → Signature → Prop}
    {Φ : α → VerifM.Env → iProp} {ρ ρ' : VerifM.Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : VerifM.Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    Assertion.pre Φ m ρ ⊢ Assertion.pre Φ m ρ' := by
  induction m generalizing Δ ρ ρ' with
  | ret a => exact hΦ a Δ ρ ρ' hwf hagree
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.pre]
    istart
    iintro ⟨%hφ, Hk⟩
    isplitr
    · ipure_intro
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
      (show p.eval ρ w ⊢ p.eval ρ' w by
        simp [(Atom.eval_env_agree hpwf hagree)])
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
        ipure_intro
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
        ipure_intro
        exact mt (Formula.eval_env_agree hφwf hagree).mp hnφ
      iapply (ihe hkewf hagree)
      iapply Hke
      iapply hnφ
      iapply Hnφ

theorem Assertion.post_env_agree {m : Assertion α} {retWf : α → Signature → Prop}
    {Φ : α → VerifM.Env → iProp} {ρ ρ' : VerifM.Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : VerifM.Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    Assertion.post Φ m ρ ⊢ Assertion.post Φ m ρ' := by
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
    ipure_intro
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
    iapply (show p.eval ρ' w ⊢ p.eval ρ w by simp [(Atom.eval_env_agree hpwf hagree)])
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
      ipure_intro
      exact hφ'
    · apply BI.and_elim_r.trans
      iintro Hke
      iintro %hnφ
      have hnφ' : ¬ φ.eval ρ.env := mt (Formula.eval_env_agree hφwf hagree).mp hnφ
      iapply (ihe hkewf hagree)
      iapply Hke
      ipure_intro
      exact hnφ'

/-- Combining caller-side `pre` with verifier-side `post`. -/
theorem Assertion.pre_post_combine {α : Type}
    {m : Assertion α}
    {Φ : α → VerifM.Env → iProp} {Ψ : α → VerifM.Env → iProp}
    {ρ : VerifM.Env}
    {R : iProp}
    (hR : ∀ (a : α) (ρ0 : VerifM.Env), Φ a ρ0 ∗ Ψ a ρ0 ⊢ R)
    : (Assertion.pre Φ m ρ ∗ Assertion.post Ψ m ρ) ⊢ R := by
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
      ipure_intro
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
        ipure_intro
        exact hφ
      · iapply Hpost
        ipure_intro
        exact hφ
    · istart
      iintro ⟨Hpre, Hpost⟩
      iapply (ihe (ρ := ρ) (R := R) hR)
      isplitl [Hpre]
      · iapply Hpre
        ipure_intro
        exact hφ
      · iapply Hpost
        ipure_intro
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
    VerifM.assume ((p.subst σ.subst).toItem (.const (.uninterpreted v'.name v.sort)))
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
    | none => VerifM.fatal s!"could not resolve type predicate for {v.name}"
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

theorem Assertion.assume_correct (m : Assertion α) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : (FiniteSubst × α) → TransState → VerifM.Env → Prop) (Φ : α → VerifM.Env → iProp) (R : iProp)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    σ.wf st.decls →
    (Signature.ofVars σ.dom).wf →
    m.wfIn retWf (Signature.ofVars σ.dom) →
    VerifM.eval (Assertion.assume σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wf st'.decls → (Signature.ofVars σ'.dom).wf →
      retWf a (Signature.ofVars σ'.dom) →
      st'.sl ρ' ∗ R ⊢ Φ a (ρ'.withEnv (σ'.subst.eval ρ'.env))) →
    st.sl ρ ∗ R ⊢ Assertion.post Φ m (ρ.withEnv (σ.subst.eval ρ.env)) := by
  intro hσwf hdomwf hwf heval hpost
  have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
  induction m generalizing σ st ρ Ψ with
  | ret a =>
    exact hpost _ _ _ _ (VerifM.eval_ret heval) hσwf hdomwf hwf
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    simp only [Assertion.post]
    iintro Howns %hφ
    have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
      FiniteSubst.subst_wfIn_formula hσwf hφwf hwfst
    have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1 hdomwf hσwf.2.2).mpr hφ
    have hassume := VerifM.eval_assumePure hb hsubst_wf hsubst_eval
    iapply (ih σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hkwf hassume hpost hwfst)
    simp [TransState.sl]
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hdecl := VerifM.eval_decl hb
    simp only [Assertion.post]
    set v' := st.freshConst (some v.name) v.sort
    have hv'_fresh_decls : v'.name ∉ st.decls.allNames :=
      fresh_not_mem (addNumbers (v.name)) (st.decls.allNames) (addNumbers_injective _)
    have hv'_fresh_range : v'.name ∉ σ.range.allNames :=
      fun h => hv'_fresh_decls (Signature.allNames_subset hσwf.2.1 _ h)
    set u := t.eval (σ.subst.eval ρ.env)
    specialize hdecl u
    have hb2 := VerifM.eval_bind _ _ _ _ hdecl
    -- Show the equality formula is well-formed and holds
    have ht_subst_wf_range : (t.subst σ.subst).wfIn σ.range :=
      Term.subst_wfIn htwf hσwf.1 (by simp [Signature.ofVars])
        (Signature.SymbolSubset.ofVars _ _)
        hσwf.2.2
    have ht_subst_wf : (t.subst σ.subst).wfIn st.decls :=
      Term.wfIn_mono _ ht_subst_wf_range hσwf.2.1 hwfst
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
      · exact Term.wfIn_mono _ ht_subst_wf (Signature.Subset.subset_addConst _ _) (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
    have heq_holds : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)).eval
        (ρ.updateConst v.sort v'.name u).env := by
      rw [Formula.eval, Term.eval, Const.denote]
      rw [Term.eval_subst htwf hσwf.1 hσwf.2.2]
      simpa [u, Env.lookupConst, Env.updateConst] using
        (Term.eval_env_agree htwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range))
    have hassume := VerifM.eval_assumePure hb2 heq_wf heq_holds
    -- Apply IH with σ' = σ.rename v v'.name
    set σ' := σ.rename v v'.name
    have hσ'wf : σ'.wf (st.decls.addConst v') :=
      by simpa [σ'] using (FiniteSubst.rename_wf (σ := σ) (v := v) (name' := v'.name) hσwf hv'_fresh_range)
    have hσ'domwf : (Signature.ofVars σ'.dom).wf := by
      simpa [σ'] using (FiniteSubst.rename_dom_wf (σ := σ) (v := v) (name' := v'.name) hdomwf)
    have hkwf' : k.wfIn retWf (Signature.ofVars σ'.dom) := by
      simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using hkwf
    have hih := ih σ' { st with decls := st.decls.addConst v', asserts := _ :: st.asserts }
      (ρ.updateConst v.sort v'.name u) Ψ hσ'wf hσ'domwf hkwf' hassume hpost
        (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
    have hinterp_bi : st.sl ρ ⊣⊢ st.sl (ρ.updateConst v.sort v'.name u) :=
      SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf
        (agreeOn_update_fresh_const (c := v') hv'_fresh_decls)
    exact (sep_mono hinterp_bi.1 (by
      iintro HR
      iexact HR)).trans <| hih.trans <| Assertion.post_env_agree hkwf
      (by
        simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
          (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
      hΦ
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hall := VerifM.eval_all hb
    simp only [Assertion.post]
    apply and_intro
    · iintro Howns %hφ
      have htrue := hall true (List.mem_cons_self ..)
      simp at htrue
      have hb2 := VerifM.eval_bind _ _ _ _ htrue
      have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hφwf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1 hdomwf hσwf.2.2).mpr hφ
      have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
      iapply (iht σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hktwf hassume hpost hwfst)
      simp [TransState.sl]
    · iintro Howns %hnφ
      have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
      simp at hfalse
      have hb2 := VerifM.eval_bind _ _ _ _ hfalse
      have hnot_wf : (Formula.not φ).wfIn (Signature.ofVars σ.dom) := by
        simp only [Formula.wfIn]; exact hφwf
      have hsubst_wf : (φ.not.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hnot_wf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hnot_wf hσwf.1 hdomwf hσwf.2.2).mpr hnφ
      have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
      iapply (ihe σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hkewf hassume hpost hwfst)
      simp [TransState.sl]
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    apply forall_intro; intro u
    iintro Howns
    iintro Hpu
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hdecl := VerifM.eval_decl hb
    set v' := st.freshConst (some v.name) v.sort
    have hv'_fresh_decls : v'.name ∉ st.decls.allNames :=
      fresh_not_mem (addNumbers (v.name)) (st.decls.allNames) (addNumbers_injective _)
    have hv'_fresh_range : v'.name ∉ σ.range.allNames :=
      fun h => hv'_fresh_decls (Signature.allNames_subset hσwf.2.1 _ h)
    specialize hdecl u
    have hb2 := VerifM.eval_bind _ _ _ _ hdecl
    -- Show the atom formula is well-formed and holds
    have hp_subst_wf_range : (p.subst σ.subst).wfIn σ.range :=
      Atom.subst_wfIn hpwf hσwf.1 (by simp [Signature.ofVars])
        (Signature.SymbolSubset.ofVars _ _)
        hσwf.2.2
    have hp_subst_wf : (p.subst σ.subst).wfIn st.decls :=
      Atom.wfIn_mono hp_subst_wf_range hσwf.2.1 hwfst
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
    have hpu' : p.eval (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢ (p.subst σ.subst).eval (ρ.updateConst v.sort v'.name u)
        ((.const (.uninterpreted v'.name v.sort) : Term v.sort).eval (ρ.updateConst v.sort v'.name u).env) := by
      have hconst : ((.const (.uninterpreted v'.name v.sort) : Term v.sort).eval
          (ρ.updateConst v.sort v'.name u).env) = u := by
        simp [Term.eval, Const.denote, Env.updateConst]
      rw [hconst]
      rw [Atom.eval_subst hpwf hσwf.1 hσwf.2.2]
      have hagree := FiniteSubst.eval_update_fresh (σ := σ) (ρ := ρ.env)
        (τ := v.sort) (name' := v'.name) (u := u) hσwf.1 hv'_fresh_range
      have heval_agree :
          p.eval (ρ.withEnv (σ.subst.eval ρ.env)) =
            p.eval ((ρ.updateConst v.sort v'.name u).withEnv
              (σ.subst.eval (ρ.updateConst v.sort v'.name u).env)) :=
        Atom.eval_env_agree (p := p)
          (ρ := ρ.withEnv (σ.subst.eval ρ.env))
          (ρ' := (ρ.updateConst v.sort v'.name u).withEnv
            (σ.subst.eval (ρ.updateConst v.sort v'.name u).env))
          (Δ := Signature.ofVars σ.dom) hpwf (by
            simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv_env] using hagree)
      rw [heval_agree]
      exact .rfl
    set item := (p.subst σ.subst).toItem (.const (.uninterpreted v'.name v.sort))
    set σ' := σ.rename v v'.name
    have hσ'wf : σ'.wf (st.decls.addConst v') :=
      by simpa [σ'] using (FiniteSubst.rename_wf (σ := σ) (v := v) (name' := v'.name) hσwf hv'_fresh_range)
    have hσ'domwf : (Signature.ofVars σ'.dom).wf := by
      simpa [σ'] using (FiniteSubst.rename_dom_wf (σ := σ) (v := v) (name' := v'.name) hdomwf)
    have hkwf' : k.wfIn retWf (Signature.ofVars σ'.dom) := by
      simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using hkwf
    cases hitem : item with
    | pure φ =>
      have hφ_entail : p.eval (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
          ⌜φ.eval (ρ.updateConst v.sort v'.name u).env⌝ := by
        simpa [item, hitem] using
          (hpu'.trans (Atom.eval_purePart (p := p.subst σ.subst)
            (t := .const (.uninterpreted v'.name v.sort))
            (ρ := (ρ.updateConst v.sort v'.name u))))
      ihave Hφ : ⌜φ.eval (ρ.updateConst v.sort v'.name u).env⌝ $$ [Hpu]
      · iapply hφ_entail
        simp [VerifM.Env.withEnv]
      icases Hφ with %hφ
      have hb2' : (VerifM.assume (.pure φ)).eval
          { st with decls := st.decls.addConst v' } (ρ.updateConst v.sort v'.name u)
          (fun r st' ρ' => (Assertion.assume σ' k).eval st' ρ' Ψ) := by
        simpa [item, hitem] using hb2
      have hitem_wf' : (.pure φ : CtxItem).wfIn (st.decls.addConst v') := by
        simpa [item, hitem] using hitem_wf
      have hassume := VerifM.eval_assume hb2' hitem_wf' hφ
      have hih := ih σ' (TransState.addItem { st with decls := st.decls.addConst v' } (.pure φ))
        (ρ.updateConst v.sort v'.name u) Ψ hσ'wf hσ'domwf hkwf' hassume hpost
          (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
      have hframe :
          st.sl ρ ∗ R ⊢
            (TransState.addItem { st with decls := st.decls.addConst v' } (.pure φ)).sl
              (ρ.updateConst v.sort v'.name u) ∗ R := by
        simp [TransState.addItem]
        exact sep_mono
          (SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf
            (agreeOn_update_fresh_const (c := v') hv'_fresh_decls)).1
          (by
            iintro HR
            iexact HR)
      iapply (hframe.trans <| hih.trans <| Assertion.post_env_agree hkwf'
        (by
          simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
            (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
        hΦ)
      iexact Howns
    | spatial a =>
      have hb2' : (VerifM.assume (.spatial a)).eval
          { st with decls := st.decls.addConst v' } (ρ.updateConst v.sort v'.name u)
          (fun r st' ρ' => (Assertion.assume σ' k).eval st' ρ' Ψ) := by
        simpa [item, hitem] using hb2
      have hitem_wf' : (.spatial a : CtxItem).wfIn (st.decls.addConst v') := by
        simpa [item, hitem] using hitem_wf
      have hassume := VerifM.eval_assume hb2' hitem_wf' trivial
      have hih := ih σ' (TransState.addItem { st with decls := st.decls.addConst v' } (.spatial a))
        (ρ.updateConst v.sort v'.name u) Ψ hσ'wf hσ'domwf hkwf' hassume hpost
          (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
      have hitem_interp :
          p.eval (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
            CtxItem.interp (ρ.updateConst v.sort v'.name u) item := by
        simpa [item] using
          (hpu'.trans (Atom.toItem_eval (p := p.subst σ.subst)
            (t := .const (.uninterpreted v'.name v.sort))
            (ρ := (ρ.updateConst v.sort v'.name u))).2)
      have hspatial_interp :
          p.eval (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
            SpatialAtom.interp (ρ.updateConst v.sort v'.name u).env a := by
        simpa [item, hitem, CtxItem.interp] using hitem_interp
      have howns_agree :
          st.sl ρ ⊢
            st.sl (ρ.updateConst v.sort v'.name u) :=
        (SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf
          (agreeOn_update_fresh_const (c := v') hv'_fresh_decls)).1
      iapply (hih.trans <| Assertion.post_env_agree hkwf'
        (by
          simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
            (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
        hΦ)
      simp [TransState.addItem]
      icases Howns with ⟨HS, HR⟩
      isplitr [HR]
      · isplitr [HS]
        · have hspatial_interp' :
            p.eval (ρ.withEnv (σ.subst.eval ρ.env)) u ⊢
              SpatialAtom.interp (Env.updateConst ρ.env v.sort v'.name u) a := by
            simpa [VerifM.Env.updateConst] using hspatial_interp
          iapply hspatial_interp'
          simp [VerifM.Env.withEnv]
        · have howns_agree' :
            st.sl ρ ⊢ SpatialContext.interp (Env.updateConst ρ.env v.sort v'.name u) st.owns := by
            simpa [TransState.sl, VerifM.Env.updateConst] using howns_agree
          iapply howns_agree'
          simp [TransState.sl]
      · iexact HR

theorem Assertion.prove_correct (m : Assertion α) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : (FiniteSubst × α) → TransState → VerifM.Env → Prop) (Φ : α → VerifM.Env → iProp) (R : iProp)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → VerifM.Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ ⊢ Φ a ρ₂) :
    σ.wf st.decls →
    (Signature.ofVars σ.dom).wf →
    m.wfIn retWf (Signature.ofVars σ.dom) →
    VerifM.eval (Assertion.prove σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wf st'.decls → (Signature.ofVars σ'.dom).wf →
      retWf a (Signature.ofVars σ'.dom) →
      st'.sl ρ' ∗ R ⊢ Φ a (ρ'.withEnv (σ'.subst.eval ρ'.env))) →
    st.sl ρ ∗ R ⊢ Assertion.pre Φ m (ρ.withEnv (σ.subst.eval ρ.env)) := by
  intro hσwf hdomwf hwf heval hpost
  have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
  induction m generalizing σ st ρ Ψ with
  | ret a =>
    exact hpost _ _ _ _ (VerifM.eval_ret heval) hσwf hdomwf hwf
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.prove] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
      FiniteSubst.subst_wfIn_formula hσwf hφwf hwfst
    have hassert := VerifM.eval_assert hb hsubst_wf
    have hφ_holds := (FiniteSubst.eval_subst_formula hφwf hσwf.1 hdomwf hσwf.2.2).mp hassert.1
    show st.sl ρ ∗ R ⊢
      (⌜φ.eval (σ.subst.eval ρ.env)⌝ ∗ Assertion.pre Φ k (ρ.withEnv (σ.subst.eval ρ.env)) : iProp)
    istart
    iintro ⟨Howns, HR⟩
    isplitr [Howns HR]
    · ipure_intro
      exact hφ_holds
    · iapply (ih σ st ρ Ψ hσwf hdomwf hkwf hassert.2 hpost hwfst)
      isplitl [Howns]
      · iexact Howns
      · iexact HR
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.prove] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hdecl := VerifM.eval_decl hb
    simp only [Assertion.pre]
    set v' := st.freshConst (some v.name) v.sort
    have hv'_fresh_decls : v'.name ∉ st.decls.allNames :=
      fresh_not_mem (addNumbers (v.name)) (st.decls.allNames) (addNumbers_injective _)
    have hv'_fresh_range : v'.name ∉ σ.range.allNames :=
      fun h => hv'_fresh_decls (Signature.allNames_subset hσwf.2.1 _ h)
    set u := t.eval (σ.subst.eval ρ.env)
    specialize hdecl u
    have hb2 := VerifM.eval_bind _ _ _ _ hdecl
    have ht_subst_wf_range : (t.subst σ.subst).wfIn σ.range :=
      Term.subst_wfIn htwf hσwf.1 (by simp [Signature.ofVars])
        (Signature.SymbolSubset.ofVars _ _)
        hσwf.2.2
    have ht_subst_wf : (t.subst σ.subst).wfIn st.decls :=
      Term.wfIn_mono _ ht_subst_wf_range hσwf.2.1 hwfst
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
      · exact Term.wfIn_mono _ ht_subst_wf (Signature.Subset.subset_addConst _ _) (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
    have heq_holds : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst)).eval
        (ρ.updateConst v.sort v'.name u).env := by
      rw [Formula.eval, Term.eval, Const.denote]
      rw [Term.eval_subst htwf hσwf.1 hσwf.2.2]
      simpa [u, Env.lookupConst, Env.updateConst] using
        (Term.eval_env_agree htwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range))
    have hassume := VerifM.eval_assumePure hb2 heq_wf heq_holds
    set σ' := σ.rename v v'.name
    have hσ'wf : σ'.wf (st.decls.addConst v') :=
      by simpa [σ'] using (FiniteSubst.rename_wf (σ := σ) (v := v) (name' := v'.name) hσwf hv'_fresh_range)
    have hσ'domwf : (Signature.ofVars σ'.dom).wf := by
      simpa [σ'] using (FiniteSubst.rename_dom_wf (σ := σ) (v := v) (name' := v'.name) hdomwf)
    have hkwf' : k.wfIn retWf (Signature.ofVars σ'.dom) := by
      simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using hkwf
    have hih := ih σ' { st with decls := st.decls.addConst v', asserts := _ :: st.asserts }
      (ρ.updateConst v.sort v'.name u) Ψ hσ'wf hσ'domwf hkwf' hassume hpost
        (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
    have hinterp_bi : st.sl ρ ⊣⊢ st.sl (ρ.updateConst v.sort v'.name u) :=
      SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf
        (agreeOn_update_fresh_const (c := v') hv'_fresh_decls)
    exact (sep_mono hinterp_bi.1 (by
      iintro HR
      iexact HR)).trans <| hih.trans <| Assertion.pre_env_agree hkwf'
      (by
        simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
          (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
      hΦ
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.prove] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hpwf_range : (p.subst σ.subst).wfIn σ.range :=
      Atom.subst_wfIn hpwf hσwf.1 (by simp [Signature.ofVars])
        (Signature.SymbolSubset.ofVars _ _)
        hσwf.2.2
    have hpwf_decls : (p.subst σ.subst).wfIn st.decls :=
      Atom.wfIn_mono hpwf_range hσwf.2.1 hwfst
    exact VerifM.eval_resolve hb hpwf_decls
      (fun st' hq hdecls => by
        simp at hq
        exact (VerifM.eval_fatal hq).elim)
      (fun t st' hq hdecls htwf => by
        simp [Assertion.pre]
        have hwfst' : st'.decls.wf := by simpa [hdecls] using hwfst
        have htwf' : t.wfIn st'.decls := by simpa [hdecls] using htwf
        istart
        iintro H
        icases H with ⟨Hpred, Howns, HR⟩
        iexists (t.eval ρ.env)
        isplitr [Howns HR]
        · have hpred_subst :
              (p.subst σ.subst).eval ρ (t.eval ρ.env) ⊢
                p.eval (ρ.withEnv (σ.subst.eval ρ.env)) (t.eval ρ.env) := by
              simpa [VerifM.Env.withEnv] using
                (show (p.subst σ.subst).eval ρ (t.eval ρ.env) ⊢
                    p.eval (ρ.withEnv (σ.subst.eval ρ.env)) (t.eval ρ.env) by
                  rw [Atom.eval_subst hpwf hσwf.1 hσwf.2.2]
                  exact BIBase.Entails.rfl)
          iapply hpred_subst
          iexact Hpred
        · have hb2 := VerifM.eval_bind _ _ _ _ hq
          have hdecl := VerifM.eval_decl hb2
          set v' := st'.freshConst (some v.name) v.sort
          have hv'_fresh_decls : v'.name ∉ st'.decls.allNames :=
            fresh_not_mem (addNumbers (v.name)) (st'.decls.allNames) (addNumbers_injective _)
          have hv'_fresh_range : v'.name ∉ σ.range.allNames := by
            intro h
            apply hv'_fresh_decls
            rw [hdecls]
            exact Signature.allNames_subset hσwf.2.1 _ h
          specialize hdecl (t.eval ρ.env)
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
            · exact Term.wfIn_mono _ htwf' (Signature.Subset.subset_addConst _ _)
                (TransState.freshConst.wf _ (VerifM.eval.wf hq)).namesDisjoint
          have heq_holds : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) t).eval
              (ρ.updateConst v.sort v'.name (t.eval ρ.env)).env := by
            simp only [Formula.eval, Term.eval, Const.denote]
            simpa [Env.lookupConst, Env.updateConst] using
              (Term.eval_env_agree htwf' (agreeOn_update_fresh_const hv'_fresh_decls))
          have hassume := VerifM.eval_assumePure hb3 heq_wf heq_holds
          set σ' := σ.rename v v'.name
          have hσ'wf : σ'.wf (st'.decls.addConst v') := by
            rw [hdecls]
            simpa [σ'] using (FiniteSubst.rename_wf (σ := σ) (v := v) (name' := v'.name) hσwf hv'_fresh_range)
          have hσ'domwf : (Signature.ofVars σ'.dom).wf := by
            simpa [σ'] using (FiniteSubst.rename_dom_wf (σ := σ) (v := v) (name' := v'.name) hdomwf)
          have hkwf' : k.wfIn retWf (Signature.ofVars σ'.dom) := by
            simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using hkwf
          have hih := ih σ' { st' with decls := st'.decls.addConst v', asserts := _ :: st'.asserts }
            (ρ.updateConst v.sort v'.name (t.eval ρ.env)) Ψ hσ'wf hσ'domwf hkwf' hassume hpost
            (TransState.freshConst.wf _ (VerifM.eval.wf hq)).namesDisjoint
          have hinterp_bi : st'.sl ρ ⊣⊢ st'.sl (ρ.updateConst v.sort v'.name (t.eval ρ.env)) :=
            SpatialContext.interp_env_agree (VerifM.eval.wf hq).ownsWf
              (agreeOn_update_fresh_const (c := v') hv'_fresh_decls)
          have hframe : st'.sl ρ ∗ R ⊢
              st'.sl (ρ.updateConst v.sort v'.name (t.eval ρ.env)) ∗ R := by
            exact sep_mono hinterp_bi.1 (by
              iintro HR
              iexact HR)
          iapply (hframe.trans <| hih.trans <| Assertion.pre_env_agree hkwf'
            (by
              simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
                (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
            hΦ)
          isplitl [Howns]
          · simp [TransState.sl]
          · iexact HR)
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.prove] at heval
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
      have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hφwf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1 hdomwf hσwf.2.2).mpr hφ
      have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
      iapply (iht σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hktwf hassume hpost hwfst)
      simp [TransState.sl]
    · apply wand_intro
      iintro H
      icases H with ⟨Howns, %hnφ⟩
      have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
      simp at hfalse
      have hb2 := VerifM.eval_bind _ _ _ _ hfalse
      have hnot_wf : (Formula.not φ).wfIn (Signature.ofVars σ.dom) := by
        simp only [Formula.wfIn]; exact hφwf
      have hsubst_wf : (φ.not.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hnot_wf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hnot_wf hσwf.1 hdomwf hσwf.2.2).mpr hnφ
      have hassume := VerifM.eval_assumePure hb2 hsubst_wf hsubst_eval
      iapply (ihe σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hkewf hassume hpost hwfst)
      simp [TransState.sl]
