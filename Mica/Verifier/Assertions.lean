import Mica.TinyML.Expr
import Mica.TinyML.Typing
import Mica.TinyML.WeakestPre
import Mica.FOL.Printing
import Mica.Verifier.Utils
import Mica.Verifier.Monad
import Mica.Verifier.Atoms
import Mica.Base.Fresh
import Mica.Base.Except

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

def Assertion.pre (Φ : α → Env → Prop) (m : Assertion α) (ρ : Env) : Prop :=
  match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => φ.eval ρ ∧ Assertion.pre Φ k ρ
  | .let_ x t k   => let v := t.eval ρ; Assertion.pre Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => ∃ v : x.sort.denote, p.eval ρ v ∧ Assertion.pre Φ k (ρ.updateConst x.sort x.name v)
  | .ite φ kt ke  =>
    (φ.eval ρ → Assertion.pre Φ kt ρ) ∧ (¬ φ.eval ρ → Assertion.pre Φ ke ρ)

def Assertion.post {α} (Φ : α → Env → Prop) (m : Assertion α) (ρ : Env) : Prop :=
  match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => φ.eval ρ → Assertion.post Φ k ρ
  | .let_ x t k   => let v := t.eval ρ; Assertion.post Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => ∀ v : x.sort.denote, p.eval ρ v → Assertion.post Φ k (ρ.updateConst x.sort x.name v)
  | .ite φ kt ke  =>
    (φ.eval ρ → Assertion.post Φ kt ρ)
  ∧ (¬ φ.eval ρ → Assertion.post Φ ke ρ)


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
    {Φ : α → Env → Prop} {ρ ρ' : Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ → Φ a ρ₂)
    (h : Assertion.pre Φ m ρ) : Assertion.pre Φ m ρ' := by
  induction m generalizing Δ ρ ρ' with
  | ret a => exact hΦ a Δ ρ ρ' hwf hagree h
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    exact ⟨(Formula.eval_env_agree hφwf hagree).mp h.1, ih hkwf hagree h.2⟩
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.pre] at h ⊢
    rw [← Term.eval_env_agree htwf hagree]
    exact ih hkwf (Env.agreeOn_declVar hagree) h
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    obtain ⟨w, hpw, hk⟩ := h
    exact ⟨w, (Atom.eval_env_agree hpwf hagree) ▸ hpw,
      ih hkwf (Env.agreeOn_declVar hagree) hk⟩
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    constructor
    · intro hφ
      exact iht hktwf hagree (h.1 ((Formula.eval_env_agree hφwf hagree).mpr hφ))
    · intro hnφ
      exact ihe hkewf hagree (h.2 (mt (Formula.eval_env_agree hφwf hagree).mp hnφ))

theorem Assertion.post_env_agree {m : Assertion α} {retWf : α → Signature → Prop}
    {Φ : α → Env → Prop} {ρ ρ' : Env} {Δ : Signature}
    (hwf : m.wfIn retWf Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ → Φ a ρ₂)
    (h : Assertion.post Φ m ρ) : Assertion.post Φ m ρ' := by
  induction m generalizing Δ ρ ρ' with
  | ret a => exact hΦ a Δ ρ ρ' hwf hagree h
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    intro hφ
    exact ih hkwf hagree (h ((Formula.eval_env_agree hφwf hagree).mpr hφ))
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.post] at h ⊢
    rw [← Term.eval_env_agree htwf hagree]
    exact ih hkwf (Env.agreeOn_declVar hagree) h
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    intro w hpw
    exact ih hkwf (Env.agreeOn_declVar hagree)
      (h w ((Atom.eval_env_agree hpwf hagree) ▸ hpw))
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    constructor
    · intro hφ
      exact iht hktwf hagree (h.1 ((Formula.eval_env_agree hφwf hagree).mpr hφ))
    · intro hnφ
      exact ihe hkewf hagree (h.2 (mt (Formula.eval_env_agree hφwf hagree).mp hnφ))

/-- Combining Assertion.pre (caller-side) with Assertion.post (verifier-side):
    if both hold for the same assertion and environment, we can extract a combined conclusion
    at the leaves. -/
theorem Assertion.pre_post_combine {m : Assertion α} {Φ Ψ : α → Env → Prop} {ρ : Env}
    (hpre : Assertion.pre Φ m ρ) (hpost : Assertion.post Ψ m ρ)
    {R : Prop} (hR : ∀ a ρ', Φ a ρ' → Ψ a ρ' → R) : R := by
  induction m generalizing ρ R with
  | ret a => exact hR a ρ hpre hpost
  | assert φ k ih =>
    exact ih hpre.2 (hpost hpre.1) hR
  | let_ v t k ih =>
    exact ih hpre hpost hR
  | pred v p k ih =>
    obtain ⟨u, hpu, hpre'⟩ := hpre
    exact ih hpre' (hpost u hpu) hR
  | ite φ kt ke iht ihe =>
    by_cases hφ : φ.eval ρ
    · exact iht (hpre.1 hφ) (hpost.1 hφ) hR
    · exact ihe (hpre.2 hφ) (hpost.2 hφ) hR

-- ---------------------------------------------------------------------------
-- VerifM helpers
-- ---------------------------------------------------------------------------

/-- Introduce preconditions: assume formulas, declare and bind let-variables.
    Threads a `FiniteSubst` that maps assertion-level names to fresh SMT-level names. -/
def Assertion.assume (σ : FiniteSubst) : Assertion α → VerifM (FiniteSubst × α)
  | .ret a => pure (σ, a)
  | .assert φ k => do
    VerifM.assume (φ.subst σ.subst σ.range.allNames)
    Assertion.assume σ k
  | .let_ v t k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.assume (.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst))
    Assertion.assume σ' k
  | .pred v p k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.assume ((p.subst σ.subst).toFormula (.const (.uninterpreted v'.name v.sort)))
    Assertion.assume σ' k
  | .ite φ kt ke => do
    let branch ← VerifM.all [true, false]
    if branch then do
      VerifM.assume (φ.subst σ.subst σ.range.allNames)
      Assertion.assume σ kt
    else do
      VerifM.assume (.not (φ.subst σ.subst σ.range.allNames))
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
    VerifM.assume (.eq v.sort (.const (.uninterpreted v'.name v.sort)) (t.subst σ.subst))
    Assertion.prove σ' k
  | .pred v p k => do
    match ← VerifM.resolve (p.subst σ.subst) with
    | some t =>
      let v' ← VerifM.decl (some v.name) v.sort
      let σ' := σ.rename v v'.name
      VerifM.assume (.eq v.sort (.const (.uninterpreted v'.name v.sort)) t)
      Assertion.prove σ' k
    | none => VerifM.fatal s!"could not resolve type predicate for {v.name}"
  | .ite φ kt ke => do
    let branch ← VerifM.all [true, false]
    if branch then do
      VerifM.assume (φ.subst σ.subst σ.range.allNames)
      Assertion.prove σ kt
    else do
      VerifM.assume (.not (φ.subst σ.subst σ.range.allNames))
      Assertion.prove σ ke


-- ---------------------------------------------------------------------------
-- Correctness theorems
-- ---------------------------------------------------------------------------

theorem Assertion.assume_correct (m : Assertion α) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : Env)
    (Ψ : (FiniteSubst × α) → TransState → Env → Prop) (Φ : α → Env → Prop)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ → Φ a ρ₂) :
    σ.wf st.decls →
    (Signature.ofVars σ.dom).wf →
    m.wfIn retWf (Signature.ofVars σ.dom) →
    VerifM.eval (Assertion.assume σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wf st'.decls → (Signature.ofVars σ'.dom).wf →
      retWf a (Signature.ofVars σ'.dom) → Φ a (σ'.subst.eval ρ')) →
    Assertion.post Φ m (σ.subst.eval ρ) := by
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
    intro hφ
    have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
      FiniteSubst.subst_wfIn_formula hσwf hφwf hwfst
    have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1 hdomwf hσwf.2.2).mpr hφ
    have hassume := VerifM.eval_assume hb hsubst_wf hsubst_eval
    exact ih σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hkwf hassume hpost hwfst
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
    set u := t.eval (σ.subst.eval ρ)
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
        (ρ.updateConst v.sort v'.name u) := by
      rw [Formula.eval, Term.eval, Const.denote]
      rw [Term.eval_subst htwf hσwf.1 hσwf.2.2]
      simpa [u, Env.lookupConst, Env.updateConst] using
        (Term.eval_env_agree htwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range))
    have hassume := VerifM.eval_assume hb2 heq_wf heq_holds
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
    exact Assertion.post_env_agree hkwf
      (by
        simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
          (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
      hΦ hih
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    intro u hpu
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
    have hformula_wf : ((p.subst σ.subst).toFormula (.const (.uninterpreted v'.name v.sort))).wfIn
        (st.decls.addConst v') :=
      Atom.toFormula_wfIn
        (Atom.wfIn_mono hp_subst_wf (Signature.Subset.subset_addConst _ _)
          (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint) hvar_wf
    have hpu' : (p.subst σ.subst).eval (ρ.updateConst v.sort v'.name u) u := by
      rw [Atom.eval_subst hpwf hσwf.1 hσwf.2.2]
      exact (congrFun (Atom.eval_env_agree hpwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range)) u).mp hpu
    have hformula_holds : ((p.subst σ.subst).toFormula (.const (.uninterpreted v'.name v.sort))).eval
        (ρ.updateConst v.sort v'.name u) :=
      Atom.toFormula_eval_1 (by simpa [Term.eval, Const.denote, Env.lookupConst, Env.updateConst] using hpu')
    have hassume := VerifM.eval_assume hb2 hformula_wf hformula_holds
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
    exact Assertion.post_env_agree hkwf
      (by
        simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
          (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
      hΦ hih
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hall := VerifM.eval_all hb
    simp only [Assertion.post]
    constructor
    · intro hφ
      have htrue := hall true (List.mem_cons_self ..)
      simp at htrue
      have hb2 := VerifM.eval_bind _ _ _ _ htrue
      have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hφwf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1 hdomwf hσwf.2.2).mpr hφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact iht σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hktwf hassume hpost hwfst
    · intro hnφ
      have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
      simp at hfalse
      have hb2 := VerifM.eval_bind _ _ _ _ hfalse
      have hnot_wf : (Formula.not φ).wfIn (Signature.ofVars σ.dom) := by
        simp only [Formula.wfIn]; exact hφwf
      have hsubst_wf : (φ.not.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hnot_wf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hnot_wf hσwf.1 hdomwf hσwf.2.2).mpr hnφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact ihe σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hkewf hassume hpost hwfst

theorem Assertion.prove_correct (m : Assertion α) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : Env)
    (Ψ : (FiniteSubst × α) → TransState → Env → Prop) (Φ : α → Env → Prop)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ → Φ a ρ₂) :
    σ.wf st.decls →
    (Signature.ofVars σ.dom).wf →
    m.wfIn retWf (Signature.ofVars σ.dom) →
    VerifM.eval (Assertion.prove σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wf st'.decls → (Signature.ofVars σ'.dom).wf →
      retWf a (Signature.ofVars σ'.dom) → Φ a (σ'.subst.eval ρ')) →
    Assertion.pre Φ m (σ.subst.eval ρ) := by
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
    exact ⟨hφ_holds, ih σ st ρ Ψ hσwf hdomwf hkwf hassert.2 hpost hwfst⟩
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
    set u := t.eval (σ.subst.eval ρ)
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
        (ρ.updateConst v.sort v'.name u) := by
      rw [Formula.eval, Term.eval, Const.denote]
      rw [Term.eval_subst htwf hσwf.1 hσwf.2.2]
      simpa [u, Env.lookupConst, Env.updateConst] using
        (Term.eval_env_agree htwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range))
    have hassume := VerifM.eval_assume hb2 heq_wf heq_holds
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
    exact Assertion.pre_env_agree hkwf
      (by
        simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
          (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
      hΦ hih
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
    obtain ⟨result, hq, hresult_eval, hresult_wf⟩ := VerifM.eval_resolve hb hpwf_decls
    cases hr : result with
    | none =>
      simp [hr] at hq
      exact (VerifM.eval_fatal hq).elim
    | some t =>
      simp only [hr] at hq hresult_eval hresult_wf
      specialize hresult_eval t rfl
      specialize hresult_wf t rfl
      simp only [Assertion.pre]
      -- The witness is t.eval ρ
      have hpu : p.eval (σ.subst.eval ρ) (t.eval ρ) := by
        rw [← Atom.eval_subst hpwf hσwf.1 hσwf.2.2]
        exact Atom.toFormula_eval_iff.mp hresult_eval
      refine ⟨t.eval ρ, hpu, ?_⟩
      -- Now decompose: decl, assert eq, then prove σ' k
      have hb2 := VerifM.eval_bind _ _ _ _ hq
      have hdecl := VerifM.eval_decl hb2
      set v' := st.freshConst (some v.name) v.sort
      have hv'_fresh_decls : v'.name ∉ st.decls.allNames :=
        fresh_not_mem (addNumbers (v.name)) (st.decls.allNames) (addNumbers_injective _)
      have hv'_fresh_range : v'.name ∉ σ.range.allNames :=
        fun h => hv'_fresh_decls (Signature.allNames_subset hσwf.2.1 _ h)
      specialize hdecl (t.eval ρ)
      have hb3 := VerifM.eval_bind _ _ _ _ hdecl
      have heq_wf : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) t).wfIn
          (st.decls.addConst v') := by
        refine ⟨?_, ?_⟩
        · simp only [Term.wfIn, Const.wfIn, Signature.addConst]
          have hwf_add : (st.decls.addConst v').wf := Signature.wf_addConst hwfst hv'_fresh_decls
          refine ⟨List.Mem.head _, ?_, ?_⟩
          · intro τ' hvar
            exact hv'_fresh_decls (Signature.mem_allNames_of_var hvar)
          · intro τ' hc'
            exact Signature.wf_unique_const hwf_add (List.Mem.head _) hc'
        · exact Term.wfIn_mono _ hresult_wf (Signature.Subset.subset_addConst _ _)
            (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
      have heq_holds : (Formula.eq v.sort (.const (.uninterpreted v'.name v.sort)) t).eval
          (ρ.updateConst v.sort v'.name (t.eval ρ)) := by
        simp only [Formula.eval, Term.eval, Const.denote]
        simpa [Env.lookupConst, Env.updateConst] using
          (Term.eval_env_agree hresult_wf (agreeOn_update_fresh_const hv'_fresh_decls))
      have hassume := VerifM.eval_assume hb3 heq_wf heq_holds
      set σ' := σ.rename v v'.name
      have hσ'wf : σ'.wf (st.decls.addConst v') :=
        by simpa [σ'] using (FiniteSubst.rename_wf (σ := σ) (v := v) (name' := v'.name) hσwf hv'_fresh_range)
      have hσ'domwf : (Signature.ofVars σ'.dom).wf := by
        simpa [σ'] using (FiniteSubst.rename_dom_wf (σ := σ) (v := v) (name' := v'.name) hdomwf)
      have hkwf' : k.wfIn retWf (Signature.ofVars σ'.dom) := by
        simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using hkwf
      have hih := ih σ' { st with decls := st.decls.addConst v', asserts := _ :: st.asserts }
        (ρ.updateConst v.sort v'.name (t.eval ρ)) Ψ hσ'wf hσ'domwf hkwf' hassume hpost
          (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
      exact Assertion.pre_env_agree hkwf
        (by
          simpa [σ', FiniteSubst.rename, Signature.ofVars, Signature.remove, Signature.addVar] using
            (FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := v') hσwf.1 hv'_fresh_range rfl))
        hΦ hih
  | ite φ kt ke iht ihe =>
    obtain ⟨hφwf, hktwf, hkewf⟩ := hwf
    simp only [Assertion.prove] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hall := VerifM.eval_all hb
    simp only [Assertion.pre]
    constructor
    · intro hφ
      have htrue := hall true (List.mem_cons_self ..)
      simp at htrue
      have hb2 := VerifM.eval_bind _ _ _ _ htrue
      have hsubst_wf : (φ.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hφwf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1 hdomwf hσwf.2.2).mpr hφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact iht σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hktwf hassume hpost hwfst
    · intro hnφ
      have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
      simp at hfalse
      have hb2 := VerifM.eval_bind _ _ _ _ hfalse
      have hnot_wf : (Formula.not φ).wfIn (Signature.ofVars σ.dom) := by
        simp only [Formula.wfIn]; exact hφwf
      have hsubst_wf : (φ.not.subst σ.subst σ.range.allNames).wfIn st.decls :=
        FiniteSubst.subst_wfIn_formula hσwf hnot_wf hwfst
      have hsubst_eval := (FiniteSubst.eval_subst_formula hnot_wf hσwf.1 hdomwf hσwf.2.2).mpr hnφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact ihe σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hdomwf hkewf hassume hpost hwfst
