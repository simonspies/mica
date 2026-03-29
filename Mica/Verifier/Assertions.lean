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
  | .let_ x t k   => let v := t.eval ρ; Assertion.pre Φ k (ρ.update x.sort x.name v)
  | .pred x p k   => ∃ v : x.sort.denote, p.eval ρ v ∧ Assertion.pre Φ k (ρ.update x.sort x.name v)
  | .ite φ kt ke  =>
    (φ.eval ρ → Assertion.pre Φ kt ρ) ∧ (¬ φ.eval ρ → Assertion.pre Φ ke ρ)

def Assertion.post {α} (Φ : α → Env → Prop) (m : Assertion α) (ρ : Env) : Prop :=
  match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => φ.eval ρ → Assertion.post Φ k ρ
  | .let_ x t k   => let v := t.eval ρ; Assertion.post Φ k (ρ.update x.sort x.name v)
  | .pred x p k   => ∀ v : x.sort.denote, p.eval ρ v → Assertion.post Φ k (ρ.update x.sort x.name v)
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
  | .let_ v t k  => t.wfIn Δ ∧ k.wfIn retWf (Δ.addVar v)
  | .pred v p k  => p.wfIn Δ ∧ k.wfIn retWf (Δ.addVar v)
  | .ite φ kt ke => φ.wfIn Δ ∧ kt.wfIn retWf Δ ∧ ke.wfIn retWf Δ


def Assertion.checkWf (retCheck : α → Signature → Except String Unit)
    (Δ : Signature) : Assertion α → Except String Unit
  | .ret a       => retCheck a Δ
  | .assert φ k  => do φ.checkWf Δ; k.checkWf retCheck Δ
  | .let_ v t k  => do t.checkWf Δ; k.checkWf retCheck (Δ.addVar v)
  | .pred v p k  => do p.checkWf Δ; k.checkWf retCheck (Δ.addVar v)
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
    (hret : ∀ a Δ Δ', Δ.Subset Δ' → retWf a Δ → retWf a Δ')
    {Δ Δ' : Signature}
    (h : m.wfIn retWf Δ) (hsub : Δ.Subset Δ') : m.wfIn retWf Δ' := by
  induction m generalizing Δ Δ' with
  | ret a => exact hret a Δ Δ' hsub h
  | assert φ k ih => exact ⟨Formula.wfIn_mono φ h.1 hsub, ih h.2 hsub⟩
  | let_ v t k ih => exact ⟨Term.wfIn_mono t h.1 hsub, ih h.2 (hsub.addVar v)⟩
  | pred v p k ih => exact ⟨Atom.wfIn_mono h.1 hsub, ih h.2 (hsub.addVar v)⟩
  | ite φ kt ke iht ihe =>
    exact ⟨Formula.wfIn_mono φ h.1 hsub, iht h.2.1 hsub, ihe h.2.2 hsub⟩

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
    exact ih hkwf (Env.agreeOn_update hagree) h
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    obtain ⟨w, hpw, hk⟩ := h
    exact ⟨w, (Atom.eval_env_agree hpwf hagree) ▸ hpw, ih hkwf (Env.agreeOn_update hagree) hk⟩
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
    exact ih hkwf (Env.agreeOn_update hagree) h
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    intro w hpw
    exact ih hkwf (Env.agreeOn_update hagree)
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
    VerifM.assume (φ.subst σ.subst σ.range)
    Assertion.assume σ k
  | .let_ v t k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.assume (.eq v.sort (.var v.sort v'.name) (t.subst σ.subst))
    Assertion.assume σ' k
  | .pred v p k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.assume ((p.subst σ.subst).toFormula (.var v.sort v'.name))
    Assertion.assume σ' k
  | .ite φ kt ke => do
    let branch ← VerifM.all [true, false]
    if branch then do
      VerifM.assume (φ.subst σ.subst σ.range)
      Assertion.assume σ kt
    else do
      VerifM.assume (.not (φ.subst σ.subst σ.range))
      Assertion.assume σ ke

/-- Assert postconditions: assert formulas, declare and bind let-variables.
    Threads a `FiniteSubst` that maps assertion-level names to fresh SMT-level names. -/
def Assertion.prove (σ : FiniteSubst) : Assertion α → VerifM (FiniteSubst × α)
  | .ret a => pure (σ, a)
  | .assert φ k => do
    VerifM.assert (φ.subst σ.subst σ.range)
    Assertion.prove σ k
  | .let_ v t k => do
    let v' ← VerifM.decl (some v.name) v.sort
    let σ' := σ.rename v v'.name
    VerifM.assume (.eq v.sort (.var v.sort v'.name) (t.subst σ.subst))
    Assertion.prove σ' k
  | .pred v p k => do
    match ← VerifM.resolve (p.subst σ.subst) with
    | some t =>
      let v' ← VerifM.decl (some v.name) v.sort
      let σ' := σ.rename v v'.name
      VerifM.assume (.eq v.sort (.var v.sort v'.name) t)
      Assertion.prove σ' k
    | none => VerifM.fatal s!"could not resolve type predicate for {v.name}"
  | .ite φ kt ke => do
    let branch ← VerifM.all [true, false]
    if branch then do
      VerifM.assume (φ.subst σ.subst σ.range)
      Assertion.prove σ kt
    else do
      VerifM.assume (.not (φ.subst σ.subst σ.range))
      Assertion.prove σ ke


-- ---------------------------------------------------------------------------
-- Correctness theorems
-- ---------------------------------------------------------------------------

theorem Assertion.assume_correct (m : Assertion α) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : Env)
    (Ψ : (FiniteSubst × α) → TransState → Env → Prop) (Φ : α → Env → Prop)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ → Φ a ρ₂) :
    σ.wf st.decls.vars →
    m.wfIn retWf (Signature.ofVars σ.dom) →
    VerifM.eval (Assertion.assume σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wf st'.decls.vars → retWf a (Signature.ofVars σ'.dom) → Φ a (σ'.subst.eval ρ')) →
    Assertion.post Φ m (σ.subst.eval ρ) := by
  intro hσwf hwf heval hpost
  induction m generalizing σ st ρ Ψ with
  | ret a =>
    exact hpost _ _ _ _ (VerifM.eval_ret heval) hσwf hwf
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    simp only [Assertion.post]
    intro hφ
    have hsubst_wf' := FiniteSubst.subst_wfIn_formula hσwf hφwf
    have hsubst_wf : (φ.subst σ.subst σ.range).wfIn st.decls :=
      Formula.wfIn_mono _ hsubst_wf' ⟨fun x hx => hx, fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
    have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1).mpr hφ
    have hassume := VerifM.eval_assume hb hsubst_wf hsubst_eval
    exact ih σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hkwf hassume hpost
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hdecl := VerifM.eval_decl hb
    simp only [Assertion.post]
    set v' := st.freshVar (some v.name) v.sort
    have hv'_fresh_decls : v'.name ∉ st.decls.vars.map Var.name :=
      fresh_not_mem (addNumbers (v.name)) (st.decls.vars.map Var.name) (addNumbers_injective _)
    have hv'_fresh_range : ⟨v'.name, v.sort⟩ ∉ σ.range := by
      intro hmem; exact hv'_fresh_decls (List.mem_map.mpr ⟨⟨v'.name, v.sort⟩, hσwf.2 hmem, rfl⟩)
    set u := t.eval (σ.subst.eval ρ)
    specialize hdecl u
    have hb2 := VerifM.eval_bind _ _ _ _ hdecl
    -- Show the equality formula is well-formed and holds
    have ht_subst_wf : (t.subst σ.subst).wfIn (Signature.ofVars σ.range) := Term.subst_wfIn htwf hσwf.1
    have heq_wf : (Formula.eq v.sort (.var v.sort v'.name) (t.subst σ.subst)).wfIn
        (st.decls.addVar v') := by
      simp only [Formula.wfIn, Term.wfIn]
      refine ⟨List.mem_cons_self, ?_⟩
      have hsub : (Signature.ofVars σ.range).Subset (st.decls.addVar v') :=
        Signature.Subset.trans
          ⟨fun x hx => hσwf.2 hx, fun _ h => absurd h List.not_mem_nil,
           fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
          (Signature.Subset.subset_addVar _ _)
      exact Term.wfIn_mono _ ht_subst_wf hsub
    have heq_holds : (Formula.eq v.sort (.var v.sort v'.name) (t.subst σ.subst)).eval
        (ρ.update v.sort v'.name u) := by
      simp only [Formula.eval, Term.eval, Env.lookup_update_same, u, Term.eval_subst]
      exact Term.eval_env_agree htwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range)
    have hassume := VerifM.eval_assume hb2 heq_wf heq_holds
    -- Apply IH with σ' = σ.rename v v'.name
    set σ' := σ.rename v v'.name
    have hσ'wf : σ'.wf (v' :: st.decls.vars) := FiniteSubst.rename_wf hσwf hv'_fresh_range
    -- Need: post Φ k (σ'.subst.eval ρ') where ρ' = ρ.update v.sort v'.name u
    -- By IH: post Φ k (σ'.subst.eval (ρ.update v.sort v'.name u))
    -- By rename_agreeOn: σ'.subst.eval (ρ.update ...) agreeOn (v :: σ.dom) with (σ.subst.eval ρ).update v.sort v.name u
    -- By post_env_agree: can transport between them
    have hih := ih σ' { st with decls := st.decls.addVar v', asserts := _ :: st.asserts }
      (ρ.update v.sort v'.name u) Ψ hσ'wf hkwf hassume hpost
    exact Assertion.post_env_agree hkwf (FiniteSubst.rename_agreeOn hσwf.1 hv'_fresh_range)
      hΦ hih
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.post]
    intro u hpu
    simp only [Assertion.assume] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hdecl := VerifM.eval_decl hb
    set v' := st.freshVar (some v.name) v.sort
    have hv'_fresh_decls : v'.name ∉ st.decls.vars.map Var.name :=
      fresh_not_mem (addNumbers (v.name)) (st.decls.vars.map Var.name) (addNumbers_injective _)
    have hv'_fresh_range : ⟨v'.name, v.sort⟩ ∉ σ.range := by
      intro hmem; exact hv'_fresh_decls (List.mem_map.mpr ⟨⟨v'.name, v.sort⟩, hσwf.2 hmem, rfl⟩)
    specialize hdecl u
    have hb2 := VerifM.eval_bind _ _ _ _ hdecl
    -- Show the atom formula is well-formed and holds
    have hp_subst_wf : (p.subst σ.subst).wfIn (Signature.ofVars σ.range) := Atom.subst_wfIn hpwf hσwf.1
    have hvar_wf : (Term.var v.sort v'.name).wfIn (st.decls.addVar v') := by
      simp only [Term.wfIn]; exact List.mem_cons_self
    have hformula_wf : ((p.subst σ.subst).toFormula (.var v.sort v'.name)).wfIn
        (st.decls.addVar v') :=
      Atom.toFormula_wfIn (Atom.wfIn_mono hp_subst_wf (by
        constructor
        · intro x hx; exact List.mem_cons_of_mem _ (hσwf.2 hx)
        · intro _ h; simp [Signature.ofVars] at h
        · intro _ h; simp [Signature.ofVars] at h
        · intro _ h; simp [Signature.ofVars] at h)) hvar_wf
    have hpu' : (p.subst σ.subst).eval (ρ.update v.sort v'.name u) u := by
      rw [Atom.eval_subst]
      rwa [← Atom.eval_env_agree hpwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range)]
    have hformula_holds : ((p.subst σ.subst).toFormula (.var v.sort v'.name)).eval
        (ρ.update v.sort v'.name u) :=
      Atom.toFormula_eval_1 (by simp [Term.eval, Env.lookup_update_same]; exact hpu')
    have hassume := VerifM.eval_assume hb2 hformula_wf hformula_holds
    set σ' := σ.rename v v'.name
    have hσ'wf : σ'.wf (v' :: st.decls.vars) := FiniteSubst.rename_wf hσwf hv'_fresh_range
    have hih := ih σ' { st with decls := st.decls.addVar v', asserts := _ :: st.asserts }
      (ρ.update v.sort v'.name u) Ψ hσ'wf hkwf hassume hpost
    exact Assertion.post_env_agree hkwf (FiniteSubst.rename_agreeOn hσwf.1 hv'_fresh_range)
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
      have hsubst_wf' := FiniteSubst.subst_wfIn_formula hσwf hφwf
      have hsubst_wf : (φ.subst σ.subst σ.range).wfIn st.decls :=
        Formula.wfIn_mono _ hsubst_wf' ⟨fun x hx => hx, fun _ h => absurd h List.not_mem_nil,
          fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1).mpr hφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact iht σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hktwf hassume hpost
    · intro hnφ
      have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
      simp at hfalse
      have hb2 := VerifM.eval_bind _ _ _ _ hfalse
      have hnot_wf : (Formula.not φ).wfIn (Signature.ofVars σ.dom) := by
        simp only [Formula.wfIn]; exact hφwf
      have hsubst_wf' := FiniteSubst.subst_wfIn_formula hσwf hnot_wf
      have hsubst_wf : (φ.not.subst σ.subst σ.range).wfIn st.decls :=
        Formula.wfIn_mono _ hsubst_wf' ⟨fun x hx => hx, fun _ h => absurd h List.not_mem_nil,
          fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      have hsubst_eval := (FiniteSubst.eval_subst_formula hnot_wf hσwf.1).mpr hnφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact ihe σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hkewf hassume hpost

theorem Assertion.prove_correct (m : Assertion α) (σ : FiniteSubst)
    (retWf : α → Signature → Prop)
    (st : TransState) (ρ : Env)
    (Ψ : (FiniteSubst × α) → TransState → Env → Prop) (Φ : α → Env → Prop)
    (hΦ : ∀ a Δ ρ₁ ρ₂, retWf a Δ → Env.agreeOn Δ ρ₁ ρ₂ → Φ a ρ₁ → Φ a ρ₂) :
    σ.wf st.decls.vars →
    m.wfIn retWf (Signature.ofVars σ.dom) →
    VerifM.eval (Assertion.prove σ m) st ρ Ψ →
    (∀ σ' a st' ρ', Ψ (σ', a) st' ρ' → σ'.wf st'.decls.vars → retWf a (Signature.ofVars σ'.dom) → Φ a (σ'.subst.eval ρ')) →
    Assertion.pre Φ m (σ.subst.eval ρ) := by
  intro hσwf hwf heval hpost
  induction m generalizing σ st ρ Ψ with
  | ret a =>
    exact hpost _ _ _ _ (VerifM.eval_ret heval) hσwf hwf
  | assert φ k ih =>
    obtain ⟨hφwf, hkwf⟩ := hwf
    simp only [Assertion.prove] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hsubst_wf' := FiniteSubst.subst_wfIn_formula hσwf hφwf
    have hsubst_wf : (φ.subst σ.subst σ.range).wfIn st.decls :=
      Formula.wfIn_mono _ hsubst_wf' ⟨fun x hx => hx, fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
    have hassert := VerifM.eval_assert hb hsubst_wf
    have hφ_holds := (FiniteSubst.eval_subst_formula hφwf hσwf.1).mp hassert.1
    exact ⟨hφ_holds, ih σ st ρ Ψ hσwf hkwf hassert.2 hpost⟩
  | let_ v t k ih =>
    obtain ⟨htwf, hkwf⟩ := hwf
    simp only [Assertion.prove] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hdecl := VerifM.eval_decl hb
    simp only [Assertion.pre]
    set v' := st.freshVar (some v.name) v.sort
    have hv'_fresh_decls : v'.name ∉ st.decls.vars.map Var.name :=
      fresh_not_mem (addNumbers (v.name)) (st.decls.vars.map Var.name) (addNumbers_injective _)
    have hv'_fresh_range : ⟨v'.name, v.sort⟩ ∉ σ.range := by
      intro hmem; exact hv'_fresh_decls (List.mem_map.mpr ⟨⟨v'.name, v.sort⟩, hσwf.2 hmem, rfl⟩)
    set u := t.eval (σ.subst.eval ρ)
    specialize hdecl u
    have hb2 := VerifM.eval_bind _ _ _ _ hdecl
    have ht_subst_wf : (t.subst σ.subst).wfIn (Signature.ofVars σ.range) := Term.subst_wfIn htwf hσwf.1
    have heq_wf : (Formula.eq v.sort (.var v.sort v'.name) (t.subst σ.subst)).wfIn
        (st.decls.addVar v') := by
      simp only [Formula.wfIn, Term.wfIn]
      refine ⟨List.mem_cons_self, ?_⟩
      have hsub : (Signature.ofVars σ.range).Subset (st.decls.addVar v') :=
        Signature.Subset.trans
          ⟨fun x hx => hσwf.2 hx, fun _ h => absurd h List.not_mem_nil,
           fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
          (Signature.Subset.subset_addVar _ _)
      exact Term.wfIn_mono _ ht_subst_wf hsub
    have heq_holds : (Formula.eq v.sort (.var v.sort v'.name) (t.subst σ.subst)).eval
        (ρ.update v.sort v'.name u) := by
      simp only [Formula.eval, Term.eval, Env.lookup_update_same, u, Term.eval_subst]
      exact Term.eval_env_agree htwf (FiniteSubst.eval_update_fresh hσwf.1 hv'_fresh_range)
    have hassume := VerifM.eval_assume hb2 heq_wf heq_holds
    set σ' := σ.rename v v'.name
    have hσ'wf : σ'.wf (v' :: st.decls.vars) := FiniteSubst.rename_wf hσwf hv'_fresh_range
    have hih := ih σ' { st with decls := st.decls.addVar v', asserts := _ :: st.asserts }
      (ρ.update v.sort v'.name u) Ψ hσ'wf hkwf hassume hpost
    exact Assertion.pre_env_agree hkwf (FiniteSubst.rename_agreeOn hσwf.1 hv'_fresh_range)
      hΦ hih
  | pred v p k ih =>
    obtain ⟨hpwf, hkwf⟩ := hwf
    simp only [Assertion.prove] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    have hpwf_decls : (p.subst σ.subst).wfIn st.decls :=
      Atom.wfIn_mono (Atom.subst_wfIn hpwf hσwf.1) (by
        constructor
        · intro x hx; exact hσwf.2 hx
        · intro _ h; simp [Signature.ofVars] at h
        · intro _ h; simp [Signature.ofVars] at h
        · intro _ h; simp [Signature.ofVars] at h)
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
        rw [← Atom.eval_subst]; exact Atom.toFormula_eval_iff.mp hresult_eval
      refine ⟨t.eval ρ, hpu, ?_⟩
      -- Now decompose: decl, assert eq, then prove σ' k
      have hb2 := VerifM.eval_bind _ _ _ _ hq
      have hdecl := VerifM.eval_decl hb2
      set v' := st.freshVar (some v.name) v.sort
      have hv'_fresh_decls : v'.name ∉ st.decls.vars.map Var.name :=
        fresh_not_mem (addNumbers (v.name)) (st.decls.vars.map Var.name) (addNumbers_injective _)
      have hv'_fresh_range : ⟨v'.name, v.sort⟩ ∉ σ.range := by
        intro hmem; exact hv'_fresh_decls (List.mem_map.mpr ⟨⟨v'.name, v.sort⟩, hσwf.2 hmem, rfl⟩)
      specialize hdecl (t.eval ρ)
      have hb3 := VerifM.eval_bind _ _ _ _ hdecl
      have heq_wf : (Formula.eq v.sort (.var v.sort v'.name) t).wfIn
          (st.decls.addVar v') := by
        simp only [Formula.wfIn, Term.wfIn]
        exact ⟨List.mem_cons_self,
               Term.wfIn_mono _ hresult_wf (Signature.Subset.subset_addVar _ _)⟩
      have heq_holds : (Formula.eq v.sort (.var v.sort v'.name) t).eval
          (ρ.update v.sort v'.name (t.eval ρ)) := by
        simp only [Formula.eval, Term.eval, Env.lookup_update_same]
        exact Term.eval_env_agree hresult_wf (agreeOn_update_fresh hv'_fresh_decls)
      have hassume := VerifM.eval_assume hb3 heq_wf heq_holds
      set σ' := σ.rename v v'.name
      have hσ'wf : σ'.wf (v' :: st.decls.vars) := FiniteSubst.rename_wf hσwf hv'_fresh_range
      have hih := ih σ' { st with decls := st.decls.addVar v', asserts := _ :: st.asserts }
        (ρ.update v.sort v'.name (t.eval ρ)) Ψ hσ'wf hkwf hassume hpost
      exact Assertion.pre_env_agree hkwf (FiniteSubst.rename_agreeOn hσwf.1 hv'_fresh_range)
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
      have hsubst_wf' := FiniteSubst.subst_wfIn_formula hσwf hφwf
      have hsubst_wf : (φ.subst σ.subst σ.range).wfIn st.decls :=
        Formula.wfIn_mono _ hsubst_wf' ⟨fun x hx => hx, fun _ h => absurd h List.not_mem_nil,
          fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      have hsubst_eval := (FiniteSubst.eval_subst_formula hφwf hσwf.1).mpr hφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact iht σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hktwf hassume hpost
    · intro hnφ
      have hfalse := hall false (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
      simp at hfalse
      have hb2 := VerifM.eval_bind _ _ _ _ hfalse
      have hnot_wf : (Formula.not φ).wfIn (Signature.ofVars σ.dom) := by
        simp only [Formula.wfIn]; exact hφwf
      have hsubst_wf' := FiniteSubst.subst_wfIn_formula hσwf hnot_wf
      have hsubst_wf : (φ.not.subst σ.subst σ.range).wfIn st.decls :=
        Formula.wfIn_mono _ hsubst_wf' ⟨fun x hx => hx, fun _ h => absurd h List.not_mem_nil,
          fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      have hsubst_eval := (FiniteSubst.eval_subst_formula hnot_wf hσwf.1).mpr hnφ
      have hassume := VerifM.eval_assume hb2 hsubst_wf hsubst_eval
      exact ihe σ { st with asserts := _ :: st.asserts } ρ Ψ hσwf hkewf hassume hpost
