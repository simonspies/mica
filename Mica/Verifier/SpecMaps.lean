-- SUMMARY: Finite maps of function specifications, together with satisfaction, update, and well-formedness lemmas.
import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.FOL.Printing
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.Utils
import Mica.Verifier.Specifications
import Mica.Base.Fresh
import Mathlib.Data.Finmap

open Iris Iris.BI

-- ---------------------------------------------------------------------------
-- SpecMap
-- ---------------------------------------------------------------------------

abbrev SpecMap := Finmap (fun _ : TinyML.Var => Spec)

def SpecMap.satisfiedBy (Θ : TinyML.TypeEnv) (S : SpecMap) (γ : Runtime.Subst) : iProp :=
  iprop(□ (∀ x s, ⌜S.lookup x = some s⌝ -∗ ∃ f, ⌜γ x = some f⌝ ∗ s.isPrecondFor Θ f))

instance : Iris.BI.Persistent (SpecMap.satisfiedBy Θ S γ) := by
  unfold SpecMap.satisfiedBy; infer_instance

theorem SpecMap.project {x : TinyML.Var} {s : Spec} {Q : iProp} (P : iProp) (Θ : TinyML.TypeEnv) (S : SpecMap) (γ : Runtime.Subst) :
  (P ⊢ S.satisfiedBy Θ γ) →
  S.lookup x = some s →
  (∀ fval, γ x = some fval → s.isPrecondFor Θ fval ∗ P ⊢ Q) →
  (P ⊢ Q) := by
  intro hsat hlook hcont
  simp only [SpecMap.satisfiedBy] at hsat
  have hstep : P ⊢ (∃ fval, ⌜γ x = some fval⌝ ∗ s.isPrecondFor Θ fval) ∗ P := by
    refine (persistent_entails_r hsat).trans ?_
    istart
    iintro ⟨□Hall, HP⟩
    ispecialize Hall $$ %x
    ispecialize Hall $$ %s
    isplitl []
    · iapply Hall
      ipure_intro
      exact hlook
    · iexact HP
  refine hstep.trans ?_
  istart
  iintro ⟨⟨%fval, Hγ, Hpre⟩, HP⟩
  ipure Hγ
  iapply (hcont fval Hγ)
  isplitl [Hpre]
  · iexact Hpre
  · iexact HP


def SpecMap.wfIn (S : SpecMap) (Δ : Signature) : Prop :=
  ∀ f spec, S.lookup f = some spec → spec.wfIn Δ

theorem SpecMap.wfIn_mono {S : SpecMap} {Δ Δ' : Signature}
    (h : S.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    S.wfIn Δ' :=
  fun f spec hlookup => Spec.wfIn_mono (h f spec hlookup) hsub hwf

theorem SpecMap.wfIn_erase {S : SpecMap} {x : TinyML.Var} {Δ : Signature}
    (h : S.wfIn Δ) : SpecMap.wfIn (Finmap.erase x S) Δ := by
  intro f spec hlookup
  by_cases hfx : f = x
  · subst hfx; rw [Finmap.lookup_erase] at hlookup; exact absurd hlookup (by simp)
  · rw [Finmap.lookup_erase_ne hfx] at hlookup
    exact h f spec hlookup

/-- Erase multiple keys from a SpecMap. -/
def SpecMap.eraseAll (keys : List String) (S : SpecMap) : SpecMap :=
  keys.foldl (fun acc k => Finmap.erase k acc) S

@[simp] theorem SpecMap.eraseAll_nil (S : SpecMap) : SpecMap.eraseAll [] S = S := rfl

@[simp] theorem SpecMap.eraseAll_cons (k : String) (ks : List String) (S : SpecMap) :
    SpecMap.eraseAll (k :: ks) S = SpecMap.eraseAll ks (Finmap.erase k S) := by
  simp [SpecMap.eraseAll, List.foldl_cons]

theorem SpecMap.lookup_eraseAll {keys : List String} {S : SpecMap} {y : String} :
    (SpecMap.eraseAll keys S).lookup y = if y ∈ keys then none else S.lookup y := by
  induction keys generalizing S with
  | nil => simp
  | cons k ks ih =>
    rw [eraseAll_cons, ih]
    by_cases hky : k = y
    · subst hky; simp [Finmap.lookup_erase]
    · rw [Finmap.lookup_erase_ne (Ne.symm hky)]
      by_cases hmem : y ∈ ks <;> simp [hmem, Ne.symm hky]

theorem SpecMap.eraseAll_lookup_none {keys : List String} {S : SpecMap} {y : String}
    (hy : y ∈ keys) : (SpecMap.eraseAll keys S).lookup y = none := by
  simp [lookup_eraseAll, hy]

theorem SpecMap.eraseAll_lookup_of_notin {keys : List String} {y : String}
    (hy : y ∉ keys) (S : SpecMap) :
    (SpecMap.eraseAll keys S).lookup y = S.lookup y := by
  simp [lookup_eraseAll, hy]

theorem SpecMap.wfIn_eraseAll {keys : List String} {S : SpecMap} {Δ : Signature}
    (h : S.wfIn Δ) : (SpecMap.eraseAll keys S).wfIn Δ := by
  induction keys generalizing S with
  | nil => exact h
  | cons k ks ih => exact ih (SpecMap.wfIn_erase h)

def SpecMap.insertBinder (S : SpecMap) (b : Typed.Binder) (spec : Spec) : SpecMap :=
  match b.name with
  | some x => S.insert x spec
  | none => S

@[simp] theorem SpecMap.insertBinder_none {S : SpecMap} {b : Typed.Binder} {spec : Spec}
    (h : b.name = none) : S.insertBinder b spec = S := by
  simp [SpecMap.insertBinder, h]

@[simp] theorem SpecMap.insertBinder_some {S : SpecMap} {b : Typed.Binder} {spec : Spec}
    {x : TinyML.Var} (h : b.name = some x) : S.insertBinder b spec = S.insert x spec := by
  simp [SpecMap.insertBinder, h]

def SpecMap.eraseBinder (S : SpecMap) (b : Typed.Binder) : SpecMap :=
  match b.name with
  | some x => S.erase x
  | none => S

@[simp] theorem SpecMap.eraseBinder_none {S : SpecMap} {b : Typed.Binder}
    (h : b.name = none) : S.eraseBinder b = S := by
  simp [SpecMap.eraseBinder, h]

@[simp] theorem SpecMap.eraseBinder_some {S : SpecMap} {b : Typed.Binder} {x : TinyML.Var}
    (h : b.name = some x) : S.eraseBinder b = S.erase x := by
  simp [SpecMap.eraseBinder, h]

/-- Generic preservation: if every `y` in the domain of `S'` has the same spec in `S` and
    its value is preserved from `γ` to `γ'`, then satisfiedness transfers. -/
theorem SpecMap.satisfiedBy_preserved {Θ : TinyML.TypeEnv} {S S' : SpecMap} {γ γ' : Runtime.Subst}
    (h : ∀ y s, S'.lookup y = some s →
      S.lookup y = some s ∧ (∀ f, γ y = some f → γ' y = some f)) :
    S.satisfiedBy Θ γ ⊢ S'.satisfiedBy Θ γ' := by
  simp only [SpecMap.satisfiedBy]
  iintro □HS
  imodintro
  iintro %y %s %hlookup
  obtain ⟨hlookup', hγ⟩ := h y s hlookup
  ispecialize HS $$ %y %s %hlookup'
  icases HS with ⟨%f, %hγf, Hpre⟩
  iexists f
  isplitl [Hpre]
  · ipure_intro; exact hγ f hγf
  · iexact Hpre

/-- Generic insert: fresh precondition for `x ↦ fval` plus preservation elsewhere. -/
theorem SpecMap.satisfiedBy_insert_of_preserved {Θ : TinyML.TypeEnv} {S : SpecMap}
    {γ γ' : Runtime.Subst} {x : TinyML.Var} {fval : Runtime.Val} {spec : Spec}
    (hγ' : γ' x = some fval)
    (hγ : ∀ y f, y ≠ x → γ y = some f → γ' y = some f) :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ fval ⊢
      SpecMap.satisfiedBy Θ (Finmap.insert x spec S) γ' := by
  simp only [SpecMap.satisfiedBy, Spec.isPrecondFor]
  iintro ⟨□HS, □Hf⟩
  imodintro
  iintro %y %s' %hlookup
  by_cases hyx : y = x
  · subst hyx
    have : s' = spec := by rw [Finmap.lookup_insert] at hlookup; simpa using hlookup.symm
    subst this
    iexists fval
    isplitr
    · ipure_intro; exact hγ'
    · iexact Hf
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    ispecialize HS $$ %y %s' %hlookup
    icases HS with ⟨%f, %hγf, Hpre⟩
    iexists f
    isplitl [Hpre]
    · ipure_intro; exact hγ y f hyx hγf
    · iexact Hpre

theorem SpecMap.satisfiedBy_insert {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {x : TinyML.Var} {fval : Runtime.Val} {spec : Spec} (hγ : γ x = some fval) :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ fval ⊢
      SpecMap.satisfiedBy Θ (Finmap.insert x spec S) γ :=
  SpecMap.satisfiedBy_insert_of_preserved hγ (fun _ _ _ hf => hf)

theorem SpecMap.satisfiedBy_insert_update {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : Runtime.Val} {spec : Spec} :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ v ⊢
      SpecMap.satisfiedBy Θ (Finmap.insert x spec S) (γ.update x v) :=
  SpecMap.satisfiedBy_insert_of_preserved
    (by simp [Runtime.Subst.update])
    (fun y f hyx hf => by simp [Runtime.Subst.update, beq_false_of_ne hyx, hf])

theorem SpecMap.wfIn_insert {S : SpecMap} {x : TinyML.Var} {spec : Spec} {Δ : Signature}
    (hS : S.wfIn Δ) (hs : spec.wfIn Δ) : SpecMap.wfIn (Finmap.insert x spec S) Δ := by
  intro y s' hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup; exact hs
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup; exact hS y s' hlookup

theorem SpecMap.satisfiedBy_insertBinder {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {b : Typed.Binder} {fval : Runtime.Val} {spec : Spec}
    (hγ : ∀ x ty, b = Typed.Binder.named x ty → γ x = some fval) :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ fval ⊢ SpecMap.satisfiedBy Θ (S.insertBinder b spec) γ := by
  rcases hb : b.name with _ | x
  · rw [SpecMap.insertBinder_none hb]; iintro ⟨HS, _⟩; iexact HS
  · obtain ⟨_, ty⟩ := b; cases hb
    rw [SpecMap.insertBinder_some rfl]; exact SpecMap.satisfiedBy_insert (hγ x ty rfl)

theorem SpecMap.satisfiedBy_insertBinder_updateBinder {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {b : Typed.Binder} {v : Runtime.Val} {spec : Spec} :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ v ⊢ SpecMap.satisfiedBy Θ (S.insertBinder b spec) (Runtime.Subst.updateBinder b.runtime v γ) := by
  rcases hb : b.name with _ | _
  · rw [SpecMap.insertBinder_none hb, Typed.Binder.runtime_of_name_none hb]
    simp [Runtime.Subst.updateBinder]; iintro ⟨HS, _⟩; iexact HS
  · rw [SpecMap.insertBinder_some hb, Typed.Binder.runtime_of_name_some hb]
    exact SpecMap.satisfiedBy_insert_update

theorem SpecMap.wfIn_insertBinder {S : SpecMap} {b : Typed.Binder} {spec : Spec} {Δ : Signature}
    (hS : S.wfIn Δ) (hs : spec.wfIn Δ) : SpecMap.wfIn (S.insertBinder b spec) Δ := by
  rcases hb : b.name with _ | _
  · rwa [SpecMap.insertBinder_none hb]
  · rw [SpecMap.insertBinder_some hb]; exact SpecMap.wfIn_insert hS hs

theorem SpecMap.wfIn_eraseBinder {S : SpecMap} {b : Typed.Binder} {Δ : Signature}
    (hS : S.wfIn Δ) : SpecMap.wfIn (S.eraseBinder b) Δ := by
  rcases hb : b.name with _ | _
  · rwa [SpecMap.eraseBinder_none hb]
  · rw [SpecMap.eraseBinder_some hb]; exact SpecMap.wfIn_erase hS

theorem SpecMap.satisfiedBy_eraseAll_updateAllBinder {Θ : TinyML.TypeEnv} {keys : List String} {S : SpecMap} {γ : Runtime.Subst}
    {vs : List Runtime.Val} (hlen : keys.length = vs.length) :
    S.satisfiedBy Θ γ ⊢ (SpecMap.eraseAll keys S).satisfiedBy Θ (γ.updateAllBinder (keys.map Runtime.Binder.named) vs) := by
  apply SpecMap.satisfiedBy_preserved
  intro y s hlookup
  have hy_notin : y ∉ keys := by
    intro hmem; rw [eraseAll_lookup_none hmem] at hlookup; exact absurd hlookup (by simp)
  refine ⟨by rwa [eraseAll_lookup_of_notin hy_notin] at hlookup, fun f hf => ?_⟩
  rw [Runtime.Subst.updateAllBinder_eq _ _ _ _ (by simp; omega),
      findVal_none_of_not_mem keys vs y (by omega) hy_notin]
  exact hf

theorem SpecMap.empty_satisfiedBy (γ : Runtime.Subst) :
    ⊢ SpecMap.satisfiedBy Θ (∅ : SpecMap) γ := by
  simp only [SpecMap.satisfiedBy]
  imodintro
  iintro %x %s %h
  simp [Finmap.lookup_empty] at h

theorem SpecMap.empty_wfIn (Δ : Signature) :
    SpecMap.wfIn (∅ : SpecMap) Δ := by
  intro f spec h; simp [Finmap.lookup_empty] at h

theorem SpecMap.satisfiedBy_erase {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst} {x : TinyML.Var} {v : Runtime.Val} :
    S.satisfiedBy Θ γ ⊢ SpecMap.satisfiedBy Θ (Finmap.erase x S) (Runtime.Subst.update γ x v) := by
  apply SpecMap.satisfiedBy_preserved
  intro y s hlookup
  have hyx : y ≠ x := fun heq => by
    subst heq; rw [Finmap.lookup_erase] at hlookup; exact absurd hlookup (by simp)
  exact ⟨by rwa [Finmap.lookup_erase_ne hyx] at hlookup,
    fun f hf => by simp [Runtime.Subst.update, hyx, hf]⟩

theorem SpecMap.satisfiedBy_eraseBinder {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {b : Typed.Binder} {v : Runtime.Val} :
    S.satisfiedBy Θ γ ⊢ SpecMap.satisfiedBy Θ (S.eraseBinder b) (Runtime.Subst.updateBinder b.runtime v γ) := by
  rcases hb : b.name with _ | _
  · rw [SpecMap.eraseBinder_none hb, Typed.Binder.runtime_of_name_none hb]
    simp [Runtime.Subst.updateBinder]
  · rw [SpecMap.eraseBinder_some hb, Typed.Binder.runtime_of_name_some hb]
    exact SpecMap.satisfiedBy_erase

theorem SpecMap.satisfiedBy_update_of_not_mem {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : Runtime.Val} (hx : S.lookup x = none) :
    S.satisfiedBy Θ γ ⊢ S.satisfiedBy Θ (γ.update x v) := by
  apply SpecMap.satisfiedBy_preserved
  intro y s hlookup
  have hyx : y ≠ x := fun heq => by subst heq; rw [hx] at hlookup; exact absurd hlookup (by simp)
  exact ⟨hlookup, fun f hf => by simp [Runtime.Subst.update, hyx, hf]⟩
