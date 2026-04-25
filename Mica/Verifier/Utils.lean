-- SUMMARY: Supporting infrastructure for verifier finite substitutions and argument-handling helpers.
import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.Base.Fresh
import Mica.Base.Except
import Mica.SeparationLogic.LogicalRelation
import Mica.Verifier.Bindings
import Mica.Verifier.State
import Mathlib.Data.Finmap

theorem argVars_cons_perm {name : String}
    {rest : List (String × TinyML.Typ)} {dom : List Var} {x : Var}
    (hx : x ∈ (⟨name, .value⟩ :: rest.map (fun (name, _) => ⟨name, .value⟩) ++ dom)) :
    x ∈ (rest.map (fun (name, _) => ⟨name, .value⟩) ++ ⟨name, .value⟩ :: dom) := by
  simp only [List.cons_append, List.mem_cons,
    List.mem_append, List.mem_map] at hx ⊢
  rcases hx with rfl | ⟨a, ha, rfl⟩ | hmem
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr (Or.inr hmem)

/-- Extract argument names from binders, pairing with spec arg info.
    Requires exact length match. -/
def extractArgNames : List Typed.Binder → List (String × TinyML.Typ) →
    Except String (List String)
  | [], [] => .ok []
  | ⟨some x, _⟩ :: rest, _ :: specRest => do
      let tail ← extractArgNames rest specRest
      .ok (x :: tail)
  | _, _ => .error "argument mismatch"

theorem extractArgNames_spec {argBinders : List Typed.Binder}
    {specArgs : List (String × TinyML.Typ)} {names : List String}
    (h : extractArgNames argBinders specArgs = .ok names) :
    names.length = specArgs.length ∧
    argBinders.length = specArgs.length ∧
    argBinders.map Typed.Binder.runtime = names.map Runtime.Binder.named := by
  induction specArgs generalizing argBinders names with
  | nil =>
    cases argBinders with
    | nil => simp [extractArgNames] at h; subst h; simp
    | cons _ _ => simp [extractArgNames] at h
  | cons sa sas ih =>
    cases argBinders with
    | nil => simp [extractArgNames] at h
    | cons ab abs =>
      cases ab with
      | mk name ty =>
        cases name with
        | none =>
          simp [extractArgNames] at h
        | some x =>
          simp [extractArgNames] at h
          cases hrec : extractArgNames abs sas with
          | error =>
              simp [hrec] at h
              cases h
          | ok tail =>
              simp [hrec] at h
              cases h
              obtain ⟨h1, h2, h3⟩ := ih hrec
              exact ⟨by simp [h1], by simp [h2], by simp [Typed.Binder.runtime, h3]⟩

-- ---------------------------------------------------------------------------
-- FiniteSubst
-- ---------------------------------------------------------------------------

structure FiniteSubst where
  subst : Subst
  dom   : List Var
  range : Signature

def FiniteSubst.id : FiniteSubst where
  subst := Subst.id
  dom   := []
  range := Signature.empty

def FiniteSubst.wf (σ : FiniteSubst) (Δ : Signature) : Prop :=
  σ.subst.wfIn σ.dom σ.range ∧ σ.range.Subset Δ ∧ σ.range.wf

def FiniteSubst.rename (σ : FiniteSubst) (v : Var) (name' : String) : FiniteSubst where
  subst := (σ.subst.eraseName v.name).update v.sort v.name (.const (.uninterpreted name' v.sort))
  dom   := v :: σ.dom.filter (·.name != v.name)
  range := σ.range.addConst ⟨name', v.sort⟩

theorem FiniteSubst.rename_dom_wf {σ : FiniteSubst} {v : Var} {name' : String}
    (hdomwf : (Signature.ofVars σ.dom).wf) :
    (Signature.ofVars (σ.rename v name').dom).wf := by
  simpa [FiniteSubst.rename, Signature.ofVars, Signature.declVar, Signature.remove] using
    (Signature.wf_declVar (Δ := Signature.ofVars σ.dom) (v := v) hdomwf)

theorem FiniteSubst.rename_wf {σ : FiniteSubst} {v : Var} {name' : String} {Δ : Signature}
    (hσ : σ.wf Δ) (hfresh : name' ∉ σ.range.allNames) :
    (σ.rename v name').wf (Δ.addConst ⟨name', v.sort⟩) := by
  rcases hσ with ⟨hsubst, hrange, hwfRange⟩
  constructor
  · have hrangeWf : (σ.range.addConst ⟨name', v.sort⟩).wf :=
      Signature.wf_addConst hwfRange hfresh
    have hsubst' : σ.subst.wfIn σ.dom (σ.range.addConst ⟨name', v.sort⟩) :=
      Subst.wfIn_mono hsubst (Signature.Subset.subset_addConst _ _) hrangeWf
    have herase :
        (σ.subst.eraseName v.name).wfIn (σ.dom.filter (fun w => w.name != v.name))
          (σ.range.addConst ⟨name', v.sort⟩) :=
      Subst.wfIn_eraseName hsubst'
    have hconstwf : (Term.const (.uninterpreted name' v.sort)).wfIn (σ.range.addConst ⟨name', v.sort⟩) := by
      refine ⟨List.Mem.head _, ?_, ?_⟩
      · intro τ' hvar
        exact Signature.wf_no_var_of_const hrangeWf (List.Mem.head _) hvar
      · intro τ' hc'
        exact Signature.wf_unique_const hrangeWf (List.Mem.head _) hc'
    simpa [FiniteSubst.rename] using
      (Subst.wfIn_update (σ := σ.subst.eraseName v.name)
        (dom := σ.dom.filter (fun w => w.name != v.name))
        (τ := v.sort) (x := v.name) herase hconstwf)
  · constructor
    · constructor
      · intro x hx
        exact hrange.vars x hx
      · intro c hc
        cases hc with
        | head => exact List.Mem.head _
        | tail _ hc => exact List.Mem.tail _ (hrange.consts c hc)
      · intro u hu
        exact hrange.unary u hu
      · intro b hb
        exact hrange.binary b hb
    · exact Signature.wf_addConst hwfRange hfresh

/-- Generic bundle for renaming `σ` on `v` to a fresh name `name'`. -/
theorem FiniteSubst.rename_bundle_of_fresh {σ : FiniteSubst} {decls : Signature}
    {v : Var} {name' : String}
    (hσwf : σ.wf decls) (hσdomwf : (Signature.ofVars σ.dom).wf)
    (_hfresh_decls : name' ∉ decls.allNames)
    (hfresh_range : name' ∉ σ.range.allNames) :
    let c : FOL.Const := ⟨name', v.sort⟩
    let σ' := σ.rename v name'
    σ'.wf (decls.addConst c) ∧
    (Signature.ofVars σ'.dom).wf := by
  exact ⟨FiniteSubst.rename_wf hσwf hfresh_range,
    FiniteSubst.rename_dom_wf hσdomwf⟩

/-- Standard bundle after declaring a fresh constant of `v.sort` and renaming `σ` on `v`:
    freshness facts and well-formedness of the renamed substitution in the extended
    signature. -/
theorem FiniteSubst.rename_bundle_of_freshConst {σ : FiniteSubst} {st : TransState}
    {hint : Option String} {v : Var}
    (hσwf : σ.wf st.decls) (hσdomwf : (Signature.ofVars σ.dom).wf) :
    let c := st.freshConst hint v.sort
    let σ' := σ.rename v c.name
    c.name ∉ st.decls.allNames ∧
    c.name ∉ σ.range.allNames ∧
    σ'.wf (st.decls.addConst c) ∧
    (Signature.ofVars σ'.dom).wf := by
  have hfresh_decls := TransState.freshConst_fresh st hint v.sort
  have hfresh_range : (st.freshConst hint v.sort).name ∉ σ.range.allNames :=
    fun h => hfresh_decls (Signature.allNames_subset hσwf.2.1 _ h)
  have hrename :=
    rename_bundle_of_fresh (v := v) (name' := (st.freshConst hint v.sort).name)
      hσwf hσdomwf hfresh_decls hfresh_range
  exact ⟨hfresh_decls, hfresh_range, hrename.1, hrename.2⟩

theorem FiniteSubst.rename_agreeOn {σ : FiniteSubst} {v : Var} {c : FOL.Const}
    {ρ : Env} {u : v.sort.denote}
    (hσwf : σ.subst.wfIn σ.dom σ.range) (hfresh : c.name ∉ σ.range.allNames)
    (hsort : c.sort = v.sort) :
    Env.agreeOn (Signature.ofVars (σ.rename v c.name).dom)
      ((σ.rename v c.name).subst.eval (ρ.updateConst v.sort c.name u))
      ((σ.subst.eval ρ).updateConst v.sort v.name u) := by
  constructor
  · intro w hw
    simp [FiniteSubst.rename, Signature.ofVars] at hw
    rcases hw with rfl | ⟨hwdom, hneq⟩
    · change
        Term.eval (ρ.updateConst w.sort c.name u)
          (((σ.subst.eraseName w.name).update w.sort w.name
            (Term.const (Const.uninterpreted c.name w.sort))).apply w.sort w.name) =
          (((σ.subst.eval ρ).updateConst w.sort w.name u).lookupConst w.sort w.name)
      simp [Subst.eval, Env.updateConst, Env.lookupConst, Subst.apply, Subst.update,
        Term.eval, Const.denote]
    · have hne : w.name ≠ v.name := hneq
      change
        Term.eval (ρ.updateConst v.sort c.name u)
            (((σ.subst.eraseName v.name).update v.sort v.name
              (Term.const (Const.uninterpreted c.name v.sort))).apply w.sort w.name) =
          ((σ.subst.eval ρ).updateConst v.sort v.name u).lookupConst w.sort w.name
      rw [Subst.apply_update_ne (Or.inl hne), Subst.apply_eraseName_ne hne,
        Env.lookupConst_updateConst_ne' (Or.inl hne), Subst.eval_lookup]
      exact (Term.eval_env_agree (hσwf.1 w hwdom)
        (Env.agreeOn_update_fresh_const (c := ⟨c.name, v.sort⟩) hfresh)).symm
  · simp [Signature.ofVars]

theorem FiniteSubst.rename_dom_declVar {σ : FiniteSubst} {Δ : Signature} {v : Var} {name' : String}
    (hdom : Δ.vars ⊆ σ.dom) :
    (Δ.declVar v).vars ⊆ (σ.rename v name').dom := by
  intro w hw
  simp [Signature.declVar, Signature.addVar, FiniteSubst.rename] at hw ⊢
  rcases hw with rfl | ⟨hw, hneq⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hdom hw, hneq⟩

theorem FiniteSubst.rename_agreeOn_declVar {σ : FiniteSubst} {decls : Signature}
    {v : Var} {c : FOL.Const} {ρ : Env} {u : v.sort.denote}
    (hσwf : σ.wf decls)
    (hfresh : c.name ∉ decls.allNames) (hsort : c.sort = v.sort) :
    Env.agreeOn ((Signature.ofVars σ.dom).declVar v)
      ((σ.rename v c.name).subst.eval (ρ.updateConst v.sort c.name u))
      ((σ.subst.eval ρ).updateConst v.sort v.name u) := by
  have hfresh_range : c.name ∉ σ.range.allNames := by
    intro h
    exact hfresh (Signature.allNames_subset hσwf.2.1 _ h)
  have hrename := FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := c) (ρ := ρ) (u := u)
    hσwf.1 hfresh_range hsort
  constructor
  · intro w hw
    exact hrename.1 w (FiniteSubst.rename_dom_declVar (σ := σ) (Δ := Signature.ofVars σ.dom) (v := v) (name' := c.name) (by intro x hx; exact hx) hw)
  · simp [Signature.declVar, Signature.ofVars, Signature.addVar, Signature.remove]

theorem FiniteSubst.eval_update_fresh {σ : FiniteSubst} {ρ : Env} {τ : Srt} {name' : String}
    {u : τ.denote} (hσ : σ.subst.wfIn σ.dom σ.range) (hfresh : name' ∉ σ.range.allNames) :
    Env.agreeOn (Signature.ofVars σ.dom) (σ.subst.eval ρ) (σ.subst.eval (ρ.updateConst τ name' u)) := by
  constructor
  · intro v hv
    exact Term.eval_env_agree (hσ.1 v hv) (Env.agreeOn_update_fresh_const (c := ⟨name', τ⟩) hfresh)
  · simp [Signature.ofVars]

theorem FiniteSubst.subst_wfIn_formula {σ : FiniteSubst} {φ : Formula} {Δ : Signature}
    (hσ : σ.wf Δ) (hφ : φ.wfIn (Signature.ofVars σ.dom)) (hwfΔ : Δ.wf) :
    (φ.subst σ.subst σ.range.allNames).wfIn Δ := by
  rcases hσ with ⟨hsubst, hrange, hwfRange⟩
  have hwf_range : (φ.subst σ.subst σ.range.allNames).wfIn σ.range := by
    simpa using
      (Formula.subst_wfIn (Δ := Signature.ofVars σ.dom) (Δ' := σ.range) hφ hsubst
        (Signature.SymbolSubset.ofVars _ _) hwfRange)
  exact Formula.wfIn_mono _ hwf_range hrange hwfΔ

theorem FiniteSubst.eval_subst_formula {σ : FiniteSubst} {φ : Formula} {ρ : Env}
    (hφ : φ.wfIn (Signature.ofVars σ.dom)) (hσ : σ.subst.wfIn σ.dom σ.range)
    (hdomwf : (Signature.ofVars σ.dom).wf) :
    σ.range.wf →
    ((φ.subst σ.subst σ.range.allNames).eval ρ ↔ φ.eval (σ.subst.eval ρ)) := by
  intro hwf
  exact Formula.eval_subst (ρ := ρ) hφ hσ (Signature.SymbolSubset.ofVars _ _) hdomwf hwf

theorem FiniteSubst.id_wf (Δ : Signature) : FiniteSubst.id.wf Δ := by
  constructor
  · apply Subst.id_wfIn
    · intro x hx; cases hx
    · exact Signature.wf_empty
  · constructor
    · constructor
      · intro _ h; cases h
      · intro _ h; cases h
      · intro _ h; cases h
      · intro _ h; cases h
    · exact Signature.wf_empty

theorem FiniteSubst.eval_agreeOn {σ : FiniteSubst} {ρ ρ' : Env}
    (hσ : σ.subst.wfIn σ.dom σ.range) (hagree : Env.agreeOn σ.range ρ ρ') :
    Env.agreeOn (Signature.ofVars σ.dom) (σ.subst.eval ρ) (σ.subst.eval ρ') := by
  constructor
  · intro v hv
    exact Term.eval_env_agree (hσ.1 v hv) hagree
  · simp [Signature.ofVars]
