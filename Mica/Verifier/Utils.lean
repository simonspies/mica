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

def FiniteSubst.base (Δ_base : Signature) : FiniteSubst where
  subst := Subst.id
  dom   := []
  range := Δ_base

/-- `σ.wfIn Δ_base Δ_use` separates the source and target sides of a finite substitution.

- `Δ_base` is the signature in which source formulas are written before substitution.
  It contributes ambient constants/unary/binary symbols, but no free variables of its own.
- `σ.dom` is the list of source variables that may be substituted, so source formulas are
  checked in `Δ_base.declVars σ.dom`.
- `σ.range` is the signature available inside the substituted terms themselves; it contains
  every symbol that may appear after substitution.
- `Δ_use` is the larger signature available at the eventual use site; substituted formulas
  are first shown well-formed in `σ.range`, then transported to `Δ_use` by monotonicity.

The well-formedness conditions enforce exactly that split:
- `σ.subst` is well-formed for the source variable context `Δ_base.declVars σ.dom`
  and produces terms in `σ.range`;
- every non-variable symbol from `Δ_base` is also available in `σ.range`;
- `σ.range` is available at the use site `Δ_use`;
- the source, range, and use signatures are themselves well-formed;
- `Δ_base` has no free variables of its own. -/
def FiniteSubst.wfIn (σ : FiniteSubst) (Δ_base Δ_use : Signature) : Prop :=
  σ.subst.wfIn (Δ_base.declVars σ.dom).vars σ.range ∧
  Δ_base.SymbolSubset σ.range ∧
  σ.range.Subset Δ_use ∧
  (Δ_base.declVars σ.dom).wf ∧
  σ.range.wf ∧
  Δ_use.wf ∧
  Δ_base.vars = []

abbrev FiniteSubst.wf := FiniteSubst.wfIn

def FiniteSubst.rename (σ : FiniteSubst) (v : Var) (name' : String) : FiniteSubst where
  subst := (σ.subst.remove v.name).update v.sort v.name (.const (.uninterpreted name' v.sort))
  dom   := σ.dom ++ [v]
  range := σ.range.addConst ⟨name', v.sort⟩

private theorem declVars_append_single (Δ : Signature) (vs : List Var) (v : Var) :
    Δ.declVars (vs ++ [v]) = (Δ.declVars vs).declVar v := by
  induction vs generalizing Δ with
  | nil => simp [Signature.declVars]
  | cons w vs ih =>
      simp [Signature.declVars]

/-- The source signature induced by a renamed substitution is exactly the old source
    signature with the renamed variable redeclared. -/
theorem FiniteSubst.rename_source_eq (σ : FiniteSubst) (Δ : Signature)
    (v : Var) (name' : String) :
    Δ.declVars (σ.rename v name').dom = (Δ.declVars σ.dom).declVar v := by
  simpa [FiniteSubst.rename] using declVars_append_single Δ σ.dom v

/-- Redeclaring `v` after all old source variables is contained in the source signature
    induced by `σ.rename v name'`. This is the direction used to transport assertion
    well-formedness after a verifier-side fresh declaration. -/
theorem FiniteSubst.rename_source_subset (σ : FiniteSubst) (Δ : Signature)
    (v : Var) (name' : String) :
    ((Δ.declVars σ.dom).declVar v).Subset
      (Δ.declVars (σ.rename v name').dom) := by
  rw [FiniteSubst.rename_source_eq]
  exact Signature.Subset.refl _

/-- Converse of `FiniteSubst.rename_source_subset`; useful for obligations that need
    to interpret renamed source variables back in the pre-rename source signature. -/
theorem FiniteSubst.rename_source_subset_rev (σ : FiniteSubst) (Δ : Signature)
    (v : Var) (name' : String) :
    (Δ.declVars (σ.rename v name').dom).Subset
      ((Δ.declVars σ.dom).declVar v) := by
  rw [FiniteSubst.rename_source_eq]
  exact Signature.Subset.refl _

/-- Renaming preserves well-formedness of the source signature. The proof uses that the
    renamed source has the same names, up to permutation, as the old source with `v`
    redeclared. -/
theorem FiniteSubst.rename_source_wf {σ : FiniteSubst} {Δ : Signature}
    {v : Var} {name' : String}
    (h : (Δ.declVars σ.dom).wf) :
    (Δ.declVars (σ.rename v name').dom).wf := by
  rw [FiniteSubst.rename_source_eq]
  exact Signature.wf_declVar h

private theorem subst_wfIn_dom_congr {σ : Subst} {dom dom' : VarCtx} {Δ : Signature}
    (hσ : σ.wfIn dom Δ) (h₁ : dom' ⊆ dom) (h₂ : dom ⊆ dom') :
    σ.wfIn dom' Δ :=
  ⟨fun v hv => hσ.1 v (h₁ hv),
   fun v hv => hσ.2 v (fun h => hv (h₂ h))⟩

private theorem subset_addConst_same {Δ Δ' : Signature} (h : Δ.Subset Δ') (c : FOL.Const) :
    (Δ.addConst c).Subset (Δ'.addConst c) :=
  ⟨h.vars,
   fun c' hc' => by
    cases hc' with
    | head => left
    | tail _ hc => exact List.mem_cons_of_mem _ (h.consts c' hc),
   h.unary,
   h.binary,
   h.unaryRel,
   h.binaryRel⟩

private theorem const_wfIn_addConst {Δ : Signature} {name : String} {τ : Srt}
    (hΔ : Δ.wf) (hfresh : name ∉ Δ.allNames) :
    (Term.const (.uninterpreted name τ)).wfIn (Δ.addConst ⟨name, τ⟩) := by
  simp only [Term.wfIn, Const.wfIn, Signature.addConst]
  have hΔ' : (Δ.addConst ⟨name, τ⟩).wf := Signature.wf_addConst hΔ hfresh
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro τ' hvar
    exact hfresh (Signature.mem_allNames_of_var hvar)
  · intro τ' hc'
    exact Signature.wf_unique_const hΔ' (List.Mem.head _) hc'

/-- Renaming a source variable to a fresh use-site constant preserves finite-substitution
    well-formedness, extending both the substitution range and the use-site signature by
    that fresh constant. -/
theorem FiniteSubst.rename_wfIn {σ : FiniteSubst} {Δ_base Δ_use : Signature}
    {v : Var} {name' : String}
    (hσ : σ.wfIn Δ_base Δ_use)
    (hfresh_range : name' ∉ σ.range.allNames)
    (hfresh_use : name' ∉ Δ_use.allNames) :
    (σ.rename v name').wfIn Δ_base (Δ_use.addConst ⟨name', v.sort⟩) := by
  rcases hσ with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
  have hrange_add_wf : (σ.range.addConst ⟨name', v.sort⟩).wf :=
    Signature.wf_addConst hrangewf hfresh_range
  have huse_add_wf : (Δ_use.addConst ⟨name', v.sort⟩).wf :=
    Signature.wf_addConst husewf hfresh_use
  have hconst_wf :
      (Term.const (.uninterpreted name' v.sort)).wfIn
        (σ.range.addConst ⟨name', v.sort⟩) :=
    const_wfIn_addConst hrangewf hfresh_range
  have hremove :
      (σ.subst.remove v.name).wfIn
        ((Δ_base.declVars σ.dom).remove v.name).vars
        (σ.range.addConst ⟨name', v.sort⟩) := by
    exact Subst.wfIn_mono (Subst.wfIn_remove hsubst)
      (Signature.Subset.subset_addConst _ _) hrange_add_wf
  have hupdate :
      ((σ.subst.remove v.name).update v.sort v.name
        (Term.const (.uninterpreted name' v.sort))).wfIn
        ((Δ_base.declVars σ.dom).declVar v).vars
        (σ.range.addConst ⟨name', v.sort⟩) := by
    simpa [Signature.declVar, Signature.addVar] using
      (Subst.wfIn_update (σ := σ.subst.remove v.name)
        (dom := ((Δ_base.declVars σ.dom).remove v.name).vars)
        (x := v.name) hremove hconst_wf)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hbasevars⟩
  · have hsub₁ :
        (Δ_base.declVars (σ.rename v name').dom).vars ⊆
          ((Δ_base.declVars σ.dom).declVar v).vars :=
      (FiniteSubst.rename_source_subset_rev σ Δ_base v name').vars
    have hsub₂ :
        ((Δ_base.declVars σ.dom).declVar v).vars ⊆
          (Δ_base.declVars (σ.rename v name').dom).vars :=
      (FiniteSubst.rename_source_subset σ Δ_base v name').vars
    simpa [FiniteSubst.rename] using subst_wfIn_dom_congr hupdate hsub₁ hsub₂
  · exact Signature.SymbolSubset.trans hbase (Signature.SymbolSubset.subset_addConst _ _)
  · exact subset_addConst_same huse ⟨name', v.sort⟩
  · exact FiniteSubst.rename_source_wf hsrcwf
  · exact hrange_add_wf
  · exact huse_add_wf

theorem declVars_symbolSubset {Δ_base : Signature} {vs : List Var} :
    (Δ_base.declVars vs).SymbolSubset Δ_base := by
  induction vs generalizing Δ_base with
  | nil =>
    simpa [Signature.declVars] using Signature.SymbolSubset.refl Δ_base
  | cons v vs ih =>
    simpa [Signature.declVars] using
      Signature.SymbolSubset.trans (ih (Δ_base := Δ_base.declVar v))
        (Signature.SymbolSubset.declVar (Signature.SymbolSubset.refl Δ_base) v)

theorem FiniteSubst.subst_wfIn_formula_range {σ : FiniteSubst} {φ : Formula}
    {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use)
    (hφ : φ.wfIn (Δ_base.declVars σ.dom)) :
    (φ.subst σ.subst σ.range.allNames).wfIn σ.range := by
  rcases hσ with ⟨hsubst, hbase, _huse, _hsrcwf, hrangewf, _husewf, _hbasevars⟩
  exact Formula.subst_wfIn hφ hsubst
    (Signature.SymbolSubset.trans declVars_symbolSubset hbase) hrangewf

theorem FiniteSubst.subst_wfIn_formula {σ : FiniteSubst} {φ : Formula}
    {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use)
    (hφ : φ.wfIn (Δ_base.declVars σ.dom)) :
    (φ.subst σ.subst σ.range.allNames).wfIn Δ_use := by
  have hrange := FiniteSubst.subst_wfIn_formula_range hσ hφ
  rcases hσ with ⟨_hsubst, _hbase, huse, _hsrcwf, _hrangewf, husewf, _hbasevars⟩
  exact Formula.wfIn_mono _ hrange huse husewf

theorem FiniteSubst.subst_wfIn_term_range {σ : FiniteSubst} {t : Term τ}
    {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use)
    (ht : t.wfIn (Δ_base.declVars σ.dom)) :
    (t.subst σ.subst).wfIn σ.range := by
  rcases hσ with ⟨hsubst, hbase, _huse, _hsrcwf, hrangewf, _husewf, _hbasevars⟩
  exact Term.subst_wfIn ht hsubst (by intro x hx; exact hx)
    (Signature.SymbolSubset.trans declVars_symbolSubset hbase) hrangewf

theorem FiniteSubst.subst_wfIn_term {σ : FiniteSubst} {t : Term τ}
    {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use)
    (ht : t.wfIn (Δ_base.declVars σ.dom)) :
    (t.subst σ.subst).wfIn Δ_use := by
  have hrange := FiniteSubst.subst_wfIn_term_range hσ ht
  rcases hσ with ⟨_hsubst, _hbase, huse, _hsrcwf, _hrangewf, husewf, _hbasevars⟩
  exact Term.wfIn_mono _ hrange huse husewf

theorem FiniteSubst.eval_subst_formula {σ : FiniteSubst} {φ : Formula} {ρ : Env}
    {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use)
    (hφ : φ.wfIn (Δ_base.declVars σ.dom)) :
    ((φ.subst σ.subst σ.range.allNames).eval ρ ↔ φ.eval (σ.subst.eval ρ)) := by
  rcases hσ with ⟨hsubst, hbase, _huse, hsrcwf, hrangewf, _husewf, _hbasevars⟩
  exact Formula.eval_subst hφ hsubst
    (Signature.SymbolSubset.trans declVars_symbolSubset hbase) hsrcwf hrangewf

theorem FiniteSubst.eval_subst_term {σ : FiniteSubst} {t : Term τ} {ρ : Env}
    {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use)
    (ht : t.wfIn (Δ_base.declVars σ.dom)) :
    Term.eval ρ (t.subst σ.subst) = Term.eval (σ.subst.eval ρ) t := by
  rcases hσ with ⟨hsubst, _hbase, _huse, _hsrcwf, hrangewf, _husewf, _hbasevars⟩
  exact Term.eval_subst ht hsubst hrangewf

theorem FiniteSubst.eval_agreeOn {σ : FiniteSubst} {ρ ρ' : Env}
    {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use)
    (hagree : Env.agreeOn Δ_use ρ ρ') :
    Env.agreeOn (Δ_base.declVars σ.dom) (σ.subst.eval ρ) (σ.subst.eval ρ') := by
  rcases hσ with ⟨hsubst, hbase, huse, hsrcwf, _hrangewf, _husewf, _hbasevars⟩
  have hagree_range : Env.agreeOn σ.range ρ ρ' := Env.agreeOn_mono huse hagree
  have hsymbols : (Δ_base.declVars σ.dom).SymbolSubset σ.range :=
    Signature.SymbolSubset.trans declVars_symbolSubset hbase
  constructor
  · intro v hv
    exact Term.eval_env_agree (hsubst.1 v hv) hagree_range
  · constructor
    · intro c hc
      have hc' : c ∈ σ.range.consts := hsymbols.consts c hc
      have hnot : ⟨c.name, c.sort⟩ ∉ (Δ_base.declVars σ.dom).vars := by
        intro hv
        exact Signature.wf_no_var_of_const hsrcwf hc hv
      have hvar : σ.subst.apply c.sort c.name = Term.var c.sort c.name := hsubst.2 _ hnot
      simp [Subst.eval, Term.eval, hvar]
      exact hagree_range.2.1 c hc'
    · constructor
      · intro u hu
        have hu' : u ∈ σ.range.unary := hsymbols.unary u hu
        exact hagree_range.2.2.1 u hu'
      · constructor
        · intro b hb
          have hb' : b ∈ σ.range.binary := hsymbols.binary b hb
          exact hagree_range.2.2.2.1 b hb'
        · constructor
          · intro u hu
            have hu' : u ∈ σ.range.unaryRel := hsymbols.unaryRel u hu
            exact hagree_range.2.2.2.2.1 u hu'
          · intro b hb
            have hb' : b ∈ σ.range.binaryRel := hsymbols.binaryRel b hb
            exact hagree_range.2.2.2.2.2 b hb'

theorem FiniteSubst.eval_update_fresh {σ : FiniteSubst} {ρ : Env} {τ : Srt} {name' : String}
    {u : τ.denote} {Δ_base Δ_use : Signature}
    (hσ : σ.wfIn Δ_base Δ_use) (hfresh : name' ∉ σ.range.allNames) :
    Env.agreeOn (Δ_base.declVars σ.dom) (σ.subst.eval ρ) (σ.subst.eval (ρ.updateConst τ name' u)) := by
  rcases hσ with ⟨hsubst, hbase, _huse, hsrcwf, _hrangewf, _husewf, _hbasevars⟩
  have hagree_range : Env.agreeOn σ.range ρ (ρ.updateConst τ name' u) :=
    Env.agreeOn_update_fresh_const (c := ⟨name', τ⟩) hfresh
  have hsymbols : (Δ_base.declVars σ.dom).SymbolSubset σ.range :=
    Signature.SymbolSubset.trans declVars_symbolSubset hbase
  constructor
  · intro v hv
    exact Term.eval_env_agree (hsubst.1 v hv) hagree_range
  · constructor
    · intro c hc
      have hc' : c ∈ σ.range.consts := hsymbols.consts c hc
      have hnot : ⟨c.name, c.sort⟩ ∉ (Δ_base.declVars σ.dom).vars := by
        intro hv
        exact Signature.wf_no_var_of_const hsrcwf hc hv
      have hvar : σ.subst.apply c.sort c.name = Term.var c.sort c.name := hsubst.2 _ hnot
      simp [Subst.eval, Term.eval, hvar]
      exact hagree_range.2.1 c hc'
    · constructor
      · intro u' hu
        exact hagree_range.2.2.1 u' (hsymbols.unary u' hu)
      · constructor
        · intro b hb
          exact hagree_range.2.2.2.1 b (hsymbols.binary b hb)
        · constructor
          · intro u' hu
            exact hagree_range.2.2.2.2.1 u' (hsymbols.unaryRel u' hu)
          · intro b hb
            exact hagree_range.2.2.2.2.2 b (hsymbols.binaryRel b hb)

/-- After `rename`, evaluating the renamed substitution in an environment containing the
    fresh verifier constant agrees with evaluating the old substitution and updating the
    source-level variable. -/
theorem FiniteSubst.rename_agreeOn {σ : FiniteSubst} {Δ_base Δ_use : Signature}
    {v : Var} {name' : String} {ρ : Env} {u : v.sort.denote}
    (hσ : σ.wfIn Δ_base Δ_use) (hfresh : name' ∉ σ.range.allNames) :
    Env.agreeOn (Δ_base.declVars (σ.rename v name').dom)
      ((σ.rename v name').subst.eval (ρ.updateConst v.sort name' u))
      ((σ.subst.eval ρ).updateConst v.sort v.name u) := by
  rcases hσ with ⟨hsubst, hbase, huse, hsrcwf, hrangewf, husewf, hbasevars⟩
  have hsymbols : (Δ_base.declVars σ.dom).SymbolSubset σ.range :=
    Signature.SymbolSubset.trans declVars_symbolSubset hbase
  have hlarge :
      Env.agreeOn ((Δ_base.declVars σ.dom).declVar v)
        ((σ.rename v name').subst.eval (ρ.updateConst v.sort name' u))
        ((σ.subst.eval ρ).updateConst v.sort v.name u) := by
    constructor
    · intro w hw
      simp [Signature.declVar, Signature.addVar] at hw
      rcases hw with rfl | hw
      · simp [FiniteSubst.rename, Subst.eval, Env.updateConst, Subst.apply,
          Subst.update, Term.eval, Const.denote]
      · rcases hw with ⟨hwsrc, hwne⟩
        have hwne' : w.name ≠ v.name := hwne
        change Term.eval (ρ.updateConst v.sort name' u)
            (((σ.subst.remove v.name).update v.sort v.name
              (Term.const (Const.uninterpreted name' v.sort))).apply w.sort w.name) =
          ((σ.subst.eval ρ).updateConst v.sort v.name u).lookupConst w.sort w.name
        rw [Subst.apply_update_ne (Or.inl hwne'), Subst.apply_remove_ne hwne',
          Env.lookupConst_updateConst_ne' (Or.inl hwne'), Subst.eval_lookup]
        exact (Term.eval_env_agree (hsubst.1 w hwsrc)
          (Env.agreeOn_update_fresh_const (c := ⟨name', v.sort⟩) hfresh)).symm
    · constructor
      · intro c hc
        simp [Signature.declVar, Signature.addVar] at hc
        rcases hc with ⟨hcsrc, hcne⟩
        have hnotvar : ⟨c.name, c.sort⟩ ∉ (Δ_base.declVars σ.dom).vars := by
          intro hv
          exact Signature.wf_no_var_of_const hsrcwf hcsrc hv
        have hvar : σ.subst.apply c.sort c.name = Term.var c.sort c.name := hsubst.2 _ hnotvar
        have hcne' : c.name ≠ v.name := hcne
        have hc_range : c ∈ σ.range.consts := hsymbols.consts c hcsrc
        have hname : c.name ≠ name' := by
          intro heq
          exact hfresh (by
            rw [← heq]
            exact Signature.mem_allNames_of_const hc_range)
        change Term.eval (ρ.updateConst v.sort name' u)
            (((σ.subst.remove v.name).update v.sort v.name
              (Term.const (Const.uninterpreted name' v.sort))).apply c.sort c.name) =
          ((σ.subst.eval ρ).updateConst v.sort v.name u).lookupConst c.sort c.name
        rw [Subst.apply_update_ne (Or.inl hcne'), Subst.apply_remove_ne hcne',
          Env.lookupConst_updateConst_ne' (Or.inl hcne'), Subst.eval_lookup, hvar]
        simp only [Term.eval, Env.lookupConst]
        by_cases hs : c.sort = v.sort
        · cases c
          simp only at hs hname
          subst hs
          simp [Env.updateConst, hname]
        · simp [Env.updateConst, hs]
      · constructor
        · intro unary hunary
          simp [Subst.eval, Env.updateConst]
        · constructor
          · intro binary hbinary
            simp [Subst.eval, Env.updateConst]
          · constructor
            · intro unaryRel hunaryRel
              simp [Subst.eval, Env.updateConst]
            · intro binaryRel hbinaryRel
              simp [Subst.eval, Env.updateConst]
  exact Env.agreeOn_mono (FiniteSubst.rename_source_subset_rev σ Δ_base v name') hlarge

theorem FiniteSubst.id_wf {Δ_use : Signature}
    (husewf : Δ_use.wf) :
    FiniteSubst.id.wfIn Signature.empty Δ_use := by
  refine ⟨?_, ?_, ?_, ?_, Signature.wf_empty, husewf, rfl⟩
  · apply Subst.id_wfIn
    · intro x hx
      cases hx
    · exact Signature.wf_empty
  · constructor
    · intro c hc
      cases hc
    · intro u hu
      cases hu
    · intro b hb
      cases hb
    · intro u hu
      cases hu
    · intro b hb
      cases hb
  · constructor
    · intro x hx
      cases hx
    · intro c hc
      cases hc
    · intro u hu
      cases hu
    · intro b hb
      cases hb
    · intro u hu
      cases hu
    · intro b hb
      cases hb
  · simp [FiniteSubst.id, Signature.empty, Signature.declVars, Signature.wf, Signature.allNames]

theorem FiniteSubst.base_wfIn {Δ_base Δ_use : Signature}
    (hbase : Δ_base.Subset Δ_use) (hbasewf : Δ_base.wf) (husewf : Δ_use.wf)
    (hvars : Δ_base.vars = []) :
    (FiniteSubst.base Δ_base).wfIn Δ_base Δ_use := by
  refine ⟨?_, Signature.SymbolSubset.refl Δ_base, hbase, ?_, hbasewf, husewf, hvars⟩
  · apply Subst.id_wfIn
    · intro v hv
      simp [FiniteSubst.base, Signature.declVars, hvars] at hv
    · exact hbasewf
  · simpa [FiniteSubst.base, Signature.declVars] using hbasewf
