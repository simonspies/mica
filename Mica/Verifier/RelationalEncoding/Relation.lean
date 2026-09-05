-- SUMMARY: Stage 1 — encode a recursive TinyML body as a binary FOL relation defined by least fixpoint.
import Mica.Verifier.RelationalEncoding.Expr

/-!
# Relational encoding of recursive TinyML bodies

First stage of the encoding. A recursive definition `rec f x := e` becomes a
binary FOL relation, interpreted as the least fixpoint of the encoded body
operator. Diverging inputs are absent from the relation.
-/
def Formula.iteBool (cond : Term .bool) (φ ψ : Formula) : Formula :=
  .and (.implies (.eq .bool cond (.const (.b true)))  φ)
       (.implies (.eq .bool cond (.const (.b false))) ψ)

theorem Formula.iteBool_wfIn {cond : Term .bool} {φ ψ : Formula} {Δ : Signature}
    (hc : cond.wfIn Δ) (hφ : φ.wfIn Δ) (hψ : ψ.wfIn Δ) :
    (Formula.iteBool cond φ ψ).wfIn Δ := by
  simp [Formula.iteBool, Formula.wfIn, Term.wfIn, Const.wfIn, hc, hφ, hψ]

namespace Verifier.RelationalEncoding

abbrev ValRel : Type := RelationFix.Rel Srt.value.denote Srt.value.denote

/-- Interpret `fn`'s relation as `R` and pin the input and result variables. -/
def _root_.SpecFn.Env.rel (ρ : Env) (fn : SpecFn) (x res : TinyML.Var)
    (R : ValRel) (vin vout : Srt.value.denote) : Env :=
  ((ρ.updateBinaryRel .value .value fn.relName R).updateConst .value x vin).updateConst
    .value res vout

/-! ## Reading the IR as a formula -/

/-- Translate the IR into a formula pinned at the result variable `res`: a call
binds its result name existentially and asserts the relation. -/
def Expr.toFormula (res : String) : Expr → Formula
  | .ret v           => .eq .value v (.var .value res)
  | .call fn arg r c => .exists_ r .value (.and (fn.relates arg (.var .value r)) (toFormula res c))
  | .ite cond t e    => Formula.iteBool cond (toFormula res t) (toFormula res e)

theorem Expr.toFormula_wfIn {Γ : FunCtx} {res : String} {avoid : List String} {Δ : Signature}
    {c : Expr} (hc : Expr.WfIn Γ avoid Δ c) (hΓ : Γ.relWfIn Δ) (hΔ : Δ.wf)
    (hres : (⟨res, .value⟩ : Var) ∈ Δ.vars) :
    (toFormula res c).wfIn Δ := by
  induction hc with
  | ret hv => exact ⟨hv, var_value_wfIn hΔ hres⟩
  | @call Δ f fn arg r c hmem harg _ hfresh _ ih =>
      have hsub : Δ.Subset (Δ.declVar ⟨r, .value⟩) := Signature.subset_declVar_of_fresh hfresh
      have hΔ' : (Δ.declVar ⟨r, .value⟩).wf := Signature.wf_declVar hΔ
      have hrvar : (Term.var .value r).wfIn (Δ.declVar ⟨r, .value⟩) :=
        var_value_wfIn hΔ' (Signature.var_mem_declVar _ _)
      refine ⟨SpecFn.relates_wfIn (hsub.binaryRel _ (hΓ f fn hmem)) hΔ'
        (Term.wfIn_mono _ harg hsub hΔ') hrvar, ?_⟩
      exact ih (FunCtx.relWfIn_mono hΓ hsub) hΔ' (hsub.vars _ hres)
  | ite hcond _ _ iht ihe =>
      exact Formula.iteBool_wfIn hcond (iht hΓ hΔ hres) (ihe hΓ hΔ hres)

theorem Expr.toFormula_mono (res : String) (c : Expr) :
    Eval.Mono Formula.eval (toFormula res c) := by
  induction c with
  | ret v =>
      intro ρ ρ' hle h
      simp only [toFormula, Formula.eval] at h ⊢
      rw [← Term.eval_env_le hle, ← Term.eval_env_le hle]; exact h
  | call fn arg r c ih =>
      intro ρ ρ' hle h
      simp only [toFormula, Formula.eval] at h ⊢
      rcases h with ⟨w, hcall, hbody⟩
      refine ⟨w, ?_, ih (hle.updateConst .value r w) hbody⟩
      simp only [SpecFn.relates, Formula.eval, BinPred.eval] at hcall ⊢
      have hleU : Env.le (ρ.updateConst .value r w) (ρ'.updateConst .value r w) :=
        Env.le.updateConst hle .value r w
      rw [← Term.eval_env_le hleU, ← Term.eval_env_le hleU]
      exact hleU.2.2.2.2.2 _ _ _ _ _ hcall
  | ite cond t e iht ihe =>
      intro ρ ρ' hle h
      simp only [toFormula, Formula.iteBool, Formula.eval] at h ⊢
      constructor
      · intro hcond
        exact iht hle (h.1 (by rw [Term.eval_env_le hle]; exact hcond))
      · intro hcond
        exact ihe hle (h.2 (by rw [Term.eval_env_le hle]; exact hcond))

/-! ## Determinism -/

/-- The relation symbols of `Γ` relate each input to at most one output, across
the two environments. -/
def FunCtx.Functional (Γ : FunCtx) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ vin y₁ y₂,
      fn.evalRelates ρ₁ vin y₁ →
      fn.evalRelates ρ₂ vin y₂ →
      y₁ = y₂

/-- A relational formula determines `res` when two environments that agree on
the terms of `Δ` and on the relations of `Γ` and both satisfy it must also agree
on `res`. -/
private def _root_.Formula.Determines (φ : Formula) (Γ : FunCtx) (Δ : Signature)
    (res : String) : Prop :=
  ∀ ρ₁ ρ₂, Γ.Functional ρ₁ ρ₂ → Env.agreeOnTerms Δ ρ₁ ρ₂ →
    φ.eval ρ₁ → φ.eval ρ₂ →
    ρ₁.lookupConst .value res = ρ₂.lookupConst .value res

private theorem Expr.toFormula_determines {Γ : FunCtx} {res : String} {avoid : List String}
    {Δ : Signature} {c : Expr} (hc : Expr.WfIn Γ avoid Δ c) (hΔ : Δ.wf) (hres : res ∈ avoid) :
    (toFormula res c).Determines Γ Δ res := by
  induction hc with
  | @ret Δ v hv =>
      intro ρ₁ ρ₂ _ hagree hφ₁ hφ₂
      simp only [toFormula, Formula.eval, Term.eval] at hφ₁ hφ₂
      rw [← hφ₁, ← hφ₂, Term.eval_agreeOnTerms hv hagree]
  | @call Δ f fn arg r c hmem harg hr hfresh _ ih =>
      intro ρ₁ ρ₂ hrel hagree hφ₁ hφ₂
      have hsub : Δ.Subset (Δ.declVar ⟨r, .value⟩) := Signature.subset_declVar_of_fresh hfresh
      have hΔ' : (Δ.declVar ⟨r, .value⟩).wf := Signature.wf_declVar hΔ
      have hres_ne : res ≠ r := fun heq => hr (heq ▸ hres)
      have hargΔ' : arg.wfIn (Δ.declVar ⟨r, .value⟩) := Term.wfIn_mono _ harg hsub hΔ'
      simp only [toFormula, Formula.eval] at hφ₁ hφ₂
      rcases hφ₁ with ⟨w₁, hcall₁, hbody₁⟩
      rcases hφ₂ with ⟨w₂, hcall₂, hbody₂⟩
      have hagree' : Env.agreeOnTerms (Δ.declVar ⟨r, .value⟩)
          (ρ₁.updateConst .value r w₁) (ρ₂.updateConst .value r w₁) :=
        Env.agreeOnTerms_declVar (x := r) (τ := .value) (v := w₁) hagree
      simp only [SpecFn.relates, Formula.eval, BinPred.eval, Term.eval] at hcall₁ hcall₂
      have hw : w₁ = w₂ := by
        refine hrel f fn hmem (arg.eval (ρ₁.updateConst .value r w₁)) w₁ w₂ ?_ ?_
        · simpa [SpecFn.evalRelates, Env.updateConst_binaryRel,
            Env.lookupConst_updateConst_same] using hcall₁
        · rw [Term.eval_agreeOnTerms hargΔ' hagree',
            Term.eval_agreeOnTerms harg
              (Env.agreeOnTerms_of_agreeOn (Env.agreeOn_trans
                (Env.agreeOn_symm (Env.agreeOn_update_fresh_const
                  (ρ := ρ₂) (c := ⟨r, .value⟩) (u := w₁) hfresh))
                (Env.agreeOn_update_fresh_const
                  (ρ := ρ₂) (c := ⟨r, .value⟩) (u := w₂) hfresh)))]
          simpa [SpecFn.evalRelates, Env.updateConst_binaryRel,
            Env.lookupConst_updateConst_same] using hcall₂
      subst hw
      have hrelUpd : FunCtx.Functional Γ
          (ρ₁.updateConst .value r w₁) (ρ₂.updateConst .value r w₁) := by
        intro f' fn' hmem' vin y₁ y₂ hy₁ hy₂
        simp only [SpecFn.evalRelates_updateConst] at hy₁ hy₂
        exact hrel f' fn' hmem' vin y₁ y₂ hy₁ hy₂
      have := ih hΔ' _ _ hrelUpd hagree' hbody₁ hbody₂
      simpa [Env.lookupConst_updateConst_ne hres_ne] using this
  | @ite Δ cond t e hcond _ _ iht ihe =>
      intro ρ₁ ρ₂ hrel hagree hφ₁ hφ₂
      simp only [toFormula, Formula.iteBool, Formula.eval] at hφ₁ hφ₂
      have hcondEq : cond.eval ρ₁ = cond.eval ρ₂ := Term.eval_agreeOnTerms hcond hagree
      cases hc : cond.eval ρ₁ with
      | false =>
          exact ihe hΔ ρ₁ ρ₂ hrel hagree (hφ₁.2 hc) (hφ₂.2 (by rw [← hcondEq]; exact hc))
      | true =>
          exact iht hΔ ρ₁ ρ₂ hrel hagree (hφ₁.1 hc) (hφ₂.1 (by rw [← hcondEq]; exact hc))

/-! ## The relation a formula denotes -/

namespace Relation

/-- One unfolding of an encoded body: read the formula in the environment that
interprets the head relation as the recursive candidate. -/
def eval (φ : Formula) (ρ : Env) (fn : SpecFn) (x res : TinyML.Var) : ValRel → ValRel :=
  fun self vin vout => φ.eval (SpecFn.Env.rel ρ fn x res self vin vout)

def fixpoint (φ : Formula) (ρ : Env) (fn : SpecFn) (x res : TinyML.Var) : ValRel :=
  RelationFix.lfp (eval φ ρ fn x res)

theorem eval_mono {φ : Formula} {ρ : Env} {fn : SpecFn} {x res : TinyML.Var}
    (hm : Eval.Mono Formula.eval φ) : RelationFix.Mono (eval φ ρ fn x res) := by
  intro S S' hSS' vin vout hF
  have hle : Env.le (SpecFn.Env.rel ρ fn x res S vin vout)
                    (SpecFn.Env.rel ρ fn x res S' vin vout) := by
    refine Env.le.updateConst (Env.le.updateConst ?_ _ _ _) _ _ _
    refine ⟨rfl, rfl, rfl, rfl, fun _ _ _ h => h, ?_⟩
    intro τ₁ τ₂ name a b
    simp only [Env.updateBinaryRel]
    split
    · rename_i heq; rcases heq with ⟨rfl, rfl, rfl⟩
      intro h; exact hSS' a b h
    · intro h; exact h
  exact hm hle hF

end Relation

/-! ## Body encoding -/

/-- The encoder IR of `rec f x := e`'s body. Both readings consume it. -/
def encodeBody (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String Expr :=
  encode primitives Δ (Γ.recursive f fn) (VarEnv.ofSignature (SpecFn.Sig.relArg Δ fn x)) e
    (SpecFn.supply Δ fn x res)

/-- The body of `rec f x := e` as a closed FOL formula pinned at `res`. -/
def encodeFormula (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String Formula :=
  Expr.toFormula res <$> encodeBody primitives Γ Δ f fn x res e

end Verifier.RelationalEncoding

/-! ## What the relation symbol denotes -/

namespace SpecFn.Semantics
open Verifier.RelationalEncoding

/-- Least-fixpoint relational interpretation of `rec f x := e`. A body that
fails to encode denotes the empty relation. -/
def rel (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    ValRel :=
  match encodeFormula primitives Γ Δ f fn x res e with
  | .error _ => fun _ _ => False
  | .ok φ    => Relation.fixpoint φ ρ fn x res

/-- The relation induced by an encoded pure body is functional. -/
theorem rel_functional_of_encodeBody
    {primitives : PrimEncodings} {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {c : Expr}
    (hlaw : primitives.Lawful)
    (henc : encodeBody primitives Γ Δ f fn x res e = .ok c)
    (hΓ : Γ.relWfIn Δ)
    (hrelFresh : fn.relName ∉ Δ.allNames)
    (hsubBody : Δ.Subset (Sig.relArg Δ fn x))
    (hΔbody : (Sig.relArg Δ fn x).wf)
    (hresFresh : res ∉ (Sig.relArg Δ fn x).allNames)
    (hρdet : Γ.Functional ρ ρ)
    (vin y₁ y₂ : Srt.value.denote) :
    rel primitives Γ Δ ρ f fn x res e vin y₁ →
      rel primitives Γ Δ ρ f fn x res e vin y₂ →
      y₁ = y₂ := by
  set body := Expr.toFormula res c with hbody_def
  let F : ValRel → ValRel := Relation.eval body ρ fn x res
  let R : ValRel := rel primitives Γ Δ ρ f fn x res e
  have hR : R = RelationFix.lfp F := by
    simp [R, F, rel, Relation.fixpoint, encodeFormula, henc, hbody_def]
  have hmono : RelationFix.Mono F :=
    Relation.eval_mono (ρ := ρ) (fn := fn) (x := x) (res := res)
      (Expr.toFormula_mono res c)
  have hxres : x ≠ res := by
    intro h
    exact hresFresh (by
      simp [Sig.relArg, Sig.rel, Signature.declVar, Signature.addVar, Signature.allNames, h])
  have hcovBody : (SpecFn.supply Δ fn x res).Covers (Sig.relArg Δ fn x) := by
    intro n hn
    by_contra hnAvoid
    have hnΔ : n ∉ Δ.allNames := fun h => hnAvoid (by simp [supply, reserved, names, h])
    have hnRel : n ≠ fn.relName := fun h => hnAvoid (by simp [supply, reserved, names, h])
    have hnX : n ≠ x := fun h => hnAvoid (by simp [supply, reserved, names, h])
    exact (Signature.not_mem_allNames_declVar
      (Signature.not_mem_allNames_addBinaryRel hnΔ hnRel) hnX)
      (by simpa [Sig.relArg, Sig.rel] using hn)
  have hcWf : Expr.WfIn (Γ.recursive f fn) (reserved fn x res) (Sig.relArg Δ fn x) c :=
    (encode_wfIn hlaw e hsubBody hΔbody (VarEnv.ofSignature_wfIn hΔbody)
      hcovBody henc).weaken reserved_subset_supply
  have hdet : body.Determines (Γ.recursive f fn) (Sig.relArg Δ fn x) res :=
    Expr.toFormula_determines hcWf hΔbody (by simp [reserved, names])
  let S : ValRel := fun a b => R a b ∧ ∀ b', R a b' → b = b'
  have hSleR : RelationFix.le S R := fun _ _ h => h.1
  have hpre : RelationFix.le (F S) S := by
    intro a b hFS
    constructor
    · rw [hR]
      have hFR : F R a b := hmono hSleR a b hFS
      rw [hR] at hFR
      exact RelationFix.lfp_prefixed hmono a b hFR
    · intro b' hRb'
      have hFR : F R a b' := by
        have hFRlfp : F (RelationFix.lfp F) a b' := by
          rw [hR] at hRb'
          exact (RelationFix.lfp_unfold hmono a b').mp hRb'
        simpa [hR] using hFRlfp
      have hrelDet :
          FunCtx.Functional (Γ.recursive f fn)
            (Env.rel ρ fn x res S a b)
            (Env.rel ρ fn x res R a b') := by
        intro f' fn' hmem' vin' z₁ z₂ hz₁ hz₂
        cases hmem' with
        | head =>
            simp [evalRelates, SpecFn.rel, Env.rel,
              _root_.Env.updateConst_binaryRel, _root_.Env.updateBinaryRel] at hz₁ hz₂
            exact hz₁.2 z₂ hz₂
        | tail _ htail =>
            have hrel'_mem : fn'.rel ∈ Δ.binaryRel := hΓ f' fn' htail
            have hne : fn'.relName ≠ fn.relName := fun h =>
              hrelFresh (h ▸ Signature.mem_allNames_of_binaryRel hrel'_mem)
            simp only [evalRelates, SpecFn.rel, Env.rel,
              _root_.Env.updateConst_binaryRel, _root_.Env.updateBinaryRel] at hz₁ hz₂
            simp [hne] at hz₁ hz₂
            exact hρdet f' fn' htail vin' z₁ z₂ hz₁ hz₂
      have hagreeOnTerms :
          _root_.Env.agreeOnTerms (Sig.relArg Δ fn x)
            (Env.rel ρ fn x res S a b)
            (Env.rel ρ fn x res R a b') := by
        unfold Sig.relArg Env.rel
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro v hv
          have hv' : v ∈ ⟨x, .value⟩ ::
              ((Δ.addBinaryRel fn.rel).remove x).vars := by
            simpa [Sig.rel, Signature.declVar, Signature.addVar] using hv
          cases hv' with
          | head =>
              simp [_root_.Env.updateConst, _root_.Env.updateBinaryRel, hxres]
          | tail _ htail =>
              have hneX : v.name ≠ x := by
                intro hxv
                have hmem : v.name ∈
                    ((Δ.addBinaryRel fn.rel).remove x).allNames :=
                  Signature.mem_allNames_of_var htail
                exact Signature.remove_allNames hmem hxv
              have hneRes : v.name ≠ res := by
                intro hres
                have hmem : v.name ∈ (Sig.relArg Δ fn x).allNames :=
                  Signature.mem_allNames_of_var hv
                exact hresFresh (hres ▸ hmem)
              simp [_root_.Env.updateConst, _root_.Env.updateBinaryRel, hneX, hneRes]
        · intro c hc
          have hneX : c.name ≠ x := by
            intro hcx
            have hmem : c.name ∈
                ((Δ.addBinaryRel fn.rel).remove x).allNames :=
              Signature.mem_allNames_of_const (by
                simpa [Sig.relArg, Sig.rel, Signature.declVar, Signature.addVar] using hc)
            exact Signature.remove_allNames hmem hcx
          have hneRes : c.name ≠ res := by
            intro hres
            have hmem : c.name ∈ (Sig.relArg Δ fn x).allNames :=
              Signature.mem_allNames_of_const hc
            exact hresFresh (hres ▸ hmem)
          simp [_root_.Env.updateConst, _root_.Env.updateBinaryRel, hneX, hneRes]
        · intro u hu
          simp [_root_.Env.updateConst_unary, _root_.Env.updateBinaryRel]
        · intro bin hbin
          simp [_root_.Env.updateConst_binary, _root_.Env.updateBinaryRel]
        · intro t ht
          simp [_root_.Env.updateConst_ternary, _root_.Env.updateBinaryRel]
      have hresEq :=
        hdet (Env.rel ρ fn x res S a b) (Env.rel ρ fn x res R a b')
          hrelDet hagreeOnTerms hFS hFR
      simpa [Env.rel, _root_.Env.lookupConst_updateConst_same] using hresEq
  intro hy₁ hy₂
  have hy₁S : S vin y₁ := by
    change R vin y₁ at hy₁
    rw [hR] at hy₁
    exact RelationFix.lfp_le_of_prefixed hpre vin y₁ hy₁
  exact hy₁S.2 y₂ hy₂

end SpecFn.Semantics
