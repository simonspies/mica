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
namespace Relation

abbrev ValRel : Type := RelationFix.Rel Srt.value.denote Srt.value.denote

def relEnv (ρ : Env) (fn : SpecFn) (x res : TinyML.Var)
    (self : ValRel) (vin vout : Srt.value.denote) : Env :=
  let ρ1 := ρ.updateBinaryRel .value .value fn.relName self
  let ρ2 := ρ1.updateConst .value x vin
  ρ2.updateConst .value res vout

def semanticBody {M : Type} (sem : SemPred M)
    (ρ : Env) (fn : SpecFn) (x res : TinyML.Var) (m : M) : ValRel → ValRel :=
  fun self vin vout => sem m (relEnv ρ fn x res self vin vout)

def semanticFixpoint {M : Type} (encoded : Except String M) (sem : SemPred M)
    (ρ : Env) (fn : SpecFn) (x res : TinyML.Var) : ValRel :=
  match encoded with
  | .error _ => fun _ _ => False
  | .ok m    => RelationFix.lfp (semanticBody sem ρ fn x res m)

theorem semanticBody_mono_of_semanticMono {M : Type} {sem : SemPred M}
    {ρ : Env} {fn : SpecFn} {x res : TinyML.Var} {m : M}
    (hm : SemanticMono sem m) :
    RelationFix.Mono (semanticBody sem ρ fn x res m) := by
  intro S S' hSS' vin vout hF
  have hle : Env.le (relEnv ρ fn x res S vin vout)
                    (relEnv ρ fn x res S' vin vout) := by
    refine Env.le.updateConst (Env.le.updateConst ?_ _ _ _) _ _ _
    refine ⟨rfl, rfl, rfl, rfl, fun _ _ _ h => h, ?_⟩
    intro τ₁ τ₂ name a b
    simp only [Env.updateBinaryRel]
    split
    · rename_i heq; rcases heq with ⟨rfl, rfl, rfl⟩
      intro h; exact hSS' a b h
    · intro h; exact h
  exact hm hle hF

/-! ## From the IR to a formula -/

/-- Translate the IR into a formula pinned at the result variable `res`: a call
binds its result name existentially and asserts the relation. -/
def ofExpr (res : String) : Expr → Formula
  | .ret v           => .eq .value v (.var .value res)
  | .call fn arg r c => .exists_ r .value (.and (fn.relates arg (.var .value r)) (ofExpr res c))
  | .ite cond t e    => Formula.iteBool cond (ofExpr res t) (ofExpr res e)

def Formula.sem (φ : Formula) (ρ : Env) : Prop :=
  φ.eval ρ

theorem ofExpr_wfIn {Γ : FunCtx} {res : String} {avoid : List String} {Δ : Signature}
    {c : Expr} (hc : Expr.WfIn Γ avoid Δ c) (hΓ : Γ.relWfIn Δ) (hΔ : Δ.wf)
    (hres : (⟨res, .value⟩ : Var) ∈ Δ.vars) :
    (ofExpr res c).wfIn Δ := by
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

theorem ofExpr_mono (res : String) (c : Expr) : SemanticMono Formula.sem (ofExpr res c) := by
  induction c with
  | ret v =>
      intro ρ ρ' hle h
      unfold Formula.sem at h ⊢
      simp only [ofExpr, Formula.eval] at h ⊢
      rw [← Term.eval_env_le hle, ← Term.eval_env_le hle]; exact h
  | call fn arg r c ih =>
      intro ρ ρ' hle h
      unfold Formula.sem at h ⊢
      simp only [ofExpr, Formula.eval] at h ⊢
      rcases h with ⟨w, hcall, hbody⟩
      refine ⟨w, ?_, ih (hle.updateConst .value r w) hbody⟩
      simp only [SpecFn.relates, Formula.eval, BinPred.eval] at hcall ⊢
      have hleU : Env.le (ρ.updateConst .value r w) (ρ'.updateConst .value r w) :=
        Env.le.updateConst hle .value r w
      rw [← Term.eval_env_le hleU, ← Term.eval_env_le hleU]
      exact hleU.2.2.2.2.2 _ _ _ _ _ hcall
  | ite cond t e iht ihe =>
      intro ρ ρ' hle h
      unfold Formula.sem at h ⊢
      simp only [ofExpr, Formula.iteBool, Formula.eval] at h ⊢
      constructor
      · intro hcond
        exact iht hle (h.1 (by rw [Term.eval_env_le hle]; exact hcond))
      · intro hcond
        exact ihe hle (h.2 (by rw [Term.eval_env_le hle]; exact hcond))

/-! ## Determinism -/

/-- Cross-environment determinism for the relation symbols registered in `Γ`. -/
def BinaryRelDet (Γ : FunCtx) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ vin y₁ y₂,
      fn.evalRelates ρ₁ vin y₁ →
      fn.evalRelates ρ₂ vin y₂ →
      y₁ = y₂

/-- A relational formula is deterministic in `res` when two environments that
agree on the terms of `Δ` and on the relations of `Γ` and both satisfy it must
also agree on `res`. -/
def Det (Γ : FunCtx) (res : String) (Δ : Signature) (φ : Formula) : Prop :=
  ∀ ρ₁ ρ₂, BinaryRelDet Γ ρ₁ ρ₂ → Env.agreeOnTerms Δ ρ₁ ρ₂ →
    φ.eval ρ₁ → φ.eval ρ₂ →
    ρ₁.lookupConst .value res = ρ₂.lookupConst .value res

theorem ofExpr_det {Γ : FunCtx} {res : String} {avoid : List String} {Δ : Signature}
    {c : Expr} (hc : Expr.WfIn Γ avoid Δ c) (hΔ : Δ.wf) (hres : res ∈ avoid) :
    Det Γ res Δ (ofExpr res c) := by
  induction hc with
  | @ret Δ v hv =>
      intro ρ₁ ρ₂ _ hagree hφ₁ hφ₂
      simp only [ofExpr, Formula.eval, Term.eval] at hφ₁ hφ₂
      rw [← hφ₁, ← hφ₂, Term.eval_agreeOnTerms hv hagree]
  | @call Δ f fn arg r c hmem harg hr hfresh _ ih =>
      intro ρ₁ ρ₂ hrel hagree hφ₁ hφ₂
      have hsub : Δ.Subset (Δ.declVar ⟨r, .value⟩) := Signature.subset_declVar_of_fresh hfresh
      have hΔ' : (Δ.declVar ⟨r, .value⟩).wf := Signature.wf_declVar hΔ
      have hres_ne : res ≠ r := fun heq => hr (heq ▸ hres)
      have hargΔ' : arg.wfIn (Δ.declVar ⟨r, .value⟩) := Term.wfIn_mono _ harg hsub hΔ'
      simp only [ofExpr, Formula.eval] at hφ₁ hφ₂
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
      have hrelUpd : BinaryRelDet Γ
          (ρ₁.updateConst .value r w₁) (ρ₂.updateConst .value r w₁) := by
        intro f' fn' hmem' vin y₁ y₂ hy₁ hy₂
        simp only [SpecFn.evalRelates_updateConst] at hy₁ hy₂
        exact hrel f' fn' hmem' vin y₁ y₂ hy₁ hy₂
      have := ih hΔ' _ _ hrelUpd hagree' hbody₁ hbody₂
      simpa [Env.lookupConst_updateConst_ne hres_ne] using this
  | @ite Δ cond t e hcond _ _ iht ihe =>
      intro ρ₁ ρ₂ hrel hagree hφ₁ hφ₂
      simp only [ofExpr, Formula.iteBool, Formula.eval] at hφ₁ hφ₂
      have hcondEq : cond.eval ρ₁ = cond.eval ρ₂ := Term.eval_agreeOnTerms hcond hagree
      cases hc : cond.eval ρ₁ with
      | false =>
          exact ihe hΔ ρ₁ ρ₂ hrel hagree (hφ₁.2 hc) (hφ₂.2 (by rw [← hcondEq]; exact hc))
      | true =>
          exact iht hΔ ρ₁ ρ₂ hrel hagree (hφ₁.1 hc) (hφ₂.1 (by rw [← hcondEq]; exact hc))

/-! ## Body encoding -/

/-- The encoder IR of `rec f x := e`'s body. Both encodings consume it. -/
def encodeBody (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String Expr :=
  encode primitives Δ (ctx Γ f fn) (VarEnv.ofSignature (bodySig Δ fn x)) e
    (relBodySupply Δ fn x res)

/-- Relational body encoding: encodes `rec f x := e` into a closed FOL formula
pinned at result variable `res`. -/
def relEncodeBody (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String Formula :=
  ofExpr res <$> encodeBody primitives Γ Δ f fn x res e

/-- Least-fixpoint relational interpretation of `rec f x := e`. -/
def semrel (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    ValRel :=
  semanticFixpoint (relEncodeBody primitives Γ Δ f fn x res e) Formula.sem ρ fn x res

/-- The relational semantics induced by an encoded pure body is functional. -/
theorem semrel_functional
    {primitives : PrimEncodings} {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {c : Expr}
    (hlaw : primitives.Lawful)
    (henc : encodeBody primitives Γ Δ f fn x res e = .ok c)
    (hΓ : Γ.relWfIn Δ)
    (hrelFresh : fn.relName ∉ Δ.allNames)
    (hsubBody : Δ.Subset (bodySig Δ fn x))
    (hΔbody : (bodySig Δ fn x).wf)
    (hresFresh : res ∉ (bodySig Δ fn x).allNames)
    (hρdet : BinaryRelDet Γ ρ ρ)
    (vin y₁ y₂ : Srt.value.denote) :
    semrel primitives Γ Δ ρ f fn x res e vin y₁ →
      semrel primitives Γ Δ ρ f fn x res e vin y₂ →
      y₁ = y₂ := by
  set body := ofExpr res c with hbody_def
  let F : ValRel → ValRel := semanticBody Formula.sem ρ fn x res body
  let R : ValRel := semrel primitives Γ Δ ρ f fn x res e
  have hR : R = RelationFix.lfp F := by
    simp [R, F, semrel, semanticFixpoint, relEncodeBody, henc, hbody_def]
  have hmono : RelationFix.Mono F :=
    semanticBody_mono_of_semanticMono (ρ := ρ) (fn := fn) (x := x) (res := res)
      (ofExpr_mono res c)
  have hxres : x ≠ res := by
    intro h
    exact hresFresh (by
      simp [bodySig, relBase, Signature.declVar, Signature.addVar, Signature.allNames, h])
  have hcovBody : (relBodySupply Δ fn x res).Covers (bodySig Δ fn x) := by
    intro n hn
    by_contra hnAvoid
    have hnΔ : n ∉ Δ.allNames := fun h => hnAvoid (by simp [relBodySupply, bodyAvoid, SpecFn.names, h])
    have hnRel : n ≠ fn.relName := fun h => hnAvoid (by simp [relBodySupply, bodyAvoid, SpecFn.names, h])
    have hnX : n ≠ x := fun h => hnAvoid (by simp [relBodySupply, bodyAvoid, SpecFn.names, h])
    exact (Signature.not_mem_allNames_declVar
      (Signature.not_mem_allNames_addBinaryRel hnΔ hnRel) hnX)
      (by simpa [bodySig, relBase] using hn)
  have hcWf : Expr.WfIn (ctx Γ f fn) (bodyAvoid fn x res) (bodySig Δ fn x) c :=
    (encode_wfIn hlaw e hsubBody hΔbody (VarEnv.ofSignature_wfIn hΔbody)
      hcovBody henc).weaken bodyAvoid_subset_relBodySupply
  have hdet : Det (ctx Γ f fn) res (bodySig Δ fn x) body :=
    ofExpr_det hcWf hΔbody (by simp [bodyAvoid, SpecFn.names])
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
          BinaryRelDet (ctx Γ f fn)
            (relEnv ρ fn x res S a b)
            (relEnv ρ fn x res R a b') := by
        intro f' fn' hmem' vin' z₁ z₂ hz₁ hz₂
        cases hmem' with
        | head =>
            simp [SpecFn.evalRelates, SpecFn.rel, relEnv,
              Env.updateConst_binaryRel, Env.updateBinaryRel] at hz₁ hz₂
            exact hz₁.2 z₂ hz₂
        | tail _ htail =>
            have hrel'_mem : fn'.rel ∈ Δ.binaryRel := hΓ f' fn' htail
            have hne : fn'.relName ≠ fn.relName := fun h =>
              hrelFresh (h ▸ Signature.mem_allNames_of_binaryRel hrel'_mem)
            simp only [SpecFn.evalRelates, SpecFn.rel, relEnv,
              Env.updateConst_binaryRel, Env.updateBinaryRel] at hz₁ hz₂
            simp [hne] at hz₁ hz₂
            exact hρdet f' fn' htail vin' z₁ z₂ hz₁ hz₂
      have hagreeOnTerms :
          Env.agreeOnTerms (bodySig Δ fn x)
            (relEnv ρ fn x res S a b)
            (relEnv ρ fn x res R a b') := by
        unfold bodySig relEnv
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro v hv
          have hv' : v ∈ ⟨x, .value⟩ ::
              ((Δ.addBinaryRel fn.rel).remove x).vars := by
            simpa [Signature.declVar, Signature.addVar] using hv
          cases hv' with
          | head =>
              simp [Env.updateConst, Env.updateBinaryRel, hxres]
          | tail _ htail =>
              have hneX : v.name ≠ x := by
                intro hxv
                have hmem : v.name ∈
                    ((Δ.addBinaryRel fn.rel).remove x).allNames :=
                  Signature.mem_allNames_of_var htail
                exact Signature.remove_allNames hmem hxv
              have hneRes : v.name ≠ res := by
                intro hres
                have hmem : v.name ∈ (bodySig Δ fn x).allNames :=
                  Signature.mem_allNames_of_var hv
                exact hresFresh (hres ▸ hmem)
              simp [Env.updateConst, Env.updateBinaryRel, hneX, hneRes]
        · intro c hc
          have hneX : c.name ≠ x := by
            intro hcx
            have hmem : c.name ∈
                ((Δ.addBinaryRel fn.rel).remove x).allNames :=
              Signature.mem_allNames_of_const (by
                simpa [bodySig, Signature.declVar, Signature.addVar] using hc)
            exact Signature.remove_allNames hmem hcx
          have hneRes : c.name ≠ res := by
            intro hres
            have hmem : c.name ∈ (bodySig Δ fn x).allNames :=
              Signature.mem_allNames_of_const hc
            exact hresFresh (hres ▸ hmem)
          simp [Env.updateConst, Env.updateBinaryRel, hneX, hneRes]
        · intro u hu
          simp [Env.updateConst_unary, Env.updateBinaryRel]
        · intro bin hbin
          simp [Env.updateConst_binary, Env.updateBinaryRel]
        · intro t ht
          simp [Env.updateConst_ternary, Env.updateBinaryRel]
      have hresEq :=
        hdet (relEnv ρ fn x res S a b) (relEnv ρ fn x res R a b')
          hrelDet hagreeOnTerms hFS hFR
      simpa [relEnv, Env.lookupConst_updateConst_same] using hresEq
  intro hy₁ hy₂
  have hy₁S : S vin y₁ := by
    change R vin y₁ at hy₁
    rw [hR] at hy₁
    exact RelationFix.lfp_le_of_prefixed hpre vin y₁ hy₁
  exact hy₁S.2 y₂ hy₂
end Relation
end Verifier.RelationalEncoding
