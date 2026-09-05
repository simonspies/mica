-- SUMMARY: Stage 1 — encode a recursive TinyML body as a binary FOL relation defined by least fixpoint.
import Mica.Verifier.RelationalEncoding.Expr

/-!
# Relational encoding of recursive TinyML bodies

First stage of the encoding. A recursive definition `rec f x := e` becomes a
binary FOL relation, interpreted as the least fixpoint of the encoded body
operator. Diverging inputs are absent from the relation.
-/
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
private def FunCtx.Functional (Γ : FunCtx) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ vin y₁ y₂,
      fn.evalRelates ρ₁ vin y₁ →
      fn.evalRelates ρ₂ vin y₂ →
      y₁ = y₂

/-- Relations that read as graphs are single-valued. -/
private theorem FunCtx.Agreement.functional {Γ : FunCtx} {ρ : Env} (h : Γ.Agreement ρ) :
    Γ.Functional ρ ρ := fun f fn hmem vin y₁ y₂ h₁ h₂ =>
  ((h f fn hmem vin y₁).mp h₁).2.symm.trans ((h f fn hmem vin y₂).mp h₂).2

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

/-! ## Reading the head relation as a candidate -/

open SpecFn.Sig in
/-- Two runs of an encoded body that read the head relation differently still
agree on every term of the body signature: they differ only in the head
relation and in the result variable, and the body signature declares neither. -/
private theorem Env.rel_agreeOnTerms {Δ : Signature} {ρ : Env} {fn : SpecFn}
    {x res : TinyML.Var} {R R' : ValRel} {a b b' : Srt.value.denote}
    (hresFresh : res ∉ (relArg Δ fn x).allNames) :
    Env.agreeOnTerms (relArg Δ fn x)
      (SpecFn.Env.rel ρ fn x res R a b) (SpecFn.Env.rel ρ fn x res R' a b') := by
  have hxres : x ≠ res := by
    intro h
    exact hresFresh (by
      simp [relArg, rel, Signature.declVar, Signature.addVar, Signature.allNames, h])
  unfold relArg SpecFn.Env.rel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ ⟨x, .value⟩ :: ((Δ.addBinaryRel fn.rel).remove x).vars := by
      simpa [rel, Signature.declVar, Signature.addVar] using hv
    cases hv' with
    | head => simp [_root_.Env.updateConst, _root_.Env.updateBinaryRel, hxres]
    | tail _ htail =>
        have hneX : v.name ≠ x := fun hxv =>
          Signature.remove_allNames (Signature.mem_allNames_of_var htail) hxv
        have hneRes : v.name ≠ res := fun hres =>
          hresFresh (hres ▸ Signature.mem_allNames_of_var hv)
        simp [_root_.Env.updateConst, _root_.Env.updateBinaryRel, hneX, hneRes]
  · intro c hc
    have hneX : c.name ≠ x := fun hcx =>
      Signature.remove_allNames
        (Signature.mem_allNames_of_const
          (by simpa [rel, Signature.declVar, Signature.addVar] using hc)) hcx
    have hneRes : c.name ≠ res := fun hres =>
      hresFresh (hres ▸ Signature.mem_allNames_of_const hc)
    simp [_root_.Env.updateConst, _root_.Env.updateBinaryRel, hneX, hneRes]
  · intro u _; simp [_root_.Env.updateConst_unary, _root_.Env.updateBinaryRel]
  · intro bin _; simp [_root_.Env.updateConst_binary, _root_.Env.updateBinaryRel]
  · intro t _; simp [_root_.Env.updateConst_ternary, _root_.Env.updateBinaryRel]

/-- Reading the head relation as a candidate that is single-valued against `R`
keeps the extended context functional: the head is single-valued by assumption,
and the tail reads through to `ρ`. -/
private theorem FunCtx.recursive_functional {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {R S : ValRel}
    {a b b' : Srt.value.denote}
    (hΓ : Γ.relWfIn Δ) (hrelFresh : fn.relName ∉ Δ.allNames) (hρ : Γ.Functional ρ ρ)
    (hSR : ∀ u v, S u v → ∀ w, R u w → v = w) :
    FunCtx.Functional (Γ.recursive f fn)
      (SpecFn.Env.rel ρ fn x res S a b) (SpecFn.Env.rel ρ fn x res R a b') := by
  intro g fn' hmem vin z₁ z₂ hz₁ hz₂
  cases hmem with
  | head =>
      simp [SpecFn.evalRelates, SpecFn.rel, SpecFn.Env.rel,
        _root_.Env.updateConst_binaryRel, _root_.Env.updateBinaryRel] at hz₁ hz₂
      exact hSR vin z₁ hz₁ z₂ hz₂
  | tail _ htail =>
      have hne : fn'.relName ≠ fn.relName := fun h =>
        hrelFresh (h ▸ Signature.mem_allNames_of_binaryRel (hΓ g fn' htail))
      simp only [SpecFn.evalRelates, SpecFn.rel, SpecFn.Env.rel,
        _root_.Env.updateConst_binaryRel, _root_.Env.updateBinaryRel] at hz₁ hz₂
      simp [hne] at hz₁ hz₂
      exact hρ g fn' htail vin z₁ z₂ hz₁ hz₂

/-! ## Body encoding -/

/-- The definition of one spec function, `fn := rec f x := e`, together with the
context it is defined in. -/
structure SpecDef where
  primitives : PrimEncodings
  Γ : FunCtx
  Δ : Signature
  f : TinyML.Var
  fn : SpecFn
  x : TinyML.Var
  e : Typed.Expr

namespace SpecDef

/-- The variable the equation pins the result to, chosen outside `Δ`, the head
symbols, and the argument. -/
def res (sd : SpecDef) : TinyML.Var :=
  Fresh.freshName (sd.Δ.allNames ++ sd.fn.names ++ [sd.x]) "r"

/-- The head symbols and the argument are new for `Δ`, and so is the result
variable. -/
abbrev Fresh (sd : SpecDef) : Prop := SpecFnFresh.WithRes sd.Δ sd.fn sd.x sd.res

/-- Freshness of the head is all the caller has to give: the result variable
is chosen fresh. -/
theorem fresh {sd : SpecDef} (hf : SpecFnFresh sd.Δ sd.fn sd.x) : sd.Fresh :=
  { toSpecFnFresh := hf, resFresh := Fresh.freshName_not_in_avoid _ _ }

end SpecDef

/-- The encoder IR of the definition's body. Both readings consume it. -/
def encodeBody (sd : SpecDef) : Except String Expr :=
  encode sd.primitives sd.Δ (sd.Γ.recursive sd.f sd.fn)
    (VarEnv.ofSignature (SpecFn.Sig.relArg sd.Δ sd.fn sd.x)) sd.e
    (SpecFn.avoid sd.Δ sd.fn sd.x sd.res)

/-- The definition's body as a closed FOL formula pinned at its result variable. -/
def encodeFormula (sd : SpecDef) : Except String Formula :=
  Expr.toFormula sd.res <$> encodeBody sd

end Verifier.RelationalEncoding

/-! ## What the relation symbol denotes -/

namespace SpecFn.Semantics
open Verifier.RelationalEncoding

/-- Least-fixpoint relational interpretation of one definition. A body that
fails to encode denotes the empty relation. -/
def rel (sd : SpecDef) (ρ : Env) : ValRel :=
  match encodeFormula sd with
  | .error _ => fun _ _ => False
  | .ok φ    => Relation.fixpoint φ ρ sd.fn sd.x sd.res

/-- The relation induced by an encoded pure body is functional. -/
theorem rel_functional {sd : SpecDef} {ρ : Env}
    (hlaw : sd.primitives.Lawful) (hΓwf : sd.Γ.relWfIn sd.Δ) (hΓ : sd.Γ.Agreement ρ)
    (hΔ : sd.Δ.wf) (hfresh : sd.Fresh)
    (vin y₁ y₂ : Srt.value.denote) :
    rel sd ρ vin y₁ → rel sd ρ vin y₂ → y₁ = y₂ := by
  cases henc : encodeBody sd with
  | error msg => intro h; simp [rel, encodeFormula, henc] at h
  | ok c =>
      have hΔbody := hfresh.toSpecFnFresh.sigRelArg_wf (x := sd.x) hΔ
      let F : ValRel → ValRel := Relation.eval (Expr.toFormula sd.res c) ρ sd.fn sd.x sd.res
      let R : ValRel := rel sd ρ
      have hR : R = RelationFix.lfp F := by
        simp [R, F, rel, Relation.fixpoint, encodeFormula, henc]
      have hmono : RelationFix.Mono F :=
        Relation.eval_mono (ρ := ρ) (fn := sd.fn) (x := sd.x) (res := sd.res)
          (Expr.toFormula_mono sd.res c)
      have hdet : (Expr.toFormula sd.res c).Determines
          (sd.Γ.recursive sd.f sd.fn) (Sig.relArg sd.Δ sd.fn sd.x) sd.res :=
        Expr.toFormula_determines
          ((encode_wfIn hlaw sd.e hfresh.toSpecFnFresh.subset_sigRelArg hΔbody
            (VarEnv.ofSignature_wfIn hΔbody) hfresh.covers_sigRelArg henc).weaken
            reserved_subset_avoid)
          hΔbody (by simp [reserved, names])
      -- The part of `R` that relates its input to exactly one output.
      let S : ValRel := fun a b => R a b ∧ ∀ b', R a b' → b = b'
      have hpre : RelationFix.le (F S) S := by
        intro a b hFS
        have hFR : F R a b := hmono (fun _ _ h => h.1) a b hFS
        constructor
        · rw [hR]
          exact RelationFix.lfp_prefixed hmono a b (by rw [← hR]; exact hFR)
        · intro b' hRb'
          have hFR' : F R a b' := by
            have h := (RelationFix.lfp_unfold hmono a b').mp (by rw [← hR]; exact hRb')
            rw [← hR] at h
            exact h
          have hresEq :=
            hdet (SpecFn.Env.rel ρ sd.fn sd.x sd.res S a b)
              (SpecFn.Env.rel ρ sd.fn sd.x sd.res R a b')
              (FunCtx.recursive_functional hΓwf hfresh.toSpecFnFresh.relFresh hΓ.functional
                (fun _ _ hv _ hw => hv.2 _ hw))
              (Env.rel_agreeOnTerms hfresh.resFresh_sigRelArg) hFS hFR'
          simpa [SpecFn.Env.rel, _root_.Env.lookupConst_updateConst_same] using hresEq
      intro hy₁ hy₂
      have hy₁S : S vin y₁ := by
        change R vin y₁ at hy₁
        rw [hR] at hy₁
        exact RelationFix.lfp_le_of_prefixed hpre vin y₁ hy₁
      exact hy₁S.2 y₂ hy₂

end SpecFn.Semantics
