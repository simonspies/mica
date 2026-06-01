-- SUMMARY: Stage 1 — encode a recursive TinyML body as a binary FOL relation defined by least fixpoint.
import Mica.Verifier.RelationalEncoding.Monad

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

abbrev ValRel : Type := Fix.Rel Srt.value.denote Srt.value.denote

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
  | .ok m    => Fix.lfp (semanticBody sem ρ fn x res m)

theorem semanticBody_mono_of_semanticMono {M : Type} {sem : SemPred M}
    {ρ : Env} {fn : SpecFn} {x res : TinyML.Var} {m : M}
    (hm : SemanticMono sem m) :
    Fix.Mono (semanticBody sem ρ fn x res m) := by
  intro S S' hSS' vin vout hF
  have hle : Fix.Env.le (relEnv ρ fn x res S vin vout)
                    (relEnv ρ fn x res S' vin vout) := by
    refine Fix.Env.le.updateConst (Fix.Env.le.updateConst ?_ _ _ _) _ _ _
    refine ⟨rfl, rfl, rfl, fun _ _ _ h => h, ?_⟩
    intro τ₁ τ₂ name a b
    simp only [Env.updateBinaryRel]
    split
    · rename_i heq; rcases heq with ⟨rfl, rfl, rfl⟩
      intro h; exact hSS' a b h
    · intro h; exact h
  exact hm hle hF

abbrev Rel : Type := NameSupply → Except String Formula

def Rel.error (msg : String) : Rel := fun _ => .error msg

def Rel.call (fn : SpecFn) (arg : Term .value) (k : Term .value → Rel) : Rel :=
  fun s =>
    let r := s.fresh "r"
    let s' := s.reserve r
    do
      let φ ← k (.var .value r) s'
      .ok (.exists_ r .value (.and (fn.relates arg (.var .value r)) φ))

def Rel.ite (cond : Term .bool) (thenEnc elseEnc : Rel) : Rel :=
  fun s => do
    let φt ← thenEnc s
    let φe ← elseEnc s
    .ok (Formula.iteBool cond φt φe)

def encoderOps : EncoderOps Rel where
  call  := Rel.call
  ite   := Rel.ite
  error := Rel.error

def Rel.wfIn (Δ : Signature) (m : Rel) : Prop :=
  ∀ Δ' s φ, Δ.Subset Δ' → Δ'.wf → s.Covers Δ' →
    m s = .ok φ → φ.wfIn Δ'

theorem Rel.error_wfIn {Δ : Signature} {msg : String} :
    Rel.wfIn Δ (Rel.error msg) := by
  intro Δ' s φ _ _ _ hrun
  simp [Rel.error] at hrun

theorem Rel.call_wfIn {Δ : Signature} {fn : SpecFn} {arg : Term .value}
    (hrel : fn.rel ∈ Δ.binaryRel)
    (harg : arg.wfIn Δ)
    {k : Term .value → Rel}
    (hk : ∀ {Δ'}, Δ.Subset Δ' → Δ'.wf →
      ∀ v, v.wfIn Δ' → Rel.wfIn Δ' (k v)) :
    Rel.wfIn Δ (Rel.call fn arg k) := by
  intro Δ' s φ hsub hΔ' hcov hrun
  simp only [Rel.call] at hrun
  set r := s.fresh "r" with hr
  set s' := s.reserve r with hs'
  set Δ'' := Δ'.declVar ⟨r, .value⟩ with hΔ''
  have hfresh_avoid : r ∉ s.avoid := by
    simpa [hr] using NameSupply.fresh_not_in_avoid s "r"
  have hfresh : r ∉ Δ'.allNames := fun hmem => hfresh_avoid (hcov r hmem)
  have hΔ''wf : Δ''.wf := by simpa [hΔ''] using Signature.wf_declVar hΔ'
  have hsub'' : Δ'.Subset Δ'' := by
    simpa [hΔ''] using (Signature.subset_declVar_of_fresh (Δ := Δ') (v := ⟨r, .value⟩) hfresh)
  have hsubt : Δ.Subset Δ'' := hsub.trans hsub''
  have harg'' : arg.wfIn Δ'' :=
    Term.wfIn_mono _ harg hsubt hΔ''wf
  have hrvar : (Term.var .value r).wfIn Δ'' :=
    var_value_wfIn hΔ''wf (by simpa [hΔ''] using Signature.var_mem_declVar Δ' ⟨r, .value⟩)
  have hrel'' : fn.rel ∈ Δ''.binaryRel :=
    hsub''.binaryRel _ (hsub.binaryRel _ hrel)
  have hcov' : s'.Covers Δ'' := by
    simpa [hΔ'', hs'] using NameSupply.Covers.declVar hcov r .value
  cases hinner : k (.var .value r) s' with
  | error msg => simp [hinner, bind, Except.bind] at hrun
  | ok inner =>
    simp [hinner, bind, Except.bind] at hrun
    subst hrun
    have hkWf : Rel.wfIn Δ'' (k (.var .value r)) :=
      hk hsubt hΔ''wf _ hrvar
    have hinnerWf : inner.wfIn Δ'' :=
      hkWf Δ'' s' inner (Signature.Subset.refl _) hΔ''wf hcov' hinner
    exact ⟨SpecFn.relates_wfIn hrel'' hΔ''wf harg'' hrvar, hinnerWf⟩

theorem Rel.ite_wfIn {Δ : Signature} {cond : Term .bool}
    {thenEnc elseEnc : Rel}
    (hcond : cond.wfIn Δ) (ht : Rel.wfIn Δ thenEnc) (he : Rel.wfIn Δ elseEnc) :
    Rel.wfIn Δ (Rel.ite cond thenEnc elseEnc) := by
  intro Δ' s φ hsub hΔ' hcov hrun
  simp only [Rel.ite, Bind.bind, Except.bind] at hrun
  cases htRun : thenEnc s with
  | error msg => simp only [htRun] at hrun; cases hrun
  | ok φt =>
    cases heRun : elseEnc s with
    | error msg => simp only [htRun, heRun] at hrun; cases hrun
    | ok φe =>
      simp only [htRun, heRun, Except.ok.injEq] at hrun
      subst hrun
      have hφt := ht Δ' s φt hsub hΔ' hcov htRun
      have hφe := he Δ' s φe hsub hΔ' hcov heRun
      exact Formula.iteBool_wfIn (Term.wfIn_mono _ hcond hsub hΔ') hφt hφe

def encoderOps_wf : EncoderOpsSig encoderOps Rel.wfIn FunCtx.relWfIn where
  ctx_mono := fun hΓ hsub => FunCtx.relWfIn_mono hΓ hsub
  call_ind := by
    intro Γ Δ f fn arg k hΔ hΓ hmem harg hk
    exact Rel.call_wfIn (hΓ f fn hmem) harg hk
  ite_ind := by
    intro Δ cond t e _ hcond ht he
    exact Rel.ite_wfIn hcond ht he
  error_ind := Rel.error_wfIn

def Formula.sem (φ : Formula) (ρ : Env) : Prop :=
  φ.eval ρ

def Rel.Mono (m : Rel) : Prop :=
  ∀ s φ, m s = .ok φ → SemanticMono Formula.sem φ

theorem Rel.error_mono {msg : String} : Rel.Mono (Rel.error msg) := by
  intro _ _ hrun; simp [Rel.error] at hrun

theorem Rel.call_mono {fn : SpecFn} {arg : Term .value}
    {k : Term .value → Rel}
    (hk : ∀ v, Rel.Mono (k v)) :
    Rel.Mono (Rel.call fn arg k) := by
  intro s φ hrun ρ ρ' hle hφ
  simp only [Rel.call, Bind.bind, Except.bind] at hrun
  set r : String := s.fresh "r" with hr
  set s' : NameSupply := s.reserve r with hs'
  cases hinner : k (.var .value r) s' with
  | error msg => simp [hinner] at hrun
  | ok inner =>
    simp [hinner] at hrun
    subst hrun
    have hkMono := hk (.var .value r)
    unfold Formula.sem at hφ ⊢
    simp only [Formula.eval] at hφ ⊢
    rcases hφ with ⟨w, hcall_ev, hbody⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [SpecFn.relates, Formula.eval, BinPred.eval] at hcall_ev ⊢
      have hleU : Fix.Env.le (ρ.updateConst .value r w) (ρ'.updateConst .value r w) :=
        Fix.Env.le.updateConst hle .value r w
      rw [← Fix.Term.eval_le hleU, ← Fix.Term.eval_le hleU]
      exact hleU.2.2.2.2 _ _ _ _ _ hcall_ev
    · exact hkMono s' inner hinner (hle.updateConst .value r w) hbody

theorem Rel.ite_mono {cond : Term .bool} {t e : Rel}
    (ht : Rel.Mono t) (he : Rel.Mono e) :
    Rel.Mono (Rel.ite cond t e) := by
  intro s φ hrun ρ ρ' hle hφ
  simp only [Rel.ite, Bind.bind, Except.bind] at hrun
  cases htRun : t s with
  | error msg => simp [htRun] at hrun
  | ok φt =>
    cases heRun : e s with
    | error msg => simp [htRun, heRun] at hrun
    | ok φe =>
      simp [htRun, heRun] at hrun
      subst hrun
      unfold Formula.sem at hφ ⊢
      simp only [Formula.iteBool, Formula.eval] at hφ ⊢
      constructor
      · intro hcond
        have hcond' : cond.eval ρ = true := by
          rw [Fix.Term.eval_le hle]; exact hcond
        exact ht s φt htRun hle (hφ.1 hcond')
      · intro hcond
        have hcond' : cond.eval ρ = false := by
          rw [Fix.Term.eval_le hle]; exact hcond
        exact he s φe heRun hle (hφ.2 hcond')

def encoderOps_preservesMono :
    EncoderOpsInd encoderOps Rel.Mono where
  call_ind := Rel.call_mono
  ite_ind  := Rel.ite_mono
  error_ind := Rel.error_mono

def kEq (res : String) : Term .value → Rel :=
  fun v _ => .ok (.eq .value v (.var .value res))

theorem kEq_wfCont {Δ : Signature} {res : String}
    (hres : (⟨res, .value⟩ : Var) ∈ Δ.vars) :
    ∀ {Δ'}, Δ.Subset Δ' → Δ'.wf →
      ∀ v, v.wfIn Δ' → Rel.wfIn Δ' (kEq res v) := by
  intro Δ' hsub hΔ' v hv Δ'' s φ hsub' hΔ'' _ hrun
  simp only [kEq, Except.ok.injEq] at hrun
  subst hrun
  exact ⟨Term.wfIn_mono _ hv hsub' hΔ'',
    var_value_wfIn hΔ'' ((hsub.trans hsub').vars _ hres)⟩

theorem kEq_mono (res : String) :
    ∀ v, Rel.Mono (kEq res v) := by
  intro v s φ hrun ρ ρ' hle
  simp only [kEq, Except.ok.injEq] at hrun
  subst hrun
  intro h
  unfold Formula.sem at h ⊢
  simp only [Formula.eval] at h ⊢
  rw [← Fix.Term.eval_le hle, ← Fix.Term.eval_le hle]; exact h

/-- Extend the function context so recursive calls to `f` resolve to `fn`. -/
def ctx (Γ : FunCtx) (f : TinyML.Var) (fn : SpecFn) : FunCtx :=
  (f, fn) :: Γ

/-- Relational body encoding: encodes `rec f x := e` into a closed FOL formula
pinned at result variable `res`. -/
def relEncodeBody (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String Formula :=
  encodeWith encoderOps Δ (ctx Γ f fn) (VarEnv.ofSignature (bodySig Δ fn x)) e (kEq res)
    (relBodySupply Δ fn x res)

/-- Least-fixpoint relational interpretation of `rec f x := e`. -/
def semrel
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    ValRel :=
  semanticFixpoint (relEncodeBody Γ Δ f fn x res e) Formula.sem ρ fn x res

/-- Cross-environment determinism for the relation symbols registered in `Γ`. -/
def BinaryRelDet (Γ : FunCtx) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ vin y₁ y₂,
      fn.evalRelates ρ₁ vin y₁ →
      fn.evalRelates ρ₂ vin y₂ →
      y₁ = y₂

/-- A relational carrier is deterministic in `res` at any extension of its
view signature. -/
def Rel.Det (Γ : FunCtx) (res : String) (Δview : Signature) (m : Rel) : Prop :=
  ∀ Δ s φ ρ₁ ρ₂,
    Δview.Subset Δ → Δ.wf → s.Covers Δ → res ∈ s.avoid →
    m s = .ok φ →
    BinaryRelDet Γ ρ₁ ρ₂ →
    Env.termAgree Δ ρ₁ ρ₂ →
    φ.eval ρ₁ → φ.eval ρ₂ →
    ρ₁.lookupConst .value res = ρ₂.lookupConst .value res

theorem Rel.error_det {Γ : FunCtx} {res : String} {Δview : Signature}
    {msg : String} : Rel.Det Γ res Δview (Rel.error msg) := by
  intro Δ s φ ρ₁ ρ₂ _ _ _ _ hrun _ _ _ _
  simp [Rel.error] at hrun

theorem kEq_det {Γ : FunCtx} {res : String} {Δview : Signature}
    {v : Term .value} (hv : v.wfIn Δview) :
    Rel.Det Γ res Δview (kEq res v) := by
  intro Δ s φ ρ₁ ρ₂ hsub hΔ _ _ hrun _ hagree hφ₁ hφ₂
  simp only [kEq, Except.ok.injEq] at hrun
  subst hrun
  have hvWf : v.wfIn Δ := Term.wfIn_mono _ hv hsub hΔ
  simp only [Formula.eval, Term.eval] at hφ₁ hφ₂
  have hveq : v.eval ρ₁ = v.eval ρ₂ := Term.eval_termAgree hvWf hagree
  rw [← hφ₁, ← hφ₂, hveq]

theorem Rel.call_det {Γ : FunCtx} {res : String} {Δview : Signature}
    {f : TinyML.Var} {fn : SpecFn} {arg : Term .value}
    (hmem : (f, fn) ∈ Γ) (harg : arg.wfIn Δview)
    {k : Term .value → Rel}
    (hk : ∀ {Δ : Signature} {v : Term .value},
            Δview.Subset Δ → Δ.wf → v.wfIn Δ → Rel.Det Γ res Δ (k v)) :
    Rel.Det Γ res Δview (Rel.call fn arg k) := by
  intro Δ s φ ρ₁ ρ₂ hsubView hΔ hcov hresA hrun hrel hagree hφ₁ hφ₂
  simp only [Rel.call, Bind.bind, Except.bind] at hrun
  set r : String := s.fresh "r" with hr
  set s' : NameSupply := s.reserve r with hs'
  set Δ' : Signature := Δ.declVar ⟨r, .value⟩ with hΔ'def
  have hfresh_avoid : r ∉ s.avoid := by
    simpa [hr] using NameSupply.fresh_not_in_avoid s "r"
  have hfresh : r ∉ Δ.allNames := fun hmem => hfresh_avoid (hcov r hmem)
  have hΔ'wf : Δ'.wf := by simpa [hΔ'def] using Signature.wf_declVar hΔ
  have hsub' : Δ.Subset Δ' := by
    simpa [hΔ'def] using
      (Signature.subset_declVar_of_fresh (Δ := Δ) (v := ⟨r, .value⟩) hfresh)
  have hsubView' : Δview.Subset Δ' := hsubView.trans hsub'
  have hcov' : s'.Covers Δ' := by
    simpa [hΔ'def, hs'] using NameSupply.Covers.declVar hcov r .value
  have hresA' : res ∈ s'.avoid := by
    simp [hs', NameSupply.reserve, hresA]
  have hres_ne_r : res ≠ r := by
    intro heq; exact hfresh_avoid (by simpa [heq] using hresA)
  have hrvar : (Term.var .value r).wfIn Δ' :=
    var_value_wfIn hΔ'wf (by simpa [hΔ'def] using Signature.var_mem_declVar Δ ⟨r, .value⟩)
  have hargΔ : arg.wfIn Δ := Term.wfIn_mono _ harg hsubView hΔ
  have hargΔ' : arg.wfIn Δ' := Term.wfIn_mono _ hargΔ hsub' hΔ'wf
  cases hinner : k (.var .value r) s' with
  | error msg => simp [hinner] at hrun
  | ok inner =>
    simp [hinner] at hrun
    subst hrun
    simp only [Formula.eval] at hφ₁ hφ₂
    rcases hφ₁ with ⟨w₁, hcall₁, hbody₁⟩
    rcases hφ₂ with ⟨w₂, hcall₂, hbody₂⟩
    have hagree' : Env.termAgree Δ'
        (ρ₁.updateConst .value r w₁) (ρ₂.updateConst .value r w₁) :=
      Env.termAgree_declVar (x := r) (τ := .value) (v := w₁) hagree
    have hargEval :
        arg.eval (ρ₁.updateConst .value r w₁) =
          arg.eval (ρ₂.updateConst .value r w₁) :=
      Term.eval_termAgree hargΔ' hagree'
    simp only [SpecFn.relates, Formula.eval, BinPred.eval, Term.eval] at hcall₁ hcall₂
    have hargEq₂ :
        arg.eval (ρ₂.updateConst .value r w₁) =
          arg.eval (ρ₂.updateConst .value r w₂) := by
      have hag : Env.termAgree Δ
          (ρ₂.updateConst .value r w₁) (ρ₂.updateConst .value r w₂) :=
        Env.termAgree_of_agreeOn (Env.agreeOn_trans
          (Env.agreeOn_symm
            (Env.agreeOn_update_fresh_const (ρ := ρ₂) (c := ⟨r, .value⟩) (u := w₁) hfresh))
          (Env.agreeOn_update_fresh_const (ρ := ρ₂) (c := ⟨r, .value⟩) (u := w₂) hfresh))
      exact Term.eval_termAgree hargΔ hag
    have hw : w₁ = w₂ := by
      have hcall₁base :
          fn.evalRelates ρ₁ (arg.eval (ρ₁.updateConst .value r w₁)) w₁ := by
        simpa [SpecFn.evalRelates, Env.updateConst_binaryRel,
          Env.lookupConst_updateConst_same] using hcall₁
      have hcall₂base :
          fn.evalRelates ρ₂ (arg.eval (ρ₂.updateConst .value r w₂)) w₂ := by
        simpa [SpecFn.evalRelates, Env.updateConst_binaryRel,
          Env.lookupConst_updateConst_same] using hcall₂
      apply hrel f fn hmem (arg.eval (ρ₁.updateConst .value r w₁))
      · exact hcall₁base
      · rw [hargEval, hargEq₂]
        exact hcall₂base
    subst w₂
    have hrelUpd :
        BinaryRelDet Γ
          (ρ₁.updateConst .value r w₁) (ρ₂.updateConst .value r w₁) := by
      intro f' fn' hmem' vin y₁ y₂ hy₁ hy₂
      simp only [SpecFn.evalRelates_updateConst] at hy₁ hy₂
      exact hrel f' fn' hmem' vin y₁ y₂ hy₁ hy₂
    have hkDet : Rel.Det Γ res Δ' (k (.var .value r)) :=
      hk hsubView' hΔ'wf hrvar
    have hresEqUpd :=
      hkDet Δ' s' inner
        (ρ₁.updateConst .value r w₁) (ρ₂.updateConst .value r w₁)
        (Signature.Subset.refl _) hΔ'wf hcov' hresA' hinner
        hrelUpd hagree' hbody₁ hbody₂
    simpa [Env.lookupConst_updateConst_ne hres_ne_r] using hresEqUpd

theorem Rel.ite_det {Γ : FunCtx} {res : String} {Δview : Signature}
    {cond : Term .bool} {t e : Rel}
    (hcond : cond.wfIn Δview)
    (ht : Rel.Det Γ res Δview t) (he : Rel.Det Γ res Δview e) :
    Rel.Det Γ res Δview (Rel.ite cond t e) := by
  intro Δ s φ ρ₁ ρ₂ hsubView hΔ hcov hresA hrun hrel hagree hφ₁ hφ₂
  simp only [Rel.ite, Bind.bind, Except.bind] at hrun
  cases htRun : t s with
  | error msg => simp [htRun] at hrun
  | ok φt =>
    cases heRun : e s with
    | error msg => simp [htRun, heRun] at hrun
    | ok φe =>
      simp [htRun, heRun] at hrun
      subst hrun
      have hcondΔ : cond.wfIn Δ := Term.wfIn_mono _ hcond hsubView hΔ
      simp only [Formula.iteBool, Formula.eval] at hφ₁ hφ₂
      have hcondEq : cond.eval ρ₁ = cond.eval ρ₂ :=
        Term.eval_termAgree hcondΔ hagree
      cases hc : cond.eval ρ₁
      · have hc₂ : cond.eval ρ₂ = false := by simpa [hcondEq] using hc
        exact he Δ s φe ρ₁ ρ₂ hsubView hΔ hcov hresA heRun hrel hagree
          (hφ₁.2 hc) (hφ₂.2 hc₂)
      · have hc₂ : cond.eval ρ₂ = true := by simpa [hcondEq] using hc
        exact ht Δ s φt ρ₁ ρ₂ hsubView hΔ hcov hresA htRun hrel hagree
          (hφ₁.1 hc) (hφ₂.1 hc₂)

private def encoderOps_det (Γ : FunCtx) (res : String) :
    EncoderOpsSig encoderOps (fun Δview m => Rel.Det Γ res Δview m)
      (fun Γ' _ => Γ' = Γ) where
  ctx_mono := fun h _ => h
  call_ind := by
    intro Γ' _ _ _ _ _ _ hΓeq hmem harg hk
    subst hΓeq
    exact Rel.call_det hmem harg (fun hsub hΔ hv => hk hsub hΔ _ hv)
  ite_ind := fun _ hcond ht he => Rel.ite_det hcond ht he
  error_ind := Rel.error_det

/-- Successful relational encodings produce deterministic carriers. -/
theorem encodeWith_det {Γ : FunCtx} {Δenc : Signature} {res : String}
    {e : Typed.Expr} {Δview : Signature} {δ : VarEnv} {k : Term .value → Rel}
    (hsubView : Δenc.Subset Δview) (hΔview : Δview.wf)
    (hδ : δ.wfIn Δview)
    (hk : ∀ {Δ : Signature} {v : Term .value},
        Δview.Subset Δ → Δ.wf → v.wfIn Δ → Rel.Det Γ res Δ (k v)) :
    Rel.Det Γ res Δview (encodeWith encoderOps Δenc Γ δ e k) :=
  encodeWith_indWithSig (encoderOps_det Γ res) e hsubView hΔview rfl
    hδ
    (fun hsub hΔ' _ hv => hk hsub hΔ' hv)

/-- The relational semantics induced by an encoded pure body is functional. -/
theorem semrel_functional
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : Formula}
    (henc : relEncodeBody Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.relWfIn Δ)
    (hrelFresh : fn.relName ∉ Δ.allNames)
    (hsubBody : Δ.Subset (bodySig Δ fn x))
    (hΔbody : (bodySig Δ fn x).wf)
    (hresFresh : res ∉ (bodySig Δ fn x).allNames)
    (hρdet : BinaryRelDet Γ ρ ρ)
    (vin y₁ y₂ : Srt.value.denote) :
    semrel Γ Δ ρ f fn x res e vin y₁ →
      semrel Γ Δ ρ f fn x res e vin y₂ →
      y₁ = y₂ := by
  let F : ValRel → ValRel := semanticBody Formula.sem ρ fn x res body
  let R : ValRel := semrel Γ Δ ρ f fn x res e
  set δ := VarEnv.ofSignature (bodySig Δ fn x) with hδ_def
  set m := encodeWith encoderOps Δ (ctx Γ f fn) δ e (kEq res) with hm_def
  have hrun : m (relBodySupply Δ fn x res) = .ok body := by
    simpa [relEncodeBody, hm_def] using henc
  have hR : R = Fix.lfp F := by simp [R, F, semrel, semanticFixpoint, henc]
  have hmMono : Rel.Mono m :=
    encodeWith_ind encoderOps_preservesMono e (kEq_mono res)
  have hmonoBody : SemanticMono Formula.sem body :=
    hmMono (relBodySupply Δ fn x res) body hrun
  have hmono : Fix.Mono F := by
    simpa [F] using
      (semanticBody_mono_of_semanticMono
        (ρ := ρ) (fn := fn) (x := x) (res := res) hmonoBody)
  have hdetM : Rel.Det (ctx Γ f fn) res (bodySig Δ fn x) m :=
    by
      simpa [hm_def] using
        encodeWith_det (Γ := ctx Γ f fn) (Δenc := Δ)
          (res := res) (e := e) (Δview := bodySig Δ fn x) (δ := δ)
          hsubBody hΔbody
          (by simpa [hδ_def] using VarEnv.ofSignature_wfIn hΔbody)
          (fun _ _ hv => kEq_det hv)
  have hxres : x ≠ res := by
    intro h
    exact hresFresh (by
      simp [bodySig, Signature.declVar, Signature.addVar, Signature.allNames, h])
  have hcovBody : (relBodySupply Δ fn x res).Covers (bodySig Δ fn x) := by
    intro n hn
    by_contra hnAvoid
    have hnΔ : n ∉ Δ.allNames := fun h => hnAvoid (by simp [relBodySupply, h])
    have hnRel : n ≠ fn.relName := fun h => hnAvoid (by simp [relBodySupply, h])
    have hnX : n ≠ x := fun h => hnAvoid (by simp [relBodySupply, h])
    exact (Signature.not_mem_allNames_declVar
      (Signature.not_mem_allNames_addBinaryRel hnΔ hnRel) hnX)
      (by simpa [bodySig] using hn)
  have hresAvoid : res ∈ (relBodySupply Δ fn x res).avoid := by simp [relBodySupply]
  let S : ValRel := fun a b => R a b ∧ ∀ b', R a b' → b = b'
  have hSleR : Fix.le S R := fun _ _ h => h.1
  have hpre : Fix.le (F S) S := by
    intro a b hFS
    constructor
    · rw [hR]
      have hFR : F R a b := hmono hSleR a b hFS
      rw [hR] at hFR
      exact Fix.lfp_prefixed hmono a b hFR
    · intro b' hRb'
      have hFR : F R a b' := by
        have hFRlfp : F (Fix.lfp F) a b' := by
          rw [hR] at hRb'
          exact (Fix.lfp_unfold hmono a b').mp hRb'
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
            have hrel'_mem : fn'.rel ∈ Δ.binaryRel :=
              hΓ f' fn' htail
            have hne : fn'.relName ≠ fn.relName := fun h =>
              hrelFresh (h ▸ Signature.mem_allNames_of_binaryRel hrel'_mem)
            simp only [SpecFn.evalRelates, SpecFn.rel, relEnv,
              Env.updateConst_binaryRel, Env.updateBinaryRel] at hz₁ hz₂
            simp [hne] at hz₁ hz₂
            exact hρdet f' fn' htail vin' z₁ z₂ hz₁ hz₂
      have htermAgree :
          Env.termAgree (bodySig Δ fn x)
            (relEnv ρ fn x res S a b)
            (relEnv ρ fn x res R a b') := by
        unfold bodySig relEnv
        refine ⟨?_, ?_, ?_, ?_⟩
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
                have hmem : v.name ∈ (bodySig Δ fn x).allNames := by
                  exact Signature.mem_allNames_of_var hv
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
      have hresEq :=
        hdetM (bodySig Δ fn x) (relBodySupply Δ fn x res) body
        (relEnv ρ fn x res S a b) (relEnv ρ fn x res R a b')
        (Signature.Subset.refl _) hΔbody hcovBody hresAvoid hrun
        hrelDet htermAgree hFS hFR
      simpa [relEnv, Env.lookupConst_updateConst_same] using hresEq
  intro hy₁ hy₂
  have hy₁S : S vin y₁ := by
    change R vin y₁ at hy₁
    rw [hR] at hy₁
    exact Fix.lfp_le_of_prefixed hpre vin y₁ hy₁
  exact hy₁S.2 y₂ hy₂
end Relation
end Verifier.RelationalEncoding
