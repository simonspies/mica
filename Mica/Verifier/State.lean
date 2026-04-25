-- SUMMARY: Verifier state and environments, together with their well-formedness conditions and fresh-name infrastructure.
import Mica.Verifier.Scoped
import Mica.Base.Fresh
import Mica.SeparationLogic.SpatialAtom
import Mica.SeparationLogic

open Iris Iris.BI

structure TransState where
  decls   : Signature
  asserts : Context
  owns    : SpatialContext

inductive CtxItem where
  | pure : Formula → CtxItem
  | spatial : SpatialAtom → CtxItem

namespace CtxItem

def wfIn : CtxItem → Signature → Prop
  | .pure φ, Δ => φ.wfIn Δ
  | .spatial a, Δ => a.wfIn Δ

end CtxItem

namespace VerifM

structure Env where
  env : _root_.Env

def Env.empty : Env :=
  { env := _root_.Env.empty }

@[simp] theorem Env.empty_env : Env.empty.env = _root_.Env.empty := rfl

def Env.updateConst (ρ : Env) (t : Srt) (x : String) (u : t.denote) : Env :=
  { ρ with env := _root_.Env.updateConst ρ.env t x u }

@[simp] theorem Env.updateConst_env (ρ : Env) (t : Srt) (x : String) (u : t.denote) :
    (ρ.updateConst t x u).env = ρ.env.updateConst t x u := rfl

def Env.withEnv (ρ : Env) (env' : _root_.Env) : Env :=
  { ρ with env := env' }

@[simp] theorem Env.withEnv_env (ρ : Env) (env' : _root_.Env) :
    (ρ.withEnv env').env = env' := rfl

def Env.agreeOn (Δ : Signature) (ρ ρ' : Env) : Prop :=
  _root_.Env.agreeOn Δ ρ.env ρ'.env

theorem Env.agreeOn_refl : Env.agreeOn Δ ρ ρ :=
  _root_.Env.agreeOn_refl

theorem Env.agreeOn_mono {Δ₁ Δ₂ : Signature} (hsub : Δ₁.Subset Δ₂)
    (h : Env.agreeOn Δ₂ ρ ρ') : Env.agreeOn Δ₁ ρ ρ' :=
  _root_.Env.agreeOn_mono hsub h

theorem Env.agreeOn_symm {Δ : Signature} (h : Env.agreeOn Δ ρ ρ') :
    Env.agreeOn Δ ρ' ρ :=
  _root_.Env.agreeOn_symm h

theorem Env.agreeOn_trans {Δ : Signature}
    (h₁₂ : Env.agreeOn Δ ρ₁ ρ₂) (h₂₃ : Env.agreeOn Δ ρ₂ ρ₃) :
    Env.agreeOn Δ ρ₁ ρ₃ :=
  _root_.Env.agreeOn_trans h₁₂ h₂₃

theorem Env.agreeOn_declVar {ρ ρ' : Env} {Δ : Signature} {τ : Srt} {x : String} {v : τ.denote} :
    Env.agreeOn Δ ρ ρ' →
    Env.agreeOn (Δ.declVar ⟨x, τ⟩) (ρ.updateConst τ x v) (ρ'.updateConst τ x v) := by
  intro hagree
  simpa [Env.agreeOn, Env.updateConst] using
    (_root_.Env.agreeOn_declVar (ρ := ρ.env) (ρ' := ρ'.env) (Δ := Δ) (τ := τ) (x := x) (v := v) hagree)

theorem Env.agreeOn_update_fresh {ρ : Env} {c : FOL.Const} {u : c.sort.denote}
    {Δ : Signature} (hfresh : c.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateConst c.sort c.name u) := by
  simpa [Env.agreeOn, Env.updateConst] using
    (Env.agreeOn_update_fresh_const (ρ := ρ.env) (c := c) (u := u) (Δ := Δ) hfresh)

end VerifM

/-- Semantic interpretation of a verifier context item. -/
def CtxItem.interp (ρ : VerifM.Env) : CtxItem → iProp
  | .pure φ => ⌜φ.eval ρ.env⌝
  | .spatial a => a.interp ρ.env

def CtxItem.purePart (i : CtxItem) (ρ : VerifM.Env) : Prop :=
  match i with
  | .pure φ => φ.eval ρ.env
  | .spatial _ => True

def TransState.sl (st : TransState) (ρ : VerifM.Env) : iProp :=
  SpatialContext.interp ρ.env st.owns

@[simp] theorem TransState.sl_eq (st : TransState) (ρ : VerifM.Env) :
    st.sl ρ = SpatialContext.interp ρ.env st.owns := rfl

/-- Drop the non-persistent spatial part of the verifier state. -/
def TransState.persist (st : TransState) : TransState :=
  { st with owns := [] }

@[simp] theorem TransState.persist_decls (st : TransState) :
    st.persist.decls = st.decls := rfl

@[simp] theorem TransState.persist_asserts (st : TransState) :
    st.persist.asserts = st.asserts := rfl

theorem TransState.sl_entails_persist (st : TransState) (ρ : VerifM.Env) :
    st.sl ρ ⊢ □ st.persist.sl ρ := by
  istart
  iintro _
  imodintro
  simp [TransState.persist]

/-- Translation to `ScopedM`'s flat context. -/
def TransState.toFlatCtx (st : TransState) : FlatCtx :=
  ⟨st.decls, st.asserts⟩

@[simp] theorem TransState.toFlatCtx_decls (st : TransState) :
    st.toFlatCtx.decls = st.decls := rfl

@[simp] theorem TransState.toFlatCtx_asserts (st : TransState) :
    st.toFlatCtx.asserts = st.asserts := rfl

@[simp] theorem TransState.toFlatCtx_addConst (st : TransState) (c : FOL.Const) :
    { st with decls := st.decls.addConst c }.toFlatCtx = st.toFlatCtx.addConst c.name c.sort := by
  simp [toFlatCtx, FlatCtx.addConst]

@[simp] theorem TransState.toFlatCtx_addAssert (st : TransState) (φ : Formula) :
    { st with asserts := φ :: st.asserts }.toFlatCtx = st.toFlatCtx.addAssert φ := by
  simp [toFlatCtx, FlatCtx.addAssert]

def TransState.empty : TransState := ⟨Signature.empty, [], []⟩

@[simp] theorem TransState.empty_toFlatCtx : TransState.empty.toFlatCtx = FlatCtx.empty := rfl

def TransState.holdsFor (st : TransState) (ρ : VerifM.Env) := ∀ φ ∈ st.asserts, φ.eval ρ.env

theorem TransState.holdsFor_mono {st st' : TransState} {ρ : VerifM.Env}
    (hsub : st.asserts ⊆ st'.asserts) (h : st'.holdsFor ρ) : st.holdsFor ρ :=
  fun φ hφ => h φ (hsub hφ)

structure TransState.wf (st : TransState) : Prop where
  assertsWf : st.asserts.wfIn st.decls
  namesDisjoint : st.decls.allNames.Nodup
  ownsWf : st.owns.wfIn st.decls

def TransState.freshConst (hint : Option String) (t : Srt) (st : TransState) : FOL.Const :=
  let base := hint.getD "_v"
  let x' := Fresh.freshNumbers base st.decls.allNames
  ⟨x', t⟩

def TransState.addItem (st : TransState) (item : CtxItem) :=
  match item with
  | .pure φ => { st with asserts := φ :: st.asserts }
  | .spatial p => { st with owns := p :: st.owns }

theorem TransState.freshConst.wf {hint t} (st : TransState) :
    TransState.wf st →
    TransState.wf { st with decls := st.decls.addConst (st.freshConst hint t) } := by
  intro hwf
  have hfresh : (st.freshConst hint t).name ∉ st.decls.allNames :=
    Fresh.freshNumbers_not_mem (hint.getD "_v") st.decls.allNames
  have hwf' := Signature.wf_addConst hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addConst _ _) hwf'
  · exact Signature.nodup_allNames_addConst hwf.namesDisjoint hfresh
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addConst _ _) hwf'

/-- The name produced by `freshConst` is not in the existing decls. -/
theorem TransState.freshConst_fresh (st : TransState) (hint : Option String) (τ : Srt) :
    (st.freshConst hint τ).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_v") st.decls.allNames

theorem TransState.addAssert.wf (st : TransState) :
    TransState.wf st →
    φ.wfIn st.decls →
    TransState.wf { st with asserts := φ :: st.asserts } := by
  intro hwf hφ
  constructor
  · intro ψ hψ
    simp only [List.mem_cons] at hψ
    rcases hψ with rfl | hψ
    · exact hφ
    · exact hwf.assertsWf ψ hψ
  · exact hwf.namesDisjoint
  · exact hwf.ownsWf

theorem TransState.addSpatial.wf (st : TransState) :
    TransState.wf st →
    a.wfIn st.decls →
    TransState.wf { st with owns := a :: st.owns } := by
  intro hwf ha
  constructor
  · exact hwf.assertsWf
  · exact hwf.namesDisjoint
  · simpa [SpatialContext.wfIn_cons] using And.intro ha hwf.ownsWf

theorem TransState.persist_wf (st : TransState) :
    TransState.wf st →
    TransState.wf st.persist := by
  intro hwf
  constructor
  · exact hwf.assertsWf
  · exact hwf.namesDisjoint
  · simp [TransState.persist]
