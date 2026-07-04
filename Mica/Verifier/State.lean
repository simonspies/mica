-- SUMMARY: Verifier state and environments, together with their well-formedness conditions and fresh-name infrastructure.
import Mica.Verifier.Scoped
import Mica.Verifier.Guard
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

def Env.updateUnary (ρ : Env) (τ₁ τ₂ : Srt) (x : String) (f : τ₁.denote → τ₂.denote) : Env :=
  { ρ with env := _root_.Env.updateUnary ρ.env τ₁ τ₂ x f }

@[simp] theorem Env.updateUnary_env (ρ : Env) (τ₁ τ₂ : Srt) (x : String) (f : τ₁.denote → τ₂.denote) :
    (ρ.updateUnary τ₁ τ₂ x f).env = ρ.env.updateUnary τ₁ τ₂ x f := rfl

def Env.updateBinary (ρ : Env) (τ₁ τ₂ τ₃ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → τ₃.denote) : Env :=
  { ρ with env := _root_.Env.updateBinary ρ.env τ₁ τ₂ τ₃ x f }

@[simp] theorem Env.updateBinary_env (ρ : Env) (τ₁ τ₂ τ₃ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → τ₃.denote) :
    (ρ.updateBinary τ₁ τ₂ τ₃ x f).env = ρ.env.updateBinary τ₁ τ₂ τ₃ x f := rfl

def Env.updateUnaryRel (ρ : Env) (τ : Srt) (x : String) (f : τ.denote → Prop) : Env :=
  { ρ with env := _root_.Env.updateUnaryRel ρ.env τ x f }

@[simp] theorem Env.updateUnaryRel_env (ρ : Env) (τ : Srt) (x : String) (f : τ.denote → Prop) :
    (ρ.updateUnaryRel τ x f).env = ρ.env.updateUnaryRel τ x f := rfl

def Env.updateBinaryRel (ρ : Env) (τ₁ τ₂ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → Prop) : Env :=
  { ρ with env := _root_.Env.updateBinaryRel ρ.env τ₁ τ₂ x f }

@[simp] theorem Env.updateBinaryRel_env (ρ : Env) (τ₁ τ₂ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → Prop) :
    (ρ.updateBinaryRel τ₁ τ₂ x f).env = ρ.env.updateBinaryRel τ₁ τ₂ x f := rfl

/-- Builtin declarations the verifier requires in a signature; extend with a
field per builtin. -/
structure Builtins.wf (Δ : Signature) : Prop where
  guard : Δ.supportsGuarding

theorem Builtins.wf.mono {Δ Δ' : Signature} (hsub : Δ.Subset Δ')
    (h : Builtins.wf Δ) : Builtins.wf Δ' :=
  ⟨h.guard.mono hsub⟩

/-- Facts about the environment required by the verifier's builtin constants;
extend with a field per builtin. -/
structure Builtins.holdsFor (ρ : Env) : Prop where
  guard : ρ.env.supportsGuarding

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

theorem Env.agreeOn_update_fresh_unary {ρ : Env} {u : FOL.Unary}
    {f : u.arg.denote → u.ret.denote}
    {Δ : Signature} (hfresh : u.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateUnary u.arg u.ret u.name f) := by
  simpa [Env.agreeOn, Env.updateUnary] using
    (_root_.Env.agreeOn_update_fresh_unary (ρ := ρ.env) (u := u) (f := f) (Δ := Δ) hfresh)

theorem Env.agreeOn_update_fresh_binary {ρ : Env} {b : FOL.Binary}
    {f : b.arg1.denote → b.arg2.denote → b.ret.denote}
    {Δ : Signature} (hfresh : b.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateBinary b.arg1 b.arg2 b.ret b.name f) := by
  simpa [Env.agreeOn, Env.updateBinary] using
    (_root_.Env.agreeOn_update_fresh_binary (ρ := ρ.env) (b := b) (f := f) (Δ := Δ) hfresh)

theorem Env.agreeOn_update_fresh_unaryRel {ρ : Env} {u : FOL.UnaryRel}
    {f : u.arg.denote → Prop}
    {Δ : Signature} (hfresh : u.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateUnaryRel u.arg u.name f) := by
  simpa [Env.agreeOn, Env.updateUnaryRel] using
    (_root_.Env.agreeOn_update_fresh_unaryRel (ρ := ρ.env) (u := u) (f := f) (Δ := Δ) hfresh)

theorem Env.agreeOn_update_fresh_binaryRel {ρ : Env} {b : FOL.BinaryRel}
    {f : b.arg1.denote → b.arg2.denote → Prop}
    {Δ : Signature} (hfresh : b.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateBinaryRel b.arg1 b.arg2 b.name f) := by
  simpa [Env.agreeOn, Env.updateBinaryRel] using
    (_root_.Env.agreeOn_update_fresh_binaryRel (ρ := ρ.env) (b := b) (f := f) (Δ := Δ) hfresh)

/-- Builtin facts transfer along environments that agree on a signature
declaring the builtins. -/
theorem Builtins.holdsFor.agree {Δ : Signature} {ρ ρ' : Env}
    (hΔ : Builtins.wf Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (h : Builtins.holdsFor ρ) : Builtins.holdsFor ρ' :=
  ⟨h.guard.agree hΔ.guard hagree⟩

end VerifM

/-- Semantic interpretation of a verifier context item. -/
def CtxItem.interp [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv)
    (ρ : VerifM.Env) : CtxItem → iProp
  | .pure φ => ⌜φ.eval ρ.env⌝
  | .spatial a => a.interp Θ ρ.env

def CtxItem.purePart (i : CtxItem) (ρ : VerifM.Env) : Prop :=
  match i with
  | .pure φ => φ.eval ρ.env
  | .spatial _ => True

def TransState.sl [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv)
    (st : TransState) (ρ : VerifM.Env) : iProp :=
  SpatialContext.interp Θ ρ.env st.owns

@[simp] theorem TransState.sl_eq [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv)
    (st : TransState) (ρ : VerifM.Env) :
    st.sl Θ ρ = SpatialContext.interp Θ ρ.env st.owns := rfl

/-- Drop the non-persistent spatial part of the verifier state. -/
def TransState.persist (st : TransState) : TransState :=
  { st with owns := [] }

@[simp] theorem TransState.persist_decls (st : TransState) :
    st.persist.decls = st.decls := rfl

@[simp] theorem TransState.persist_asserts (st : TransState) :
    st.persist.asserts = st.asserts := rfl

theorem TransState.sl_entails_persist [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv)
    (st : TransState) (ρ : VerifM.Env) :
    st.sl Θ ρ ⊢ □ st.persist.sl Θ ρ := by
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

@[simp] theorem TransState.toFlatCtx_addUnary (st : TransState) (u : FOL.Unary) :
    { st with decls := st.decls.addUnary u }.toFlatCtx =
      st.toFlatCtx.addUnary u.name u.arg u.ret := by
  simp [toFlatCtx, FlatCtx.addUnary]

@[simp] theorem TransState.toFlatCtx_addBinary (st : TransState) (b : FOL.Binary) :
    { st with decls := st.decls.addBinary b }.toFlatCtx =
      st.toFlatCtx.addBinary b.name b.arg1 b.arg2 b.ret := by
  simp [toFlatCtx, FlatCtx.addBinary]

@[simp] theorem TransState.toFlatCtx_addUnaryRel (st : TransState) (u : FOL.UnaryRel) :
    { st with decls := st.decls.addUnaryRel u }.toFlatCtx =
      st.toFlatCtx.addUnaryRel u.name u.arg := by
  simp [toFlatCtx, FlatCtx.addUnaryRel]

@[simp] theorem TransState.toFlatCtx_addBinaryRel (st : TransState) (b : FOL.BinaryRel) :
    { st with decls := st.decls.addBinaryRel b }.toFlatCtx =
      st.toFlatCtx.addBinaryRel b.name b.arg1 b.arg2 := by
  simp [toFlatCtx, FlatCtx.addBinaryRel]

@[simp] theorem TransState.toFlatCtx_addAssert (st : TransState) (φ : Formula) :
    { st with asserts := φ :: st.asserts }.toFlatCtx = st.toFlatCtx.addAssert φ := by
  simp [toFlatCtx, FlatCtx.addAssert]

/-- The initial verifier state: only the builtin guard constant is declared. -/
def TransState.init : TransState := ⟨Signature.empty.addConst guardConst, [], []⟩

@[simp] theorem TransState.init_toFlatCtx :
    TransState.init.toFlatCtx = FlatCtx.empty.addConst guardConst.name guardConst.sort := rfl

/-- The environment satisfies the verifier state: every assertion holds and the
builtin facts are in force. -/
structure TransState.holdsFor (st : TransState) (ρ : VerifM.Env) : Prop where
  asserts : ∀ φ ∈ st.asserts, φ.eval ρ.env
  builtins : VerifM.Builtins.holdsFor ρ

theorem TransState.holdsFor_mono {st st' : TransState} {ρ : VerifM.Env}
    (hsub : st.asserts ⊆ st'.asserts) (h : st'.holdsFor ρ) : st.holdsFor ρ :=
  ⟨fun φ hφ => h.asserts φ (hsub hφ), h.builtins⟩

structure TransState.wf (st : TransState) : Prop where
  assertsWf : st.asserts.wfIn st.decls
  namesDisjoint : st.decls.allNames.Nodup
  ownsWf : st.owns.wfIn st.decls
  builtins : VerifM.Builtins.wf st.decls

theorem TransState.init_wf : TransState.init.wf where
  assertsWf := fun φ hφ => by simp [TransState.init] at hφ
  namesDisjoint := by
    simp [TransState.init, Signature.allNames, Signature.addConst, Signature.empty]
  ownsWf := fun a ha => by simp [TransState.init] at ha
  builtins := ⟨List.Mem.head _⟩

/-- The canonical initial environment: the guard constant pinned to true. -/
def VerifM.Env.init : VerifM.Env :=
  VerifM.Env.empty.updateConst guardConst.sort guardConst.name true

theorem TransState.init_holdsFor : TransState.init.holdsFor VerifM.Env.init where
  asserts := fun φ hφ => by simp [TransState.init] at hφ
  builtins := ⟨by simpa [VerifM.Env.init] using
    Env.supportsGuarding_updateConst VerifM.Env.empty.env⟩

def TransState.freshConst (hint : Option String) (t : Srt) (st : TransState) : FOL.Const :=
  let base := hint.getD "_v"
  let x' := Fresh.freshNumbers base st.decls.allNames
  ⟨x', t⟩

def TransState.freshUnaryRel (st : TransState) (hint : Option String) (τ : Srt) : FOL.UnaryRel :=
  ⟨Fresh.freshNumbers (hint.getD "_p") st.decls.allNames, τ⟩

def TransState.freshBinaryRel (st : TransState) (hint : Option String) (τ₁ τ₂ : Srt) :
    FOL.BinaryRel :=
  ⟨Fresh.freshNumbers (hint.getD "_r") st.decls.allNames, τ₁, τ₂⟩

def TransState.freshUnary (st : TransState) (hint : Option String) (τ₁ τ₂ : Srt) : FOL.Unary :=
  ⟨Fresh.freshNumbers (hint.getD "_f") st.decls.allNames, τ₁, τ₂⟩

def TransState.freshBinary (st : TransState) (hint : Option String) (τ₁ τ₂ τ₃ : Srt) :
    FOL.Binary :=
  ⟨Fresh.freshNumbers (hint.getD "_g") st.decls.allNames, τ₁, τ₂, τ₃⟩

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
  · exact hwf.builtins.mono (Signature.Subset.subset_addConst _ _)

theorem TransState.addUnary.wf (st : TransState) (u : FOL.Unary) :
    TransState.wf st →
    u.name ∉ st.decls.allNames →
    TransState.wf { st with decls := st.decls.addUnary u } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addUnary hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addUnary _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addUnary _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addUnary _ _)

theorem TransState.addBinary.wf (st : TransState) (b : FOL.Binary) :
    TransState.wf st →
    b.name ∉ st.decls.allNames →
    TransState.wf { st with decls := st.decls.addBinary b } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addBinary hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addBinary _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addBinary _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addBinary _ _)

theorem TransState.addUnaryRel.wf (st : TransState) (u : FOL.UnaryRel) :
    TransState.wf st →
    u.name ∉ st.decls.allNames →
    TransState.wf { st with decls := st.decls.addUnaryRel u } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addUnaryRel hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addUnaryRel _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addUnaryRel _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addUnaryRel _ _)

theorem TransState.addBinaryRel.wf (st : TransState) (b : FOL.BinaryRel) :
    TransState.wf st →
    b.name ∉ st.decls.allNames →
    TransState.wf { st with decls := st.decls.addBinaryRel b } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addBinaryRel hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addBinaryRel _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addBinaryRel _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addBinaryRel _ _)

/-- The name produced by `freshConst` is not in the existing decls. -/
theorem TransState.freshConst_fresh (st : TransState) (hint : Option String) (τ : Srt) :
    (st.freshConst hint τ).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_v") st.decls.allNames

theorem TransState.freshUnaryRel_fresh (st : TransState) (hint : Option String) (τ : Srt) :
    (st.freshUnaryRel hint τ).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_p") st.decls.allNames

theorem TransState.freshBinaryRel_fresh (st : TransState) (hint : Option String) (τ₁ τ₂ : Srt) :
    (st.freshBinaryRel hint τ₁ τ₂).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_r") st.decls.allNames

theorem TransState.freshUnary_fresh (st : TransState) (hint : Option String) (τ₁ τ₂ : Srt) :
    (st.freshUnary hint τ₁ τ₂).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_f") st.decls.allNames

theorem TransState.freshBinary_fresh (st : TransState) (hint : Option String) (τ₁ τ₂ τ₃ : Srt) :
    (st.freshBinary hint τ₁ τ₂ τ₃).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_g") st.decls.allNames

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
  · exact hwf.builtins

theorem TransState.addSpatial.wf (st : TransState) :
    TransState.wf st →
    a.wfIn st.decls →
    TransState.wf { st with owns := a :: st.owns } := by
  intro hwf ha
  constructor
  · exact hwf.assertsWf
  · exact hwf.namesDisjoint
  · simpa [SpatialContext.wfIn_cons] using And.intro ha hwf.ownsWf
  · exact hwf.builtins

theorem TransState.persist_wf (st : TransState) :
    TransState.wf st →
    TransState.wf st.persist := by
  intro hwf
  constructor
  · exact hwf.assertsWf
  · exact hwf.namesDisjoint
  · simp [TransState.persist]
  · exact hwf.builtins
