-- SUMMARY: Verifier state and environments, together with their well-formedness conditions and fresh-name infrastructure.
import Mica.Verifier.Scoped
import Mica.Verifier.Guard
import Mica.Base.Fresh
import Mica.Verifier.Interpretations

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
  guard : ρ.supportsGuarding

/-- Builtin facts transfer along environments that agree on a signature
declaring the builtins. -/
theorem Builtins.holdsFor.agree {Δ : Signature} {ρ ρ' : Env}
    (hΔ : Builtins.wf Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (h : Builtins.holdsFor ρ) : Builtins.holdsFor ρ' :=
  ⟨h.guard.agree hΔ.guard hagree⟩

end VerifM

/-- Semantic interpretation of a verifier context item. -/
def CtxItem.interp [MicaGS HasLC.hasLC Sig] (W : TinyML.World)
    (ρ : Env) : CtxItem → iProp
  | .pure φ => ⌜φ.eval ρ⌝
  | .spatial a => a.interp W ρ

def CtxItem.purePart (i : CtxItem) (ρ : Env) : Prop :=
  match i with
  | .pure φ => φ.eval ρ
  | .spatial _ => True

/-- Pure formulas implied by an item's interpretation. -/
def CtxItem.facts : CtxItem → List Formula
  | .pure _ => []
  | .spatial a => a.facts

/-- The pure facts of a well-formed item are well-formed. -/
theorem CtxItem.facts_wfIn {i : CtxItem} {Δ : Signature} (h : i.wfIn Δ) :
    ∀ φ ∈ i.facts, φ.wfIn Δ := by
  cases i with
  | pure φ => simp [facts]
  | spatial a => exact SpatialAtom.facts_wfIn h

/-- An item's interpretation implies its pure facts. -/
theorem CtxItem.interp_facts [MicaGS HasLC.hasLC Sig] (W : TinyML.World)
    (ρ : Env) (i : CtxItem) :
    i.interp W ρ ⊢ ⌜∀ φ ∈ i.facts, φ.eval ρ⌝ ∗ i.interp W ρ := by
  cases i with
  | pure φ =>
    istart
    iintro H
    isplitr [H]
    · ipureintro
      simp [facts]
    · iexact H
  | spatial a =>
    exact SpatialAtom.interp_facts W a

def TransState.sl [MicaGS HasLC.hasLC Sig] (W : TinyML.World)
    (st : TransState) (ρ : Env) : iProp :=
  SpatialContext.interp W ρ st.owns

@[simp] theorem TransState.sl_eq [MicaGS HasLC.hasLC Sig] (W : TinyML.World)
    (st : TransState) (ρ : Env) :
    st.sl W ρ = SpatialContext.interp W ρ st.owns := rfl

/-- Drop the non-persistent spatial part of the verifier state. -/
def TransState.persist (st : TransState) : TransState :=
  { st with owns := [] }

@[simp] theorem TransState.persist_decls (st : TransState) :
    st.persist.decls = st.decls := rfl

@[simp] theorem TransState.persist_asserts (st : TransState) :
    st.persist.asserts = st.asserts := rfl

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

@[simp] theorem TransState.toFlatCtx_addTernary (st : TransState) (t : FOL.Ternary) :
    { st with decls := st.decls.addTernary t }.toFlatCtx =
      st.toFlatCtx.addTernary t.name t.arg1 t.arg2 t.arg3 t.ret := by
  simp [toFlatCtx, FlatCtx.addTernary]

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
structure TransState.holdsFor (st : TransState) (ρ : Env) : Prop where
  asserts : ∀ φ ∈ st.asserts, φ.eval ρ
  builtins : VerifM.Builtins.holdsFor ρ

theorem TransState.holdsFor_mono {st st' : TransState} {ρ : Env}
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
def Env.init : Env :=
  Env.empty.updateConst guardConst.sort guardConst.name true

theorem TransState.init_holdsFor : TransState.init.holdsFor Env.init where
  asserts := fun φ hφ => by simp [TransState.init] at hφ
  builtins := ⟨by simpa [Env.init] using
    Env.supportsGuarding_updateConst Env.empty⟩

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

def TransState.freshTernary (st : TransState) (hint : Option String) (τ₁ τ₂ τ₃ τ₄ : Srt) :
    FOL.Ternary :=
  ⟨Fresh.freshNumbers (hint.getD "_h") st.decls.allNames, τ₁, τ₂, τ₃, τ₄⟩

def TransState.addItem (st : TransState) (item : CtxItem) :=
  match item with
  | .pure φ => { st with asserts := φ :: st.asserts }
  | .spatial p => { st with owns := p :: st.owns }

theorem TransState.wf_freshConst {hint t} (st : TransState) :
    TransState.wf st →
    TransState.wf { st with decls := st.decls.addConst (st.freshConst hint t) } := by
  intro hwf
  have hfresh : (st.freshConst hint t).name ∉ st.decls.allNames :=
    Fresh.freshNumbers_not_mem (hint.getD "_v") st.decls.allNames
  have hwf' := Signature.wf_addConst hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addConst _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addConst _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addConst _ _)

theorem TransState.wf_addUnary (st : TransState) (u : FOL.Unary) :
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

theorem TransState.wf_addBinary (st : TransState) (b : FOL.Binary) :
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

theorem TransState.wf_addTernary (st : TransState) (t : FOL.Ternary) :
    TransState.wf st →
    t.name ∉ st.decls.allNames →
    TransState.wf { st with decls := st.decls.addTernary t } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addTernary hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addTernary _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addTernary _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addTernary _ _)

theorem TransState.wf_addUnaryRel (st : TransState) (u : FOL.UnaryRel) :
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

theorem TransState.wf_addBinaryRel (st : TransState) (b : FOL.BinaryRel) :
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

theorem TransState.freshTernary_fresh (st : TransState) (hint : Option String)
    (τ₁ τ₂ τ₃ τ₄ : Srt) :
    (st.freshTernary hint τ₁ τ₂ τ₃ τ₄).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_h") st.decls.allNames

theorem TransState.wf_addAssert (st : TransState) :
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

theorem TransState.wf_addSpatial (st : TransState) :
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
