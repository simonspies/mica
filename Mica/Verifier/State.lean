-- SUMMARY: Verifier state and environments, together with their well-formedness conditions and fresh-name infrastructure.
import Mica.Engine.Scoped
import Mica.Pure.Guard
import Mica.Base.Fresh
import Mica.Verifier.SpatialAtom

open Iris Iris.BI

/-!
# Verifier state

The verifier state is a signature, the formulas assumed so far, and the owned
spatial atoms. `State.wf` says every part is well formed in the signature;
`State.holdsFor ρ` says the environment `ρ` satisfies the assumptions.
-/

/-! ## Builtins -/

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

/-! ## Context items -/

/-- What the verifier can assume: a formula or an owned atom. -/
inductive CtxItem where
  | pure : Formula → CtxItem
  | spatial : SpatialAtom → CtxItem

namespace CtxItem

def wfIn : CtxItem → Signature → Prop
  | .pure φ, Δ => φ.wfIn Δ
  | .spatial a, Δ => a.wfIn Δ

end CtxItem

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

theorem CtxItem.facts_wfIn {i : CtxItem} {Δ : Signature} (h : i.wfIn Δ) :
    ∀ φ ∈ i.facts, φ.wfIn Δ := by
  cases i with
  | pure φ => simp [facts]
  | spatial a => exact SpatialAtom.facts_wfIn h

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

/-! ## The state -/

structure Verifier.State where
  decls   : Signature
  asserts : Context
  owns    : SpatialContext

open Verifier (State)

def Verifier.State.sl [MicaGS HasLC.hasLC Sig] (W : TinyML.World)
    (st : State) (ρ : Env) : iProp :=
  SpatialContext.interp W ρ st.owns

@[simp] theorem Verifier.State.sl_eq [MicaGS HasLC.hasLC Sig] (W : TinyML.World)
    (st : State) (ρ : Env) :
    st.sl W ρ = SpatialContext.interp W ρ st.owns := rfl

theorem Verifier.State.sl_of_owns_nil [MicaGS HasLC.hasLC Sig] {W : TinyML.World} {st : State} {ρ : Env}
    (hst : st.owns = []) : ⊢ □ st.sl W ρ := by
  simp [State.sl, hst]
  istart
  imodintro
  iempintro

/-- Drop the non-persistent spatial part of the verifier state. -/
def Verifier.State.persist (st : State) : State :=
  { st with owns := [] }

/-- Translation to `ScopedM`'s flat context. -/
def Verifier.State.toFlatCtx (st : State) : FlatCtx :=
  ⟨st.decls, st.asserts⟩

/-- The initial verifier state: only the builtin guard constant is declared. -/
def Verifier.State.init : State := ⟨Signature.empty.addConst guardConst, [], []⟩

/-- The environment satisfies the verifier state: every assertion holds and the
builtin facts are in force. -/
structure Verifier.State.holdsFor (st : State) (ρ : Env) : Prop where
  asserts : ∀ φ ∈ st.asserts, φ.eval ρ
  builtins : Builtins.holdsFor ρ

structure Verifier.State.wf (st : State) : Prop where
  assertsWf : st.asserts.wfIn st.decls
  namesDisjoint : st.decls.allNames.Nodup
  ownsWf : st.owns.wfIn st.decls
  builtins : Builtins.wf st.decls

theorem Verifier.State.init_wf : State.init.wf where
  assertsWf := fun φ hφ => by simp [State.init] at hφ
  namesDisjoint := by
    simp [State.init, Signature.allNames, Signature.addConst, Signature.empty]
  ownsWf := fun a ha => by simp [State.init] at ha
  builtins := ⟨List.Mem.head _⟩

/-- The canonical initial environment: the guard constant pinned to true. -/
def Env.init : Env :=
  Env.empty.updateConst guardConst.sort guardConst.name true

theorem Verifier.State.init_holdsFor : State.init.holdsFor Env.init where
  asserts := fun φ hφ => by simp [State.init] at hφ
  builtins := ⟨by simpa [Env.init] using
    Env.supportsGuarding_updateConst Env.empty⟩

def Verifier.State.freshConst (hint : Option String) (t : Srt) (st : State) : Decl.Const :=
  let base := hint.getD "_v"
  let x' := Fresh.freshNumbers base st.decls.allNames
  ⟨x', t⟩

def Verifier.State.addItem (st : State) (item : CtxItem) :=
  match item with
  | .pure φ => { st with asserts := φ :: st.asserts }
  | .spatial p => { st with owns := p :: st.owns }

theorem Verifier.State.wf_addConst (st : State) (c : Decl.Const) :
    State.wf st →
    c.name ∉ st.decls.allNames →
    State.wf { st with decls := st.decls.addConst c } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addConst hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addConst _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addConst _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addConst _ _)

theorem Verifier.State.wf_addUnary (st : State) (u : Decl.Unary) :
    State.wf st →
    u.name ∉ st.decls.allNames →
    State.wf { st with decls := st.decls.addUnary u } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addUnary hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addUnary _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addUnary _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addUnary _ _)

theorem Verifier.State.wf_addBinary (st : State) (b : Decl.Binary) :
    State.wf st →
    b.name ∉ st.decls.allNames →
    State.wf { st with decls := st.decls.addBinary b } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addBinary hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addBinary _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addBinary _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addBinary _ _)

theorem Verifier.State.wf_addTernary (st : State) (t : Decl.Ternary) :
    State.wf st →
    t.name ∉ st.decls.allNames →
    State.wf { st with decls := st.decls.addTernary t } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addTernary hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addTernary _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addTernary _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addTernary _ _)

theorem Verifier.State.wf_addUnaryRel (st : State) (u : Decl.UnaryRel) :
    State.wf st →
    u.name ∉ st.decls.allNames →
    State.wf { st with decls := st.decls.addUnaryRel u } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addUnaryRel hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addUnaryRel _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addUnaryRel _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addUnaryRel _ _)

theorem Verifier.State.wf_addBinaryRel (st : State) (b : Decl.BinaryRel) :
    State.wf st →
    b.name ∉ st.decls.allNames →
    State.wf { st with decls := st.decls.addBinaryRel b } := by
  intro hwf hfresh
  have hwf' := Signature.wf_addBinaryRel hwf.namesDisjoint hfresh
  constructor
  · exact Context.wfIn_mono _ hwf.assertsWf (Signature.Subset.subset_addBinaryRel _ _) hwf'
  · exact hwf'
  · exact SpatialContext.wfIn_mono hwf.ownsWf (Signature.Subset.subset_addBinaryRel _ _) hwf'
  · exact hwf.builtins.mono (Signature.Subset.subset_addBinaryRel _ _)

theorem Verifier.State.freshConst_fresh (st : State) (hint : Option String) (τ : Srt) :
    (st.freshConst hint τ).name ∉ st.decls.allNames :=
  Fresh.freshNumbers_not_mem (hint.getD "_v") st.decls.allNames

theorem Verifier.State.wf_addAssert (st : State) :
    State.wf st →
    φ.wfIn st.decls →
    State.wf { st with asserts := φ :: st.asserts } := by
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

theorem Verifier.State.wf_addSpatial (st : State) :
    State.wf st →
    a.wfIn st.decls →
    State.wf { st with owns := a :: st.owns } := by
  intro hwf ha
  constructor
  · exact hwf.assertsWf
  · exact hwf.namesDisjoint
  · simpa [SpatialContext.wfIn_cons] using And.intro ha hwf.ownsWf
  · exact hwf.builtins
