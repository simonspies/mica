-- SUMMARY: Concrete Iris ghost-state signature for Mica: invariants, later credits, and heap resources over TinyML heaps.
import Iris.BI.Lib.GenHeap
import Iris.ProgramLogic.WeakestPre
import Iris.ProofMode
import Mica.TinyML.Language

/-!
The concrete Iris signature for Mica: a `MicaGpreS`/`MicaGS` pair of ghost-state
classes for the generic heap over TinyML locations and blocks, and the bundled
functor signature `Sig` they are instantiated at.
-/

open Iris ProgramLogic Std

/-- Ghost-state prerequisites: the signature supports invariants, later
    credits, and a generic heap over TinyML locations and blocks. -/
class MicaGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGpreS GF where
  heap_pre : genHeapPreS PNat Runtime.Location TinyML.Block GF TinyML.HeapF

attribute [reducible, instance] MicaGpreS.heap_pre

/-- Allocated ghost state: invariant machinery plus a heap instance (ghost
    names for the heap and meta maps). Mica's `iProp` definitions are stated
    parametrically in this class so that adequacy can allocate the names. -/
class MicaGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  heap : genHeapGS PNat Runtime.Location TinyML.Block GF TinyML.HeapF

attribute [reducible, instance] MicaGS.heap

/-- The concrete bundled functor signature for Mica: invariants (0–2), later
    credits (3), the heap and meta ghost maps (4–6). -/
def Sig : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (F := PNat) (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView PNat Runtime.Location (Agree (LeibnizO TinyML.Block)) TinyML.HeapF),
          by infer_instance⟩
  | 5 => ⟨constOF (HeapView PNat Runtime.Location (Agree (LeibnizO GName)) TinyML.HeapF),
          by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instMicaGpreS_Sig : MicaGpreS HasLC.hasLC Sig where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6

/-- The gen-heap `insert` (alter-based) agrees with `Heap.update`. -/
theorem TinyML.Heap.insert_eq_update (μ : TinyML.Heap) (l : Runtime.Location)
    (b : TinyML.Block) : Iris.Std.insert μ l b = μ.update l b := by
  refine Std.ExtTreeMap.ext_getElem? fun k => ?_
  show (μ.alter l fun _ => some b)[k]? = (μ.insert l b)[k]?
  simp [Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]

/-- `genHeap_alloc` restated against `Heap.update`. -/
theorem genHeap_alloc' {hlc} {GF : BundledGFunctors} [MicaGS hlc GF] {σ : TinyML.Heap}
    {l : Runtime.Location} {b : TinyML.Block} (h : σ.lookup l = none) :
    genHeapInterp (F := PNat) (GF := GF) (H := TinyML.HeapF) σ ⊢
      |==> (genHeapInterp (F := PNat) (GF := GF) (H := TinyML.HeapF) (σ.update l b) ∗
        pointsTo l (DFrac.own 1) b ∗ metaToken l ⊤) := by
  have := genHeap_alloc (GF := GF) (H := TinyML.HeapF) (v := b)
    (show Iris.Std.get? σ l = none from h)
  rwa [TinyML.Heap.insert_eq_update] at this

/-- `genHeap_update` restated against `Heap.update`. -/
theorem genHeap_update' {hlc} {GF : BundledGFunctors} [MicaGS hlc GF] {σ : TinyML.Heap}
    {l : Runtime.Location} {b₁ b₂ : TinyML.Block} :
    genHeapInterp (F := PNat) (GF := GF) (H := TinyML.HeapF) σ ∗ pointsTo l (DFrac.own 1) b₁ ==∗
      genHeapInterp (F := PNat) (GF := GF) (H := TinyML.HeapF) (σ.update l b₂) ∗
        pointsTo l (DFrac.own 1) b₂ := by
  have := genHeap_update (GF := GF) (H := TinyML.HeapF) (σ := σ) (l := l)
    (v₁ := b₁) (v₂ := b₂)
  rwa [TinyML.Heap.insert_eq_update] at this

/-- Ownership of the physical TinyML heap — Mica's state interpretation.
    The heap assertion that the generic primitive-call rule (`wp.prim`)
    interfaces with. -/
abbrev heapInterp {hlc} {GF : BundledGFunctors} [MicaGS hlc GF] (σ : TinyML.Heap) :
    IProp GF :=
  genHeapInterp (F := PNat) (GF := GF) (H := TinyML.HeapF) σ

/-- State interpretation: ownership of the physical TinyML heap. -/
instance instStateInterp {hlc} {GF : BundledGFunctors} [MicaGS hlc GF] :
    StateInterp TinyML.Heap Empty GF where
  stateInterp σ _ _ _ := genHeapInterp (F := PNat) (GF := GF) (H := TinyML.HeapF) σ

/-- The Iris ghost-state interface for the TinyML language: no observations,
    no forked threads, no extra laters per step. -/
instance instIrisGS {hlc} {GF : BundledGFunctors} (ctx : TinyML.PrimCtx) [MicaGS hlc GF] :
    IrisGS_gen hlc (TinyML.LExpr ctx) GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $
