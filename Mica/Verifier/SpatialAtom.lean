-- SUMMARY: Spatial atoms and contexts of the verifier state: their well-formedness, basic operations, and Iris interpretation.
import Mica.FirstOrderLogic.Terms
import Mica.SeparationLogic.Wp
import Mica.SourceTinyML.LogicalRelation
import Mica.SourceTinyML.Types

open Iris Iris.BI

/-! # Spatial Atoms and Contexts

A `SpatialAtom` is an ownership item stored in the verifier state: a points-to
of a reference or an owned array. A `SpatialContext` is a list of them. Both are
interpreted as Iris assertions, and a context as the separating conjunction of
its atoms. -/

inductive SpatialAtom where
  /-- Field `0` of the block at location term `l` holds value term `v`, whose TinyML type is `ty`.
  The interpretation carries the value typing fact as part of the same spatial atom. -/
  | pointsTo : Term .value → Term .value → TinyML.Typ → SpatialAtom
  /-- An owned mutable array and its immutable vector snapshot. -/
  | arrayPointsTo : Term .value → Term .value → TinyML.Typ → SpatialAtom
  deriving DecidableEq

abbrev SpatialContext := List SpatialAtom

namespace SpatialAtom

/-- The head constructor of a spatial atom. Both constructors carry a key
term, a value term, and a type, so atoms can be processed generically by
kind. -/
inductive Kind where
  | ref
  | array
  deriving DecidableEq

/-- The atom of a given kind, from its key term, value term, and type. -/
def Kind.atom : Kind → Term .value → Term .value → TinyML.Typ → SpatialAtom
  | .ref => .pointsTo
  | .array => .arrayPointsTo

/-- For error messages. -/
def Kind.print : Kind → String
  | .ref => "points-to"
  | .array => "owned array"

def kind : SpatialAtom → Kind
  | .pointsTo .. => .ref
  | .arrayPointsTo .. => .array

/-- The key term an atom asserts ownership of: the location of a points-to,
the array value of an owned array. -/
def key : SpatialAtom → Term .value
  | .pointsTo l _ _ => l
  | .arrayPointsTo a _ _ => a

/-- The value term stored under an atom's key: the contents of a reference,
the vector snapshot of an owned array. -/
def val : SpatialAtom → Term .value
  | .pointsTo _ v _ => v
  | .arrayPointsTo _ v _ => v

def ty : SpatialAtom → TinyML.Typ
  | .pointsTo _ _ ty => ty
  | .arrayPointsTo _ _ ty => ty

@[simp] theorem eta (a : SpatialAtom) : a.kind.atom a.key a.val a.ty = a := by
  cases a <;> rfl

def wfIn : SpatialAtom → Signature → Prop
  | .pointsTo l v _, Δ => l.wfIn Δ ∧ v.wfIn Δ
  | .arrayPointsTo a v _, Δ => a.wfIn Δ ∧ v.wfIn Δ

@[simp] theorem atom_wfIn {k : Kind} {t v : Term .value} {ty : TinyML.Typ} {Δ : Signature} :
    (k.atom t v ty).wfIn Δ ↔ t.wfIn Δ ∧ v.wfIn Δ := by
  cases k <;> exact Iff.rfl

theorem wfIn.key {a : SpatialAtom} {Δ : Signature} (h : a.wfIn Δ) : a.key.wfIn Δ := by
  cases a <;> exact h.1

theorem wfIn.val {a : SpatialAtom} {Δ : Signature} (h : a.wfIn Δ) : a.val.wfIn Δ := by
  cases a <;> exact h.2

theorem wfIn_mono {a : SpatialAtom} {Δ Δ' : Signature}
    (h : a.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : a.wfIn Δ' := by
  cases a with
  | pointsTo l v _ => exact ⟨Term.wfIn_mono l h.1 hsub hwf, Term.wfIn_mono v h.2 hsub hwf⟩
  | arrayPointsTo a v _ => exact ⟨Term.wfIn_mono a h.1 hsub hwf, Term.wfIn_mono v h.2 hsub hwf⟩

def interp [MicaGS HasLC.hasLC Sig] (W : TinyML.World) (ρ : Env) :
    SpatialAtom → iProp
  | .pointsTo l v ty => ∃ (loc : Runtime.Location),
      ⌜Term.eval ρ l = .loc loc⌝ ∗ loc ↦ [Term.eval ρ v] ∗
        TinyML.ValHasType W (Term.eval ρ v) ty
  | .arrayPointsTo a v ty => ∃ (loc : Runtime.Location) (vs : List Runtime.Val),
      ⌜Term.eval ρ a = .array vs.length loc⌝ ∗
      ⌜Term.eval ρ v = .vec vs⌝ ∗ loc ↦ vs ∗
        TinyML.ValHasType W (.vec vs) (.vec ty)

/-- Congruence of interpretation in the key and value terms, at equal evaluation. -/
theorem congr [MicaGS HasLC.hasLC Sig] (W : TinyML.World) {ρ : Env} {k : Kind}
    {t t' v v' : Term .value} {ty : TinyML.Typ}
    (ht : Term.eval ρ t = Term.eval ρ t')
    (hv : Term.eval ρ v = Term.eval ρ v') :
    interp W ρ (k.atom t v ty) ⊣⊢ interp W ρ (k.atom t' v' ty) := by
  cases k <;> simp only [Kind.atom, interp, ht, hv] <;>
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩

/-- Pure formulas implied by an atom's interpretation. They are assumed
alongside the atom whenever it enters the verifier's spatial context. -/
def facts : SpatialAtom → List Formula
  | .pointsTo .. => []
  | .arrayPointsTo a v ty =>
      .eq .int (.unop .vecLen (.unop .toVec v)) (.unop .arrayLen a) ::
        TinyML.elementConstraints ty v

theorem facts_wfIn {a : SpatialAtom} {Δ : Signature} (h : a.wfIn Δ) :
    ∀ φ ∈ a.facts, φ.wfIn Δ := by
  cases a with
  | pointsTo l v ty => simp [facts]
  | arrayPointsTo a v ty =>
    intro φ hφ
    simp only [facts, List.mem_cons] at hφ
    rcases hφ with rfl | hφ
    · exact ⟨⟨trivial, ⟨trivial, h.2⟩⟩, ⟨trivial, h.1⟩⟩
    · exact TinyML.elementConstraints_wfIn h.2 φ hφ

end SpatialAtom

namespace SpatialContext

def wfIn (ctx : SpatialContext) (Δ : Signature) : Prop :=
  ∀ a ∈ ctx, a.wfIn Δ

@[simp] theorem wfIn_nil (Δ : Signature) : wfIn ([] : SpatialContext) Δ := by
  intro a ha
  cases ha

@[simp] theorem wfIn_cons (a : SpatialAtom) (ctx : SpatialContext) (Δ : Signature) :
    wfIn (a :: ctx) Δ ↔ a.wfIn Δ ∧ wfIn ctx Δ := by
  constructor
  · intro h
    refine ⟨h a (by simp), ?_⟩
    intro b hb
    exact h b (by simp [hb])
  · intro h b hb
    simp at hb
    rcases hb with rfl | hb
    · exact h.1
    · exact h.2 b hb

theorem wfIn_mono {ctx : SpatialContext} {Δ Δ' : Signature}
    (h : wfIn ctx Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : wfIn ctx Δ' :=
  fun a ha => SpatialAtom.wfIn_mono (h a ha) hsub hwf

abbrev insert (a : SpatialAtom) (ctx : SpatialContext) : SpatialContext := a :: ctx

/-- The atom at index `n`, and the context without it. -/
def remove : List SpatialAtom → Nat → Option (SpatialAtom × List SpatialAtom)
  | [],     _     => none
  | a :: Γ, 0     => some (a, Γ)
  | a :: Γ, n + 1 => (remove Γ n).map fun (b, Γ') => (b, a :: Γ')

@[simp] theorem remove_nil (n : Nat) : remove [] n = none := by
  cases n <;> simp [remove]

@[simp] theorem remove_cons_zero (a : SpatialAtom) (Γ : List SpatialAtom) :
    remove (a :: Γ) 0 = some (a, Γ) := rfl

@[simp] theorem remove_cons_succ (a : SpatialAtom) (Γ : List SpatialAtom) (n : Nat) :
    remove (a :: Γ) (n + 1) = (remove Γ n).map fun (b, Γ') => (b, a :: Γ') := rfl

theorem wfIn_remove {ctx : SpatialContext} {Δ : Signature} {n : Nat}
    {a : SpatialAtom} {rest : SpatialContext}
    (hctx : wfIn ctx Δ) (hrem : remove ctx n = some (a, rest)) :
    a.wfIn Δ ∧ wfIn rest Δ := by
  induction ctx generalizing n a rest with
  | nil => simp at hrem
  | cons b ctx ih =>
    cases n with
    | zero =>
      simp [remove] at hrem
      obtain ⟨rfl, rfl⟩ := hrem
      simpa [wfIn_cons] using hctx
    | succ n =>
      have htail : wfIn ctx Δ := (wfIn_cons b ctx Δ).1 hctx |>.2
      have hhead : b.wfIn Δ := (wfIn_cons b ctx Δ).1 hctx |>.1
      simp only [remove_cons_succ] at hrem
      match hr : remove ctx n with
      | none => simp [hr] at hrem
      | some (a', rest') =>
        simp [hr] at hrem
        obtain ⟨rfl, rfl⟩ := hrem
        obtain ⟨ha, hrest⟩ := ih htail hr
        exact ⟨ha, (wfIn_cons b rest' Δ).2 ⟨hhead, hrest⟩⟩

end SpatialContext

/-! ## Interpretation of contexts -/

variable [MicaGS HasLC.hasLC Sig]

namespace SpatialAtom

/-- Interpreting a well-formed atom only depends on the environment values of
    symbols in the ambient signature. -/
theorem interp_agreeOn (W : TinyML.World) {a : SpatialAtom} {Δ : Signature} {ρ ρ' : Env}
    (hwf : a.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') :
    interp W ρ a ⊣⊢ interp W ρ' a := by
  cases a with
  | pointsTo l v ty =>
    simp only [interp, Term.eval_agreeOn hwf.1 hagree, Term.eval_agreeOn hwf.2 hagree]
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩
  | arrayPointsTo a v ty =>
    simp only [interp, Term.eval_agreeOn hwf.1 hagree, Term.eval_agreeOn hwf.2 hagree]
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩

/-- If a points-to atom's location term evaluates to `loc`, its interpretation
    is equivalent to the raw heap ownership together with the bundled value
    typing fact. -/
theorem interp_pointsTo (W : TinyML.World) {ρ : Env} {lt vt : Term .value}
    {ty : TinyML.Typ} {loc : Runtime.Location}
    (hloc : Term.eval ρ lt = .loc loc) :
    interp W ρ (.pointsTo lt vt ty) ⊣⊢
      loc ↦ [Term.eval ρ vt] ∗ TinyML.ValHasType W (Term.eval ρ vt) ty := by
  constructor
  · simp only [interp]
    istart
    iintro ⟨%loc', %Hloc', Hpt, Hty⟩
    have : loc' = loc := Runtime.Val.loc.inj (Hloc'.symm.trans hloc)
    subst this
    iframe Hpt Hty
  · simp only [interp]
    istart
    iintro ⟨Hpt, Hty⟩
    iexists loc
    isplitr
    · ipureintro
      exact hloc
    · iframe Hpt Hty

/-- If an owned-array atom's array and snapshot terms evaluate to the same
    runtime block, its interpretation exposes ownership of that whole block
    together with the element-typing fact carried by the vector snapshot. -/
theorem interp_arrayPointsTo (W : TinyML.World) {ρ : Env} {arrt vt : Term .value}
    {ty : TinyML.Typ} {loc : Runtime.Location} {vs : List Runtime.Val}
    (harr : Term.eval ρ arrt = .array vs.length loc)
    (hvec : Term.eval ρ vt = .vec vs) :
    interp W ρ (.arrayPointsTo arrt vt ty) ⊣⊢
      loc ↦ vs ∗ TinyML.ValHasType W (.vec vs) (.vec ty) := by
  constructor
  · simp only [interp]
    istart
    iintro ⟨%loc', %vs', %Harr', %Hvec', Hpt, Hty⟩
    have hloc : loc' = loc := by
      exact Runtime.Val.array.inj (Harr'.symm.trans harr) |>.2
    have hvs : vs' = vs := Runtime.Val.vec.inj (Hvec'.symm.trans hvec)
    subst hloc
    subst hvs
    iframe Hpt Hty
  · simp only [interp]
    istart
    iintro ⟨Hpt, Hty⟩
    iexists loc, vs
    isplitr
    · ipureintro
      exact harr
    · isplitr
      · ipureintro
        exact hvec
      · iframe Hpt Hty

/-- Destruct an owned-array atom at an in-bounds index: expose the underlying
block, the integer index witness, and the persistent element typing of the
snapshot. -/
theorem interp_arrayPointsTo_lookup (W : TinyML.World) {ρ : Env}
    {arr contents idx : Term .value} {elemTy : TinyML.Typ} {vidx : Runtime.Val}
    (hidx : Term.eval ρ idx = vidx)
    (hi : 0 ≤ Term.eval ρ (.unop .toInt idx))
    (hlt : Term.eval ρ (.unop .toInt idx) < Term.eval ρ (.unop .arrayLen arr)) :
    SpatialAtom.interp W ρ (.arrayPointsTo arr contents elemTy) ⊢
      TinyML.ValHasType W vidx .int -∗
      ∃ (loc : Runtime.Location) (vs : List Runtime.Val) (i : Int),
        ⌜Term.eval ρ arr = .array vs.length loc⌝ ∗ ⌜Term.eval ρ contents = .vec vs⌝ ∗
        ⌜vidx = .int i⌝ ∗ ⌜0 ≤ i⌝ ∗ ⌜i.toNat < vs.length⌝ ∗
        loc ↦ vs ∗ □ TinyML.ValHasType W (.vec vs) (.vec elemTy) := by
  simp only [SpatialAtom.interp]
  istart
  iintro Hatom
  iintro HidxTy
  icases Hatom with ⟨%loc, %vs, %ha, %hv, Hpt, #HvecTy⟩
  ihave Hidx' := (TinyML.ValHasType.int W vidx).1 $$ HidxTy
  icases Hidx' with ⟨%i, %hvidx⟩
  have hi' : 0 ≤ i := by simpa [Term.eval, UnOp.eval, hidx, hvidx] using hi
  have hlt' : i.toNat < vs.length := by
    have : i < (vs.length : Int) := by
      simpa [Term.eval, UnOp.eval, ha, hidx, hvidx] using hlt
    omega
  iexists loc, vs, i
  isplitr
  · ipureintro
    exact ha
  · isplitr
    · ipureintro
      exact hv
    · isplitr
      · ipureintro
        exact hvidx
      · isplitr
        · ipureintro
          exact hi'
        · isplitr
          · ipureintro
            exact hlt'
          · isplitl [Hpt]
            · iexact Hpt
            · imodintro
              iexact HvecTy

/-- An owned-array atom types every element its snapshot holds in bounds. -/
theorem interp_arrayPointsTo_elem (W : TinyML.World) {ρ : Env}
    {arr contents idx : Term .value} {elemTy : TinyML.Typ}
    (hi : 0 ≤ Term.eval ρ (.unop .toInt idx))
    (hlt : Term.eval ρ (.unop .toInt idx) < Term.eval ρ (.unop .arrayLen arr)) :
    SpatialAtom.interp W ρ (.arrayPointsTo arr contents elemTy) ⊢
      SpatialAtom.interp W ρ (.arrayPointsTo arr contents elemTy) ∗
      TinyML.ValHasType W
        (Term.eval ρ (.binop .vecGet (.unop .toVec contents) (.unop .toInt idx))) elemTy := by
  simp only [SpatialAtom.interp]
  istart
  iintro ⟨%loc, %vs, %ha, %hv, Hpt, #HvecTy⟩
  have hi' : 0 ≤ Term.eval ρ (.unop .toInt idx) := hi
  have hlt' : (Term.eval ρ (.unop .toInt idx)).toNat < vs.length := by
    have : Term.eval ρ (.unop .toInt idx) < (vs.length : Int) := by
      simpa [Term.eval, UnOp.eval, ha] using hlt
    exact (Int.toNat_lt hi').2 this
  obtain ⟨w, hw⟩ : ∃ w, vs[(Term.eval ρ (.unop .toInt idx)).toNat]? = some w :=
    ⟨_, List.getElem?_eq_getElem hlt'⟩
  have hresult :
      Term.eval ρ (.binop .vecGet (.unop .toVec contents) (.unop .toInt idx)) = w := by
    rw [Term.eval]
    generalize Term.eval ρ (.unop .toInt idx) = I at hi' hw ⊢
    simp [BinOp.eval, Term.eval, UnOp.eval, hv, hi', hw]
  ihave Helem := (TinyML.ValHasType.vec W (.vec vs) elemTy).1 $$ HvecTy
  icases Helem with ⟨%ws, %hws, Htys⟩
  have hws_eq : ws = vs := Runtime.Val.vec.inj hws.symm
  subst ws
  ihave Hty := (BigSepL.bigSepL_lookup (Φ := fun _ w => TinyML.ValHasType W w elemTy)
    hw) $$ Htys
  rw [hresult]
  isplitl [Hpt]
  · iexists loc, vs
    isplitr
    · ipureintro; exact ha
    · isplitr
      · ipureintro; exact hv
      · iframe Hpt HvecTy
  · iexact Hty

theorem interp_facts (W : TinyML.World) {ρ : Env} (a : SpatialAtom) :
    interp W ρ a ⊢ ⌜∀ φ ∈ a.facts, φ.eval ρ⌝ ∗ interp W ρ a := by
  cases a with
  | pointsTo l v ty =>
    istart
    iintro H
    isplitr [H]
    · ipureintro
      simp [facts]
    · iexact H
  | arrayPointsTo a v ty =>
    simp only [interp]
    istart
    iintro H
    icases H with ⟨%loc, %vs, %ha, %hv, Hpt, #Hty⟩
    ihave %helements := TinyML.elementConstraints_hold (ty := ty) hv $$ Hty
    isplitl []
    · ipureintro
      intro φ hφ
      simp only [facts, List.mem_cons] at hφ
      rcases hφ with rfl | hφ
      · simp [Formula.eval, Term.eval, UnOp.eval, ha, hv]
      · exact helements φ hφ
    · iexists loc, vs
      isplitr
      · ipureintro
        exact ha
      · isplitr
        · ipureintro
          exact hv
        · iframe Hpt Hty

end SpatialAtom

namespace SpatialContext

def interp (W : TinyML.World) (ρ : Env) : SpatialContext → iProp
  | []     => emp
  | a :: Γ => a.interp W ρ ∗ interp W ρ Γ

/-- Interpreting a well-formed context only depends on the environment values of
    symbols in the ambient signature. -/
theorem interp_agreeOn (W : TinyML.World) {ctx : SpatialContext} {Δ : Signature} {ρ ρ' : Env}
    (hwf : wfIn ctx Δ) (hagree : Env.agreeOn Δ ρ ρ') :
    interp W ρ ctx ⊣⊢ interp W ρ' ctx := by
  induction ctx with
  | nil => simp [interp]
  | cons a ctx ih =>
    have ha : SpatialAtom.interp W ρ a ⊣⊢ SpatialAtom.interp W ρ' a :=
      SpatialAtom.interp_agreeOn W (hwf a (by simp)) hagree
    have htail : wfIn ctx Δ := (wfIn_cons a ctx Δ).1 hwf |>.2
    have hctx : interp W ρ ctx ⊣⊢ interp W ρ' ctx := ih htail
    simp only [interp]
    exact ⟨sep_mono ha.1 hctx.1, sep_mono ha.2 hctx.2⟩

@[simp] theorem interp_nil (W : TinyML.World) (ρ : Env) : interp W ρ [] = emp := rfl
@[simp] theorem interp_cons (W : TinyML.World) (ρ : Env) (a : SpatialAtom) (Γ : SpatialContext) :
    interp W ρ (a :: Γ) = (a.interp W ρ ∗ interp W ρ Γ) := rfl

@[simp] theorem interp_insert (W : TinyML.World) (ρ : Env) (a : SpatialAtom) (ctx : SpatialContext) :
    interp W ρ (insert a ctx) = (a.interp W ρ ∗ interp W ρ ctx) := rfl

omit [MicaGS HasLC.hasLC Sig] in
private theorem sep_comm3 {A B C : iProp} : A ∗ (B ∗ C) ⊣⊢ B ∗ (A ∗ C) :=
  ⟨sep_assoc.2 |>.trans (sep_mono_left sep_comm.1) |>.trans sep_assoc.1,
   sep_assoc.2 |>.trans (sep_mono_left sep_comm.2) |>.trans sep_assoc.1⟩

theorem interp_remove (W : TinyML.World) (ρ : Env) (ctx : SpatialContext) (n : Nat)
    (a : SpatialAtom) (rest : SpatialContext)
    (h : remove ctx n = some (a, rest)) :
    interp W ρ ctx ⊣⊢ a.interp W ρ ∗ interp W ρ rest := by
  induction ctx generalizing n a rest with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [remove] at h; obtain ⟨rfl, rfl⟩ := h; simp [interp]
    | succ n =>
      simp only [remove_cons_succ] at h
      match hr : remove xs n, h with
      | some (b, rest'), h =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨sep_mono_right (ih n b rest' hr).1 |>.trans sep_comm3.1,
               sep_comm3.2 |>.trans (sep_mono_right (ih n b rest' hr).2)⟩

end SpatialContext
