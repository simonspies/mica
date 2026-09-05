-- SUMMARY: Name supply, function context, local variable environments, and the head signatures and freshness conditions of the relational encoding.
import Mica.FOL.SpecFn
import Mica.Base.Fixpoint
import Mica.SourceTinyML.Typed
import Mica.Base.Fresh

namespace Verifier.RelationalEncoding

/-! ## Name supply for fresh-name allocation -/

/-- Avoid list used to generate fresh names. -/
structure NameSupply where
  avoid : List String

/-- Allocate a name not in the avoid list, derived from `base`. -/
def NameSupply.fresh (s : NameSupply) (base : String) : String :=
  Fresh.freshName s.avoid base

/-- Reserve a name in the supply so it is never returned by `fresh` again. -/
def NameSupply.reserve (s : NameSupply) (name : String) : NameSupply :=
  { avoid := name :: s.avoid }

theorem NameSupply.fresh_not_in_avoid (s : NameSupply) (base : String) :
    s.fresh base ∉ s.avoid :=
  Fresh.freshName_not_in_avoid s.avoid base

/-- A supply *covers* a signature when every name declared in the signature is
already reserved. Reservation extends across `reserve`. -/
def NameSupply.Covers (s : NameSupply) (Δ : Signature) : Prop :=
  ∀ n, n ∈ Δ.allNames → n ∈ s.avoid

theorem NameSupply.Covers.reserve {s : NameSupply} {Δ : Signature}
    (h : s.Covers Δ) (name : String) : (s.reserve name).Covers Δ := by
  intro n hn
  exact List.mem_cons_of_mem _ (h n hn)

/-- Reserving a name not currently in the signature covers the corresponding
`declVar` extension. -/
theorem NameSupply.Covers.declVar {s : NameSupply} {Δ : Signature}
    (h : s.Covers Δ) (name : String) (τ : Srt) :
    (s.reserve name).Covers (Δ.declVar ⟨name, τ⟩) := by
  intro n hn
  have hn' : n ∈ name :: (Δ.remove name).allNames := by
    simpa [Signature.declVar, Signature.addVar, Signature.allNames] using hn
  cases hn' with
  | head => simp [NameSupply.reserve]
  | tail _ ht =>
    have hΔn : n ∈ Δ.allNames := Signature.remove_allNames_subset ht
    exact List.mem_cons_of_mem _ (h n hΔn)


/-- The supply that reserves exactly the names a signature declares. -/
def NameSupply.ofSignature (Δ : Signature) : NameSupply := { avoid := Δ.allNames }

theorem NameSupply.ofSignature_covers (Δ : Signature) :
    (NameSupply.ofSignature Δ).Covers Δ := fun _ h => h

/-! ## Function context -/

/-- Maps TinyML function names to spec-level function symbols. -/
abbrev FunCtx := List (TinyML.Var × SpecFn)

def FunCtx.lookup (Γ : FunCtx) (x : TinyML.Var) : Option SpecFn :=
  (Γ.find? (·.1 == x)).map (·.2)

theorem FunCtx.mem_of_lookup {Γ : FunCtx} {x : TinyML.Var} {fn : SpecFn}
    (h : Γ.lookup x = some fn) : (x, fn) ∈ Γ := by
  simp only [FunCtx.lookup, Option.map_eq_some_iff] at h
  obtain ⟨⟨x', fn'⟩, hfind, hsnd⟩ := h
  simp at hsnd
  subst hsnd
  have hp := List.find?_some hfind
  simp at hp
  subst hp
  exact List.mem_of_find?_eq_some hfind

/-- Every relation in `Γ` is registered in `Δ` as a binary uninterpreted predicate
on `value × value`. -/
def FunCtx.relWfIn (Γ : FunCtx) (Δ : Signature) : Prop :=
  ∀ x (fn : SpecFn), (x, fn) ∈ Γ → fn.rel ∈ Δ.binaryRel

theorem FunCtx.relWfIn_mono {Γ : FunCtx} {Δ Δ' : Signature}
    (h : Γ.relWfIn Δ) (hsub : Δ.Subset Δ') : Γ.relWfIn Δ' :=
  fun x fn hxr => hsub.binaryRel _ (h x fn hxr)

/-- Every relation in `Γ` has its solver-facing value function and definedness
predicate registered in `Δ`. -/
def FunCtx.funcWfIn (Γ : FunCtx) (Δ : Signature) : Prop :=
  ∀ x (fn : SpecFn), (x, fn) ∈ Γ →
    fn.func ∈ Δ.unary ∧ fn.defined ∈ Δ.unaryRel

theorem FunCtx.funcWfIn_mono {Γ : FunCtx} {Δ Δ' : Signature}
    (h : Γ.funcWfIn Δ) (hsub : Δ.Subset Δ') : Γ.funcWfIn Δ' := by
  intro x fn hxr
  exact ⟨hsub.unary _ (h x fn hxr).1, hsub.unaryRel _ (h x fn hxr).2⟩

/-- Bundled well-formedness: every relation in `Γ` has all three solver-facing
symbols (the binary relation, the value function, and the definedness predicate)
registered in `Δ`. -/
structure FunCtx.wfIn (Γ : FunCtx) (Δ : Signature) : Prop where
  rel : Γ.relWfIn Δ
  func : Γ.funcWfIn Δ

theorem FunCtx.wfIn_mono {Γ : FunCtx} {Δ Δ' : Signature}
    (h : Γ.wfIn Δ) (hsub : Δ.Subset Δ') : Γ.wfIn Δ' :=
  ⟨FunCtx.relWfIn_mono h.rel hsub, FunCtx.funcWfIn_mono h.func hsub⟩

/-- In `ρ`, the relation symbol of every function in `Γ` reads as the graph of
that function's value function and definedness predicate. -/
def FunCtx.Agreement (Γ : FunCtx) (ρ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ x y, fn.evalRelates ρ x y ↔ fn.evalDefined ρ x ∧ fn.evalCall ρ x = y

theorem FunCtx.Agreement.updateConst {Γ : FunCtx} {ρ : Env}
    (hΓ : Γ.Agreement ρ) (τ : Srt) (x : String) (v : τ.denote) :
    Γ.Agreement (ρ.updateConst τ x v) := by
  intro f fn hmem a b
  simpa [Env.updateConst_unary, Env.updateConst_unaryRel, Env.updateConst_binaryRel]
    using hΓ f fn hmem a b

/-- The symbols of `fn` do not collide with those of any function in `Γ`. -/
def FunCtx.unused (Γ : FunCtx) (fn : SpecFn) : Prop :=
  ∀ g fn', (g, fn') ∈ Γ →
    fn'.relName ≠ fn.relName ∧ fn'.funcName ≠ fn.funcName ∧ fn'.defName ≠ fn.defName

/-- Extend the context so recursive calls to `f` resolve to `fn`. -/
def FunCtx.recursive (Γ : FunCtx) (f : TinyML.Var) (fn : SpecFn) : FunCtx :=
  (f, fn) :: Γ

/-! ## Value-variable well-formedness -/

/-- A bare value variable declared in a well-formed signature is a well-formed
value term. -/
theorem var_value_wfIn {x : String} {Δ : Signature}
    (hΔ : Δ.wf) (hmem : (⟨x, .value⟩ : Var) ∈ Δ.vars) :
    (Term.var .value x).wfIn Δ := by
  refine ⟨hmem, ?_, ?_⟩
  · intro τ' hc; exact Signature.wf_no_const_of_var hΔ hmem hc
  · intro τ' hv; exact Signature.wf_unique_var hΔ hmem hv

/-! ## Local variable environments -/

/-- Local TinyML variables available to the relational encoder.  Bindings are
searched from the front, so extending the environment implements shadowing. -/
abbrev VarEnv := List (String × Term .value)

namespace VarEnv

/-- Look up a TinyML variable in the local encoder environment. -/
def lookup (ρ : VarEnv) (x : String) : Option (Term .value) :=
  List.lookup x ρ

/-- Extend a local encoder environment with a TinyML variable binding. -/
def bind (ρ : VarEnv) (x : String) (v : Term .value) : VarEnv :=
  (x, v) :: ρ

/-- Extend a local encoder environment when a TinyML binder is named; anonymous
binders leave the environment unchanged. -/
def bindBinder (ρ : VarEnv) (b : Typed.Binder) (v : Term .value) : VarEnv :=
  match b.name with
  | none => ρ
  | some x => ρ.bind x v

def prodProj (v : Term .value) (i : Nat) : Term .value :=
  .unop .vhead (vtailN (.unop .toValList v) i)

private def bindBindersFrom (ρ : VarEnv) (v : Term .value) : List Typed.Binder → Nat → VarEnv
  | [], _ => ρ
  | b :: bs, i => bindBindersFrom (ρ.bindBinder b (prodProj v i)) v bs (i + 1)

def bindBinders (ρ : VarEnv) (bs : List Typed.Binder) (v : Term .value) : VarEnv :=
  bindBindersFrom ρ v bs 0

/-- Initial local environment induced by value variables declared in a FOL
signature. -/
def ofSignature (Δ : Signature) : VarEnv :=
  Δ.vars.filterMap fun v =>
    match v.sort with
    | .value => some (v.name, .var .value v.name)
    | _ => none

/-- The encoder environment reads only the declared variables. -/
private theorem ofSignature_congr {Δ Δ' : Signature} (h : Δ.vars = Δ'.vars) :
    ofSignature Δ = ofSignature Δ' := by
  rw [ofSignature, ofSignature, h]

/-- Every term stored in a local environment is well-formed in `Δ`. -/
def wfIn (δ : VarEnv) (Δ : Signature) : Prop :=
  ∀ x v, δ.lookup x = some v → v.wfIn Δ

@[simp] theorem lookup_bind (δ : VarEnv) (x : String) (v : Term .value) :
    (δ.bind x v).lookup x = some v := by
  simp [lookup, bind]

private theorem lookup_bind_of_ne {δ : VarEnv} {x y : String} {v : Term .value}
    (hxy : y ≠ x) : (δ.bind x v).lookup y = δ.lookup y := by
  have hbeq : (y == x) = false := by
    simp [hxy]
  simp [lookup, bind, List.lookup, hbeq]

theorem wfIn.bind {Δ : Signature} {δ : VarEnv} {x : String} {v : Term .value}
    (henv : δ.wfIn Δ) (hv : v.wfIn Δ) :
    (δ.bind x v).wfIn Δ := by
  intro y w hlookup
  by_cases hxy : y = x
  · subst y
    simp only [lookup_bind, Option.some.injEq] at hlookup
    subst w
    exact hv
  · have htail : δ.lookup y = some w := by
      simpa [lookup_bind_of_ne (δ := δ) (x := x) (v := v) hxy] using hlookup
    exact henv y w htail

theorem wfIn.bindBinder {Δ : Signature} {δ : VarEnv} {b : Typed.Binder}
    {v : Term .value} (henv : δ.wfIn Δ) (hv : v.wfIn Δ) :
    (δ.bindBinder b v).wfIn Δ := by
  cases b with
  | mk name ty =>
      cases name with
      | none => simpa [bindBinder] using henv
      | some x => simpa [bindBinder] using henv.bind hv

theorem prodProj_wfIn {Δ : Signature} {v : Term .value} (hv : v.wfIn Δ) (i : Nat) :
    (prodProj v i).wfIn Δ := by
  unfold prodProj
  have hto : (Term.unop UnOp.toValList v).wfIn Δ := by
    change UnOp.toValList.wfIn Δ ∧ v.wfIn Δ
    exact And.intro trivial hv
  change UnOp.vhead.wfIn Δ ∧ (vtailN (.unop .toValList v) i).wfIn Δ
  exact And.intro trivial (vtailN_wfIn hto i)

private theorem wfIn.bindBindersFrom {Δ : Signature} {δ : VarEnv} {v : Term .value}
    (henv : δ.wfIn Δ) (hv : v.wfIn Δ) :
    ∀ bs i, (bindBindersFrom δ v bs i).wfIn Δ
  | [], _ => henv
  | _ :: bs, i =>
      wfIn.bindBindersFrom
        (wfIn.bindBinder henv (prodProj_wfIn hv i)) hv bs (i + 1)

theorem wfIn.bindBinders {Δ : Signature} {δ : VarEnv} {bs : List Typed.Binder}
    {v : Term .value} (henv : δ.wfIn Δ) (hv : v.wfIn Δ) :
    (δ.bindBinders bs v).wfIn Δ := by
  simpa [bindBinders] using wfIn.bindBindersFrom henv hv bs 0

theorem ofSignature_wfIn {Δ : Signature} (hΔ : Δ.wf) :
    (ofSignature Δ).wfIn Δ := by
  intro x v hlookup
  obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hlookup
  have hmem : (x, v) ∈ ofSignature Δ := by
    rw [heq]
    simp
  unfold ofSignature at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨a, haΔ, ha⟩
  cases a with
  | mk name sort =>
    cases sort <;> simp at ha
    rcases ha with ⟨rfl, rfl⟩
    exact var_value_wfIn hΔ haΔ

end VarEnv

end Verifier.RelationalEncoding

/-! ## Head signature extensions

Encoding `rec f x := e` declares three solver-facing symbols on top of `Δ`: the
binary relation, the value function, and the definedness predicate. The
relational encoding reads only the relation, the func-form encoding only the
value function and the definedness predicate, and their equivalence needs all
three. `rel`, `func` and `both` say which of the symbols a signature declares;
the suffix `Arg` adds the input variable and `Res` the pinned result variable.
-/

namespace SpecFn.Sig
open Verifier.RelationalEncoding

def rel (Δ : Signature) (fn : SpecFn) : Signature :=
  Δ.addBinaryRel fn.rel

def func (Δ : Signature) (fn : SpecFn) : Signature :=
  (Δ.addUnary fn.func).addUnaryRel fn.defined

def both (Δ : Signature) (fn : SpecFn) : Signature :=
  func (rel Δ fn) fn

def relArg (Δ : Signature) (fn : SpecFn) (x : TinyML.Var) : Signature :=
  (rel Δ fn).declVar ⟨x, .value⟩

def relArgRes (Δ : Signature) (fn : SpecFn) (x res : TinyML.Var) : Signature :=
  (relArg Δ fn x).declVar ⟨res, .value⟩

/-- The body signature without the binary relation. The func-form body and the
axioms emitted for it are well-formed here, which is what makes them insensitive
to how the relation is interpreted. -/
def funcArg (Δ : Signature) (fn : SpecFn) (x : TinyML.Var) : Signature :=
  (func Δ fn).declVar ⟨x, .value⟩

def bothArg (Δ : Signature) (fn : SpecFn) (x : TinyML.Var) : Signature :=
  (both Δ fn).declVar ⟨x, .value⟩

private def bothArgRes (Δ : Signature) (fn : SpecFn) (x res : TinyML.Var) : Signature :=
  (bothArg Δ fn x).declVar ⟨res, .value⟩

variable {Δ : Signature} {fn : SpecFn} {x res : String}

private theorem subset_rel (Δ : Signature) (fn : SpecFn) : Δ.Subset (rel Δ fn) :=
  Signature.Subset.subset_addBinaryRel _ _

private theorem subset_func (Δ : Signature) (fn : SpecFn) : Δ.Subset (func Δ fn) :=
  (Signature.Subset.subset_addUnary _ _).trans (Signature.Subset.subset_addUnaryRel _ _)

private theorem rel_subset_both (Δ : Signature) (fn : SpecFn) :
    (rel Δ fn).Subset (both Δ fn) :=
  subset_func _ _

private theorem func_subset_both (Δ : Signature) (fn : SpecFn) :
    (func Δ fn).Subset (both Δ fn) :=
  ((subset_rel Δ fn).addUnary fn.func).addUnaryRel fn.defined

private theorem subset_both (Δ : Signature) (fn : SpecFn) : Δ.Subset (both Δ fn) :=
  (subset_rel Δ fn).trans (rel_subset_both Δ fn)

theorem relArg_subset_bothArg : (relArg Δ fn x).Subset (bothArg Δ fn x) :=
  Signature.Subset.declVar (rel_subset_both Δ fn) _

theorem funcArg_subset_bothArg : (funcArg Δ fn x).Subset (bothArg Δ fn x) :=
  Signature.Subset.declVar (func_subset_both Δ fn) _

end SpecFn.Sig

/-! ## Name allocation for a head

The two body encodings share one supply, so neither can bind a name the other
needs.
-/

namespace SpecFn
open Verifier.RelationalEncoding

/-- The names a body encoding must not bind: `fn`'s three symbols, the input
variable, and the result variable. -/
def reserved (fn : SpecFn) (x res : TinyML.Var) : List String :=
  fn.names ++ [x, res]

/-- The supply the body encodings run in: the names of `Δ` on top of the
reserved ones. -/
def supply (Δ : Signature) (fn : SpecFn) (x res : TinyML.Var) : NameSupply :=
  { avoid := Δ.allNames ++ reserved fn x res }

theorem reserved_subset_supply {Δ : Signature} {fn : SpecFn} {x res : TinyML.Var} :
    ∀ n ∈ reserved fn x res, n ∈ (supply Δ fn x res).avoid :=
  fun _ h => List.mem_append_right _ h

private theorem supply_covers_bothArgRes (Δ : Signature) (fn : SpecFn) (x res : String) :
    (supply Δ fn x res).Covers (Sig.bothArgRes Δ fn x res) := by
  intro n hn
  by_contra hcontra
  have hnΔ   : n ∉ Δ.allNames  := fun h => hcontra (by simp [supply, h])
  have hnRel : n ≠ fn.relName  := fun h => hcontra (by simp [supply, reserved, names, h])
  have hnFun : n ≠ fn.funcName := fun h => hcontra (by simp [supply, reserved, names, h])
  have hnDef : n ≠ fn.defName  := fun h => hcontra (by simp [supply, reserved, names, h])
  have hnX   : n ≠ x           := fun h => hcontra (by simp [supply, reserved, names, h])
  have hnRes : n ≠ res         := fun h => hcontra (by simp [supply, reserved, names, h])
  have hboth : n ∉ (Sig.both Δ fn).allNames :=
    Signature.not_mem_allNames_addUnaryRel
      (Signature.not_mem_allNames_addUnary
        (Signature.not_mem_allNames_addBinaryRel (b := fn.rel) hnΔ hnRel)
        (by simpa [func] using hnFun))
      (by simpa [defined] using hnDef)
  have hbody := Signature.not_mem_allNames_declVar hboth
    (show n ≠ (⟨x, .value⟩ : Var).name from hnX)
  exact Signature.not_mem_allNames_declVar hbody
    (show n ≠ (⟨res, .value⟩ : Var).name from hnRes) hn

variable {Δ : Signature} {fn : SpecFn} {x res : String}

/-- The supply covers every signature the body encodings run in. -/
private theorem supply_covers_of_subset {Δ' : Signature}
    (hsub : Δ'.Subset (Sig.bothArgRes Δ fn x res)) : (supply Δ fn x res).Covers Δ' :=
  fun n hn => supply_covers_bothArgRes Δ fn x res n (Signature.allNames_subset hsub n hn)

/-- Every name of a signature the body encodings run in is either a name the
encoding starts from or one it must not bind. This is the side condition of
`Expr.WfIn.mono` between two such signatures. -/
theorem names_of_subset_bothArgRes {Δbase Δ' : Signature}
    (hsub : Δ'.Subset (Sig.bothArgRes Δ fn x res)) (hbase : Δ.Subset Δbase) :
    ∀ n ∈ Δ'.allNames, n ∈ Δbase.allNames ∨ n ∈ reserved fn x res :=
  fun n hn => (List.mem_append.mp (supply_covers_of_subset hsub n hn)).imp
    (Signature.allNames_subset hbase n) id

end SpecFn

namespace Verifier.RelationalEncoding

/-- The relational and the func-form body signature declare the same value
variables, so they induce the same encoder environment. -/
theorem VarEnv.ofSignature_funcArg {Δ : Signature} {fn : SpecFn} {x : String} :
    VarEnv.ofSignature (SpecFn.Sig.relArg Δ fn x)
      = VarEnv.ofSignature (SpecFn.Sig.funcArg Δ fn x) :=
  VarEnv.ofSignature_congr rfl

/-! ## Freshness of the head names -/

/-- The head's three symbols and its argument are new for `Δ` and distinct. -/
structure SpecFnFresh (Δ : Signature) (fn : SpecFn) (x : String) : Prop where
  symFresh : ∀ n ∈ fn.names, n ∉ Δ.allNames
  argFresh : x ∉ Δ.allNames ++ fn.names

/-- `SpecFnFresh` with the variable that pins the equation's result, new for
everything before it. -/
structure EquationFresh (Δ : Signature) (fn : SpecFn) (x res : String) : Prop
    extends SpecFnFresh Δ fn x where
  resFresh : res ∉ Δ.allNames ++ fn.names ++ [x]

variable {Δ : Signature} {fn : SpecFn} {x res : String}

namespace SpecFnFresh
open SpecFn.Sig

variable (h : SpecFnFresh Δ fn x)
include h

theorem relFresh : fn.relName ∉ Δ.allNames := h.symFresh _ (by simp [SpecFn.names])
theorem funcFresh : fn.funcName ∉ Δ.allNames := h.symFresh _ (by simp [SpecFn.names])
theorem defFresh : fn.defName ∉ Δ.allNames := h.symFresh _ (by simp [SpecFn.names])

theorem argNe : x ∉ Δ.allNames ∧ x ≠ fn.relName ∧ x ≠ fn.funcName ∧ x ≠ fn.defName := by
  simpa [SpecFn.names, not_or] using h.argFresh

private theorem argFresh_sigRel : x ∉ (rel Δ fn).allNames :=
  Signature.not_mem_allNames_addBinaryRel h.argNe.1 h.argNe.2.1

theorem argFresh_sigFunc : x ∉ (func Δ fn).allNames :=
  Signature.not_mem_allNames_addUnaryRel
    (Signature.not_mem_allNames_addUnary h.argNe.1 h.argNe.2.2.1) h.argNe.2.2.2

theorem argFresh_sigBoth : x ∉ (both Δ fn).allNames :=
  Signature.not_mem_allNames_addUnaryRel
    (Signature.not_mem_allNames_addUnary h.argFresh_sigRel h.argNe.2.2.1) h.argNe.2.2.2

private theorem sigRel_wf (hΔ : Δ.wf) : (rel Δ fn).wf :=
  Signature.wf_addBinaryRel hΔ h.relFresh

private theorem sigFunc_wf (hΔ : Δ.wf) : (func Δ fn).wf :=
  Signature.wf_addUnaryRel (Signature.wf_addUnary hΔ h.funcFresh)
    (Signature.not_mem_allNames_addUnary h.defFresh (SpecFn.defName_ne_funcName fn))

/-- Declaring the head's three symbols on top of a well-formed `Δ` keeps the
signature well-formed: the symbols are new for `Δ` and pairwise distinct. -/
theorem sigBoth_wf (hΔ : Δ.wf) : (both Δ fn).wf :=
  Signature.wf_addUnaryRel
    (Signature.wf_addUnary (h.sigRel_wf hΔ)
      (Signature.not_mem_allNames_addBinaryRel h.funcFresh (SpecFn.funcName_ne_relName fn)))
    (Signature.not_mem_allNames_addUnary
      (Signature.not_mem_allNames_addBinaryRel h.defFresh (SpecFn.defName_ne_relName fn))
      (SpecFn.defName_ne_funcName fn))

theorem sigRelArg_wf (hΔ : Δ.wf) : (relArg Δ fn x).wf :=
  Signature.wf_declVar (h.sigRel_wf hΔ)

theorem sigFuncArg_wf (hΔ : Δ.wf) : (funcArg Δ fn x).wf :=
  Signature.wf_declVar (h.sigFunc_wf hΔ)

theorem sigBothArg_wf (hΔ : Δ.wf) : (bothArg Δ fn x).wf :=
  Signature.wf_declVar (h.sigBoth_wf hΔ)

theorem subset_sigRelArg : Δ.Subset (relArg Δ fn x) :=
  (subset_rel Δ fn).trans (Signature.subset_declVar_of_fresh h.argFresh_sigRel)

theorem subset_sigFuncArg : Δ.Subset (funcArg Δ fn x) :=
  (subset_func Δ fn).trans (Signature.subset_declVar_of_fresh h.argFresh_sigFunc)

private theorem subset_sigBothArg : Δ.Subset (bothArg Δ fn x) :=
  (subset_both Δ fn).trans (Signature.subset_declVar_of_fresh h.argFresh_sigBoth)

/-- The head symbols do not collide with those already present in `Γ`. -/
theorem unused {Γ : FunCtx} (hΓ : Γ.wfIn Δ) : Γ.unused fn := by
  intro g fn' hmem
  exact ⟨fun heq => h.relFresh
      (heq ▸ Signature.mem_allNames_of_binaryRel (hΓ.rel g fn' hmem)),
    fun heq => h.funcFresh
      (heq ▸ Signature.mem_allNames_of_unary (hΓ.func g fn' hmem).1),
    fun heq => h.defFresh
      (heq ▸ Signature.mem_allNames_of_unaryRel (hΓ.func g fn' hmem).2)⟩

end SpecFnFresh

namespace EquationFresh
open SpecFn.Sig

variable (h : EquationFresh Δ fn x res)
include h

private theorem resNe : res ∉ Δ.allNames ∧ res ≠ fn.relName ∧ res ≠ fn.funcName ∧
    res ≠ fn.defName ∧ res ≠ x := by
  simpa [SpecFn.names, not_or, and_assoc] using h.resFresh

theorem resFresh_sigRelArg : res ∉ (relArg Δ fn x).allNames :=
  Signature.not_mem_allNames_declVar
    (Signature.not_mem_allNames_addBinaryRel h.resNe.1 h.resNe.2.1) h.resNe.2.2.2.2

theorem resFresh_sigBothArg : res ∉ (bothArg Δ fn x).allNames :=
  Signature.not_mem_allNames_declVar
    (Signature.not_mem_allNames_addUnaryRel
      (Signature.not_mem_allNames_addUnary
        (Signature.not_mem_allNames_addBinaryRel h.resNe.1 h.resNe.2.1) h.resNe.2.2.1)
      h.resNe.2.2.2.1)
    h.resNe.2.2.2.2

theorem sigBothArg_subset_sigBothArgRes :
    (bothArg Δ fn x).Subset (bothArgRes Δ fn x res) :=
  Signature.subset_declVar_of_fresh h.resFresh_sigBothArg

theorem sigRelArg_subset_sigRelArgRes :
    (relArg Δ fn x).Subset (relArgRes Δ fn x res) :=
  Signature.subset_declVar_of_fresh h.resFresh_sigRelArg

theorem sigRelArgRes_wf (hΔ : Δ.wf) : (relArgRes Δ fn x res).wf :=
  Signature.wf_declVar (h.sigRelArg_wf hΔ)

/-- The body supply covers a body signature, phrased for the `Expr.WfIn` side
conditions that need it. -/
theorem covers_sigRelArg : (SpecFn.supply Δ fn x res).Covers (relArg Δ fn x) :=
  SpecFn.supply_covers_of_subset
    (relArg_subset_bothArg.trans h.sigBothArg_subset_sigBothArgRes)

theorem covers_sigFuncArg : (SpecFn.supply Δ fn x res).Covers (funcArg Δ fn x) :=
  SpecFn.supply_covers_of_subset
    (funcArg_subset_bothArg.trans h.sigBothArg_subset_sigBothArgRes)

end EquationFresh

/-! ## The function context under a fresh head -/

open SpecFn.Sig in
/-- Extending a context that is well-formed in `Δ` with a fresh head keeps every
relation of the tail well-formed in the relational run signature. -/
theorem FunCtx.recursive_relWfIn_relArgRes {Γ : FunCtx} {f : TinyML.Var}
    (hΓ : Γ.relWfIn Δ) (h : EquationFresh Δ fn x res) :
    (Γ.recursive f fn).relWfIn (relArgRes Δ fn x res) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      exact h.sigRelArg_subset_sigRelArgRes.binaryRel _
        ((Signature.subset_declVar_of_fresh h.argFresh_sigRel).binaryRel _ (List.Mem.head _))
  | tail _ htail =>
      exact (h.subset_sigRelArg.trans h.sigRelArg_subset_sigRelArgRes).binaryRel _
        (hΓ g fn' htail)

/-- The head's own func-form symbols live in every signature that declares them,
and the tail's survive by monotonicity. -/
private theorem FunCtx.recursive_funcWfIn_declVar {Γ : FunCtx} {Δbase : Signature}
    {f : TinyML.Var}
    (hΓ : Γ.funcWfIn Δ) (hsub : Δ.Subset (Δbase.declVar ⟨x, .value⟩))
    (hfresh : x ∉ Δbase.allNames)
    (hfunc : fn.func ∈ Δbase.unary) (hdef : fn.defined ∈ Δbase.unaryRel) :
    (Γ.recursive f fn).funcWfIn (Δbase.declVar ⟨x, .value⟩) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      exact ⟨(Signature.subset_declVar_of_fresh hfresh).unary _ hfunc,
        (Signature.subset_declVar_of_fresh hfresh).unaryRel _ hdef⟩
  | tail _ htail => exact FunCtx.funcWfIn_mono hΓ hsub g fn' htail

theorem FunCtx.recursive_funcWfIn_bothArg {Γ : FunCtx} {f : TinyML.Var}
    (hΓ : Γ.funcWfIn Δ) (h : EquationFresh Δ fn x res) :
    (Γ.recursive f fn).funcWfIn (SpecFn.Sig.bothArg Δ fn x) :=
  FunCtx.recursive_funcWfIn_declVar hΓ h.subset_sigBothArg h.argFresh_sigBoth
    (List.Mem.head _) (List.Mem.head _)

theorem FunCtx.recursive_funcWfIn_funcArg {Γ : FunCtx} {f : TinyML.Var}
    (hΓ : Γ.funcWfIn Δ) (h : EquationFresh Δ fn x res) :
    (Γ.recursive f fn).funcWfIn (SpecFn.Sig.funcArg Δ fn x) :=
  FunCtx.recursive_funcWfIn_declVar hΓ h.subset_sigFuncArg h.argFresh_sigFunc
    (List.Mem.head _) (List.Mem.head _)

end Verifier.RelationalEncoding
