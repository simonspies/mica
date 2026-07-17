-- SUMMARY: Data model for verifier intrinsics, with generic theorems characterizing the effect of registry setup.
import Mica.TinyML.OpSem
import Mica.SeparationLogic.Wp
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.FOL.Formulas

open Iris Iris.BI

/-! # Intrinsic framework

A `Registry` is a list of intrinsics; the verifier derives from it the two
total contexts that lower layers consume: `TinyML.PrimCtx` (OpSem) and
`WpCtx` (separation logic). Each entry contributes one FOL symbol (or
none), a list of FOL axioms, and the runtime/wp/spec facets of a built-in
function.

Theorems in this module are proved for *every possible registry*: induction
on the list, with a per-intrinsic step that case-analyzes on arity and on
whether a FOL symbol is present. No theorem mentions any particular
intrinsic by name.
-/

/-! ## Arity and FOL symbols -/

/-- Arity of an intrinsic. Extend as needed. -/
inductive Arity
  | zero
  | one
  | two
  | three
  deriving DecidableEq, Repr

/-- The number of arguments of an `Arity`. -/
def Arity.toNat : Arity → Nat
  | .zero => 0
  | .one  => 1
  | .two  => 2
  | .three => 3

/-- The shape of a tuple of `n` elements of type `α` indexed by an `Arity`. -/
abbrev Arity.tup : Arity → Type → Type
  | .zero, _ => Unit
  | .one,  α => α
  | .two,  α => α × α
  | .three, α => α × α × α

/-- A FOL symbol attached to an intrinsic: a function symbol of the given
    arity at the value sort, together with its standard interpretation. -/
structure FOL.Symbol (n : Arity) where
  name   : String
  interp : Arity.tup n (Srt.value).denote → (Srt.value).denote

/-! ## Extending signatures and environments with an FOL symbol -/

/-- Extend a signature with the FOL symbol from `s` (if any). -/
def Signature.extendWithSym : ∀ {n : Arity}, Signature → Option (FOL.Symbol n) → Signature
  | _,     Δ, none        => Δ
  | .zero, Δ, some s      => Δ.addConst ⟨s.name, .value⟩
  | .one,  Δ, some s      => Δ.addUnary ⟨s.name, .value, .value⟩
  | .two,  Δ, some s      => Δ.addBinary ⟨s.name, .value, .value, .value⟩
  | .three, Δ, some s      => Δ.addTernary ⟨s.name, .value, .value, .value, .value⟩

/-- Extending a signature is a subset extension. -/
theorem Signature.subset_extendWithSym {n : Arity} (Δ : Signature)
    (s : Option (FOL.Symbol n)) : Δ.Subset (Δ.extendWithSym s) := by
  cases s with
  | none => exact Signature.Subset.refl _
  | some s' =>
    cases n with
    | zero => exact Signature.Subset.subset_addConst _ _
    | one  => exact Signature.Subset.subset_addUnary _ _
    | two  => exact Signature.Subset.subset_addBinary _ _
    | three => exact Signature.Subset.subset_addTernary _ _

@[simp] theorem Signature.extendWithSym_vars {n : Arity} (Δ : Signature)
    (s : Option (FOL.Symbol n)) : (Δ.extendWithSym s).vars = Δ.vars := by
  cases s with
  | none => rfl
  | some _ =>
    cases n <;> rfl

/-- `extendWithSym` is monotone in the base signature. -/
theorem Signature.extendWithSym_mono {n : Arity} {Δ Δ' : Signature}
    (h : Δ.Subset Δ') (s : Option (FOL.Symbol n)) :
    (Δ.extendWithSym s).Subset (Δ'.extendWithSym s) := by
  cases s with
  | none => exact h
  | some s' =>
    cases n with
    | zero =>
      refine ⟨fun _ hx => h.vars _ hx,
              fun c hc => ?_,
              fun _ hu => h.unary _ hu,
              fun _ hb => h.binary _ hb,
              fun _ ht => h.ternary _ ht,
              fun _ hu => h.unaryRel _ hu,
              fun _ hb => h.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addConst, List.mem_cons] at hc ⊢
      exact hc.imp_right (h.consts _)
    | one =>
      refine ⟨fun _ hx => h.vars _ hx,
              fun _ hc => h.consts _ hc,
              fun u hu => ?_,
              fun _ hb => h.binary _ hb,
              fun _ ht => h.ternary _ ht,
              fun _ hu => h.unaryRel _ hu,
              fun _ hb => h.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addUnary, List.mem_cons] at hu ⊢
      exact hu.imp_right (h.unary _)
    | two =>
      refine ⟨fun _ hx => h.vars _ hx,
              fun _ hc => h.consts _ hc,
              fun _ hu => h.unary _ hu,
              fun b hb => ?_,
              fun _ ht => h.ternary _ ht,
              fun _ hu => h.unaryRel _ hu,
              fun _ hb => h.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addBinary, List.mem_cons] at hb ⊢
      exact hb.imp_right (h.binary _)
    | three =>
      refine ⟨fun _ hx => h.vars _ hx,
              fun _ hc => h.consts _ hc,
              fun _ hu => h.unary _ hu,
              fun _ hb => h.binary _ hb,
              fun t ht => ?_,
              fun _ hu => h.unaryRel _ hu,
              fun _ hb => h.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addTernary, List.mem_cons] at ht ⊢
      exact ht.imp_right (h.ternary _)

/-- If the base signature and the symbol being added are already contained in
    a target signature, extending the base with that symbol stays contained in
    the target. -/
theorem Signature.extendWithSym_subset_of_subset_of_sym {n : Arity} {Δ Δ' : Signature}
    {s : Option (FOL.Symbol n)}
    (hbase : Δ.Subset Δ')
    (hsym : (Signature.empty.extendWithSym s).Subset Δ') :
    (Δ.extendWithSym s).Subset Δ' := by
  cases s with
  | none => exact hbase
  | some s' =>
    cases n with
    | zero =>
      refine ⟨fun _ hx => hbase.vars _ hx,
              fun c hc => ?_,
              fun _ hu => hbase.unary _ hu,
              fun _ hb => hbase.binary _ hb,
              fun _ ht => hbase.ternary _ ht,
              fun _ hu => hbase.unaryRel _ hu,
              fun _ hb => hbase.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addConst, List.mem_cons] at hc
      cases hc with
      | inl hc =>
        subst hc
        exact hsym.consts _ (by simp [Signature.extendWithSym, Signature.addConst])
      | inr hc => exact hbase.consts _ hc
    | one =>
      refine ⟨fun _ hx => hbase.vars _ hx,
              fun _ hc => hbase.consts _ hc,
              fun u hu => ?_,
              fun _ hb => hbase.binary _ hb,
              fun _ ht => hbase.ternary _ ht,
              fun _ hu => hbase.unaryRel _ hu,
              fun _ hb => hbase.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addUnary, List.mem_cons] at hu
      cases hu with
      | inl hu =>
        subst hu
        exact hsym.unary _ (by simp [Signature.extendWithSym, Signature.addUnary])
      | inr hu => exact hbase.unary _ hu
    | two =>
      refine ⟨fun _ hx => hbase.vars _ hx,
              fun _ hc => hbase.consts _ hc,
              fun _ hu => hbase.unary _ hu,
              fun b hb => ?_,
              fun _ ht => hbase.ternary _ ht,
              fun _ hu => hbase.unaryRel _ hu,
              fun _ hb => hbase.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addBinary, List.mem_cons] at hb
      cases hb with
      | inl hb =>
        subst hb
        exact hsym.binary _ (by simp [Signature.extendWithSym, Signature.addBinary])
      | inr hb => exact hbase.binary _ hb
    | three =>
      refine ⟨fun _ hx => hbase.vars _ hx,
              fun _ hc => hbase.consts _ hc,
              fun _ hu => hbase.unary _ hu,
              fun _ hb => hbase.binary _ hb,
              fun t ht => ?_,
              fun _ hu => hbase.unaryRel _ hu,
              fun _ hb => hbase.binaryRel _ hb⟩
      simp only [Signature.extendWithSym, Signature.addTernary, List.mem_cons] at ht
      cases ht with
      | inl ht =>
        subst ht
        exact hsym.ternary _ (by simp [Signature.extendWithSym, Signature.addTernary])
      | inr ht => exact hbase.ternary _ ht

/-- Extend an environment with the standard interpretation of `s` (if any). -/
def Env.extendWithSym : ∀ {n : Arity}, Env → Option (FOL.Symbol n) → Env
  | _,     ρ, none        => ρ
  | .zero, ρ, some s      => ρ.updateConst .value s.name (s.interp ())
  | .one,  ρ, some s      => ρ.updateUnary .value .value s.name s.interp
  | .two,  ρ, some s      => ρ.updateBinary .value .value .value s.name
                                            (fun a b => s.interp (a, b))
  | .three, ρ, some s      => ρ.updateTernary .value .value .value .value s.name
                                            (fun a b c => s.interp (a, b, c))

/-- `ρ.respects s` says `ρ`'s entry at the value-sort/arity slot of `s` is
    the standard interpretation of `s`. Vacuously true for `none`. -/
def Env.respects : ∀ {n : Arity}, Env → Option (FOL.Symbol n) → Prop
  | _,     _, none        => True
  | .zero, ρ, some s      => ρ.lookupConst .value s.name = s.interp ()
  | .one,  ρ, some s      => ρ.unary .value .value s.name = s.interp
  | .two,  ρ, some s      => ρ.binary .value .value .value s.name
                                = (fun a b => s.interp (a, b))
  | .three, ρ, some s      => ρ.ternary .value .value .value .value s.name
                                = (fun a b c => s.interp (a, b, c))

/-- The post-extension environment respects the symbol it was extended with. -/
theorem Env.respects_extendWithSym {n : Arity} (ρ : Env) (s : Option (FOL.Symbol n)) :
    (ρ.extendWithSym s).respects s := by
  cases s with
  | none => trivial
  | some s' =>
    cases n with
    | zero => simp [Env.respects, Env.extendWithSym, Env.lookupConst, Env.updateConst]
    | one  => simp [Env.respects, Env.extendWithSym, Env.updateUnary]
    | two  => simp [Env.respects, Env.extendWithSym, Env.updateBinary]
    | three => simp [Env.respects, Env.extendWithSym, Env.updateTernary]

/-- Respect for a symbol is preserved by moving to an environment that agrees
    on a signature containing that symbol. -/
theorem Env.respects_of_agreeOn_extendWithSym {n : Arity} {Δ : Signature}
    {ρ ρ' : Env} {s : Option (FOL.Symbol n)}
    (hrespects : ρ.respects s)
    (hsub : (Signature.empty.extendWithSym s).Subset Δ)
    (hagree : Env.agreeOn Δ ρ ρ') :
    ρ'.respects s := by
  cases s with
  | none => trivial
  | some s' =>
    cases n with
    | zero =>
      have hmem : ⟨s'.name, .value⟩ ∈ Δ.consts :=
        hsub.consts _ (by simp [Signature.extendWithSym, Signature.empty, Signature.addConst])
      have heq := hagree.2.1 ⟨s'.name, .value⟩ hmem
      simpa [Env.respects, Env.lookupConst] using heq.symm.trans hrespects
    | one =>
      have hmem : ⟨s'.name, .value, .value⟩ ∈ Δ.unary :=
        hsub.unary _ (by simp [Signature.extendWithSym, Signature.empty, Signature.addUnary])
      have heq := hagree.2.2.1 ⟨s'.name, .value, .value⟩ hmem
      simpa [Env.respects] using heq.symm.trans hrespects
    | two =>
      have hmem : ⟨s'.name, .value, .value, .value⟩ ∈ Δ.binary :=
        hsub.binary _ (by simp [Signature.extendWithSym, Signature.empty, Signature.addBinary])
      have heq := hagree.2.2.2.1 ⟨s'.name, .value, .value, .value⟩ hmem
      simpa [Env.respects] using heq.symm.trans hrespects
    | three =>
      have hmem : ⟨s'.name, .value, .value, .value, .value⟩ ∈ Δ.ternary :=
        hsub.ternary _ (by simp [Signature.extendWithSym, Signature.empty, Signature.addTernary])
      have heq := hagree.2.2.2.2.1 ⟨s'.name, .value, .value, .value, .value⟩ hmem
      simpa [Env.respects] using heq.symm.trans hrespects

/-! ## The intrinsic structure -/

namespace Verifier

/-- A single intrinsic: name, typing, runtime, separation-logic, and SMT
    facets. The `name` field is the payload of the `Val.prim` constructor;
    surface-level qualified paths are resolved to this string. -/
structure Intrinsic where
  arity    : Arity
  name     : String
  /-- Optional surface module path used by concrete stdlibs to build frontend resolvers. -/
  path     : Option (String × List String)
  reduce   : Arity.tup arity Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop
  wp       : Arity.tup arity Runtime.Val → (Runtime.Val → iProp) → iProp
  /-- The intrinsic's specification, the single source of its argument names/
      types, return type, and predicate transformer. Argument and return types
      may contain type variables (a *scheme*); a polymorphic intrinsic is a
      family of functions with the same implementation, instantiated per use
      site via `Spec.instantiate`. -/
  spec     : Spec
  /-- The typing function: given the inferred argument types of a use site,
      compute the type-variable instantiation (or reject with a message). It is
      untrusted — the elaborator re-checks arguments against the instantiated
      scheme and the semantic obligations hold for every substitution. -/
  typing   : TinyML.TypeEnv → List TinyML.Typ → Except String (List (TinyML.TyVar × TinyML.Typ))
  folSym   : Option (FOL.Symbol arity)
  axioms   : List Axiom

/-- A registry is a list of intrinsics. -/
abbrev Registry := List Intrinsic

/-- Embed a pure (heap-independent, heap-preserving) relation as a heap-aware
    `reduce` field. -/
def Reduce.pure {α : Type} (rel : α → Runtime.Val → Prop) :
    α → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop :=
  fun a μ v μ' => rel a v ∧ μ' = μ

/-- The typing function of a monomorphic intrinsic: no type variables to
    solve, only the argument count to check. -/
def monoTyping (arity : Arity) :
    TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)) :=
  fun _ tys =>
    if tys.length = arity.toNat then .ok []
    else .error s!"expected {arity.toNat} arguments, got {tys.length}"

namespace Intrinsic

/-- Extending an environment with an intrinsic's fresh FOL symbol preserves
    agreement on the prefix signature. -/
theorem agreeOn_extend_fresh (i : Intrinsic) {Δ : Signature} (ρ : Env)
    (hfresh : match i.folSym with | none => True | some sym => sym.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.extendWithSym i.folSym) := by
  cases i with
  | mk arity name path reduce wp spec typing folSym axioms =>
    cases arity with
    | zero =>
      cases folSym with
      | none => exact Env.agreeOn_refl
      | some s =>
        simpa [Env.extendWithSym] using
          (Env.agreeOn_update_fresh_const (ρ := ρ) (c := ⟨s.name, .value⟩)
            (u := s.interp ()) (Δ := Δ) hfresh)
    | one =>
      cases folSym with
      | none => exact Env.agreeOn_refl
      | some s =>
        simpa [Env.extendWithSym] using
          (Env.agreeOn_update_fresh_unary (ρ := ρ) (u := ⟨s.name, .value, .value⟩)
            (f := s.interp) (Δ := Δ) hfresh)
    | two =>
      cases folSym with
      | none => exact Env.agreeOn_refl
      | some s =>
        simpa [Env.extendWithSym] using
          (Env.agreeOn_update_fresh_binary (ρ := ρ)
            (b := ⟨s.name, .value, .value, .value⟩)
            (f := fun a b => s.interp (a, b)) (Δ := Δ) hfresh)
    | three =>
      cases folSym with
      | none => exact Env.agreeOn_refl
      | some s =>
        simpa [Env.extendWithSym] using
          (Env.agreeOn_update_fresh_ternary (ρ := ρ)
            (t := ⟨s.name, .value, .value, .value, .value⟩)
            (f := fun a b c => s.interp (a, b, c)) (Δ := Δ) hfresh)

/-- The intrinsic's argument types, in left-to-right order. Read off the spec. -/
def argTysList (i : Intrinsic) : List TinyML.Typ :=
  i.spec.args.map Prod.snd

/-- The intrinsic's result type. Read off the spec. -/
def resultTy (i : Intrinsic) : TinyML.Typ :=
  i.spec.retTy

/-- The intrinsic's full arrow (scheme) type. -/
def arrowType (i : Intrinsic) : TinyML.Typ :=
  i.argTysList.foldr .arrow i.resultTy

/-- The typing face of an intrinsic, consumed by the elaborator. -/
def sig (i : Intrinsic) : Typed.PrimSig :=
  ⟨i.arrowType, i.typing⟩

/-- Adapter from the list-shaped argument call (used by OpSem and `wp`) to
    the arity-shaped representation. Out-of-shape calls produce the empty
    relation. -/
def toReduce (i : Intrinsic) :
    List Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop :=
  fun vs μ v μ' =>
    match i.arity, i.reduce, vs with
    | .zero, r, []          => r () μ v μ'
    | .one,  r, [a]         => r a μ v μ'
    | .two,  r, [a, b]      => r (a, b) μ v μ'
    | .three, r, [a, b, c]  => r (a, b, c) μ v μ'
    | _,     _, _           => False

/-- Unfolding lemma for `toReduce` at arity-two, two args. The intrinsic's
    `arity` field is destructured explicitly so that the dependent `reduce`
    field's match reduces. -/
theorem toReduce_two_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .two Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .two Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .two)) (axioms : List Axiom)
    (a b v : Runtime.Val) (μ μ' : TinyML.Heap) :
    (Intrinsic.mk .two name path reduce wp spec typing folSym axioms).toReduce [a, b] μ v μ'
      = reduce (a, b) μ v μ' := rfl

/-- Unfolding lemma for `toReduce` at arity-three, three args. -/
theorem toReduce_three_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .three Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .three Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .three)) (axioms : List Axiom)
    (a b c v : Runtime.Val) (μ μ' : TinyML.Heap) :
    (Intrinsic.mk .three name path reduce wp spec typing folSym axioms).toReduce [a, b, c] μ v μ'
      = reduce (a, b, c) μ v μ' := rfl

/-- Unfolding lemma for `toReduce` at arity-one, one arg. -/
theorem toReduce_one_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .one Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .one Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .one)) (axioms : List Axiom)
    (a v : Runtime.Val) (μ μ' : TinyML.Heap) :
    (Intrinsic.mk .one name path reduce wp spec typing folSym axioms).toReduce [a] μ v μ'
      = reduce a μ v μ' := rfl

/-- Unfolding lemma for `toReduce` at arity-zero, no args. -/
theorem toReduce_zero_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .zero Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .zero Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .zero)) (axioms : List Axiom)
    (v : Runtime.Val) (μ μ' : TinyML.Heap) :
    (Intrinsic.mk .zero name path reduce wp spec typing folSym axioms).toReduce [] μ v μ'
      = reduce () μ v μ' := rfl

/-- Adapter from the list-shaped argument call to the arity-shaped `wp`
    field. Out-of-shape calls produce `False`. -/
def toWp (i : Intrinsic) :
    List Runtime.Val → (Runtime.Val → iProp) → iProp :=
  fun vs Q =>
    match i.arity, i.wp, vs with
    | .zero, w, []          => w () Q
    | .one,  w, [a]         => w a Q
    | .two,  w, [a, b]      => w (a, b) Q
    | .three, w, [a, b, c]  => w (a, b, c) Q
    | _,     _, _           => iprop(False)

/-- Unfolding lemma for `toWp` at arity-two, two args. The intrinsic's
    `arity` field is destructured explicitly so that the dependent `wp`
    field's match reduces. -/
theorem toWp_two_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .two Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .two Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .two)) (axioms : List Axiom)
    (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    (Intrinsic.mk .two name path reduce wp spec typing folSym axioms).toWp [a, b] Q
      = wp (a, b) Q := rfl

/-- Unfolding lemma for `toWp` at arity-three, three args. -/
theorem toWp_three_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .three Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .three Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .three)) (axioms : List Axiom)
    (a b c : Runtime.Val) (Q : Runtime.Val → iProp) :
    (Intrinsic.mk .three name path reduce wp spec typing folSym axioms).toWp [a, b, c] Q
      = wp (a, b, c) Q := rfl

/-- Unfolding lemma for `toWp` at arity-one, one arg. -/
theorem toWp_one_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .one Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .one Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .one)) (axioms : List Axiom)
    (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    (Intrinsic.mk .one name path reduce wp spec typing folSym axioms).toWp [a] Q
      = wp a Q := rfl

/-- Unfolding lemma for `toWp` at arity-zero, no args. -/
theorem toWp_zero_of_arity (name : String)
    (path : Option (String × List String))
    (reduce : Arity.tup .zero Runtime.Val → TinyML.Heap → Runtime.Val → TinyML.Heap → Prop)
    (wp : Arity.tup .zero Runtime.Val → (Runtime.Val → iProp) → iProp)
    (spec : Spec)
    (typing : TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)))
    (folSym : Option (FOL.Symbol .zero)) (axioms : List Axiom)
    (Q : Runtime.Val → iProp) :
    (Intrinsic.mk .zero name path reduce wp spec typing folSym axioms).toWp [] Q
      = wp () Q := rfl

/-- Fold a registry fragment's FOL symbols into a starting signature. The
    general fold underlying `sigOf` and the registry-derived signatures. -/
def foldSig (Δ : Signature) : List Intrinsic → Signature
  | []        => Δ
  | i :: rest => foldSig (Δ.extendWithSym i.folSym) rest

/-- The FOL signature intrinsic axioms are expressed in: the empty signature
    extended with the FOL symbols of a registry fragment. The fragment may
    include the intrinsic whose axioms are being checked. -/
def sigOf (fragment : List Intrinsic) : Signature :=
  foldSig Signature.empty fragment

/-! ### Spec→wp bridge

`compile` routes a `.prim n args` call through `Spec.call` against the
intrinsic's spec. The resulting `PredTrans.apply` obligation must be bridged
to the `i.toWp` iProp consumed by the registry-derived `Registry.wp_prim`. The
bridge is one of the per-intrinsic obligations captured by `IntrinsicSound`
below. The aggregate over the registry is the def `Registry.Sound`. -/

/-- Argument list for the spec view: the spec's own argument names paired with
    their types. -/
def specArgs (i : Intrinsic) : List (String × TinyML.Typ) :=
  i.spec.args

end Intrinsic

/-- Per-intrinsic soundness obligation, discharged together for each intrinsic
    and aggregated over a registry by `Registry.Sound`. It bundles the two
    spec→wp bridge facts (`specWf`, `bridge`), the opsem↔wp fact (`wp_sound`),
    and the two axiom facts (`axiomWf`, `proof`).

    `specWf`/`bridge` are independent of `fragment`: from a `PredTrans.apply`
    obligation against `i.spec` (the shape produced by `Spec.call_correct`) and
    the typing of the arguments, `bridge` derives `i.toWp` — the iProp
    `Registry.wp_prim` demands of the registry-derived context. Both take the
    symbol's declaration / interpretation as an explicit side condition: `i.spec`
    may mention `i.folSym`, so it is only well-formed in a signature declaring
    that symbol, and the bridge only holds when the environment interprets the
    symbol by its standard interpretation. These side conditions are discharged
    by the caller from the registry-derived signature/environment.

    `bridge` is a family indexed by the type-variable substitution `σ`: it is
    stated at the *instantiated* spec `i.spec.instantiate σ`, for every `σ`.

    `axiomWf`/`proof` are stated against the dependency `fragment`: each axiom is
    well-formed in the signature supplied by the fragment, and is satisfied by
    every environment that respects every FOL symbol in the fragment. -/
class IntrinsicSound (fragment : outParam (List Intrinsic)) (i : Intrinsic) : Prop where
  specWf :
    ∀ (Δ : Signature), (Signature.empty.extendWithSym i.folSym).Subset Δ → Δ.wf →
      PredTrans.wfIn (Δ.declVars (Spec.argVars i.specArgs)) i.spec.pred
  bridge :
    ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ) (Θ : TinyML.TypeEnv)
      (vs : List Runtime.Val) (ρ : VerifM.Env) (Φ : Runtime.Val → iProp),
    ρ.env.respects i.folSym →
    TinyML.ValsHaveTypes Θ vs ((i.spec.instantiate σ).args.map Prod.snd) ∗
      PredTrans.apply Θ (fun r => TinyML.ValHasType Θ r (i.spec.instantiate σ).retTy -∗ Φ r)
        (i.spec.instantiate σ).pred
        (Spec.argsEnv ρ (i.spec.instantiate σ).args vs) ⊢ i.toWp vs Φ
  wp_sound :
    ∀ [MicaGS HasLC.hasLC Sig] (ctx : TinyML.PrimCtx),
      (∀ vs μ v μ', ctx i.name vs μ v μ' ↔ i.toReduce vs μ v μ') →
      ∀ (vs : List Runtime.Val) (Φ : Runtime.Val → iProp),
        i.toWp vs Φ ⊢ wp ctx (.app (.val (.prim i.name)) (vs.map Runtime.Expr.val)) Φ
  axiomWf : ∀ {Δ : Signature}, (Intrinsic.sigOf fragment).Subset Δ → Δ.wf →
            ∀ a ∈ i.axioms, Formula.wfIn a.formula Δ
  proof : ∀ ρ : Env,
            (∀ d ∈ fragment, ρ.respects d.folSym) →
            ∀ a ∈ i.axioms, Formula.eval ρ a.formula

namespace Registry

/-- Resolve a name to its intrinsic: the first registry entry whose `name`
    matches. The single lookup shared by the operational-semantics and `wp`
    contexts, so the two agree on which entry a name selects. -/
def lookup? (R : Registry) (n : String) : Option Intrinsic :=
  R.find? (·.name == n)

theorem mem_of_lookup? {R : Registry} {n : String} {i : Intrinsic}
    (h : R.lookup? n = some i) : i ∈ R :=
  List.mem_of_find?_eq_some h

/-- A looked-up intrinsic carries the name it was looked up by. -/
theorem lookup?_name {R : Registry} {n : String} {i : Intrinsic}
    (h : R.lookup? n = some i) : i.name = n := by
  have := List.find?_eq_some_iff_append.mp h
  exact eq_of_beq this.1

/-- The typing faces of all registered intrinsics, keyed by name; handed to the
    elaborator. -/
def sigs (R : Registry) : String → Option Typed.PrimSig :=
  fun n => (R.lookup? n).map Intrinsic.sig

/-- Build the operational-semantics context from a registry. -/
def primCtx (R : Registry) : TinyML.PrimCtx :=
  fun n vs μ v μ' =>
    match R.lookup? n with
    | some i => i.toReduce vs μ v μ'
    | none   => False

/-- Build the `wp` context from a registry. Names not in `R` map to the
    `False` iProp. -/
def wpCtx (R : Registry) : WpCtx :=
  fun n vs Q =>
    match R.lookup? n with
    | some i => i.toWp vs Q
    | none   => iprop(False)

/-- The aggregated FOL environment: each intrinsic's FOL symbol receives
    its standard interpretation. -/
def stdEnv (R : Registry) : Env :=
  R.foldl (fun ρ i => ρ.extendWithSym i.folSym) Env.empty

/-- Extend an arbitrary base environment with a registry. -/
def foldEnv (ρ : Env) (R : Registry) : Env :=
  R.foldl (fun ρ i => ρ.extendWithSym i.folSym) ρ

/-- A target signature contains every FOL symbol contributed by a registry. -/
def symSubset (R : Registry) (Δ : Signature) : Prop :=
  ∀ i ∈ R, (Signature.empty.extendWithSym i.folSym).Subset Δ

/-- An environment gives every registry FOL symbol its standard interpretation. -/
def symAgree (R : Registry) (ρ : Env) : Prop :=
  ∀ i ∈ R, ρ.respects i.folSym

/-- Folding intrinsic symbols into a larger starting signature gives a larger
    final signature. -/
theorem foldSig_mono (R : Registry) {Δ Δ' : Signature} (h : Δ.Subset Δ') :
    (Intrinsic.foldSig Δ R).Subset (Intrinsic.foldSig Δ' R) := by
  induction R generalizing Δ Δ' with
  | nil => exact h
  | cons i rest ih =>
    exact ih (Signature.extendWithSym_mono h _)

/-- Folding intrinsic symbols preserves the starting signature as a subset. -/
theorem subset_foldSig (R : Registry) (Δ : Signature) :
    Δ.Subset (Intrinsic.foldSig Δ R) := by
  induction R generalizing Δ with
  | nil => exact Signature.Subset.refl _
  | cons i rest ih =>
    exact (Signature.subset_extendWithSym Δ i.folSym).trans (ih _)

/-- The signature for a registry contains the FOL symbol of every member,
    independent of where that member appears in the list. -/
theorem extendWithSym_subset_sigOf_of_mem {R : Registry} {i : Intrinsic}
    (hi : i ∈ R) :
    (Signature.empty.extendWithSym i.folSym).Subset (Intrinsic.sigOf R) := by
  induction R with
  | nil => cases hi
  | cons j rest ih =>
    cases hi with
    | head =>
      exact subset_foldSig rest (Signature.empty.extendWithSym i.folSym)
    | tail _ hmem =>
      exact (ih hmem).trans
        (foldSig_mono rest (Signature.empty_subset (Signature.empty.extendWithSym j.folSym)))

/-- Registry-fragment signatures are monotone with respect to membership
    inclusion, not list order. -/
theorem sigOf_subset_of_subset {deps R : Registry} (hsub : deps ⊆ R) :
    (Intrinsic.sigOf deps).Subset (Intrinsic.sigOf R) := by
  suffices h :
      ∀ (todo : Registry) (Δ : Signature),
        Δ.Subset (Intrinsic.sigOf R) →
        (∀ i ∈ todo, i ∈ R) →
        (Intrinsic.foldSig Δ todo).Subset (Intrinsic.sigOf R) by
    exact h deps Signature.empty (Signature.empty_subset _) hsub
  intro todo
  induction todo with
  | nil =>
    intro Δ hΔ _
    exact hΔ
  | cons i rest ih =>
    intro Δ hΔ hmem
    apply ih
    · exact Signature.extendWithSym_subset_of_subset_of_sym hΔ
        (extendWithSym_subset_sigOf_of_mem (hmem i (by simp)))
    · intro d hd
      exact hmem d (List.mem_cons_of_mem _ hd)

/-- Registry well-formedness relative to an existing signature: each FOL
    symbol is fresh for the prefix signature before it is added. -/
def WfFrom : Signature → Registry → Prop
  | _, [] => True
  | Δ, i :: rest =>
      (match i.folSym with | none => True | some sym => sym.name ∉ Δ.allNames) ∧
      WfFrom (Δ.extendWithSym i.folSym) rest

abbrev Wf (R : Registry) : Prop := WfFrom Signature.empty R

/-- Every intrinsic in `todo` is sound against the full registry fragment `R`. -/
def SoundIn (R : Registry) : Registry → Prop
  | [] => True
  | i :: rest => IntrinsicSound R i ∧ SoundIn R rest

abbrev Sound (R : Registry) : Prop := SoundIn R R

/-- Recover a member's soundness obligation from the aggregate, stated against
    the full fragment `R`. -/
theorem SoundIn.get {R todo : Registry} (h : SoundIn R todo) :
    ∀ i ∈ todo, IntrinsicSound R i := by
  induction todo with
  | nil => intro _ hi; cases hi
  | cons j rest ih =>
    rcases h with ⟨hj, hrest⟩
    intro i hi
    cases hi with
    | head => exact hj
    | tail _ hmem => exact ih hrest i hmem

/-- Recover a member's soundness obligation from a sound registry. -/
theorem Sound.get {R : Registry} (h : Sound R) {i : Intrinsic} (hi : i ∈ R) :
    IntrinsicSound R i := SoundIn.get h i hi

/-- The wp rule for primitive calls: a sound registry's spec context (`wpCtx`)
    entails the weakest precondition at its operational context (`primCtx`).
    Dispatches the per-intrinsic `IntrinsicSound.wp_sound` obligation at the
    looked-up entry; `primCtx` agrees with that entry's `toReduce` at its name
    by construction. -/
theorem wp_prim [MicaGS HasLC.hasLC Sig] (R : Registry) (hSound : R.Sound) {n : String}
    {vs : List Runtime.Val} {Q : Runtime.Val → iProp} :
    R.wpCtx n vs Q ⊢ wp R.primCtx (.app (.val (.prim n)) (vs.map Runtime.Expr.val)) Q := by
  unfold wpCtx
  cases h : R.lookup? n with
  | none =>
    exact false_elim
  | some i =>
    obtain rfl := lookup?_name h
    refine (hSound.get (mem_of_lookup? h)).wp_sound R.primCtx (fun vs μ v μ' => ?_) vs Q
    simp [primCtx, h]

theorem stdEnv_eq_foldEnv (R : Registry) : stdEnv R = foldEnv Env.empty R := rfl

/-- Folding a well-formed registry into an environment preserves agreement
    on the starting signature. -/
theorem foldEnv_agreeOn_base {Δ : Signature} {R : Registry} (ρ : Env)
    (hWf : WfFrom Δ R) :
    Env.agreeOn Δ ρ (foldEnv ρ R) := by
  induction R generalizing Δ ρ with
  | nil =>
    exact Env.agreeOn_refl
  | cons i rest ih =>
    rcases hWf with ⟨hfresh, hrest⟩
    simp only [foldEnv, List.foldl_cons]
    have hstep : Env.agreeOn Δ ρ (ρ.extendWithSym i.folSym) :=
      i.agreeOn_extend_fresh ρ hfresh
    have htail : Env.agreeOn (Δ.extendWithSym i.folSym)
        (ρ.extendWithSym i.folSym) (foldEnv (ρ.extendWithSym i.folSym) rest) :=
      ih (ρ := ρ.extendWithSym i.folSym) hrest
    exact Env.agreeOn_trans hstep
      (Env.agreeOn_mono (Signature.subset_extendWithSym Δ i.folSym) htail)

/-- Folding a well-formed registry makes the final environment respect every
    symbol introduced by the registry. -/
theorem foldEnv_respects {Δ : Signature} {R : Registry} (ρ : Env)
    (hWf : WfFrom Δ R) :
    ∀ i ∈ R, (foldEnv ρ R).respects i.folSym := by
  induction R generalizing Δ ρ with
  | nil =>
    intro i hi; cases hi
  | cons i rest ih =>
    rcases hWf with ⟨hfresh, hrest⟩
    intro j hj
    simp only [foldEnv, List.foldl_cons]
    cases hj with
    | head =>
      have hrespects : (ρ.extendWithSym i.folSym).respects i.folSym :=
        Env.respects_extendWithSym ρ i.folSym
      refine Env.respects_of_agreeOn_extendWithSym (Δ := Δ.extendWithSym i.folSym) hrespects ?_ ?_
      · exact Signature.extendWithSym_mono (Signature.empty_subset _) _
      · exact foldEnv_agreeOn_base (ρ.extendWithSym i.folSym) hrest
    | tail _ hjrest =>
      exact ih (ρ := ρ.extendWithSym i.folSym) hrest j hjrest

theorem stdEnv_respects {R : Registry} (hWf : Wf R) :
    ∀ i ∈ R, (stdEnv R).respects i.folSym := by
  simpa [stdEnv_eq_foldEnv] using foldEnv_respects (Δ := Signature.empty) Env.empty hWf

/-- Generic registry axiom satisfaction: if the registry is sound by subset,
    and the chosen environment respects every registered symbol, then every
    registered axiom evaluates to true in that environment. -/
theorem satisfies_of_respects {R : Registry}
    (hSound : Sound R)
    (hRespect : ∀ i ∈ R, ρ.respects i.folSym) :
    ∀ i ∈ R, ∀ a ∈ i.axioms, Formula.eval ρ a.formula := by
  suffices h :
      ∀ todo, SoundIn R todo →
        ∀ i ∈ todo, ∀ a ∈ i.axioms, Formula.eval ρ a.formula by
    exact h R hSound
  intro todo
  induction todo with
  | nil =>
    intro _ i hi
    cases hi
  | cons i rest ih =>
    intro hSoundIn
    rcases hSoundIn with ⟨hiSound, hrestSound⟩
    intro j hj
    cases hj with
    | head =>
      intro φ hφ
      exact hiSound.proof ρ (fun d hd => hRespect d hd) φ hφ
    | tail _ hjrest =>
      intro φ hφ
      exact ih hrestSound j hjrest φ hφ

theorem stdEnv_satisfies {R : Registry} (hSound : Sound R) (hWf : Wf R) :
    ∀ i ∈ R, ∀ a ∈ i.axioms, Formula.eval (stdEnv R) a.formula :=
  satisfies_of_respects hSound (stdEnv_respects hWf)

end Registry

/-- Intrinsic soundness is monotone in the dependency fragment: once an
    intrinsic is sound against the symbols it actually needs, it is sound
    against any larger fragment containing those dependencies. -/
theorem IntrinsicSound.mono {deps deps' : Registry} {i : Intrinsic}
    (h : IntrinsicSound deps i) (hsub : deps ⊆ deps') :
    IntrinsicSound deps' i where
  specWf := h.specWf
  bridge := h.bridge
  wp_sound := h.wp_sound
  axiomWf := by
    intro Δ hsig hwf φ hφ
    exact h.axiomWf ((Registry.sigOf_subset_of_subset hsub).trans hsig) hwf φ hφ
  proof := by
    intro ρ hdeps' φ hφ
    exact h.proof ρ (fun d hd => hdeps' d (hsub hd)) φ hφ

/-! ## SMT setup loop -/

namespace Intrinsic

/-- Declare this intrinsic's FOL symbol (if any) into the verifier. -/
def declFOLSym (i : Intrinsic) : VerifM Unit :=
  match i.arity, i.folSym with
  | _,     none   => pure ()
  | .zero, some s => VerifM.declConstExact ⟨s.name, .value⟩
  | .one,  some s => VerifM.declUnaryExact ⟨s.name, .value, .value⟩
  | .two,  some s => VerifM.declBinaryExact ⟨s.name, .value, .value, .value⟩
  | .three, some s => VerifM.declTernaryExact ⟨s.name, .value, .value, .value, .value⟩

end Intrinsic

namespace Registry

/-- Declare every registered intrinsic's FOL symbol. -/
def declFOLSyms : Registry → VerifM Unit
  | []         => pure ()
  | i :: rest  => do i.declFOLSym; declFOLSyms rest

/-- Assume every registered intrinsic axiom, weakening guarded axioms. -/
def assumeAxioms : Registry → VerifM Unit
  | []         => pure ()
  | i :: rest  => do VerifM.assumeAxioms i.axioms; assumeAxioms rest

/-- Declare all registered intrinsic FOL symbols first, then assume all
    intrinsic axioms. This keeps axiom validity independent of registry order:
    axioms may mention any symbol in the registry, not just earlier entries. -/
def introduceRegistry (R : Registry) : VerifM Unit := do
  declFOLSyms R
  assumeAxioms R

end Registry

/-! ## Generic theorems for any registry

Proved by induction on the list and case-analysis on arity. No specific
intrinsic is named. -/

namespace Intrinsic

/-- Effect of `declFOLSym`: extends the signature with `i`'s FOL symbol,
    leaves owns and asserts untouched, and produces a post-decl environment
    that respects `i.folSym` (when present), agreeing with the original on
    the original signature. -/
theorem eval_declFOLSym (i : Intrinsic) {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval i.declFOLSym st ρ Q) :
    ∃ ρ' : VerifM.Env,
      VerifM.Env.agreeOn st.decls ρ ρ' ∧
      ρ'.env.respects i.folSym ∧
      Q () { st with decls := st.decls.extendWithSym i.folSym } ρ' := by
  cases i with
  | mk arity name path reduce wp spec typing folSym axioms =>
    cases arity with
    | zero =>
      cases folSym with
      | none =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        refine ⟨ρ, VerifM.Env.agreeOn_refl, by simp [Env.respects], ?_⟩
        exact VerifM.eval_ret heval
      | some s =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        obtain ⟨hfresh, hcont⟩ := VerifM.eval_declConstExact heval
        refine ⟨ρ.updateConst .value s.name (s.interp ()),
                VerifM.Env.agreeOn_update_fresh (c := ⟨s.name, .value⟩) hfresh,
                ?_, ?_⟩
        · simp [Env.respects, VerifM.Env.updateConst, Env.lookupConst, Env.updateConst]
        · exact hcont (s.interp ())
    | one =>
      cases folSym with
      | none =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        refine ⟨ρ, VerifM.Env.agreeOn_refl, by simp [Env.respects], ?_⟩
        exact VerifM.eval_ret heval
      | some s =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        obtain ⟨hfresh, hcont⟩ := VerifM.eval_declUnaryExact heval
        refine ⟨ρ.updateUnary .value .value s.name s.interp,
                VerifM.Env.agreeOn_update_fresh_unary (u := ⟨s.name, .value, .value⟩) hfresh,
                ?_, ?_⟩
        · simp [Env.respects, VerifM.Env.updateUnary, Env.updateUnary]
        · exact hcont s.interp
    | two =>
      cases folSym with
      | none =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        refine ⟨ρ, VerifM.Env.agreeOn_refl, by simp [Env.respects], ?_⟩
        exact VerifM.eval_ret heval
      | some s =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        obtain ⟨hfresh, hcont⟩ := VerifM.eval_declBinaryExact heval
        refine ⟨ρ.updateBinary .value .value .value s.name (fun a b => s.interp (a, b)),
                VerifM.Env.agreeOn_update_fresh_binary (b := ⟨s.name, .value, .value, .value⟩) hfresh,
                ?_, ?_⟩
        · simp [Env.respects, VerifM.Env.updateBinary, Env.updateBinary]
        · exact hcont (fun a b => s.interp (a, b))
    | three =>
      cases folSym with
      | none =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        refine ⟨ρ, VerifM.Env.agreeOn_refl, by simp [Env.respects], ?_⟩
        exact VerifM.eval_ret heval
      | some s =>
        simp only [declFOLSym, Signature.extendWithSym] at heval ⊢
        obtain ⟨hfresh, hcont⟩ := VerifM.eval_declTernaryExact heval
        refine ⟨ρ.updateTernary .value .value .value .value s.name
                  (fun a b c => s.interp (a, b, c)),
                VerifM.Env.agreeOn_update_fresh_ternary
                  (t := ⟨s.name, .value, .value, .value, .value⟩) hfresh,
                ?_, ?_⟩
        · simp [Env.respects, VerifM.Env.updateTernary, Env.updateTernary]
        · exact hcont (fun a b c => s.interp (a, b, c))

end Intrinsic

namespace Registry

/-- Effect of the declaration pass on a registry. It declares every registered
    FOL symbol before any intrinsic axiom is assumed. -/
theorem eval_declFOLSyms (R : Registry)
    {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (declFOLSyms R) st ρ Q) :
    ∃ st' ρ',
      st.decls.Subset st'.decls ∧
      (Intrinsic.foldSig st.decls R).Subset st'.decls ∧
      st'.decls.vars = st.decls.vars ∧
      st'.owns = st.owns ∧
      st'.asserts = st.asserts ∧
      (∀ ρ'' : VerifM.Env, VerifM.Env.agreeOn st'.decls ρ' ρ'' →
        ∀ d ∈ R, ρ''.env.respects d.folSym) ∧
      VerifM.Env.agreeOn st.decls ρ ρ' ∧
      Q () st' ρ' := by
  induction R generalizing st ρ Q with
  | nil =>
    simp only [declFOLSyms] at heval
    refine ⟨st, ρ, Signature.Subset.refl _, ?_, rfl, rfl, rfl, ?_,
            VerifM.Env.agreeOn_refl, VerifM.eval_ret heval⟩
    · exact Signature.Subset.refl _
    · intro _ _ d hd
      cases hd
  | cons i rest ih =>
    simp only [declFOLSyms] at heval
    have h1 := VerifM.eval_bind heval
    obtain ⟨ρ1, hag1, hiRespect, hcont⟩ := Intrinsic.eval_declFOLSym i h1
    set st1 : TransState := { st with decls := st.decls.extendWithSym i.folSym }
    obtain ⟨st', ρ', hsub2, hdep2, hvars2, howns2, hass2, hrestStable, hag2, hQ⟩ :=
      ih hcont
    have hsub1 : st.decls.Subset st1.decls := Signature.subset_extendWithSym _ _
    have hiStable :
        ∀ ρ'' : VerifM.Env, VerifM.Env.agreeOn st'.decls ρ' ρ'' →
          ρ''.env.respects i.folSym := by
      intro ρ'' hag
      refine Env.respects_of_agreeOn_extendWithSym (Δ := st1.decls) hiRespect ?_ ?_
      · exact Signature.extendWithSym_mono (Signature.empty_subset _) _
      · exact VerifM.Env.agreeOn_trans hag2 (VerifM.Env.agreeOn_mono hsub2 hag)
    have hvars1 : st1.decls.vars = st.decls.vars := by
      simp [st1]
    refine ⟨st', ρ', hsub1.trans hsub2, ?_, hvars2.trans hvars1, howns2, hass2, ?_,
            VerifM.Env.agreeOn_trans hag1 (VerifM.Env.agreeOn_mono hsub1 hag2), hQ⟩
    · exact hdep2
    · intro ρ'' hag d hd
      cases hd with
      | head => exact hiStable ρ'' hag
      | tail _ hmem => exact hrestStable ρ'' hag d hmem

/-- Effect of the axiom-assumption pass. Each intrinsic is checked against the
    full registry fragment, so axiom dependencies need not follow list order. -/
theorem eval_assumeAxioms_in (full todo : Registry)
    (hSound : SoundIn full todo)
    {st : TransState} {ρ : VerifM.Env}
    (hSig : (Intrinsic.sigOf full).Subset st.decls)
    (hRespect :
      ∀ ρ' : VerifM.Env, VerifM.Env.agreeOn st.decls ρ ρ' →
        ∀ d ∈ full, ρ'.env.respects d.folSym)
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (assumeAxioms todo) st ρ Q) :
    ∃ st',
      st'.decls = st.decls ∧
      st'.owns = st.owns ∧
      (∃ extra, st'.asserts = extra ++ st.asserts) ∧
      Q () st' ρ := by
  induction todo generalizing st Q with
  | nil =>
    simp only [assumeAxioms] at heval
    refine ⟨st, rfl, rfl, ⟨[], by simp⟩, VerifM.eval_ret heval⟩
  | cons i rest ih =>
    simp only [assumeAxioms] at heval
    have h1 := VerifM.eval_bind heval
    rcases hSound with ⟨hiSound, hrestSound⟩
    have hwfAxioms : ∀ a ∈ i.axioms, a.formula.wfIn st.decls := fun a ha =>
      hiSound.axiomWf hSig (VerifM.eval.wf h1).namesDisjoint a ha
    have hevalAxioms : ∀ a ∈ i.axioms, a.formula.eval ρ.env :=
      hiSound.proof ρ.env (fun d hd => hRespect ρ VerifM.Env.agreeOn_refl d hd)
    obtain ⟨st1, hdecls1, howns1, hass1, hcont⟩ :=
      VerifM.eval_assumeAxioms h1 hwfAxioms hevalAxioms
    have hSig1 : (Intrinsic.sigOf full).Subset st1.decls := by
      rw [hdecls1]
      exact hSig
    have hRespect1 :
        ∀ ρ' : VerifM.Env, VerifM.Env.agreeOn st1.decls ρ ρ' →
          ∀ d ∈ full, ρ'.env.respects d.folSym := by
      intro ρ' hag d hd
      exact hRespect ρ' (by rwa [hdecls1] at hag) d hd
    obtain ⟨st', hdecls2, howns2, ⟨extra2, hass2⟩, hQ⟩ :=
      ih hrestSound hSig1 hRespect1 hcont
    refine ⟨st', hdecls2.trans hdecls1, howns2.trans howns1,
            ⟨extra2 ++ (Axiom.asserts i.axioms).reverse, ?_⟩, hQ⟩
    rw [hass2, hass1, List.append_assoc]

/-- Effect of `introduceRegistry` on a whole registry. All symbols are declared
    first; all axioms are assumed afterward against the full registry
    signature. -/
theorem eval_introduceRegistry (R : Registry)
    (hSound : Sound R)
    {st : TransState} {ρ : VerifM.Env}
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (introduceRegistry R) st ρ Q) :
    ∃ st' ρ',
      st.decls.Subset st'.decls ∧
      (Intrinsic.sigOf R).Subset st'.decls ∧
      st'.decls.vars = st.decls.vars ∧
      st'.owns = st.owns ∧
      (∃ extra, st'.asserts = extra ++ st.asserts) ∧
      (∀ ρ'' : VerifM.Env, VerifM.Env.agreeOn st'.decls ρ' ρ'' →
        ∀ d ∈ R, ρ''.env.respects d.folSym) ∧
      VerifM.Env.agreeOn st.decls ρ ρ' ∧
      Q () st' ρ' := by
  unfold introduceRegistry at heval
  have hdecls := VerifM.eval_bind heval
  obtain ⟨st1, ρ1, hsub1, hfold1, hvars1, howns1, hass1, hstable, hag1, hcont⟩ :=
    eval_declFOLSyms R hdecls
  have hsig1 : (Intrinsic.sigOf R).Subset st1.decls := by
    exact (foldSig_mono R (Signature.empty_subset st.decls)).trans hfold1
  obtain ⟨st', hdecls2, howns2, ⟨extra, hass2⟩, hQ⟩ :=
    eval_assumeAxioms_in R R hSound hsig1 hstable hcont
  refine ⟨st', ρ1, ?_, ?_, ?_, howns2.trans howns1, ?_, ?_, hag1, hQ⟩
  · rw [hdecls2]
    exact hsub1
  · rw [hdecls2]
    exact hsig1
  · rw [hdecls2]
    exact hvars1
  · refine ⟨extra, ?_⟩
    rw [hass2, hass1]
  · intro ρ'' hag d hd
    exact hstable ρ'' (by rwa [hdecls2] at hag) d hd

end Registry

end Verifier
