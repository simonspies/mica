-- SUMMARY: Shared names, signatures, and freshness helpers for relational encoding.
import Mica.FOL.Formulas
import Mica.FOL.Fixpoint
import Mica.TinyML.Typed
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

/-- Frontend name of a specification-level function symbol. -/
abbrev SpecFn := String

namespace SpecFn

/-- Solver-facing binary relation name derived from a spec function name. -/
def relName (f : SpecFn) : String :=
  f ++ "-rel"

/-- Solver-facing value function name derived from a spec function name. -/
def funcName (f : SpecFn) : String :=
  f ++ "-func"

/-- Solver-facing definedness predicate name derived from a spec function name. -/
def defName (f : SpecFn) : String :=
  f ++ "-def"

theorem funcName_ne_fn (f : SpecFn) : funcName f ≠ f := by
  intro h
  have hlen := congrArg String.length h
  simp only [funcName, String.length_append,
    show ("-func" : String).length = 5 from rfl] at hlen
  omega

theorem defName_ne_fn (f : SpecFn) : defName f ≠ f := by
  intro h
  have hlen := congrArg String.length h
  simp only [defName, String.length_append,
    show ("-def" : String).length = 4 from rfl] at hlen
  omega

theorem relName_ne_fn (f : SpecFn) : relName f ≠ f := by
  intro h
  have hlen := congrArg String.length h
  simp only [relName, String.length_append,
    show ("-rel" : String).length = 4 from rfl] at hlen
  omega

theorem defName_ne_funcName (f : SpecFn) :
    defName f ≠ funcName f := by
  intro h
  have hlen := congrArg String.length h
  simp only [defName, funcName, String.length_append,
    show ("-func" : String).length = 5 from rfl,
    show ("-def" : String).length = 4 from rfl] at hlen
  omega

theorem relName_ne_funcName (f : SpecFn) :
    relName f ≠ funcName f := by
  intro h
  have hlen := congrArg String.length h
  simp only [relName, funcName, String.length_append,
    show ("-rel" : String).length = 4 from rfl,
    show ("-func" : String).length = 5 from rfl] at hlen
  omega

theorem relName_ne_defName (f : SpecFn) :
    relName f ≠ defName f := by
  intro h
  have hd := congrArg String.toList h
  simp [relName, defName, String.toList_append,
    show ("-rel" : String).toList = ['-','r','e','l'] from rfl,
    show ("-def" : String).toList = ['-','d','e','f'] from rfl] at hd

theorem funcName_ne_relName (f : SpecFn) : funcName f ≠ relName f :=
  fun h => relName_ne_funcName f h.symm

theorem defName_ne_relName (f : SpecFn) : defName f ≠ relName f :=
  fun h => relName_ne_defName f h.symm

/-- Solver-facing definedness predicate symbol for a spec-level function name. -/
def defined (f : SpecFn) : FOL.UnaryRel :=
  ⟨defName f, .value⟩

/-- Solver-facing value function symbol for a spec-level function name. -/
def func (f : SpecFn) : FOL.Unary :=
  ⟨funcName f, .value, .value⟩

/-- Solver-facing binary relation symbol for a spec-level function name. -/
def rel (f : SpecFn) : FOL.BinaryRel :=
  ⟨relName f, .value, .value⟩

/-- Apply the solver-facing value function for frontend function name `f`. -/
def call (f : SpecFn) (arg : Term .value) : Term .value :=
  .unop (.uninterpreted (funcName f) .value .value) arg

/-- Apply the solver-facing definedness predicate for frontend function name `f`. -/
def isDefined (f : SpecFn) (arg : Term .value) : Formula :=
  .unpred (.uninterpreted (defName f) .value) arg

/-- Apply the solver-facing binary relation for frontend function name `f`. -/
def relates (f : SpecFn) (arg res : Term .value) : Formula :=
  .binpred (.uninterpreted (relName f) .value .value) arg res

/-- Semantic value of the solver-facing value function on argument `arg`
under environment `ρ`. -/
def evalCall (f : SpecFn) (ρ : Env) (arg : Srt.value.denote) : Srt.value.denote :=
  ρ.unary .value .value f.func.name arg

/-- Semantic value of the solver-facing definedness predicate on argument `arg`
under environment `ρ`. -/
def evalDefined (f : SpecFn) (ρ : Env) (arg : Srt.value.denote) : Prop :=
  ρ.unaryRel .value f.defined.name arg

/-- Semantic value of the solver-facing binary relation on `(arg, res)`
under environment `ρ`. -/
def evalRelates (f : SpecFn) (ρ : Env) (arg res : Srt.value.denote) : Prop :=
  ρ.binaryRel .value .value f.rel.name arg res

/-- The value-function evaluation is preserved by `Env.updateConst`. -/
@[simp] theorem evalCall_updateConst (f : SpecFn) (ρ : Env) (τ : Srt) (x : String)
    (v : τ.denote) (a : Srt.value.denote) :
    f.evalCall (ρ.updateConst τ x v) a = f.evalCall ρ a := rfl

/-- The definedness predicate is preserved by `Env.updateConst`. -/
@[simp] theorem evalDefined_updateConst (f : SpecFn) (ρ : Env) (τ : Srt) (x : String)
    (v : τ.denote) (a : Srt.value.denote) :
    f.evalDefined (ρ.updateConst τ x v) a = f.evalDefined ρ a := rfl

/-- The binary relation is preserved by `Env.updateConst`. -/
@[simp] theorem evalRelates_updateConst (f : SpecFn) (ρ : Env) (τ : Srt) (x : String)
    (v : τ.denote) (a b : Srt.value.denote) :
    f.evalRelates (ρ.updateConst τ x v) a b = f.evalRelates ρ a b := rfl

/-- Evaluating `relates` reduces to the binary relation in the environment. -/
@[simp] theorem relates_eval (f : SpecFn) (ρ : Env) (arg res : Term .value) :
    (f.relates arg res).eval ρ = f.evalRelates ρ (arg.eval ρ) (res.eval ρ) := rfl

/-- Evaluating `isDefined` reduces to the definedness predicate in the environment. -/
@[simp] theorem isDefined_eval (f : SpecFn) (ρ : Env) (arg : Term .value) :
    (f.isDefined arg).eval ρ = f.evalDefined ρ (arg.eval ρ) := rfl

/-- Evaluating `call` reduces to the value function in the environment. -/
@[simp] theorem call_eval (f : SpecFn) (ρ : Env) (arg : Term .value) :
    (f.call arg).eval ρ = f.evalCall ρ (arg.eval ρ) := rfl

/-- A registered solver-facing value-function application is well-formed when
its argument is well-formed. -/
theorem call_wfIn {fn : SpecFn} {arg : Term .value} {Δ : Signature}
    (hfun : fn.func ∈ Δ.unary) (hΔ : Δ.wf) (harg : arg.wfIn Δ) :
    (fn.call arg).wfIn Δ := by
  refine ⟨?_, harg⟩
  refine ⟨hfun, ?_, ?_⟩
  · intro τ hrel
    exact Signature.wf_no_unaryRel_of_unary hΔ hfun hrel
  · intro τ₁ τ₂ hfun'
    exact Signature.wf_unique_unary hΔ hfun hfun'

/-- A registered solver-facing definedness-predicate application is
well-formed when its argument is well-formed. -/
theorem isDefined_wfIn {fn : SpecFn} {arg : Term .value} {Δ : Signature}
    (hrel : fn.defined ∈ Δ.unaryRel) (hΔ : Δ.wf) (harg : arg.wfIn Δ) :
    (fn.isDefined arg).wfIn Δ := by
  refine ⟨?_, harg⟩
  refine ⟨hrel, ?_, ?_⟩
  · intro τ₁ τ₂ hfun
    exact Signature.wf_no_unaryRel_of_unary hΔ hfun hrel
  · intro τ hrel'
    exact Signature.wf_unique_unaryRel hΔ hrel hrel'

/-- A registered solver-facing relation application is well-formed when its
arguments are well-formed. -/
theorem relates_wfIn {fn : SpecFn} {arg res : Term .value} {Δ : Signature}
    (hrel : fn.rel ∈ Δ.binaryRel)
    (hΔ : Δ.wf) (harg : arg.wfIn Δ) (hres : res.wfIn Δ) :
    (fn.relates arg res).wfIn Δ := by
  refine ⟨?_, harg, hres⟩
  refine ⟨hrel, ?_, ?_⟩
  · intro τ₁ τ₂ τ₃ hb
    exact Signature.wf_no_binaryRel_of_binary hΔ hb hrel
  · intro τ₁ τ₂ hb
    exact Signature.wf_unique_binaryRel hΔ hrel hb

end SpecFn

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
def FunCtx.splitWfIn (Γ : FunCtx) (Δ : Signature) : Prop :=
  ∀ x (fn : SpecFn), (x, fn) ∈ Γ →
    fn.func ∈ Δ.unary ∧ fn.defined ∈ Δ.unaryRel

theorem FunCtx.splitWfIn_mono {Γ : FunCtx} {Δ Δ' : Signature}
    (h : Γ.splitWfIn Δ) (hsub : Δ.Subset Δ') : Γ.splitWfIn Δ' := by
  intro x fn hxr
  exact ⟨hsub.unary _ (h x fn hxr).1, hsub.unaryRel _ (h x fn hxr).2⟩

/-- Bundled well-formedness: every relation in `Γ` has all three solver-facing
symbols (the binary relation, the value function, and the definedness predicate)
registered in `Δ`. -/
structure FunCtx.wfIn (Γ : FunCtx) (Δ : Signature) : Prop where
  rel : Γ.relWfIn Δ
  split : Γ.splitWfIn Δ

theorem FunCtx.wfIn_mono {Γ : FunCtx} {Δ Δ' : Signature}
    (h : Γ.wfIn Δ) (hsub : Δ.Subset Δ') : Γ.wfIn Δ' :=
  ⟨FunCtx.relWfIn_mono h.rel hsub, FunCtx.splitWfIn_mono h.split hsub⟩

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

/-- Initial local environment induced by value variables declared in a FOL
signature. -/
def ofSignature (Δ : Signature) : VarEnv :=
  Δ.vars.filterMap fun v =>
    match v.sort with
    | .value => some (v.name, .var .value v.name)
    | _ => none

/-- Every term stored in a local environment is well-formed in `Δ`. -/
def wfIn (δ : VarEnv) (Δ : Signature) : Prop :=
  ∀ x v, δ.lookup x = some v → v.wfIn Δ

@[simp] theorem lookup_bind (δ : VarEnv) (x : String) (v : Term .value) :
    (δ.bind x v).lookup x = some v := by
  simp [lookup, bind]

theorem lookup_bind_of_ne {δ : VarEnv} {x y : String} {v : Term .value}
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

/-- Paired local environments agree semantically in two FOL environments:
they share a lookup domain, and corresponding terms are well-formed in the
respective signatures and evaluate equally. -/
structure Agree (Δ₁ Δ₂ : Signature) (ρ₁ ρ₂ : Env) (δ₁ δ₂ : VarEnv) : Prop where
  /-- Both environments bind the same set of TinyML variables. -/
  sameDomain : ∀ x, (∃ v₁, δ₁.lookup x = some v₁) ↔ (∃ v₂, δ₂.lookup x = some v₂)
  /-- Corresponding bound terms are well-formed and evaluate equally. -/
  agree : ∀ x v₁ v₂,
    δ₁.lookup x = some v₁ →
    δ₂.lookup x = some v₂ →
    v₁.wfIn Δ₁ ∧ v₂.wfIn Δ₂ ∧
      Term.eval ρ₁ v₁ = Term.eval ρ₂ v₂

theorem Agree.bind {Δ₁ Δ₂ : Signature} {ρ₁ ρ₂ : Env}
    {δ₁ δ₂ : VarEnv} {x : String} {v₁ v₂ : Term .value}
    (henv : Agree Δ₁ Δ₂ ρ₁ ρ₂ δ₁ δ₂)
    (hv₁ : v₁.wfIn Δ₁) (hv₂ : v₂.wfIn Δ₂)
    (heval : Term.eval ρ₁ v₁ = Term.eval ρ₂ v₂) :
    Agree Δ₁ Δ₂ ρ₁ ρ₂ (δ₁.bind x v₁) (δ₂.bind x v₂) where
  sameDomain := by
    intro y
    by_cases hyx : y = x
    · subst y
      simp [lookup_bind]
    · rw [lookup_bind_of_ne (δ := δ₁) (x := x) (v := v₁) hyx,
        lookup_bind_of_ne (δ := δ₂) (x := x) (v := v₂) hyx]
      exact henv.sameDomain y
  agree := by
    intro y w₁ w₂ h₁ h₂
    by_cases hyx : y = x
    · subst y
      simp only [lookup_bind, Option.some.injEq] at h₁ h₂
      subst w₁; subst w₂
      exact ⟨hv₁, hv₂, heval⟩
    · have h₁' : δ₁.lookup y = some w₁ := by
        simpa [lookup_bind_of_ne (δ := δ₁) (x := x) (v := v₁) hyx] using h₁
      have h₂' : δ₂.lookup y = some w₂ := by
        simpa [lookup_bind_of_ne (δ := δ₂) (x := x) (v := v₂) hyx] using h₂
      exact henv.agree y w₁ w₂ h₁' h₂'

theorem Agree.bindBinder {Δ₁ Δ₂ : Signature} {ρ₁ ρ₂ : Env}
    {δ₁ δ₂ : VarEnv} {b : Typed.Binder} {v₁ v₂ : Term .value}
    (henv : Agree Δ₁ Δ₂ ρ₁ ρ₂ δ₁ δ₂)
    (hv₁ : v₁.wfIn Δ₁) (hv₂ : v₂.wfIn Δ₂)
    (heval : Term.eval ρ₁ v₁ = Term.eval ρ₂ v₂) :
    Agree Δ₁ Δ₂ ρ₁ ρ₂ (δ₁.bindBinder b v₁) (δ₂.bindBinder b v₂) := by
  cases b with
  | mk name ty =>
      cases name with
      | none => simpa [bindBinder] using henv
      | some x => simpa [bindBinder] using henv.bind hv₁ hv₂ heval

theorem Agree.mono {Δ₁ Δ₂ Δ₁' Δ₂' : Signature} {ρ₁ ρ₂ ρ₁' ρ₂' : Env}
    {δ₁ δ₂ : VarEnv}
    (hsub₁ : Δ₁.Subset Δ₁') (hsub₂ : Δ₂.Subset Δ₂')
    (hwf₁ : Δ₁'.wf) (hwf₂ : Δ₂'.wf)
    (ha₁ : Env.agreeOn Δ₁ ρ₁ ρ₁') (ha₂ : Env.agreeOn Δ₂ ρ₂ ρ₂')
    (henv : Agree Δ₁ Δ₂ ρ₁ ρ₂ δ₁ δ₂) :
    Agree Δ₁' Δ₂' ρ₁' ρ₂' δ₁ δ₂ where
  sameDomain := henv.sameDomain
  agree := by
    intro x v₁ v₂ h₁ h₂
    rcases henv.agree x v₁ v₂ h₁ h₂ with ⟨hv₁, hv₂, heval⟩
    have hv₁' := Term.wfIn_mono v₁ hv₁ hsub₁ hwf₁
    have hv₂' := Term.wfIn_mono v₂ hv₂ hsub₂ hwf₂
    refine ⟨hv₁', hv₂', ?_⟩
    rw [← Term.eval_env_agree hv₁ ha₁, heval, Term.eval_env_agree hv₂ ha₂]

end VarEnv

namespace Relation

/-- Signature extended for encoding the body of `rec f x := e`: adds the input
variable `x : value` and the binary predicate `fn.relName ⊆ value × value`, but
not the result variable. -/
def bodySig (Δ : Signature) (fn : SpecFn) (x : TinyML.Var) : Signature :=
  (Δ.addBinaryRel fn.rel).declVar ⟨x, .value⟩

/-- Run signature: `bodySig Δ fn x` extended with the pinned result variable `r`. -/
def sig (Δ : Signature) (fn : SpecFn) (x r : TinyML.Var) : Signature :=
  (bodySig Δ fn x).declVar ⟨r, .value⟩

/-- Body supply: reserves base-signature names plus the relation symbol, the
stage-2 split names, and the input and result variables. -/
def relBodySupply (Δ : Signature) (fn : SpecFn) (x res : TinyML.Var) : NameSupply :=
  { avoid := Δ.allNames ++ [fn.relName, fn.funcName, fn.defName, x, res] }

end Relation

namespace Skolemize

/-- Signature used to encode the body expression of `rec f x := e`. It
contains the binary relation, the split value/definedness symbols, and the
input variable. -/
def bodySig (Δ : Signature) (fn : SpecFn) (x : TinyML.Var) : Signature :=
  ((((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
    fn.defined).declVar ⟨x, .value⟩)

/-- Common run signature used for the relational pinned-result continuation. -/
def sig (Δ : Signature) (fn : SpecFn) (x res : TinyML.Var) : Signature :=
  (bodySig Δ fn x).declVar ⟨res, .value⟩

/-- Signature containing only the solver-facing split symbols and input
variable used by the defined/value body. -/
def defvalBodySig (Δ : Signature) (fn : SpecFn) (x : TinyML.Var) : Signature :=
  (((Δ.addUnary fn.func).addUnaryRel fn.defined).declVar ⟨x, .value⟩)

end Skolemize

namespace Skolemize
open Relation

/-- The shared body supply covers the combined Skolemization run signature. -/
theorem relBodySupply_covers_sig (Δ : Signature) (fn : SpecFn) (x res : String) :
    (relBodySupply Δ fn x res).Covers (sig Δ fn x res) := by
  intro n hn
  by_contra hcontra
  have hnΔ   : n ∉ Δ.allNames     := fun h => hcontra (by simp [relBodySupply, h])
  have hnRel : n ≠ fn.relName     := fun h => hcontra (by simp [relBodySupply, h])
  have hnFun : n ≠ fn.funcName    := fun h => hcontra (by simp [relBodySupply, h])
  have hnDef : n ≠ fn.defName     := fun h => hcontra (by simp [relBodySupply, h])
  have hnX   : n ≠ x              := fun h => hcontra (by simp [relBodySupply, h])
  have hnRes : n ≠ res            := fun h => hcontra (by simp [relBodySupply, h])
  have h1 : n ∉ (Δ.addBinaryRel fn.rel).allNames :=
    Signature.not_mem_allNames_addBinaryRel hnΔ hnRel
  have h2 : n ∉ ((Δ.addBinaryRel fn.rel).addUnary fn.func).allNames :=
    Signature.not_mem_allNames_addUnary h1 (by simpa [SpecFn.func] using hnFun)
  have h3 : n ∉ (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
      fn.defined).allNames :=
    Signature.not_mem_allNames_addUnaryRel h2 (by simpa [SpecFn.defined] using hnDef)
  have h4 := Signature.not_mem_allNames_declVar h3 (show n ≠ (⟨x, .value⟩ : Var).name from hnX)
  have h5 := Signature.not_mem_allNames_declVar h4 (show n ≠ (⟨res, .value⟩ : Var).name from hnRes)
  exact h5 (by simpa [sig, bodySig] using hn)

end Skolemize
end Verifier.RelationalEncoding
