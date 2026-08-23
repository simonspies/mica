-- SUMMARY: Solver-facing symbol vocabulary for specification-level function names.
import Mica.FOL.Formulas

/-!
# Specification function symbols

A frontend specification-level function name is encoded into three
solver-facing symbols: a binary relation, a value function, and a definedness
predicate. This file fixes that vocabulary — the names, the symbols, the term
and formula constructors, their evaluation, and their well-formedness — so that
both the assertion semantics (`Mica/SourceTinyML/Semantics.lean`) and the
relational encoding (`Mica/Verifier/RelationalEncoding/`) can use it.
-/

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

/-- Agreement on a signature carrying `fn`'s split symbols transports the
relational, value, and definedness evaluations between the two environments. -/
theorem eval_of_agreeOn {fn : SpecFn} {ρ ρ' : Env} {Δ : Signature}
    (h : Env.agreeOn Δ ρ ρ')
    (hr : fn.rel ∈ Δ.binaryRel) (hu : fn.func ∈ Δ.unary) (hd : fn.defined ∈ Δ.unaryRel) :
    fn.evalRelates ρ = fn.evalRelates ρ' ∧
      fn.evalCall ρ = fn.evalCall ρ' ∧ fn.evalDefined ρ = fn.evalDefined ρ' :=
  ⟨h.2.2.2.2.2.2 _ hr, h.2.2.1 _ hu, h.2.2.2.2.2.1 _ hd⟩

end SpecFn
