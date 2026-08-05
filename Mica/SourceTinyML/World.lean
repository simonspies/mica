-- SUMMARY: The fixed meta-level world in which the logical relation interprets types, including its assignment of meanings to type variables.
import Mica.SourceTinyML.Types
import Mica.TinyML.OpSem
import Mica.FOL.Variables
import Mica.SeparationLogic.Wp

namespace TinyML

/-! ### Semantic types

A type variable has no syntactic meaning to unfold, so the logical relation
takes its meaning from the world: a predicate on runtime values, given by an
assignment the world carries. -/

/-- A semantic type: a predicate on runtime values. The predicate carries its
own persistence proof, since the logical relation is persistent at every type
and interprets a variable by nothing but this. -/
structure SemType where
  holds : Runtime.Val → iProp
  persistent : ∀ v, Iris.BI.Persistent (holds v)

/-- An assignment of semantic types to type variables. A declaration quantifying
over its variables is verified at every assignment; a call site picks the one
its instantiation denotes. -/
abbrev SemTypeAssign := TyVar → SemType

/-- The assignment a program's top level runs at. Nothing observes it: a
declaration is generalized where it is installed and instantiated where it is
used, so no type reaching the top level mentions a variable. -/
def SemTypeAssign.empty : SemTypeAssign :=
  fun _ => ⟨fun _ => iprop(False), fun _ => inferInstance⟩

/-! ### The world -/

/-- The fixed model in which the logical relation interprets types and
    specifications: the primitive-operational context its weakest preconditions
    are taken in, the type environment unfolding named types, and the FOL
    signature and environment specifications are interpreted against.

    `Δ_spec`/`ρ_spec` are fixed, unlike the verifier's own growing `st.decls`
    and `ρ`; correctness maintains `W.agrees st.decls ρ.env` (see `World.agrees`).

    A world appears only in semantic definitions and correctness theorems;
    executable verifier definitions never receive one. -/
structure World where
  pctx   : PrimCtx
  Θ      : TypeEnv
  Δ_spec : Signature
  ρ_spec : Env
  eta    : SemTypeAssign

set_option linter.dupNamespace false in
/-- The world's specification signature is well-formed and closed: its names are
    distinct and it declares no variables. These conditions are fixed with the
    world, independent of the verifier's growing state. -/
structure World.wf (W : World) : Prop where
  /-- The spec signature's names are distinct. -/
  wf : W.Δ_spec.wf
  /-- The spec signature declares no variables. -/
  vars : W.Δ_spec.vars = []

/-- The world agrees with a verifier signature `Δ` and environment `ρ`: the
    fixed spec signature is a subset of `Δ`, and the fixed spec environment
    agrees with `ρ` on it. -/
structure World.agrees (W : World) (Δ : Signature) (ρ : Env) : Prop where
  /-- The fixed spec signature is contained in `Δ`. -/
  subset : W.Δ_spec.Subset Δ
  /-- The fixed spec environment agrees with `ρ` on the spec signature. -/
  agree : Env.agreeOn W.Δ_spec W.ρ_spec ρ

/-- Agreement is preserved as the verifier signature and environment grow: from
    a signature step `Δ.Subset Δ'` and an environment step agreeing on `Δ`. -/
theorem World.agrees.step {W : World} {Δ Δ' : Signature} {ρ ρ' : Env}
    (hag : W.agrees Δ ρ) (hΔ : Δ.Subset Δ') (hρ : Env.agreeOn Δ ρ ρ') :
    W.agrees Δ' ρ' where
  subset := hag.subset.trans hΔ
  agree := Env.agreeOn_trans hag.agree (Env.agreeOn_mono hag.subset hρ)

end TinyML
