-- SUMMARY: The fixed meta-level world in which the logical relation interprets types.
import Mica.TinyML.Types
import Mica.TinyML.OpSem
import Mica.FOL.Variables

namespace TinyML

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
