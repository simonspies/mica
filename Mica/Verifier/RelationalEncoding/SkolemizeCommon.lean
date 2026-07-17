-- SUMMARY: Shared split encoding and semantic infrastructure for Skolemization.
import Mica.Verifier.RelationalEncoding.Relation

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

/-! ## `DefVal` Syntax -/

/-- Solver-facing expression encoding: a value term plus the condition under
which that value is defined. -/
structure DefVal where
  value : Term .value
  defined : Formula
  deriving DecidableEq

namespace DefVal

def pure (v : Term .value) : DefVal :=
  { value := v, defined := .true_ }

def bind (m : DefVal) (k : Term .value → Except String DefVal) : Except String DefVal := do
  let n ← k m.value
  Except.ok { value := n.value, defined := .and m.defined n.defined }

def call (fn : SpecFn) (arg : Term .value) : DefVal :=
  { value := fn.call arg, defined := fn.isDefined arg }

def ite (cond : Term .bool) (thenVal elseVal : DefVal) : DefVal :=
  { value := .ite cond thenVal.value elseVal.value
    defined := Formula.iteBool cond thenVal.defined elseVal.defined }

end DefVal

/-- Defined/value instance of `EncoderOps`. The carrier is `Except String
DefVal`, so error handling lives inside the carrier itself; `error` is
`Except.error`. The CPS `call` allocates the solver-facing value/definedness
symbols and threads the value through the continuation, conjoining the local
definedness obligation via `DefVal.bind`. -/
def encoderOps : EncoderOps (Except String DefVal) where
  call fn arg k := DefVal.bind (DefVal.call fn arg) k
  ite c t e     := do let dt ← t; let de ← e; .ok (DefVal.ite c dt de)
  error msg     := .error msg

/-- Defined/value encoding of a pure typed TinyML expression for SMT emission.
Calls are encoded using total value functions and separate definedness
predicates, so this encoding introduces no existential witnesses. Implemented
as the shared traversal `encodeWith` instantiated at `encoderOps`. -/
def encode (Γ : FunCtx) (Δ : Signature) (e : Typed.Expr) :
    Except String DefVal :=
  encodeWith encoderOps Δ Γ (VarEnv.ofSignature Δ) e (fun v => .ok (DefVal.pure v))

/-! ## Well-formedness of `encode` -/

namespace DefVal

/-- A defined/value encoding is well-formed when both its value term and its
definedness formula are well-formed. -/
def wfIn (m : DefVal) (Δ : Signature) : Prop :=
  m.value.wfIn Δ ∧ m.defined.wfIn Δ

theorem pure_wfIn {v : Term .value} {Δ : Signature} (hv : v.wfIn Δ) :
    (pure v).wfIn Δ := ⟨hv, trivial⟩

theorem bind_wfIn {m n : DefVal} {Δ : Signature}
    (hm : m.wfIn Δ) (hn : n.wfIn Δ) :
    ({ value := n.value, defined := .and m.defined n.defined } : DefVal).wfIn Δ :=
  ⟨hn.1, hm.2, hn.2⟩

/-- A successful `DefVal.bind` exposes the continuation result and the final
definedness shape. -/
theorem bind_ok {m out : DefVal}
    {kc : Term .value → Except String DefVal}
    (h : bind m kc = .ok out) :
    ∃ n, kc m.value = .ok n ∧
      out = { value := n.value, defined := .and m.defined n.defined } := by
  unfold bind at h
  cases hn : kc m.value with
  | error msg =>
      simp only [hn, Bind.bind, Except.bind] at h
      cases h
  | ok n =>
      simp only [hn, Bind.bind, Except.bind, Except.ok.injEq] at h
      cases h
      exact ⟨n, rfl, rfl⟩

theorem call_wfIn {fn : SpecFn} {arg : Term .value} {Δ : Signature}
    (hfun : fn.func ∈ Δ.unary) (hrel : fn.defined ∈ Δ.unaryRel)
    (hΔ : Δ.wf) (harg : arg.wfIn Δ) :
    (call fn arg).wfIn Δ :=
  ⟨SpecFn.call_wfIn hfun hΔ harg, SpecFn.isDefined_wfIn hrel hΔ harg⟩

theorem ite_wfIn {cond : Term .bool} {thenVal elseVal : DefVal} {Δ : Signature}
    (hc : cond.wfIn Δ) (ht : thenVal.wfIn Δ) (he : elseVal.wfIn Δ) :
    (ite cond thenVal elseVal).wfIn Δ :=
  ⟨⟨hc, ht.1, he.1⟩, Formula.iteBool_wfIn hc ht.2 he.2⟩

/-- The then-branch of a well-formed defined/value conditional is well-formed. -/
theorem wfIn_of_ite_then {cond : Term .bool} {thenVal elseVal : DefVal}
    {Δ : Signature} (h : (ite cond thenVal elseVal).wfIn Δ) :
    thenVal.wfIn Δ := by
  obtain ⟨hval, hdef⟩ := h
  simp only [ite, Term.wfIn] at hval
  simp only [ite, Formula.iteBool, Formula.wfIn] at hdef
  exact ⟨hval.2.1, hdef.1.2⟩

/-- The else-branch of a well-formed defined/value conditional is well-formed. -/
theorem wfIn_of_ite_else {cond : Term .bool} {thenVal elseVal : DefVal}
    {Δ : Signature} (h : (ite cond thenVal elseVal).wfIn Δ) :
    elseVal.wfIn Δ := by
  obtain ⟨hval, hdef⟩ := h
  simp only [ite, Term.wfIn] at hval
  simp only [ite, Formula.iteBool, Formula.wfIn] at hdef
  exact ⟨hval.2.2, hdef.2.2⟩

end DefVal

/-- Successful solver-facing conditional encoding means both branches
succeeded and the output is exactly their `DefVal.ite`. -/
theorem encoderOps_ite_ok {cond : Term .bool} {t e : Except String DefVal}
    {body : DefVal} (h : encoderOps.ite cond t e = .ok body) :
    ∃ dt de, t = .ok dt ∧ e = .ok de ∧ body = DefVal.ite cond dt de := by
  simp only [encoderOps, Bind.bind, Except.bind] at h
  cases ht : t with
  | error msg => rw [ht] at h; simp at h
  | ok dt =>
    cases he : e with
    | error msg => rw [ht, he] at h; simp at h
    | ok de =>
      rw [ht, he] at h
      simp only [Except.ok.injEq] at h
      exact ⟨dt, de, rfl, rfl, h.symm⟩

/-- Successful relational conditional encoding means both relational branches
succeeded and the output is exactly their `Formula.iteBool`. -/
theorem relation_encoderOps_ite_ok {cond : Term .bool} {t e : Rel}
    {s : NameSupply} {φ : Formula}
    (h : Relation.encoderOps.ite cond t e s = .ok φ) :
    ∃ φt φe, t s = .ok φt ∧ e s = .ok φe ∧ φ = Formula.iteBool cond φt φe := by
  simp only [Relation.encoderOps, Rel.ite, Bind.bind, Except.bind] at h
  cases ht : t s with
  | error msg => rw [ht] at h; simp at h
  | ok φt =>
    cases he : e s with
    | error msg => rw [ht, he] at h; simp at h
    | ok φe =>
      simp only [ht, he] at h
      simp only [Except.ok.injEq] at h
      exact ⟨φt, φe, rfl, rfl, h.symm⟩

/-- Fresh variable data produced by a relation-call encoding at a name supply. -/
structure FreshValueCtx (s : NameSupply) (Δ : Signature) where
  r : String
  s' : NameSupply
  Δ' : Signature
  hr : r = s.fresh "r"
  hs' : s' = s.reserve r
  hΔ' : Δ' = Δ.declVar ⟨r, .value⟩
  fresh : r ∉ Δ.allNames
  wf : Δ'.wf
  subset : Δ.Subset Δ'
  covers : s'.Covers Δ'
  var_wf : (Term.var .value r).wfIn Δ'

/-- Package the standard fresh result variable facts for a relation-call
continuation. -/
def freshValueCtx (s : NameSupply) {Δ : Signature}
    (hΔ : Δ.wf) (hcov : s.Covers Δ) : FreshValueCtx s Δ := by
  let r := s.fresh "r"
  let s' := s.reserve r
  let Δ' := Δ.declVar ⟨r, .value⟩
  have hfresh_avoid : r ∉ s.avoid := by
    simpa [r] using NameSupply.fresh_not_in_avoid s "r"
  have hfresh : r ∉ Δ.allNames := fun hm => hfresh_avoid (hcov r hm)
  have hΔ'wf : Δ'.wf := by simpa [Δ'] using Signature.wf_declVar hΔ
  have hsub : Δ.Subset Δ' := by
    simpa [Δ'] using Signature.subset_declVar_of_fresh (Δ := Δ)
      (v := ⟨r, .value⟩) hfresh
  refine
    { r := r, s' := s', Δ' := Δ', hr := rfl, hs' := rfl, hΔ' := rfl,
      fresh := hfresh, wf := hΔ'wf, subset := hsub, covers := ?_,
      var_wf := ?_ }
  · simpa [Δ', s'] using NameSupply.Covers.declVar hcov r .value
  · exact var_value_wfIn hΔ'wf
      (by simp [Δ'])

namespace FreshValueCtx

theorem fresh_of_subset {s : NameSupply} {Δ Δ₀ : Signature}
    (ctx : FreshValueCtx s Δ) (hsub : Δ₀.Subset Δ) :
    ctx.r ∉ Δ₀.allNames := fun hm => ctx.fresh (Signature.allNames_subset hsub ctx.r hm)

theorem ne_of_var_mem {s : NameSupply} {Δ : Signature}
    (ctx : FreshValueCtx s Δ) {x : String}
    (hx : (⟨x, .value⟩ : Var) ∈ Δ.vars) : ctx.r ≠ x := fun heq =>
  ctx.fresh (heq ▸ Signature.mem_allNames_of_var hx)

theorem eval_update_fresh {s : NameSupply} {Δ : Signature}
    (ctx : FreshValueCtx s Δ) {ρ : Env} {τ : Srt} {w : τ.denote}
    {arg : Term .value} (harg : arg.wfIn Δ) :
    arg.eval (ρ.updateConst τ ctx.r w) = arg.eval ρ :=
  Term.eval_update_fresh (ρ := ρ) (τ := τ) (x := ctx.r) (v := w)
    (Δ := Δ) harg ctx.fresh

end FreshValueCtx

/-- A signature-derived variable environment agrees with itself in the same
semantic environment. -/
theorem varEnv_ofSignature_agree_self {Δ : Signature} {ρ : Env} (hΔ : Δ.wf) :
    VarEnv.Agree Δ Δ ρ ρ (VarEnv.ofSignature Δ) (VarEnv.ofSignature Δ) where
  sameDomain := by
    intro x
    rfl
  agree := by
    intro x v₁ v₂ h₁ h₂
    have hv₁ := VarEnv.ofSignature_wfIn hΔ x v₁ h₁
    rw [h₁] at h₂
    injection h₂ with heq
    subst v₂
    exact ⟨hv₁, hv₁, rfl⟩

/-- Carrier-level well-formedness predicate for the `Except String DefVal`
encoder carrier: an `.ok` carrier is well-formed when its `DefVal` is, an
error is vacuously well-formed. -/
def wfInE (Δ : Signature) : Except String DefVal → Prop
  | .ok d    => d.wfIn Δ
  | .error _ => True

/-- Well-formedness case for a solver-facing call in `encodeWith`. -/
theorem encoderOps_call_wfInE {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {arg : Term .value}
    {k : Term .value → Except String DefVal}
    (hΔ : Δ.wf) (hΓ : Γ.splitWfIn Δ) (hmem : (f, fn) ∈ Γ)
    (harg : arg.wfIn Δ) (hk : SigCont wfInE Δ k) :
    wfInE Δ (encoderOps.call fn arg k) := by
  have hsyms := hΓ f fn hmem
  show wfInE Δ (DefVal.bind (DefVal.call fn arg) k)
  unfold DefVal.bind
  cases hk_call : k (DefVal.call fn arg).value with
  | error _ => exact True.intro
  | ok n =>
    have hcallWf : (DefVal.call fn arg).wfIn Δ :=
      DefVal.call_wfIn hsyms.1 hsyms.2 hΔ harg
    have hnWf : n.wfIn Δ := by
      have := hk (Signature.Subset.refl _) hΔ _ hcallWf.1
      rw [hk_call] at this
      exact this
    exact DefVal.bind_wfIn hcallWf hnWf

/-- Well-formedness case for a solver-facing conditional in `encodeWith`. -/
theorem encoderOps_ite_wfInE {Δ : Signature} {cond : Term .bool}
    {t e : Except String DefVal}
    (_hΔ : Δ.wf) (hcond : cond.wfIn Δ) (ht : wfInE Δ t) (he : wfInE Δ e) :
    wfInE Δ (encoderOps.ite cond t e) := by
  show wfInE Δ (do let dt ← t; let de ← e; .ok (DefVal.ite cond dt de))
  cases ht_eq : t with
  | error _ => exact True.intro
  | ok dt =>
    cases he_eq : e with
    | error _ => exact True.intro
    | ok de =>
      rw [ht_eq] at ht
      rw [he_eq] at he
      exact DefVal.ite_wfIn hcond ht he

/-- `EncoderOpsSig` instance for the solver-facing defined/value encoder. The
generic `encodeWith_indWithSig` then yields the well-formedness of `encode`. -/
def encoderOps_wf : EncoderOpsSig encoderOps wfInE FunCtx.splitWfIn where
  ctx_mono := fun hΓ hsub => FunCtx.splitWfIn_mono hΓ hsub
  call_ind := encoderOps_call_wfInE
  ite_ind := encoderOps_ite_wfInE
  error_ind := True.intro

/-- Well-formedness of a solver-facing defined/value encoding whose `encodeWith`
gate signature `Δgate` may differ from the `VarEnv` signature `Δenc` (the two
coincide for `encode`, but the body encodings gate on the outer signature while
encoding into a body signature). -/
theorem encode_wfIn_of_gate {Γ : FunCtx} {Δgate Δenc : Signature} (e : Typed.Expr)
    {m : DefVal} (hsub : Δgate.Subset Δenc) (hΔ : Δenc.wf) (hΓ : Γ.splitWfIn Δenc)
    (henc : encodeWith encoderOps Δgate Γ (VarEnv.ofSignature Δenc) e
        (fun v => .ok (DefVal.pure v)) = .ok m) :
    m.wfIn Δenc := by
  have hcarrier : wfInE Δenc
      (encodeWith encoderOps Δgate Γ (VarEnv.ofSignature Δenc) e
        (fun v => .ok (DefVal.pure v))) := by
    refine encodeWith_indWithSig encoderOps_wf e hsub hΔ hΓ
      (VarEnv.ofSignature_wfIn hΔ) ?_
    intro Δ' _ _ v hv
    exact DefVal.pure_wfIn hv
  rw [henc] at hcarrier
  exact hcarrier

/-- Well-formedness of the solver-facing defined/value encoding. -/
theorem encode_wfIn {Γ : FunCtx} {Δ : Signature} (e : Typed.Expr)
    {m : DefVal} (hΔ : Δ.wf) (hΓ : Γ.splitWfIn Δ)
    (henc : encode Γ Δ e = .ok m) : m.wfIn Δ :=
  encode_wfIn_of_gate e (Signature.Subset.refl Δ) hΔ hΓ (by simpa [encode] using henc)

/-! ## Monotonicity of `encode` definedness -/

namespace DefVal

/-- The definedness component of a `DefVal` encoding is monotone in the
environment's uninterpreted predicates. -/
def Mono (m : DefVal) : Prop :=
  SemanticMono (fun m ρ => m.defined.eval ρ) m

theorem call_mono (fn : SpecFn) (arg : Term .value) : Mono (call fn arg) := by
  intro ρ ρ' hle hdef
  simp only [call, SpecFn.isDefined, SpecFn.isDefined, Formula.eval, UnPred.eval] at hdef ⊢
  rw [← Term.eval_env_le hle arg]
  exact hle.2.2.2.2.1 .value (fn.defName) (arg.eval ρ) hdef

theorem ite_mono {cond : Term .bool} {thenVal elseVal : DefVal}
    (ht : Mono thenVal) (he : Mono elseVal) : Mono (ite cond thenVal elseVal) := by
  intro ρ ρ' hle hdef
  simp only [ite, Formula.iteBool, Formula.eval] at hdef ⊢
  constructor
  · intro hcond
    have hcond' : cond.eval ρ = true := by
      rw [Term.eval_env_le hle]; exact hcond
    exact ht hle (hdef.1 hcond')
  · intro hcond
    have hcond' : cond.eval ρ = false := by
      rw [Term.eval_env_le hle]; exact hcond
    exact he hle (hdef.2 hcond')

end DefVal

/-- Carrier-level monotonicity predicate for the `Except String DefVal`
encoder carrier: `.ok` carriers must satisfy `DefVal.Mono`, errors are
vacuous. -/
def MonoE : Except String DefVal → Prop
  | .ok d    => d.Mono
  | .error _ => True

/-- Monotonicity case for a solver-facing call in `encodeWith`. -/
theorem encoderOps_call_monoE {fn : SpecFn} {arg : Term .value}
    {k : Term .value → Except String DefVal}
    (hk : ∀ v, MonoE (k v)) :
    MonoE (encoderOps.call fn arg k) := by
  show MonoE (DefVal.bind (DefVal.call fn arg) k)
  unfold DefVal.bind
  cases hk_call : k (DefVal.call fn arg).value with
  | error _ => exact True.intro
  | ok n =>
    have hnMono : n.Mono := by
      intro ρ ρ' hle hdef
      have h : MonoE (k (DefVal.call fn arg).value) := hk _
      rw [hk_call] at h
      exact h hle hdef
    intro ρ ρ' hle hdef
    simp only [Formula.eval] at hdef ⊢
    refine ⟨DefVal.call_mono fn arg hle hdef.1, ?_⟩
    exact hnMono hle hdef.2

/-- Monotonicity case for a solver-facing conditional in `encodeWith`. -/
theorem encoderOps_ite_monoE {cond : Term .bool} {t e : Except String DefVal}
    (ht : MonoE t) (he : MonoE e) :
    MonoE (encoderOps.ite cond t e) := by
  show MonoE (do let dt ← t; let de ← e; .ok (DefVal.ite cond dt de))
  cases ht_eq : t with
  | error _ => exact True.intro
  | ok dt =>
    cases he_eq : e with
    | error _ => exact True.intro
    | ok de =>
      rw [ht_eq] at ht
      rw [he_eq] at he
      exact DefVal.ite_mono ht he

/-- `encoderOps` preserves monotonicity of the definedness component. -/
def encoderOps_preservesMono :
    EncoderOpsInd encoderOps MonoE where
  call_ind := encoderOps_call_monoE
  ite_ind := encoderOps_ite_monoE
  error_ind := True.intro

/-! ## Body Encoding -/

/-- Encode a function body using the solver-facing defined/value presentation. -/
def encodeBody (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x _res : TinyML.Var) (e : Typed.Expr) :
    Except String DefVal :=
  let Γ' := Relation.ctx Γ f fn
  let Δ' := defvalBodySig Δ fn x
  encodeWith encoderOps Δ Γ' (VarEnv.ofSignature Δ') e
    (fun v => .ok (DefVal.pure v))

/-- Proof-only binary relation: whenever the split `DefVal` carrier succeeds,
the paired relational carrier succeeds under any name supply covering the
relational signature. -/
def RelSucceedsWhenDef (Γ : FunCtx) :
    Signature → Signature → Env → Env → Rel → Except String DefVal → Prop :=
  fun Δrel Δdef _ _ m d =>
    Δrel.wf → Δdef.wf → Γ.splitWfIn Δdef →
      ∀ s, s.Covers Δrel → ∀ body, d = .ok body → ∃ φ, m s = .ok φ

/-- Call case for `RelSucceedsWhenDef`: split success of the continuation
provides success of the relational continuation under the freshly reserved
witness name. -/
theorem relSucceedsWhenDef_call {Γ : FunCtx}
    {Δrel Δdef : Signature} {ρrel ρdef : Env}
    {f : TinyML.Var} {fn : SpecFn} {argRel argDef : Term .value}
    {kRel : Term .value → Rel} {kDef : Term .value → Except String DefVal}
    (hmem : (f, fn) ∈ Γ)
    (_hargRel : argRel.wfIn Δrel) (hargDef : argDef.wfIn Δdef)
    (_hargEval : Term.eval ρrel argRel = Term.eval ρdef argDef)
    (hk : EncoderContSpec (RelSucceedsWhenDef Γ) Δrel Δdef ρrel ρdef kRel kDef) :
  RelSucceedsWhenDef Γ Δrel Δdef ρrel ρdef
      (Relation.encoderOps.call fn argRel kRel) (encoderOps.call fn argDef kDef) := by
  intro hΔrel hΔdef hΓdef s hcov body hd
  simp only [encoderOps] at hd
  obtain ⟨n, hkn, _hbody⟩ := DefVal.bind_ok hd
  let ctx := freshValueCtx s hΔrel hcov
  have hcallWf : (fn.call argDef).wfIn Δdef :=
    SpecFn.call_wfIn (hΓdef f fn hmem).1 hΔdef hargDef
  let w := (fn.call argDef).eval ρdef
  have hagRel : Env.agreeOn Δrel ρrel (ρrel.updateConst .value ctx.r w) :=
    Env.agreeOn_update_fresh_const (c := ⟨ctx.r, .value⟩) ctx.fresh
  have heval :
      Term.eval (ρrel.updateConst .value ctx.r w) (Term.var .value ctx.r) =
        Term.eval ρdef (fn.call argDef) := by
    simp [Term.eval, Env.lookupConst_updateConst_same, w]
  have hcont :=
    hk ctx.subset (Signature.Subset.refl Δdef) ctx.wf hΔdef
      hagRel Env.agreeOn_refl
      (Term.var .value ctx.r) (fn.call argDef) ctx.var_wf hcallWf heval
  obtain ⟨φ, hφ⟩ := hcont ctx.wf hΔdef hΓdef ctx.s' ctx.covers n hkn
  exact ⟨.exists_ ctx.r .value (.and (fn.relates argRel (.var .value ctx.r)) φ), by
    change (Rel.call fn argRel kRel) s =
      .ok (.exists_ ctx.r .value (.and (fn.relates argRel (.var .value ctx.r)) φ))
    simp only [Rel.call]
    rw [← ctx.hr, ← ctx.hs', hφ]
    rfl⟩

/-- Conditional case for `RelSucceedsWhenDef`: if the split conditional
succeeds, both split branches succeeded, so both relational branches can be
run at the same supply. -/
theorem relSucceedsWhenDef_ite {Γ : FunCtx}
    {Δrel Δdef : Signature} {ρrel ρdef : Env}
    {condRel condDef : Term .bool} {thenRel elseRel : Rel}
    {thenDef elseDef : Except String DefVal}
    (_hcondEval : Term.eval ρrel condRel = Term.eval ρdef condDef)
    (ht : RelSucceedsWhenDef Γ Δrel Δdef ρrel ρdef thenRel thenDef)
    (he : RelSucceedsWhenDef Γ Δrel Δdef ρrel ρdef elseRel elseDef) :
  RelSucceedsWhenDef Γ Δrel Δdef ρrel ρdef
      (Relation.encoderOps.ite condRel thenRel elseRel)
      (encoderOps.ite condDef thenDef elseDef) := by
  intro hΔrel hΔdef hΓdef s hcov body hd
  obtain ⟨dt, de, htDef, heDef, _⟩ := encoderOps_ite_ok hd
  obtain ⟨φt, hφt⟩ := ht hΔrel hΔdef hΓdef s hcov dt htDef
  obtain ⟨φe, hφe⟩ := he hΔrel hΔdef hΓdef s hcov de heDef
  exact ⟨Formula.iteBool condRel φt φe, by
    simp [Relation.encoderOps, Rel.ite, hφt, hφe, bind, Except.bind]⟩

/-- Operation-level data used by `encodeWith_bind_binary` to recover
relational body success from split body success. -/
def relSucceedsWhenDef_ops (Γ : FunCtx) :
    EncoderOpsBinary Γ Relation.encoderOps encoderOps (RelSucceedsWhenDef Γ) where
  call_binary := relSucceedsWhenDef_call
  ite_binary := relSucceedsWhenDef_ite
  error_binary := by
    intro Δrel Δdef ρrel ρdef msg _ _ _ s _ body h
    simp [encoderOps] at h

/-! ## Semantic Infrastructure -/
def semDefined (R : ValRel) (x : Srt.value.denote) : Prop :=
  ∃ y, R x y

/-- The value function induced by a relation: choose an arbitrary related
output when one exists, and Lean's default epsilon value otherwise. -/
noncomputable def semFunc (R : ValRel) (x : Srt.value.denote) : Srt.value.denote :=
  Classical.epsilon (R x)

/-- If the relation is defined at `x`, `semFunc` chooses a related output. -/
theorem semFunc_spec {R : ValRel} {x : Srt.value.denote}
    (h : semDefined R x) : R x (semFunc R x) := by
  unfold semDefined semFunc at *
  exact Classical.epsilon_spec h

/-- Interpret the solver-facing split symbols for a relation name using a
chosen value function `F` and a candidate definedness predicate `D`. -/
def splitEnv (ρ : Env) (fn : SpecFn)
    (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote) : Env :=
  (ρ.updateUnary .value .value (fn.funcName) F).updateUnaryRel .value (fn.defName) D

/-- Combined environment used when comparing one recursive relation with its
split presentation. It interprets the binary relation, value function, and
definedness predicate for `fn` at once. -/
def relSplitEnv (ρ : Env) (fn : SpecFn)
    (R : ValRel) (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote) : Env :=
  ((ρ.updateBinaryRel .value .value fn.relName R).updateUnary .value .value (fn.funcName) F)
    |>.updateUnaryRel .value (fn.defName) D

/-- Environment for evaluating a split encoded body at input `vin`, with
recursive calls interpreted by `D` and `F`. -/
def defEnv (ρ : Env) (fn : SpecFn) (x : String)
    (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote)
    (vin : Srt.value.denote) : Env :=
  (splitEnv ρ fn D F).updateConst .value x vin

/-- The unary body operator induced by the definedness component of a
`DefVal` body under a fixed recursive value function. -/
def defBody (ρ : Env) (fn : SpecFn) (x : String) (body : DefVal)
    (F : Srt.value.denote → Srt.value.denote) :
    (Srt.value.denote → Prop) → Srt.value.denote → Prop :=
  fun D vin => body.defined.eval (defEnv ρ fn x D F vin)

/-- Increasing the candidate definedness predicate increases the corresponding
split environments. -/
theorem splitEnv_le {ρ : Env} {fn : SpecFn}
    {D D' : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hDD' : PredicateFix.le D D') :
    Env.le (splitEnv ρ fn D F) (splitEnv ρ fn D' F) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro τ name a h
    simp only [splitEnv, Env.updateUnaryRel] at h ⊢
    split at h
    · rename_i heq
      rcases heq with ⟨rfl, rfl⟩
      simpa only [Env.updateUnaryRel, dif_pos (And.intro rfl rfl)] using hDD' a h
    · rename_i hne
      simp only [dif_neg hne]
      exact h
  · intro τ₁ τ₂ name a b h
    exact h

/-- The definedness body operator is monotone whenever the encoded body has
monotone definedness. -/
theorem defBody_mono {ρ : Env} {fn : SpecFn} {x : String} {body : DefVal}
    {F : Srt.value.denote → Srt.value.denote}
    (hbody : DefVal.Mono body) :
    PredicateFix.Mono (defBody ρ fn x body F) := by
  intro D D' hDD' vin hdef
  exact hbody (Env.le.updateConst (splitEnv_le (ρ := ρ) (fn := fn)
    (D := D) (D' := D') (F := F) hDD') .value x vin) hdef

/-- Semantic definedness for the split presentation: the least fixpoint of the
encoded definedness condition, interpreted with the value function chosen from
the ground-truth relation. -/
noncomputable def semdef
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Srt.value.denote → Prop :=
  PredicateFix.lfp (defBody ρ fn x body
    (semFunc (semrel Γ Δ ρ f fn x res e)))

/-- Canonical environment for the split presentation extracted from the
ground-truth relation. -/
noncomputable def defInterpEnv
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Env :=
  let R := semrel Γ Δ ρ f fn x res e
  splitEnv ρ fn (semdef Γ Δ ρ f fn x res e body) (semFunc R)

/-- Unfolding principle specialized to a successfully encoded `DefVal` body. -/
theorem semdef_unfold_of_encode
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body)
    (vin : Srt.value.denote) :
    semdef Γ Δ ρ f fn x res e body vin ↔
      defBody ρ fn x body
        (semFunc (semrel Γ Δ ρ f fn x res e))
        (semdef Γ Δ ρ f fn x res e body) vin := by
  unfold semdef
  have hcarrier : MonoE
      (encodeWith encoderOps Δ (Relation.ctx Γ f fn)
        (VarEnv.ofSignature (defvalBodySig Δ fn x)) e
        (fun v => .ok (DefVal.pure v))) :=
    encodeWith_ind encoderOps_preservesMono e
      (by
        intro v
        show MonoE (.ok (DefVal.pure v))
        intro ρ ρ' _ _
        simp [DefVal.pure, Formula.eval])
  have henc' :
      encodeWith encoderOps Δ (Relation.ctx Γ f fn)
        (VarEnv.ofSignature (defvalBodySig Δ fn x)) e
        (fun v => .ok (DefVal.pure v)) = .ok body := by
    simpa [encodeBody] using henc
  rw [henc'] at hcarrier
  have hbodyMono : DefVal.Mono body := hcarrier
  exact PredicateFix.lfp_unfold (defBody_mono (ρ := ρ) (fn := fn) (x := x)
    (body := body) hbodyMono) vin

/-- Under the canonical split interpretation, the definedness symbol denotes
`semdef`. -/
theorem definedCall_eval_defInterpEnv
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (vin : Srt.value.denote) :
    (fn.isDefined (.var .value x)).eval
      ((defInterpEnv Γ Δ ρ f fn x res e body).updateConst .value x vin)
      ↔ semdef Γ Δ ρ f fn x res e body vin := by
  simp [SpecFn.isDefined, SpecFn.isDefined, Formula.eval, UnPred.eval, Term.eval,
    Env.lookupConst_updateConst_same]
  unfold defInterpEnv splitEnv
  simp [Env.updateConst_unaryRel, Env.updateUnaryRel]

/-- Under the canonical split interpretation, the value symbol denotes the
chosen witness function of `semrel`. -/
theorem valueCall_eval_defInterpEnv
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (vin : Srt.value.denote) :
    (fn.call (.var .value x)).eval
      ((defInterpEnv Γ Δ ρ f fn x res e body).updateConst .value x vin)
      =
    semFunc (semrel Γ Δ ρ f fn x res e) vin := by
  simp only [SpecFn.call, SpecFn.call, Term.eval, UnOp.eval, Env.lookupConst_updateConst_same]
  rw [Env.updateConst_unary]
  change ((ρ.updateUnary .value .value (fn.funcName)
    (semFunc (semrel Γ Δ ρ f fn x res e))).unary .value .value (fn.funcName) vin =
      semFunc (semrel Γ Δ ρ f fn x res e) vin)
  simp [Env.updateUnary]


end Skolemize

/-! ## Split Compatibility -/
/-- A binary relational interpretation and the split defined/value symbols
agree for every relation-marked function in the context. -/
def FunCtx.splitCompatible (Γ : FunCtx) (ρ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ x y, fn.evalRelates ρ x y ↔ fn.evalDefined ρ x ∧ fn.evalCall ρ x = y

/-- Completeness half of split compatibility: relational calls imply the
defined/value presentation. This is the half used by relational-to-split
directional proofs. -/
def FunCtx.splitComplete (Γ : FunCtx) (ρ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ x y, fn.evalRelates ρ x y → fn.evalDefined ρ x ∧ fn.evalCall ρ x = y

/-- Soundness half of split compatibility: the defined/value presentation
implies the relational call. This is the half used by split-to-relational
directional proofs. -/
def FunCtx.splitSound (Γ : FunCtx) (ρ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ x y, fn.evalDefined ρ x ∧ fn.evalCall ρ x = y → fn.evalRelates ρ x y

theorem FunCtx.splitComplete_updateConst {Γ : FunCtx} {ρ : Env}
    (hΓ : Γ.splitComplete ρ) (τ : Srt) (x : String) (v : τ.denote) :
    Γ.splitComplete (ρ.updateConst τ x v) := by
  intro f fn hmem a b hcall
  simpa [Env.updateConst_unary, Env.updateConst_unaryRel, Env.updateConst_binaryRel]
    using hΓ f fn hmem a b hcall

theorem FunCtx.splitSound_updateConst {Γ : FunCtx} {ρ : Env}
    (hΓ : Γ.splitSound ρ) (τ : Srt) (x : String) (v : τ.denote) :
    Γ.splitSound (ρ.updateConst τ x v) := by
  intro f fn hmem a b hsplit
  apply hΓ f fn hmem a b
  simpa [Env.updateConst_unary, Env.updateConst_unaryRel] using hsplit

theorem FunCtx.splitSound_of_compatible {Γ : FunCtx} {ρ : Env}
    (hΓ : Γ.splitCompatible ρ) : Γ.splitSound ρ := by
  intro f fn hmem x y hsplit
  exact (hΓ f fn hmem x y).mpr hsplit

/-- The newly introduced relation and split symbols do not collide with the
relation names already present in the tail function context. -/
def FunCtx.freshFn (Γ : FunCtx) (fn : SpecFn) : Prop :=
  ∀ g fn', (g, fn') ∈ Γ →
    fn'.relName ≠ fn.relName ∧ fn'.funcName ≠ fn.funcName ∧ fn'.defName ≠ fn.defName

namespace Skolemize

/-- Extending a split-sound context with a fresh head function preserves split
soundness when the head relation is sound for the chosen split predicate and
value function. -/
theorem splitSound_cons_relSplitEnv
    {Γ : FunCtx} {ρ : Env} {f : TinyML.Var} {fn : SpecFn}
    {R : ValRel} {D : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hΓ : FunCtx.splitSound Γ ρ)
    (hfresh : FunCtx.freshFn Γ fn)
    (hRF : ∀ x y, D x ∧ F x = y → R x y) :
    FunCtx.splitSound ((f, fn) :: Γ) (relSplitEnv ρ fn R D F) := by
  intro g fn' hmem x y hsplit
  cases hmem with
  | head =>
      have hsplit' : D x ∧ F x = y := by
        simpa [SpecFn.evalDefined, SpecFn.evalCall, SpecFn.defined, SpecFn.func,
          relSplitEnv, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel]
          using hsplit
      simpa [SpecFn.evalRelates, SpecFn.rel, relSplitEnv,
        Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel]
        using hRF x y hsplit'
  | tail _ htail =>
      have hnames := hfresh g fn' htail
      have hsplit' : fn'.evalDefined ρ x ∧ fn'.evalCall ρ x = y := by
        simpa [SpecFn.evalDefined, SpecFn.evalCall, SpecFn.defined, SpecFn.func,
          relSplitEnv, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel,
          hnames.1, hnames.2.1, hnames.2.2] using hsplit
      simpa [SpecFn.evalRelates, SpecFn.rel, relSplitEnv,
        Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel,
        hnames.1, hnames.2.1, hnames.2.2] using hΓ g fn' htail x y hsplit'


/-! ### Body-signature transport helpers -/

theorem encodeBody_def_bodySig {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body) :
    encodeWith encoderOps Δ (Relation.ctx Γ f fn)
      (VarEnv.ofSignature (bodySig Δ fn x)) e
      (fun v => .ok (DefVal.pure v)) = .ok body := by
  unfold encodeBody at henc
  have hvars :
      VarEnv.ofSignature (bodySig Δ fn x) =
        VarEnv.ofSignature (defvalBodySig Δ fn x) := by
    simp [VarEnv.ofSignature, bodySig, defvalBodySig, Signature.declVar,
      Signature.addBinaryRel, Signature.addUnary, Signature.addUnaryRel,
      Signature.remove, Signature.addVar]
  rw [hvars]
  simpa [encodeBody] using henc

/-! ### Freshness and signature infrastructure -/

/-- Freshness assumptions for the common Skolemization signature, in the exact
order in which `sig` introduces the head relation symbols and bound variables. -/
structure HeadFresh (Δ : Signature) (fn : SpecFn) (x res : String) : Prop where
  relFresh : fn.relName ∉ Δ.allNames
  funFresh :
    fn.funcName ∉ (Δ.addBinaryRel fn.rel).allNames
  defFresh :
    fn.defName ∉
    ((Δ.addBinaryRel fn.rel).addUnary fn.func).allNames
  argFresh :
    x ∉
    (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
      (fn.defined)).allNames
  resFresh :
    res ∉
    ((((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
      (fn.defined)).declVar ⟨x, .value⟩).allNames

/-! ### Subset lemmas -/

theorem relBase_subset_bodyBase {Δ : Signature} {fn : SpecFn} :
    (Δ.addBinaryRel fn.rel).Subset
      (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
        (fn.defined)) :=
  (Signature.Subset.subset_addUnary _ fn.func).trans
    (Signature.Subset.subset_addUnaryRel _ (fn.defined))

theorem subset_bodySig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    Δ.Subset (bodySig Δ fn x) := by
  unfold bodySig
  exact
    (((Signature.Subset.subset_addBinaryRel Δ fn.rel).trans
      (Signature.Subset.subset_addUnary _ fn.func)).trans
      (Signature.Subset.subset_addUnaryRel _ (fn.defined))).trans
      (Signature.subset_declVar_of_fresh (Δ :=
        (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
          (fn.defined))) (v := ⟨x, .value⟩) hfresh.argFresh)

theorem subset_relBodySig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    Δ.Subset (Relation.bodySig Δ fn x) := by
  unfold Relation.bodySig
  exact (Signature.Subset.subset_addBinaryRel Δ fn.rel).trans
    (Signature.subset_declVar_of_fresh (Δ := Δ.addBinaryRel fn.rel)
      (v := ⟨x, .value⟩) (by
        intro h
        exact hfresh.argFresh (Signature.allNames_subset
          (relBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)))

theorem splitBase_subset_bodyBase {Δ : Signature} {fn : SpecFn} :
    ((Δ.addUnary fn.func).addUnaryRel (fn.defined)).Subset
      (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
        (fn.defined)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha => List.mem_cons_of_mem _ ha⟩ <;>
    intro a ha <;>
    simpa [Signature.addUnary, Signature.addUnaryRel, Signature.addBinaryRel] using ha

theorem relBodySig_subset_bodySig {Δ : Signature} {fn : SpecFn} {x : String} :
    (Relation.bodySig Δ fn x).Subset (bodySig Δ fn x) := by
  unfold Relation.bodySig bodySig
  exact Signature.Subset.declVar relBase_subset_bodyBase ⟨x, .value⟩

theorem defvalBodySig_subset_bodySig {Δ : Signature} {fn : SpecFn} {x : String} :
    (defvalBodySig Δ fn x).Subset (bodySig Δ fn x) := by
  unfold defvalBodySig bodySig
  exact Signature.Subset.declVar splitBase_subset_bodyBase ⟨x, .value⟩

theorem subset_defvalBodySig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    Δ.Subset (defvalBodySig Δ fn x) := by
  unfold defvalBodySig
  exact ((Signature.Subset.subset_addUnary Δ fn.func).trans
    (Signature.Subset.subset_addUnaryRel _ (fn.defined))).trans
    (Signature.subset_declVar_of_fresh (Δ :=
      ((Δ.addUnary fn.func).addUnaryRel (fn.defined)))
      (v := ⟨x, .value⟩) (by
        intro h
        exact hfresh.argFresh (Signature.allNames_subset
          (splitBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)))

theorem bodySig_subset_sig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    (bodySig Δ fn x).Subset (sig Δ fn x res) := by
  unfold sig
  exact Signature.subset_declVar_of_fresh (Δ := bodySig Δ fn x) (v := ⟨res, .value⟩)
    (by simpa [bodySig] using hfresh.resFresh)

theorem relBodySig_subset_relSig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    (Relation.bodySig Δ fn x).Subset (Relation.sig Δ fn x res) := by
  unfold Relation.sig
  exact Signature.subset_declVar_of_fresh (Δ := Relation.bodySig Δ fn x) (v := ⟨res, .value⟩)
    (by
      intro h
      exact hfresh.resFresh (Signature.allNames_subset
        (relBodySig_subset_bodySig (Δ := Δ) (fn := fn) (x := x)) _ h))

/-! ### Well-formedness lemmas -/

theorem bodySig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (bodySig Δ fn x).wf := by
  unfold bodySig
  have hrel :
      (Δ.addBinaryRel fn.rel).wf :=
    Signature.wf_addBinaryRel hΔ hfresh.relFresh
  have hfun :
      ((Δ.addBinaryRel fn.rel).addUnary fn.func).wf :=
    Signature.wf_addUnary hrel hfresh.funFresh
  have hdef :
      (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
        (fn.defined)).wf :=
    Signature.wf_addUnaryRel hfun hfresh.defFresh
  exact Signature.wf_declVar hdef

theorem relBodySig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (Relation.bodySig Δ fn x).wf := by
  unfold Relation.bodySig
  exact Signature.wf_declVar (Signature.wf_addBinaryRel hΔ hfresh.relFresh)

theorem var_fresh_splitBase_of_headFresh
    {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    x ∉ ((Δ.addUnary fn.func).addUnaryRel (fn.defined)).allNames := by
  intro h
  exact hfresh.argFresh (Signature.allNames_subset
    (splitBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)

theorem res_fresh_defvalBodySig_of_headFresh
    {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    res ∉ (defvalBodySig Δ fn x).allNames := by
  intro h
  exact hfresh.resFresh (Signature.allNames_subset
    (defvalBodySig_subset_bodySig (Δ := Δ) (fn := fn) (x := x)) _ h)

theorem splitEnv_relSplitEnv_agreeOn_splitBase
    {Δ : Signature} {ρ : Env} {fn : SpecFn} {x res : String}
    {R : ValRel} {D : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hfresh : HeadFresh Δ fn x res) :
    Env.agreeOn ((Δ.addUnary fn.func).addUnaryRel (fn.defined))
      (splitEnv ρ fn D F) (relSplitEnv ρ fn R D F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 6
    intro _ _
    simp [splitEnv, relSplitEnv, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel]
  intro b hb
  have hbΔ : b ∈ Δ.binaryRel := by
    simpa [Signature.addUnary, Signature.addUnaryRel] using hb
  have hne : b.name ≠ fn.relName := fun h =>
    hfresh.relFresh (h ▸ Signature.mem_allNames_of_binaryRel hbΔ)
  simp [splitEnv, relSplitEnv, Env.updateBinaryRel, Env.updateUnary,
    Env.updateUnaryRel, hne]

/-- The split-only body signature is well-formed under the existing head
freshness assumptions. -/
theorem defvalBodySig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (defvalBodySig Δ fn x).wf := by
  unfold defvalBodySig
  exact Signature.wf_declVar
    (Signature.wf_addUnaryRel
      (Signature.wf_addUnary hΔ (fun h =>
        hfresh.funFresh (Signature.allNames_subset
          (Signature.Subset.subset_addBinaryRel Δ fn.rel) _ h)))
      (fun h =>
        hfresh.defFresh (Signature.allNames_subset
          (by
            constructor <;> intro a ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · exact List.mem_cons_of_mem _ ha) _ h)))

theorem sig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (sig Δ fn x res).wf := by
  unfold sig
  exact Signature.wf_declVar (bodySig_wf_of_headFresh hΔ hfresh)

/-! ### Freshness derivations -/

theorem freshFn_of_headFresh {Γ : FunCtx} {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΓ : Γ.wfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    FunCtx.freshFn Γ fn := by
  intro g fn' hmem
  have hrel'_mem : fn'.relName ∈ Δ.allNames :=
    Signature.mem_allNames_of_binaryRel (hΓ.rel g fn' hmem)
  have hfun_mem : (fn').funcName ∈ Δ.allNames :=
    Signature.mem_allNames_of_unary (hΓ.split g fn' hmem).1
  have hdef_mem : (fn').defName ∈ Δ.allNames :=
    Signature.mem_allNames_of_unaryRel (hΓ.split g fn' hmem).2
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hfresh.relFresh (h ▸ hrel'_mem)
  · intro h
    exact hfresh.funFresh (h ▸ Signature.allNames_subset
      (Signature.Subset.subset_addBinaryRel Δ fn.rel) _ hfun_mem)
  · intro h
    exact hfresh.defFresh (h ▸ Signature.allNames_subset
      ((Signature.Subset.subset_addBinaryRel Δ fn.rel).trans
        (Signature.Subset.subset_addUnary _ fn.func)) _ hdef_mem)


theorem ctx_relWfIn_relSig_of_headFresh
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var}
    (hΓfn : Γ.relWfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    (Relation.ctx Γ f fn).relWfIn (Relation.sig Δ fn x res) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      have hxFresh :
          x ∉ (Δ.addBinaryRel fn.rel).allNames := by
        intro h
        exact hfresh.argFresh (Signature.allNames_subset
          (relBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)
      exact (relBodySig_subset_relSig_of_headFresh hfresh).binaryRel _
        (by
          unfold Relation.bodySig
          exact (Signature.subset_declVar_of_fresh
            (Δ := Δ.addBinaryRel fn.rel)
            (v := ⟨x, .value⟩) hxFresh).binaryRel _
            (List.Mem.head _))
  | tail _ htail =>
      exact ((subset_relBodySig_of_headFresh hfresh).trans
        (relBodySig_subset_relSig_of_headFresh hfresh)).binaryRel _ (hΓfn g fn' htail)

theorem ctx_splitWfIn_bodySig_of_headFresh
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var}
    (hΓdef : Γ.splitWfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    (Relation.ctx Γ f fn).splitWfIn (bodySig Δ fn x) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      unfold bodySig
      refine ⟨?_, ?_⟩
      · exact Signature.Subset.unary
          ((Signature.Subset.subset_addUnaryRel _ (fn.defined)).trans
            (Signature.subset_declVar_of_fresh (Δ :=
              (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
                (fn.defined))) (v := ⟨x, .value⟩) hfresh.argFresh))
          fn.func (List.Mem.head _)
      · exact Signature.Subset.unaryRel
          (Signature.subset_declVar_of_fresh (Δ :=
            (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
              (fn.defined))) (v := ⟨x, .value⟩) hfresh.argFresh)
          (fn.defined) (List.Mem.head _)
  | tail _ htail =>
      exact FunCtx.splitWfIn_mono hΓdef (subset_bodySig_of_headFresh hfresh) g fn' htail

theorem ctx_splitWfIn_defvalBodySig_of_headFresh
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var}
    (hΓdef : Γ.splitWfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    (Relation.ctx Γ f fn).splitWfIn (defvalBodySig Δ fn x) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      unfold defvalBodySig
      refine ⟨?_, ?_⟩
      · exact Signature.Subset.unary
          ((Signature.Subset.subset_addUnaryRel _ (fn.defined)).trans
            (Signature.subset_declVar_of_fresh (Δ :=
              ((Δ.addUnary fn.func).addUnaryRel (fn.defined)))
              (v := ⟨x, .value⟩) (var_fresh_splitBase_of_headFresh hfresh)))
          fn.func (List.Mem.head _)
      · exact Signature.Subset.unaryRel
          (Signature.subset_declVar_of_fresh (Δ :=
            ((Δ.addUnary fn.func).addUnaryRel (fn.defined)))
            (v := ⟨x, .value⟩) (var_fresh_splitBase_of_headFresh hfresh))
          (fn.defined) (List.Mem.head _)
  | tail _ htail =>
      exact FunCtx.splitWfIn_mono hΓdef (subset_defvalBodySig_of_headFresh hfresh)
        g fn' htail

/-- If the split defined/value body encoder succeeds, the relational body
encoder succeeds too. This keeps `encodeBody` focused on the solver-facing
split encoding while preserving the relational witness needed by semantic
proofs. -/
theorem encodeBody_relEncodeBody {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal}
    (hΔ : Δ.wf) (hΓdef : Γ.splitWfIn Δ) (hheadFresh : HeadFresh Δ fn x res)
    (henc : encodeBody Γ Δ f fn x res e = .ok body) :
    ∃ φ, relEncodeBody Γ Δ f fn x res e = .ok φ := by
  have hΔbody : (bodySig Δ fn x).wf := bodySig_wf_of_headFresh hΔ hheadFresh
  have hΔrelBody : (Relation.bodySig Δ fn x).wf :=
    relBodySig_wf_of_headFresh hΔ hheadFresh
  have hΓbody : (Relation.ctx Γ f fn).splitWfIn (bodySig Δ fn x) :=
    ctx_splitWfIn_bodySig_of_headFresh hΓdef hheadFresh
  have hbinary :
      RelSucceedsWhenDef (Relation.ctx Γ f fn) (Relation.bodySig Δ fn x) (bodySig Δ fn x)
        default default
        (encodeWith Relation.encoderOps Δ (Relation.ctx Γ f fn)
          (VarEnv.ofSignature (bodySig Δ fn x)) e (Relation.kEq res))
        (encodeWith encoderOps Δ (Relation.ctx Γ f fn)
          (VarEnv.ofSignature (bodySig Δ fn x)) e
          (fun v => .ok (DefVal.pure v))) := by
    have hvars :
        VarEnv.ofSignature (bodySig Δ fn x) =
          VarEnv.ofSignature (Relation.bodySig Δ fn x) := by
      simp [VarEnv.ofSignature, bodySig, Relation.bodySig, Signature.declVar,
        Signature.addBinaryRel, Signature.addUnary, Signature.addUnaryRel,
        Signature.remove, Signature.addVar]
    have henv :
        VarEnv.Agree (Relation.bodySig Δ fn x) (bodySig Δ fn x) default default
          (VarEnv.ofSignature (bodySig Δ fn x))
          (VarEnv.ofSignature (bodySig Δ fn x)) := by
      have hself := varEnv_ofSignature_agree_self (ρ := default) hΔrelBody
      have hmono := VarEnv.Agree.mono (Signature.Subset.refl _)
        (relBodySig_subset_bodySig (Δ := Δ) (fn := fn) (x := x))
        hΔrelBody hΔbody Env.agreeOn_refl Env.agreeOn_refl hself
      simpa [hvars] using hmono
    refine encodeWith_bind_binary (δ₁ := VarEnv.ofSignature (bodySig Δ fn x))
      (δ₂ := VarEnv.ofSignature (bodySig Δ fn x))
      (relSucceedsWhenDef_ops (Relation.ctx Γ f fn)) e
      (subset_relBodySig_of_headFresh hheadFresh) (subset_bodySig_of_headFresh hheadFresh)
      hΔrelBody hΔbody Env.agreeOn_refl henv ?_
    · intro Δrel' Δdef' ρrel' ρdef' _ _ _ _ _ _ vrel vdef _ _ _ _ _ _ s _ body' hbody'
      exact ⟨.eq .value vrel (.var .value res), by simp [Relation.kEq]⟩
  have hdefBody :
      encodeWith encoderOps Δ (Relation.ctx Γ f fn)
        (VarEnv.ofSignature (bodySig Δ fn x)) e
        (fun v => .ok (DefVal.pure v)) = .ok body :=
    encodeBody_def_bodySig henc
  have hcov : (relBodySupply Δ fn x res).Covers (bodySig Δ fn x) := by
    intro n hn
    exact relBodySupply_covers_sig Δ fn x res n
      (Signature.allNames_subset (bodySig_subset_sig_of_headFresh hheadFresh) n hn)
  have hcovRel : (relBodySupply Δ fn x res).Covers (Relation.bodySig Δ fn x) := by
    intro n hn
    exact hcov n (Signature.allNames_subset
      (relBodySig_subset_bodySig (Δ := Δ) (fn := fn) (x := x)) n hn)
  obtain ⟨φ, hφ⟩ := hbinary hΔrelBody hΔbody hΓbody
    (relBodySupply Δ fn x res) hcovRel body hdefBody
  have hvars :
      VarEnv.ofSignature (bodySig Δ fn x) =
        VarEnv.ofSignature (Relation.bodySig Δ fn x) := by
    simp [VarEnv.ofSignature, bodySig, Relation.bodySig, Signature.declVar,
      Signature.addBinaryRel, Signature.addUnary, Signature.addUnaryRel,
      Signature.remove, Signature.addVar]
  exact ⟨φ, by simpa [Relation.relEncodeBody, hvars] using hφ⟩

/-- Successful split body encodings are well-formed in the split-only body
signature; the proof-only binary relation is not needed for the `DefVal`
output. -/
theorem encodeBody_wfIn_defvalBodySig
    {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal}
    (hΔ : Δ.wf) (hΓdef : Γ.splitWfIn Δ)
    (hheadFresh : HeadFresh Δ fn x res)
    (henc : encodeBody Γ Δ f fn x res e = .ok body) :
    body.wfIn (defvalBodySig Δ fn x) :=
  encode_wfIn_of_gate e
    (subset_defvalBodySig_of_headFresh hheadFresh)
    (defvalBodySig_wf_of_headFresh hΔ hheadFresh)
    (ctx_splitWfIn_defvalBodySig_of_headFresh hΓdef hheadFresh)
    (by simpa [encodeBody] using henc)

theorem relEnv_relSplitEnv_agreeOn_relSig
    {Δ : Signature} {ρ : Env} {fn : SpecFn} {x res : String}
    {R : ValRel} {D : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hfresh : HeadFresh Δ fn x res) (vin vout : Srt.value.denote) :
    Env.agreeOn (Relation.sig Δ fn x res)
      (Relation.relEnv ρ fn x res R vin vout)
      (((relSplitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) := by
  let ρbin := ρ.updateBinaryRel .value .value fn.relName R
  let ρfun := ρbin.updateUnary .value .value (fn.funcName) F
  have hbase :
      Env.agreeOn (Δ.addBinaryRel fn.rel) ρbin
        (relSplitEnv ρ fn R D F) := by
    have hfun : Env.agreeOn (Δ.addBinaryRel fn.rel) ρbin ρfun := by
      simpa [ρbin, ρfun] using
        (Env.agreeOn_update_fresh_unary (ρ := ρbin) (u := fn.func)
          (f := F) (Δ := Δ.addBinaryRel fn.rel) hfresh.funFresh)
    have hdef :
        Env.agreeOn (Δ.addBinaryRel fn.rel) ρfun
          (relSplitEnv ρ fn R D F) := by
      have hdefFresh : fn.defName ∉ (Δ.addBinaryRel fn.rel).allNames := by
        intro h
        exact hfresh.defFresh (Signature.allNames_subset
          (Signature.Subset.subset_addUnary _ fn.func) _ h)
      simpa [relSplitEnv, ρbin, ρfun] using
        (Env.agreeOn_update_fresh_unaryRel (ρ := ρfun) (u := fn.defined)
          (f := D) (Δ := Δ.addBinaryRel fn.rel) hdefFresh)
    exact Env.agreeOn_trans hfun hdef
  simpa [Relation.relEnv, Relation.sig, Relation.bodySig] using
    (Env.agreeOn_declVar
      (Env.agreeOn_declVar hbase : Env.agreeOn
        ((Δ.addBinaryRel fn.rel).declVar ⟨x, .value⟩)
        ((ρ.updateBinaryRel .value .value fn.relName R).updateConst .value x vin)
        ((relSplitEnv ρ fn R D F).updateConst .value x vin)) :
      Env.agreeOn
        (((Δ.addBinaryRel fn.rel).declVar ⟨x, .value⟩).declVar
          ⟨res, .value⟩)
        (((ρ.updateBinaryRel .value .value fn.relName R).updateConst .value x vin).updateConst
          .value res vout)
        (((relSplitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout))

theorem relEncodeBody_wfIn_relSig
    {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {φ : Formula}
    (hΓfn : Γ.relWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hrelEnc : relEncodeBody Γ Δ f fn x res e = .ok φ) :
    φ.wfIn (Relation.sig Δ fn x res) := by
  set m := encodeWith Relation.encoderOps Δ (Relation.ctx Γ f fn)
      (VarEnv.ofSignature (Relation.bodySig Δ fn x)) e (Relation.kEq res) with hm_def
  have hrun : m (relBodySupply Δ fn x res) = .ok φ := by
    simpa [Relation.relEncodeBody, hm_def] using hrelEnc
  have hsigWf : (Relation.sig Δ fn x res).wf := by
    unfold Relation.sig
    exact Signature.wf_declVar (relBodySig_wf_of_headFresh hΔ hheadFresh)
  have hres_mem : (⟨res, .value⟩ : Var) ∈ (Relation.sig Δ fn x res).vars := by
    unfold Relation.sig
    exact Signature.var_mem_declVar (Relation.bodySig Δ fn x) ⟨res, .value⟩
  have hmWf : Relation.Rel.wfIn (Relation.sig Δ fn x res) m :=
    encodeWith_indWithSig Relation.encoderOps_wf e
      ((subset_relBodySig_of_headFresh hheadFresh).trans
        (relBodySig_subset_relSig_of_headFresh hheadFresh))
      hsigWf
      (ctx_relWfIn_relSig_of_headFresh hΓfn hheadFresh)
      (fun y v hlookup =>
        Term.wfIn_mono v ((VarEnv.ofSignature_wfIn
          (relBodySig_wf_of_headFresh hΔ hheadFresh)) y v hlookup)
          (relBodySig_subset_relSig_of_headFresh hheadFresh) hsigWf)
      (Relation.kEq_wfCont hres_mem)
  have hcov : (relBodySupply Δ fn x res).Covers (Relation.sig Δ fn x res) := by
    intro n hn
    exact relBodySupply_covers_sig Δ fn x res n
      (Signature.allNames_subset
        (by
          unfold Relation.sig sig
          exact Signature.Subset.declVar relBodySig_subset_bodySig ⟨res, .value⟩)
        n hn)
  exact hmWf (Relation.sig Δ fn x res) (relBodySupply Δ fn x res) φ
    (Signature.Subset.refl _) hsigWf hcov hrun

/-- `splitEnv` (extended with `x ↦ vin`) and `relSplitEnv` (extended with
`x ↦ vin, res ↦ vout`) agree on the split-only body signature. The body's
value and definedness depend only on this signature, so both transport
proofs reduce to this fact. -/
theorem splitEnv_relSplitEnv_agreeOn_defvalBodySig
    {Δ : Signature} {ρ : Env} {fn : SpecFn} {x res : String}
    {R : ValRel} {D : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hfresh : HeadFresh Δ fn x res)
    (vin vout : Srt.value.denote) :
    Env.agreeOn (defvalBodySig Δ fn x)
      ((splitEnv ρ fn D F).updateConst .value x vin)
      (((relSplitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) := by
  have hagX :
      Env.agreeOn (defvalBodySig Δ fn x)
        ((splitEnv ρ fn D F).updateConst .value x vin)
        ((relSplitEnv ρ fn R D F).updateConst .value x vin) :=
    Env.agreeOn_declVar (splitEnv_relSplitEnv_agreeOn_splitBase hfresh)
  have hagRes :
      Env.agreeOn (defvalBodySig Δ fn x)
        ((relSplitEnv ρ fn R D F).updateConst .value x vin)
        (((relSplitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) :=
    Env.agreeOn_update_fresh_const (c := ⟨res, .value⟩)
      (res_fresh_defvalBodySig_of_headFresh hfresh)
  exact Env.agreeOn_trans hagX hagRes

/-- Evaluating the relational body formula in the combined `relSplitEnv` is
equivalent to the abstract semantic body operator. -/
theorem rel_body_eval_iff
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {φ : Formula} {R : ValRel}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (hΓrel : Γ.relWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hrelEnc : relEncodeBody Γ Δ f fn x res e = .ok φ)
    (vin vout : Srt.value.denote) :
    φ.eval (((relSplitEnv ρ fn R D F).updateConst .value x vin).updateConst
        .value res vout) ↔
      Relation.semanticBody Formula.sem ρ fn x res φ R vin vout := by
  have hφwf : φ.wfIn (Relation.sig Δ fn x res) :=
    relEncodeBody_wfIn_relSig hΓrel hΔ hheadFresh hrelEnc
  have hag :=
    relEnv_relSplitEnv_agreeOn_relSig (Δ := Δ) (ρ := ρ) (fn := fn)
      (x := x) (res := res) (R := R) (D := D) (F := F) hheadFresh vin vout
  unfold Relation.semanticBody Formula.sem
  exact (Formula.eval_env_agree hφwf hag).symm

end Skolemize
end Verifier.RelationalEncoding
