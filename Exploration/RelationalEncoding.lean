import Mica.FOL.Formulas
import Mica.FOL.Printing
import Mica.TinyML.Typed
import Mica.Base.Fresh

/-
Relational CPS encoding of pure typed TinyML expressions into FOL formulas.

[[ e ]] : (Term .value -> Formula) -> Formula
[[ n ]] k = k(ofInt n)
[[ x ]] k = k(x)
[[ e1 + e2 ]] k = [[ e1 ]] (fun v1 => [[ e2 ]] (fun v2 => k(ofInt (toInt v1 + toInt v2))))
[[ if e1 then e2 else e3 ]] k =
  [[ e1 ]] (fun b => (toBool b = true → [[ e2 ]] k) ∧ (toBool b = false → [[ e3 ]] k))
[[ f e ]] k = [[ e ]] (fun v => ∃ r, funcall(rel_f, v, r) ∧ k(r))

The continuation receives the current `Signature` so it can produce a formula
well-formed under the binders that `encode` introduces.
-/

/-- Uninterpreted relation `rel : value × value → bool` applied to `arg, res`,
encoded as `rel(arg, res) = true`. -/
def Formula.funcall (rel : String) (arg res : Term .value) : Formula :=
  .eq .bool
    (.binop (.uninterpreted rel .value .value .bool) arg res)
    (.const (.b true))

/-- Boolean-conditioned ite at the formula level: requires `cond = true → φ`
and `cond = false → ψ`. -/
def Formula.iteBool (cond : Term .bool) (φ ψ : Formula) : Formula :=
  .and (.implies (.eq .bool cond (.const (.b true)))  φ)
       (.implies (.eq .bool cond (.const (.b false))) ψ)

namespace RelationalEncoding

/-- Maps TinyML function names to FOL relation symbol names. -/
abbrev FunCtx := List (TinyML.Var × String)

def FunCtx.lookup (Γ : FunCtx) (x : TinyML.Var) : Option String :=
  (Γ.find? (·.1 == x)).map (·.2)

/-- Every relation in `Γ` is registered in `Δ` as a binary uninterpreted symbol
of sort `value × value → bool`. -/
def FunCtx.wfIn (Γ : FunCtx) (Δ : Signature) : Prop :=
  ∀ x rel, (x, rel) ∈ Γ → (⟨rel, .value, .value, .bool⟩ : FOL.Binary) ∈ Δ.binary

/-- Encode a TinyML constant into a value-sorted FOL term. -/
def encodeConst : TinyML.Const → Term .value
  | .int  n => .unop .ofInt  (.const (.i n))
  | .bool b => .unop .ofBool (.const (.b b))
  | .unit   => .const .unit

/-- Encode a TinyML unary op acting on a value-sorted argument. -/
def encodeUnOp : TinyML.UnOp → Term .value → Except String (Term .value)
  | .neg,    v => .ok (.unop .ofInt  (.unop .neg (.unop .toInt  v)))
  | .not,    v => .ok (.unop .ofBool (.unop .not (.unop .toBool v)))
  | .proj _, _ => .error "proj: unsupported"

/-- Encode a TinyML binary op acting on two value-sorted arguments. -/
def encodeBinOp : TinyML.BinOp → Term .value → Term .value → Except String (Term .value)
  | .add, a, b => .ok (.unop .ofInt  (.binop .add  (.unop .toInt a) (.unop .toInt b)))
  | .sub, a, b => .ok (.unop .ofInt  (.binop .sub  (.unop .toInt a) (.unop .toInt b)))
  | .mul, a, b => .ok (.unop .ofInt  (.binop .mul  (.unop .toInt a) (.unop .toInt b)))
  | .div, a, b => .ok (.unop .ofInt  (.binop .div  (.unop .toInt a) (.unop .toInt b)))
  | .mod, a, b => .ok (.unop .ofInt  (.binop .mod  (.unop .toInt a) (.unop .toInt b)))
  | .lt,  a, b => .ok (.unop .ofBool (.binop .less (.unop .toInt a) (.unop .toInt b)))
  | .gt,  a, b => .ok (.unop .ofBool (.binop .gt   (.unop .toInt a) (.unop .toInt b)))
  | .ge,  a, b => .ok (.unop .ofBool (.binop .ge   (.unop .toInt a) (.unop .toInt b)))
  | .eq,  a, b => .ok (.unop .ofBool (.binop .eq             a              b))
  | .le,  _, _ => .error "le: unsupported"
  | .and, _, _ => .error "and: unsupported"
  | .or,  _, _ => .error "or: unsupported"

/-- Relational CPS encoding of a pure typed TinyML expression. -/
def encode (Γ : FunCtx) (Δ : Signature) (e : Typed.Expr)
    (k : Signature → Term .value → Except String Formula)
    : Except String Formula :=
  match e with
  | .const c => k Δ (encodeConst c)
  | .var x _ =>
    if (⟨x, .value⟩ : Var) ∈ Δ.vars then
      k Δ (.var .value x)
    else
      .error s!"unbound variable: {x}"
  | .unop op e _ =>
    encode Γ Δ e (fun Δ' v => do
      let v' ← encodeUnOp op v
      k Δ' v')
  | .binop op e1 e2 _ =>
    encode Γ Δ e1 (fun Δ' v1 =>
      encode Γ Δ' e2 (fun Δ'' v2 => do
        let v ← encodeBinOp op v1 v2
        k Δ'' v))
  | .ifThenElse c t e _ =>
    encode Γ Δ c (fun Δ' b => do
      let φt ← encode Γ Δ' t k
      let φe ← encode Γ Δ' e k
      .ok (Formula.iteBool (.unop .toBool b) φt φe))
  | .app (.var f _) [arg] _ =>
    match FunCtx.lookup Γ f with
    | none     => .error s!"unknown function: {f}"
    | some rel =>
      encode Γ Δ arg (fun Δ' v =>
        let r   := Fresh.freshName Δ'.allNames "r"
        let Δ'' := Δ'.declVar ⟨r, .value⟩
        do
          let φ ← k Δ'' (.var .value r)
          .ok (.exists_ r .value
                (.and (Formula.funcall rel v (.var .value r)) φ)))
  | .cast e _    => encode Γ Δ e k
  | .app _ _ _   => .error "app: only unary calls to named functions supported"
  | .fix ..      => .error "fix: unsupported"
  | .letIn ..    => .error "letIn: unsupported"
  | .ref _       => .error "ref: unsupported"
  | .deref ..    => .error "deref: unsupported"
  | .store ..    => .error "store: unsupported"
  | .assert _    => .error "assert: unsupported"
  | .tuple _     => .error "tuple: unsupported"
  | .inj ..      => .error "inj: unsupported"
  | .match_ ..   => .error "match: unsupported"

/-! ## Well-formedness -/

theorem encodeConst_wfIn (c : TinyML.Const) (Δ : Signature) :
    (encodeConst c).wfIn Δ := by
  cases c <;> simp [encodeConst, Term.wfIn, UnOp.wfIn, Const.wfIn]

theorem encodeUnOp_wfIn {op : TinyML.UnOp} {v v' : Term .value} {Δ : Signature}
    (h : encodeUnOp op v = .ok v') (hv : v.wfIn Δ) : v'.wfIn Δ := by
  cases op with
  | neg =>
    simp only [encodeUnOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, trivial, hv⟩
  | not =>
    simp only [encodeUnOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, trivial, hv⟩
  | proj _ => simp [encodeUnOp] at h

theorem encodeBinOp_wfIn {op : TinyML.BinOp} {v1 v2 v : Term .value} {Δ : Signature}
    (h : encodeBinOp op v1 v2 = .ok v) (h1 : v1.wfIn Δ) (h2 : v2.wfIn Δ) :
    v.wfIn Δ := by
  cases op
  case add | sub | mul | div | mod | lt | gt | ge =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, ⟨trivial, h1⟩, ⟨trivial, h2⟩⟩
  case eq =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, h1, h2⟩
  case le | and | or => simp [encodeBinOp] at h

theorem funcall_wfIn {rel : String} {arg res : Term .value} {Δ : Signature}
    (hrel : (⟨rel, .value, .value, .bool⟩ : FOL.Binary) ∈ Δ.binary)
    (harg : arg.wfIn Δ) (hres : res.wfIn Δ) :
    (Formula.funcall rel arg res).wfIn Δ := by
  simp [Formula.funcall, Formula.wfIn, Term.wfIn, BinOp.wfIn, Const.wfIn,
        hrel, harg, hres]

theorem iteBool_wfIn {cond : Term .bool} {φ ψ : Formula} {Δ : Signature}
    (hc : cond.wfIn Δ) (hφ : φ.wfIn Δ) (hψ : ψ.wfIn Δ) :
    (Formula.iteBool cond φ ψ).wfIn Δ := by
  simp [Formula.iteBool, Formula.wfIn, Term.wfIn, Const.wfIn, hc, hφ, hψ]

theorem FunCtx.wfIn_mono {Γ : FunCtx} {Δ Δ' : Signature}
    (h : Γ.wfIn Δ) (hsub : Δ.Subset Δ') : Γ.wfIn Δ' :=
  fun x rel hxr => hsub.binary _ (h x rel hxr)

theorem var_value_wfIn {x : String} {Δ : Signature}
    (hΔ : Δ.wf) (hmem : (⟨x, .value⟩ : Var) ∈ Δ.vars) :
    (Term.var .value x).wfIn Δ := by
  refine ⟨hmem, ?_, ?_⟩
  · intro τ' hc; exact Signature.wf_no_const_of_var hΔ hmem hc
  · intro τ' hv; exact Signature.wf_unique_var hΔ hmem hv

theorem subset_declVar_of_fresh {Δ : Signature} {v : Var}
    (hfresh : v.name ∉ Δ.allNames) : Δ.Subset (Δ.declVar v) := by
  have heq : Δ.declVar v = Δ.addVar v := by
    show (Δ.remove v.name).addVar v = Δ.addVar v
    rw [Signature.remove_eq_of_not_in hfresh]
  rw [heq]; exact Signature.Subset.subset_addVar Δ v

theorem var_mem_declVar (Δ : Signature) (v : Var) : v ∈ (Δ.declVar v).vars :=
  List.Mem.head _

/-- Predicate: the continuation `k` produces a wf formula at any extension of `Δ`. -/
def WfCont (Γ : FunCtx) (Δ : Signature)
    (k : Signature → Term .value → Except String Formula) : Prop :=
  ∀ Δ' t ψ, Δ.Subset Δ' → Δ'.wf → Γ.wfIn Δ' → t.wfIn Δ' →
            k Δ' t = .ok ψ → ψ.wfIn Δ'

/-- Main well-formedness theorem. -/
theorem encode_wfIn {Γ : FunCtx} (Δ : Signature) (e : Typed.Expr)
    (k : Signature → Term .value → Except String Formula)
    {φ : Formula}
    (hΔ : Δ.wf) (hΓ : Γ.wfIn Δ) (hk : WfCont Γ Δ k)
    (henc : encode Γ Δ e k = .ok φ) : φ.wfIn Δ := by
  induction Δ, e, k using encode.induct (Γ := Γ) generalizing φ
  -- const
  case _ Δ k c =>
    rw [encode] at henc
    exact hk Δ _ _ (Signature.Subset.refl _) hΔ hΓ (encodeConst_wfIn c Δ) henc
  -- var, in vars
  case _ Δ k x ty hmem =>
    rw [encode, if_pos hmem] at henc
    exact hk Δ _ _ (Signature.Subset.refl _) hΔ hΓ (var_value_wfIn hΔ hmem) henc
  -- var, not in vars
  case _ Δ k x ty hmem =>
    rw [encode, if_neg hmem] at henc
    cases henc
  -- unop
  case _ Δ k op e ty ih =>
    rw [encode] at henc
    refine ih hΔ hΓ ?_ henc
    intro Δ' v ψ hsub hΔ' hΓ' hv hbind
    simp [bind, Except.bind] at hbind
    split at hbind
    · cases hbind
    · rename_i v' hu
      exact hk Δ' v' ψ hsub hΔ' hΓ' (encodeUnOp_wfIn hu hv) hbind
  -- binop
  case _ Δ k op e1 e2 ty ih2 ih1 =>
    rw [encode] at henc
    refine ih1 hΔ hΓ ?_ henc
    intro Δ' v1 ψ hsub1 hΔ' hΓ' hv1 hen2
    refine ih2 Δ' v1 hΔ' hΓ' ?_ hen2
    intro Δ'' v2 ψ' hsub2 hΔ'' hΓ'' hv2 hbind
    simp [bind, Except.bind] at hbind
    split at hbind
    · cases hbind
    · rename_i v hb
      have hv1' : v1.wfIn Δ'' := Term.wfIn_mono _ hv1 hsub2 hΔ''
      exact hk Δ'' v ψ' (hsub1.trans hsub2) hΔ'' hΓ''
              (encodeBinOp_wfIn hb hv1' hv2) hbind
  -- ifThenElse
  case _ Δ k c t e ty iht ihe ihc =>
    rw [encode] at henc
    refine ihc hΔ hΓ ?_ henc
    intro Δ' b ψ hsub hΔ' hΓ' hb hpost
    simp [bind, Except.bind] at hpost
    split at hpost
    · cases hpost
    rename_i φt hent
    split at hpost
    · cases hpost
    rename_i φe hene
    cases hpost
    have hk' : WfCont Γ Δ' k := fun Δ'' t ψ hs => hk Δ'' t ψ (hsub.trans hs)
    have hφt := iht Δ' hΔ' hΓ' hk' hent
    have hφe := ihe Δ' hΔ' hΓ' hk' hene
    exact iteBool_wfIn ⟨trivial, hb⟩ hφt hφe
  -- app (.var f _) [arg], lookup = none
  case _ Δ k f ty arg ty' hlk =>
    rw [encode, hlk] at henc
    cases henc
  -- app (.var f _) [arg], lookup = some rel
  case _ Δ k f ty arg ty' rel hlk ih =>
    rw [encode, hlk] at henc
    refine ih hΔ hΓ ?_ henc
    intro Δ' v ψ hsub hΔ' hΓ' hv hpost
    set r   := Fresh.freshName Δ'.allNames "r" with hr_eq
    set Δ'' := Δ'.declVar ⟨r, .value⟩ with hΔ''_eq
    have hfresh : r ∉ Δ'.allNames := Fresh.freshName_not_in_avoid _ _
    have hΔ''wf : Δ''.wf := Signature.wf_declVar hΔ'
    have hsub' : Δ'.Subset Δ'' := subset_declVar_of_fresh hfresh
    have hΓ'' : Γ.wfIn Δ'' := FunCtx.wfIn_mono hΓ' hsub'
    have hv'  : v.wfIn Δ'' := Term.wfIn_mono _ hv hsub' hΔ''wf
    have hrelΔ' : (⟨rel, .value, .value, .bool⟩ : FOL.Binary) ∈ Δ'.binary := by
      have hmem : (f, rel) ∈ Γ := by
        simp only [FunCtx.lookup, Option.map_eq_some_iff] at hlk
        obtain ⟨⟨x', rel'⟩, hfind, hsnd⟩ := hlk
        simp at hsnd; subst hsnd
        have hp := List.find?_some hfind
        simp at hp; subst hp
        exact List.mem_of_find?_eq_some hfind
      exact hΓ' f rel hmem
    have hrelΔ'' := hsub'.binary _ hrelΔ'
    have hvarR : (Term.var .value r).wfIn Δ'' :=
      var_value_wfIn hΔ''wf (var_mem_declVar Δ' ⟨r, .value⟩)
    simp [bind, Except.bind] at hpost
    split at hpost
    · cases hpost
    rename_i φinner hinner
    cases hpost
    have hφinner :=
      hk Δ'' (.var .value r) φinner (hsub.trans hsub') hΔ''wf hΓ'' hvarR hinner
    exact ⟨funcall_wfIn hrelΔ'' hv' hvarR, hφinner⟩
  -- cast
  case _ Δ k e ty ih =>
    rw [encode] at henc
    exact ih hΔ hΓ hk henc
  -- app (catch-all shapes): the encoding hits the catch-all `.app _ _ _ => .error`
  -- since the (.var f _, [arg]) pattern is ruled out by `hne`.
  case _ Δ k fn args ty hne =>
    cases fn <;> simp only [encode] at henc <;> cases henc
  -- fix, letIn, ref, deref, store, assert, tuple, inj, match_
  all_goals (simp only [encode] at henc; cases henc)

/-! ## Relational interpretation of a recursive definition -/

/-- A binary relation on `value.denote`. -/
abbrev ValRel : Type := Srt.value.denote → Srt.value.denote → Prop

/-- Coerce a `Prop`-valued binary relation on `value` to the `Bool`-valued
binary function expected by `Env.binary` for `rel : value × value → bool`,
using classical decidability. -/
noncomputable def ValRel.toBin (R : ValRel) :
    Srt.value.denote → Srt.value.denote → Bool :=
  fun a b => @decide _ (Classical.propDecidable (R a b))

/-- Continuation that pins the produced value to a designated result variable
`r`: `k _ v := v = r`. Used to thread the output of the encoded body. -/
def kPin (r : String) : Signature → Term .value → Except String Formula :=
  fun _ v => .ok (.eq .value v (.var .value r))

/-- Signature extended for encoding the body of `rec f x := e`: adds the input
variable `x : value`, the binary symbol `rel : value × value → bool`, and the
result variable `r : value`. -/
def relSig (Δ : Signature) (rel : String) (x r : TinyML.Var) : Signature :=
  Signature.declVar
    ((Δ.declVar ⟨x, .value⟩).addBinary ⟨rel, .value, .value, .bool⟩)
    ⟨r, .value⟩

/-- Function context extended with `(f, rel)` so recursive calls to `f` resolve
to the FOL binary symbol `rel`. -/
def relCtx (Γ : FunCtx) (f : TinyML.Var) (rel : String) : FunCtx :=
  (f, rel) :: Γ

/-- Fresh result variable name used when encoding the body of a recursive
function, generated from the names already in `Δ`. -/
def freshResult (Δ : Signature) : TinyML.Var :=
  Fresh.freshName Δ.allNames "r"

/-- Encode the body `e` of `rec f x := e` as a closed FOL formula. The caller
supplies the result variable `res`; pick `res := freshResult Δ` for a
canonical choice. Extends `Γ` with `(f, rel)` and `Δ` with `x`, `rel`, `res`. -/
def encodeFunc (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (rel : String) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String Formula :=
  encode (relCtx Γ f rel) (relSig Δ rel x res) e (kPin res)

/-- Environment update used when evaluating the encoded body for `rel f x := e`
on input `vin` and output `vout`: interpret `rel` as `self`, `x` as `vin`, and
`r` as `vout`. -/
noncomputable def relEnv (ρ : Env) (rel : String) (x r : TinyML.Var)
    (self : ValRel) (vin vout : Srt.value.denote) : Env :=
  let ρ1 := ρ.updateBinary .value .value .bool rel self.toBin
  let ρ2 := ρ1.updateConst .value x vin
  ρ2.updateConst .value r vout

/-- The body operator whose least fixpoint is the relation denoted by
`rec f x := e`. Parameterised by the encoded body formula `φ`. -/
def relBody (ρ : Env) (rel : String) (x r : TinyML.Var)
    (φ : Formula) : ValRel → ValRel :=
  fun self vin vout => Formula.eval (relEnv ρ rel x r self vin vout) φ

/-- Impredicative least (pre)fixpoint of an operator on `ValRel`. Equals the
Knaster–Tarski LFP whenever `F` is monotone. -/
def ValRel.lfp (F : ValRel → ValRel) : ValRel :=
  fun vin vout => ∀ S : ValRel, (∀ a b, F S a b → S a b) → S vin vout

/--
Relational interpretation of `rec f x := e` as a binary relation on
`value.denote`. See `relSig`, `relCtx`, `kPin`, `relBody`, `ValRel.lfp` for
the building blocks; on encoding failure the relation is empty.
-/
def relation
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (rel : String) (x res : TinyML.Var) (e : Typed.Expr) :
    ValRel :=
  match encodeFunc Γ Δ f rel x res e with
  | .error _ => fun _ _ => False
  | .ok φ    => ValRel.lfp (relBody ρ rel x res φ)

/-! ## Fixpoint properties of `ValRel.lfp` -/

/-- Pointwise inclusion of relations. -/
def ValRel.le (R S : ValRel) : Prop := ∀ a b, R a b → S a b

/-- Monotone operator on `ValRel`. Stated unbundled to keep proofs explicit. -/
def ValRel.Mono (F : ValRel → ValRel) : Prop :=
  ∀ ⦃S S' : ValRel⦄, ValRel.le S S' → ValRel.le (F S) (F S')

/-- `lfp F` is contained in any prefixed point of `F`. -/
theorem ValRel.lfp_le_of_prefixed {F : ValRel → ValRel} {S : ValRel}
    (h : ValRel.le (F S) S) : ValRel.le (ValRel.lfp F) S :=
  fun _ _ hlfp => hlfp S h

/-- `lfp F` is itself a prefixed point of `F` (assuming `F` is monotone). -/
theorem ValRel.lfp_prefixed {F : ValRel → ValRel} (hmono : ValRel.Mono F) :
    ValRel.le (F (ValRel.lfp F)) (ValRel.lfp F) := by
  intro a b hF S hS
  have hsub : ValRel.le (ValRel.lfp F) S := ValRel.lfp_le_of_prefixed hS
  exact hS a b (hmono hsub a b hF)

/-- `lfp F` is also a postfixed point of `F` (assuming `F` is monotone). -/
theorem ValRel.lfp_postfixed {F : ValRel → ValRel} (hmono : ValRel.Mono F) :
    ValRel.le (ValRel.lfp F) (F (ValRel.lfp F)) := by
  intro a b hlfp
  have hpre : ValRel.le (F (F (ValRel.lfp F))) (F (ValRel.lfp F)) :=
    hmono (ValRel.lfp_prefixed hmono)
  exact hlfp _ hpre

/-- Knaster–Tarski unfolding: `lfp F` equals `F (lfp F)` pointwise, assuming
`F` is monotone. -/
theorem ValRel.lfp_unfold {F : ValRel → ValRel} (hmono : ValRel.Mono F)
    (a b : Srt.value.denote) :
    ValRel.lfp F a b ↔ F (ValRel.lfp F) a b :=
  ⟨ValRel.lfp_postfixed hmono a b, ValRel.lfp_prefixed hmono a b⟩

/-! ## Unfolding lemma for the encoded relation -/

/-- Unfolding for the lfp of `relBody`, assuming the body operator is monotone
(which holds when `φ` mentions `rel` only positively — established separately
from the shape of `encode`'s output). -/
theorem relBody_lfp_unfold {ρ : Env} {rel : String} {x r : TinyML.Var}
    {φ : Formula}
    (hmono : ValRel.Mono (relBody ρ rel x r φ))
    (vin vout : Srt.value.denote) :
    ValRel.lfp (relBody ρ rel x r φ) vin vout ↔
    Formula.eval
      (relEnv ρ rel x r (ValRel.lfp (relBody ρ rel x r φ)) vin vout) φ :=
  ValRel.lfp_unfold hmono vin vout

/-- Unfolding for `relation` itself: under encoding success and monotonicity
of the resulting body operator, the relation equals one step of the body
applied to itself. This is the bridge to soundly admit the recursive function
as a relation to SMT. -/
theorem relation_unfold
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {φ : Formula}
    (henc : encodeFunc Γ Δ f rel x res e = .ok φ)
    (hmono : ValRel.Mono (relBody ρ rel x res φ))
    (vin vout : Srt.value.denote) :
    relation Γ Δ ρ f rel x res e vin vout ↔
    Formula.eval
      (relEnv ρ rel x res (relation Γ Δ ρ f rel x res e) vin vout) φ := by
  have hrel : relation Γ Δ ρ f rel x res e =
      ValRel.lfp (relBody ρ rel x res φ) := by
    unfold relation; rw [henc]
  rw [hrel]
  exact relBody_lfp_unfold hmono vin vout

/-! ## FOL-level defining axiom of the relation -/

/-- The defining axiom of `rec f x := e` as a closed FOL formula:
`∀ x : value. ∀ res : value. rel(x, res) = true ↔ φ`, with `iff` desugared as
two implications. This is the formula that — when added to the SMT context
with `rel` interpreted as `relation`'s denotation — soundly admits the
recursive function as a relation. -/
def relAxiom (rel : String) (x res : TinyML.Var) (φ : Formula) : Formula :=
  .forall_ x .value
    (.forall_ res .value
      (.and
        (.implies
          (Formula.funcall rel (.var .value x) (.var .value res)) φ)
        (.implies
          φ (Formula.funcall rel (.var .value x) (.var .value res)))))

/-- Soundness of the defining axiom: under any `ρ`, extending `ρ` so that
`rel` is interpreted by `relation`'s denotation makes `relAxiom` evaluate to
true. This gives the unfolding equation needed to admit `f` as the FOL
relation `rel` for SMT. -/
theorem relAxiom_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {φ : Formula}
    (hxres : x ≠ res)
    (henc : encodeFunc Γ Δ f rel x res e = .ok φ)
    (hmono : ValRel.Mono (relBody ρ rel x res φ)) :
    Formula.eval
      (ρ.updateBinary .value .value .bool rel
        (relation Γ Δ ρ f rel x res e).toBin)
      (relAxiom rel x res φ) := by
  set R : ValRel := relation Γ Δ ρ f rel x res e with hR
  simp only [relAxiom, Formula.eval]
  intro vx vres
  -- The env we end up evaluating the body under after both `forall_`s.
  set env : Env :=
    ((ρ.updateBinary .value .value .bool rel R.toBin).updateConst
      .value x vx).updateConst .value res vres with henv
  -- Compute the `funcall` side: it reduces to `R vx vres`.
  have hcall :
      (Formula.funcall rel (.var .value x) (.var .value res)).eval env
      ↔ R vx vres := by
    have hbinary : env.binary = (ρ.updateBinary .value .value .bool rel
                                    R.toBin).binary := by
      simp [henv, Env.updateConst_binary]
    have hres : env.lookupConst .value res = vres := by
      simp [henv]
    have hx : env.lookupConst .value x = vx := by
      simp [henv, Env.lookupConst_updateConst_ne hxres]
    simp only [Formula.funcall, Formula.eval, Term.eval, BinOp.eval,
               Const.denote, hbinary, hres, hx]
    show (((ρ.updateBinary .value .value .bool rel R.toBin).binary
            .value .value .bool rel) vx vres = true) ↔ R vx vres
    simp only [Env.updateBinary]
    show (R.toBin vx vres = true) ↔ R vx vres
    simp [ValRel.toBin]
  -- Evaluating φ under our env equals `relBody … R …` definitionally.
  have hbody : φ.eval env = relBody ρ rel x res φ R vx vres := rfl
  -- Apply the lfp unfolding via `relation_unfold`.
  have hunfold : R vx vres ↔ relBody ρ rel x res φ R vx vres :=
    relation_unfold henc hmono vx vres
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hbody]; exact hunfold.mp (hcall.mp h)
  · exact hcall.mpr (hunfold.mpr (hbody ▸ h))

/-! ## Example: encoding the body of `fib` -/

namespace Example

open Typed (Expr)
open TinyML

/-- `n - k` for an `Int`-typed variable `n` and literal `k`. -/
private def subLit (n : TinyML.Var) (k : Int) : Expr :=
  .binop .sub (.var n .int) (.const (.int k)) .int

/-- `fib (n - k)` as a typed application. -/
private def fibCall (n : TinyML.Var) (k : Int) : Expr :=
  .app (.var "fib" (.arrow .int .int)) [subLit n k] .int

/--
Body of `let rec fib n = if n < 2 then n else fib (n-1) + fib (n-2)`.
-/
def fibBody : Expr :=
  .ifThenElse
    (.binop .lt (.var "n" .int) (.const (.int 2)) .bool)
    (.var "n" .int)
    (.binop .add (fibCall "n" 1) (fibCall "n" 2) .int)
    .int

/-- Function context: `fib` is encoded as the relation `fib_rel`. -/
def Γfib : FunCtx := [("fib", "fib_rel")]

/-- Signature with `n : value` and `fib_rel : value × value → bool`. -/
def Δfib : Signature :=
  ((Signature.empty.addVar ⟨"n", .value⟩).addBinary
    ⟨"fib_rel", .value, .value, .bool⟩)

/-- Continuation that equates the produced value with a fresh `result` variable. -/
def kResult : Signature → Term .value → Except String Formula :=
  fun _ v => .ok (.eq .value v (.var .value "result"))

/-- Encoded fib body. -/
def fibEncoding : Except String Formula :=
  encode Γfib Δfib fibBody kResult

/-- Pretty-printed form of the encoded fib body. -/
def fibEncodingStr : String :=
  match fibEncoding with
  | .ok φ    => φ.toStringHum
  | .error e => s!"error: {e}"

#eval fibEncodingStr

end Example

end RelationalEncoding
