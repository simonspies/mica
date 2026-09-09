-- SUMMARY: The pieces the run-time and ghost compilation layers share: individual TinyML constructs and the shape of their correctness statements.
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.Typing
import Mica.TinyML.OpSem
import Mica.Verifier.Bindings
import Mica.Verifier.Monad
import Mica.Verifier.Assertions

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Typed

/-! ## Construct Compilation

The pieces every compilation layer needs, whichever judgement it targets:
lifting an operator to a term, destructuring a product into fresh constants, and
reading the components of a sum. None of them looks at the spatial state, which
is what lets a layer targeting an entailment reuse them unchanged. -/

/-! ### Operation semantics and SMT translation -/

/-- Lift a `TinyML.BinOp` to operate on `Term .value`, using `toInt`/`toBool`/`ofInt`/`ofBool`.
    Returns `none` for ops that are not (yet) supported. -/
def compileOp (op : TinyML.BinOp) (sl sr : Term .value) : Option (Term .value) :=
  let i t := Term.unop UnOp.toInt  t
  let b t := Term.unop UnOp.toBool t
  match op with
  | .add  => some (Term.unop .ofInt  (Term.binop .add  (i sl) (i sr)))
  | .sub  => some (Term.unop .ofInt  (Term.binop .sub  (i sl) (i sr)))
  | .mul  => some (Term.unop .ofInt  (Term.binop .mul  (i sl) (i sr)))
  -- Division and modulo are handled directly in `compile` with a non-zero divisor
  -- assertion, so they do not go through `compileOp`.
  | .div  => none
  | .mod  => none
  | .eq   => some (Term.unop .ofBool (Term.binop .eq   (i sl) (i sr)))
  | .lt   => some (Term.unop .ofBool (Term.binop .less (i sl) (i sr)))
  | .le   => some (Term.unop .ofBool (Term.binop .ge   (i sr) (i sl)))
  | .gt   => some (Term.unop .ofBool (Term.binop .gt   (i sl) (i sr)))
  | .ge   => some (Term.unop .ofBool (Term.binop .ge   (i sl) (i sr)))
  | .and  => some (Term.unop .ofBool (Term.ite (b sl) (b sr) (.const (.b false))))
  | .or   => some (Term.unop .ofBool (Term.ite (b sl) (.const (.b true)) (b sr)))

def compileUnop (op : TinyML.UnOp) (s : Term .value) : Option (Term .value) :=
  let i t := Term.unop UnOp.toInt  t
  let b t := Term.unop UnOp.toBool t
  match op with
  | .neg => some (Term.unop .ofInt  (Term.unop .neg (i s)))
  | .not => some (Term.unop .ofBool (Term.unop .not (b s)))
  | .proj n => some (.unop .vhead (vtailN (.unop .toValList s) n))

omit [MicaGS HasLC.hasLC Sig] in
theorem compileUnop_wfIn {op : TinyML.UnOp} {s : Term .value} {Δ : Signature}
    (hs : s.wfIn Δ) {t : Term .value} (heq : compileUnop op s = some t) :
    t.wfIn Δ := by
  cases op <;> simp [compileUnop] at heq <;> subst heq <;>
    simp only [Term.wfIn, UnOp.wfIn, true_and]
  all_goals first | exact hs | (have : (Term.unop UnOp.toValList s).wfIn _ := ⟨trivial, hs⟩; exact vtailN_wfIn this _)

omit [MicaGS HasLC.hasLC Sig] in
theorem compileUnop_eval {op : TinyML.UnOp} {s : Term .value} {ρ : Env}
    {v w : Runtime.Val} {t : Term .value}
    (hs : s.eval ρ = v) (heval : TinyML.evalUnOp op v = some w)
    (hcomp : compileUnop op s = some t) :
    t.eval ρ = w := by
  subst hs
  cases op with
  | proj n =>
    simp only [compileUnop, Option.some.injEq] at hcomp; subst hcomp
    cases h : s.eval ρ <;> simp_all [TinyML.evalUnOp]
    exact vhead_vtailN_eval heval _ ρ (by simp [Term.eval, UnOp.eval, h])
  | neg | not =>
    simp only [compileUnop, Option.some.injEq] at hcomp
    subst hcomp
    cases h : s.eval ρ <;>
    simp_all [TinyML.evalUnOp, Term.eval, UnOp.eval]

omit [MicaGS HasLC.hasLC Sig] in
theorem compileOp_wfIn {op : TinyML.BinOp} {sl sr : Term .value} {Δ : Signature}
    (hl : sl.wfIn Δ) (hr : sr.wfIn Δ) {t : Term .value} (heq : compileOp op sl sr = some t) :
    t.wfIn Δ := by
  cases op <;> simp [compileOp] at heq <;> subst heq <;>
    simp only [Term.wfIn] <;>
    tauto

omit [MicaGS HasLC.hasLC Sig] in
/-- If `evalBinOp op v1 v2 = some w` and the input terms evaluate to `v1`, `v2`,
    then the compiled SMT term evaluates to `w`.
    Pair/store return `none` from `compileOp` so those cases are vacuous via `hcomp`. -/
theorem compileOp_eval {op : TinyML.BinOp} {sl sr : Term .value} {ρ : Env}
    {v1 v2 w : Runtime.Val} {t : Term .value}
    (hsl : sl.eval ρ = v1) (hsr : sr.eval ρ = v2)
    (heval : TinyML.evalBinOp op v1 v2 = some w)
    (hcomp : compileOp op sl sr = some t) :
    t.eval ρ = w := by
  subst hsl hsr
  cases op <;>
    simp only [compileOp, Option.some.injEq] at hcomp <;>
    (try simp at hcomp) <;>
    subst hcomp <;>
    (cases h1 : sl.eval ρ <;> cases h2 : sr.eval ρ) <;>
    simp_all [TinyML.evalBinOp, Term.eval, UnOp.eval, BinOp.eval, Const.denote,
              Bool.cond_eq_ite, ge_iff_le, Bool.beq_eq_decide_eq]


/-! ### Compiler and Top-Level Verifier -/

def compileProductBindersFrom (B : Bindings) (Γ : TinyML.TyCtx)
    (names : List Binder) (tys : List TinyML.Typ) (tl : Term .vallist) :
    VerifM (Bindings × TinyML.TyCtx) := do
  match names, tys with
  | [], [] => pure (B, Γ)
  | b :: bs, ty :: tys => do
      VerifM.expectEq "letProd binder type mismatch" b.ty ty
      let si := Term.unop UnOp.vhead tl
      let rest := Term.unop UnOp.vtail tl
      match b.name with
      | none => compileProductBindersFrom B Γ bs tys rest
      | some x =>
          let x' ← VerifM.decl (some x) .value
          VerifM.assume (.pure (Formula.eq .value (.const (.uninterpreted x'.name .value)) si))
          compileProductBindersFrom ((x, x') :: B) (Γ.extend x ty) bs tys rest
  | _, _ => VerifM.fatal "letProd arity mismatch"

def compileProductBinders (B : Bindings) (Γ : TinyML.TyCtx)
    (names : List Binder) (tys : List TinyML.Typ) (se : Term .value) :
    VerifM (Bindings × TinyML.TyCtx) :=
  compileProductBindersFrom B Γ names tys (.unop .toValList se)

omit [MicaGS HasLC.hasLC Sig] in
theorem compileProductBindersFrom_length {B : Bindings} {Γ : TinyML.TyCtx}
    {names : List Binder} {tys : List TinyML.Typ} {tl : Term .vallist}
    {st : TransState} {ρ : Env}
    {Ψ : Bindings × TinyML.TyCtx → TransState → Env → Prop}
    (htl_wf : tl.wfIn st.decls)
    (heval : VerifM.eval (compileProductBindersFrom B Γ names tys tl) st ρ Ψ) :
    names.length = tys.length := by
  induction names generalizing B Γ tys tl st ρ Ψ with
  | nil =>
      cases tys with
      | nil => rfl
      | cons ty tys =>
          simp only [compileProductBindersFrom] at heval
          exact (VerifM.eval_fatal heval).elim
  | cons b bs ih =>
      cases tys with
      | nil =>
          simp only [compileProductBindersFrom] at heval
          exact (VerifM.eval_fatal heval).elim
      | cons ty tys =>
          simp only [compileProductBindersFrom] at heval
          have hexpect := VerifM.eval_bind heval
          obtain ⟨hbty, hcont⟩ := VerifM.eval_expectEq hexpect
          cases hname : b.name with
          | none =>
              simp [hname] at hcont
              have htail_wf : (Term.unop UnOp.vtail tl).wfIn st.decls := ⟨trivial, htl_wf⟩
              simp [ih htail_wf hcont]
          | some x =>
              simp [hname] at hcont
              have hdecl_eval := VerifM.eval_bind hcont
              have hdecl := VerifM.eval_decl hdecl_eval
              let x' := st.freshConst (some x) .value
              have hafter_decl := hdecl ((Term.unop UnOp.vhead tl).eval ρ)
              have hassume := VerifM.eval_assumePure (VerifM.eval_bind hafter_decl)
              have hstwf : st.decls.wf := (VerifM.eval.wf hdecl_eval).namesDisjoint
              have hfresh : x'.name ∉ st.decls.allNames := by
                simpa [x'] using TransState.freshConst_fresh st (some x) .value
              have hhead_wf : (Term.unop UnOp.vhead tl).wfIn st.decls := ⟨trivial, htl_wf⟩
              have htail_wf : (Term.unop UnOp.vtail tl).wfIn st.decls := ⟨trivial, htl_wf⟩
              have hwf :
                  (Formula.eq .value (.const (.uninterpreted x'.name .value))
                    (Term.unop UnOp.vhead tl)).wfIn { st with decls := st.decls.addConst x' }.decls := by
                simpa [x'] using
                  (Formula.eq_wfIn_addConst_of_fresh (Δ := st.decls) (c := x')
                    hstwf hhead_wf hfresh)
              have hholds :
                  (Formula.eq .value (.const (.uninterpreted x'.name .value))
                    (Term.unop UnOp.vhead tl)).eval
                      (ρ.updateConst .value x'.name ((Term.unop UnOp.vhead tl).eval ρ)) := by
                have hagree_head : Env.agreeOn st.decls ρ
                    (ρ.updateConst .value x'.name ((Term.unop UnOp.vhead tl).eval ρ)) :=
                  Env.agreeOn_update_fresh_const hfresh
                have hhead_same := Term.eval_env_agree hhead_wf hagree_head
                simpa [Formula.eval, Term.eval, Const.denote, Env.updateConst]
                  using hhead_same
              have hrec_eval := hassume hwf hholds
              have hsub : st.decls.Subset (st.decls.addConst x') :=
                Signature.Subset.subset_addConst st.decls x'
              have hstwf' : (st.decls.addConst x').wf :=
                Signature.wf_addConst hstwf hfresh
              have htail_wf' : (Term.unop UnOp.vtail tl).wfIn (st.decls.addConst x') :=
                Term.wfIn_mono (Term.unop UnOp.vtail tl) htail_wf hsub hstwf'
              have hlen := ih htail_wf' hrec_eval
              simp [hlen]

/-- Check that a function body's type is its declared return type. Unification
solves the two against each other, so they are equal or the program was rejected
before the verifier saw it. -/
def checkRet (retTy bodyTy : TinyML.Typ) : VerifM Unit :=
  if bodyTy = retTy then pure ()
  else VerifM.fatal "fix: body type does not match the return type"

/-- The components of the sum a type is, unfolding a name exactly once. An
injection's annotation is the name it was declared under, so one step suffices. -/
def sumComponents? (Θ : TinyML.TypeEnv) : TinyML.Typ → Option (List TinyML.Typ)
  | .sum ts => some ts
  | .named T args =>
      match TinyML.TypeName.unfold Θ T args with
      | some (.sum ts) => some ts
      | _ => none
  | _ => none

omit [MicaGS HasLC.hasLC Sig] in
theorem sumComponents?_eq {Θ : TinyML.TypeEnv} {ty : TinyML.Typ} {ts : List TinyML.Typ}
    (h : sumComponents? Θ ty = some ts) :
    ty = .sum ts ∨ ∃ T args, ty = .named T args ∧ TinyML.TypeName.unfold Θ T args = some (.sum ts) := by
  unfold sumComponents? at h
  split at h
  · exact .inl (by simp_all)
  · rename_i T args
    split at h
    · exact .inr ⟨T, args, rfl, by simp_all⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A value of a type is a value of the sum it unfolds to, and back. An injection
uses the second direction and a `match` the first, which is why neither needs a
cast to record the unfolding. -/
theorem valHasType_sumComponents {W : TinyML.World} {v : Runtime.Val} {ty : TinyML.Typ}
    {ts : List TinyML.Typ} (h : sumComponents? W.Θ ty = some ts) :
    TinyML.ValHasType W v ty ⊣⊢ TinyML.ValHasType W v (.sum ts) := by
  rcases sumComponents?_eq h with rfl | ⟨T, args, rfl, hunfold⟩
  · exact .rfl
  · exact TinyML.ValHasType.named_of_unfold hunfold

/-- The components of the sum an injection claims to build, when its annotation
holds up. Checking the annotation here means nothing downstream has to trust the
elaborator. -/
def injComponents? (Θ : TinyML.TypeEnv) (ty : TinyML.Typ) (tag arity : Nat)
    (payloadTy : TinyML.Typ) : Option (List TinyML.Typ) :=
  match sumComponents? Θ ty with
  | some ts => if ts.length = arity ∧ ts[tag]? = some payloadTy then some ts else none
  | none => none

omit [MicaGS HasLC.hasLC Sig] in
theorem injComponents?_eq {Θ : TinyML.TypeEnv} {ty : TinyML.Typ} {tag arity : Nat}
    {payloadTy : TinyML.Typ} {ts : List TinyML.Typ}
    (h : injComponents? Θ ty tag arity payloadTy = some ts) :
    sumComponents? Θ ty = some ts ∧ ts.length = arity ∧ ts[tag]? = some payloadTy := by
  unfold injComponents? at h
  split at h
  · split at h
    · cases h; simp_all
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ### Reshuffling the correctness statement

Both layers carry the same context — the spatial state, the typing of the scope,
and a frame — and both need it rearranged at a bind. -/

namespace Helpers

theorem ctx_dup (W : TinyML.World)
    (G B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : Env) (γg γ : Runtime.Subst) (R : iProp) :
    st.sl W ρ ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢
      st.sl W ρ ∗
        (Bindings.typedScope W G B Γ γg γ ∗
          (Bindings.typedScope W G B Γ γg γ ∗ R)) := by
  iintro ⟨Howns, #HT, HR⟩
  iframe # ∗

theorem ctx_push (W : TinyML.World)
    (G B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : Env) (γg γ : Runtime.Subst) (R : iProp)
    (v : Runtime.Val) (ty : TinyML.Typ) :
    st.sl W ρ ∗ TinyML.ValHasType W v ty ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢
      st.sl W ρ ∗
        (Bindings.typedScope W G B Γ γg γ ∗
          (TinyML.ValHasType W v ty ∗ R)) := by
  iintro ⟨Howns, Hv, #HT, HR⟩
  iframe # ∗

end Helpers
