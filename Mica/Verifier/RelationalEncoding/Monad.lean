-- SUMMARY: Generic monadic skeleton for TinyML-to-FOL encoders.
import Mica.FOL.Formulas
import Mica.FOL.Fixpoint
import Mica.TinyML.Typed
import Mica.Base.Fresh
import Mica.Verifier.RelationalEncoding.Variables

/-!
# Generic monadic skeleton for TinyML-to-FOL encoders

An *encoder* is parameterized by a carrier `M` together with three operations
(`call`, `ite`, `error`) packaged as `EncoderOps M`. Error handling lives in
`M`: every failure path goes through `ops.error`. The traversal
is in continuation-passing style: every leaf hands its value term to the
continuation; `call` consumes a continuation explicitly; for `ite` the
continuation is pushed into both branches before they are combined.

Three generic induction principles are proved once:

* **plain induction** — `encodeWith_ind`, for any carrier-side predicate
  closed under the operations (`EncoderOpsInd`);
* **signature-indexed induction** — `encodeWith_indWithSig`, for any
  signature-indexed carrier predicate closed under the operations
  (`EncoderOpsSig`). Well-formedness is the canonical instance, but
  determinism in a designated result variable is another;
* **paired-encoding binary** — `encodeWith_bind_binary`, lifting an
  operation-level binary relation between two encoders (`EncoderOpsBinary`)
  to their full traversals.
-/

namespace Verifier.RelationalEncoding

/-! ## Per-operation encoders for constants and primitives -/

/-- Encode a TinyML constant into a value-sorted FOL term. -/
def encodeConst : TinyML.Const → Term .value
  | .int  n => .unop .ofInt  (.const (.i n))
  | .bool b => .unop .ofBool (.const (.b b))
  | .unit   => .const .unit

/-- Encode a TinyML unary op acting on a value-sorted argument. -/
def encodeUnOp : TinyML.UnOp → Term .value → Except String (Term .value)
  | .neg,    v => .ok (.unop .ofInt  (.unop .neg (.unop .toInt  v)))
  | .not,    v => .ok (.unop .ofBool (.unop .not (.unop .toBool v)))
  | .proj n, v => .ok (.unop .vhead (vtailN (.unop .toValList v) n))

/-- Encode a TinyML binary op acting on two value-sorted arguments. -/
def encodeBinOp : TinyML.BinOp → Term .value → Term .value → Except String (Term .value)
  | .add, a, b => .ok (.unop .ofInt  (.binop .add  (.unop .toInt a) (.unop .toInt b)))
  | .sub, a, b => .ok (.unop .ofInt  (.binop .sub  (.unop .toInt a) (.unop .toInt b)))
  | .mul, a, b => .ok (.unop .ofInt  (.binop .mul  (.unop .toInt a) (.unop .toInt b)))
  | .div, a, b => .ok (.unop .ofInt  (.binop .div  (.unop .toInt a) (.unop .toInt b)))
  | .mod, a, b => .ok (.unop .ofInt  (.binop .mod  (.unop .toInt a) (.unop .toInt b)))
  | .lt,  a, b => .ok (.unop .ofBool (.binop .less (.unop .toInt a) (.unop .toInt b)))
  | .le,  a, b => .ok (.unop .ofBool (.binop .ge   (.unop .toInt b) (.unop .toInt a)))
  | .gt,  a, b => .ok (.unop .ofBool (.binop .gt   (.unop .toInt a) (.unop .toInt b)))
  | .ge,  a, b => .ok (.unop .ofBool (.binop .ge   (.unop .toInt a) (.unop .toInt b)))
  | .eq,  a, b => .ok (.unop .ofBool (.binop .eq             a              b))
  | .and, a, b => .ok (.unop .ofBool (.ite (.unop .toBool a) (.unop .toBool b) (.const (.b false))))
  | .or,  a, b => .ok (.unop .ofBool (.ite (.unop .toBool a) (.const (.b true)) (.unop .toBool b)))

/-! ## Well-formedness lemmas for primitive encoders -/

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
  | proj n =>
    simp only [encodeUnOp, Except.ok.injEq] at h; subst h
    have ht : (vtailN (.unop .toValList v) n).wfIn Δ := by
      apply vtailN_wfIn
      change UnOp.toValList.wfIn Δ ∧ v.wfIn Δ
      exact ⟨trivial, hv⟩
    change UnOp.vhead.wfIn Δ ∧ (vtailN (.unop .toValList v) n).wfIn Δ
    exact ⟨trivial, ht⟩

theorem encodeBinOp_wfIn {op : TinyML.BinOp} {v1 v2 v : Term .value} {Δ : Signature}
    (h : encodeBinOp op v1 v2 = .ok v) (h1 : v1.wfIn Δ) (h2 : v2.wfIn Δ) :
    v.wfIn Δ := by
  cases op
  case add | sub | mul | div | mod | lt | gt | ge =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, ⟨trivial, h1⟩, ⟨trivial, h2⟩⟩
  case le =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, ⟨trivial, h2⟩, ⟨trivial, h1⟩⟩
  case eq =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, h1, h2⟩
  case and =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    change UnOp.ofBool.wfIn Δ ∧
      (Term.ite (.unop .toBool v1) (.unop .toBool v2) (.const (.b false))).wfIn Δ
    exact ⟨trivial, ⟨⟨trivial, h1⟩, ⟨trivial, h2⟩, trivial⟩⟩
  case or =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    change UnOp.ofBool.wfIn Δ ∧
      (Term.ite (.unop .toBool v1) (.const (.b true)) (.unop .toBool v2)).wfIn Δ
    exact ⟨trivial, ⟨⟨trivial, h1⟩, trivial, ⟨trivial, h2⟩⟩⟩

/-! ## Generic encoder operations -/

/-- Generic operations needed to encode a TinyML expression in
continuation-passing style. The shared traversal `encodeWith`
pattern-matches on the syntax and delegates everything else to these.

* `call` encodes a unary call to a relation-marked function, threading the
  result through the continuation;
* `ite` combines two branches — each already obtained by encoding under the
  outer continuation — into a single carrier guarded by a boolean;
* `error` produces a failure carrier with the given message. Concrete carriers
  decide what "failure" means (e.g. an `Except`-valued thunk, or a top-level
  `Except`). -/
structure EncoderOps (M : Type) where
  call  : String → Term .value → (Term .value → M) → M
  ite   : Term .bool → M → M → M
  error : String → M

mutual
/-- Shared structural traversal of a typed TinyML expression in
continuation-passing style, parametric in the encoder operations. The only
place that pattern-matches on `Typed.Expr`. Errors are reported via
`ops.error`; the traversal itself is total in `M`. -/
def encodeWith {M : Type} (ops : EncoderOps M)
    (Γ : FunCtx) (δ : VarEnv) : Typed.Expr → (Term .value → M) → M
  | .const c, k => k (encodeConst c)
  | .var x _, k =>
    match δ.lookup x with
    | some v => k v
    | none => ops.error s!"unbound variable: {x}"
  | .unop op e _, k =>
    encodeWith ops Γ δ e fun v =>
      match encodeUnOp op v with
      | .ok v'    => k v'
      | .error msg => ops.error msg
  | .binop op e1 e2 _, k =>
    encodeWith ops Γ δ e1 fun v1 =>
      encodeWith ops Γ δ e2 fun v2 =>
        match encodeBinOp op v1 v2 with
        | .ok v     => k v
        | .error msg => ops.error msg
  | .ifThenElse c t e _, k =>
    encodeWith ops Γ δ c fun b =>
      ops.ite (.unop .toBool b) (encodeWith ops Γ δ t k) (encodeWith ops Γ δ e k)
  | .tuple es, k =>
    encodeListWith ops Γ δ es fun vs =>
      k (.unop .ofValList (Terms.toValList vs))
  | .app (.var f _) [arg] _, k =>
    match FunCtx.lookup Γ f with
    | none     => ops.error s!"unknown function: {f}"
    | some rel =>
      encodeWith ops Γ δ arg fun v => ops.call rel v k
  | .cast e _, k  => encodeWith ops Γ δ e k
  | .letIn b bound body, k =>
    encodeWith ops Γ δ bound fun v =>
      encodeWith ops Γ (VarEnv.bindBinder δ b v) body k
  | .inj tag arity payload, k =>
    encodeWith ops Γ δ payload fun v =>
      k (.unop (.mkInj tag arity) v)
  | .match_ scrut branches _, k =>
    encodeWith ops Γ δ scrut fun v =>
      encodeMatchWith ops Γ δ v branches 0 k
  | .app _ _ _, _ => ops.error "relational encoding: only unary calls to named top-level functions are supported"
  | .fix .., _    => ops.error "relational encoding: nested `fix` is not supported"
  | .ref .., _    => ops.error "relational encoding: heap allocation (`ref`) is not supported"
  | .deref .., _  => ops.error "relational encoding: heap dereference is not supported"
  | .store .., _  => ops.error "relational encoding: heap store is not supported"
  | .assert _, _  => ops.error "relational encoding: `assert` is not supported"

/-- Encode a list of expressions left-to-right, collecting their value terms.
This is the list companion to `encodeWith`, needed by tuple syntax and later
other n-ary constructs. -/
def encodeListWith {M : Type} (ops : EncoderOps M)
    (Γ : FunCtx) (δ : VarEnv) : List Typed.Expr → (List (Term .value) → M) → M
  | [], k => k []
  | e :: es, k =>
    encodeWith ops Γ δ e fun v =>
      encodeListWith ops Γ δ es fun vs => k (v :: vs)

/-- Encode a `match_` as an if-let chain. For each non-final branch
`(b, body)` at index `i`, the carrier tests whether the scrutinee
value's tag equals `i`; on the true branch the binder is bound to the
payload projection before encoding `body`; on the false branch the
remaining branches are tried. The final branch is dispatched
unconditionally — the elaborator guarantees an exhaustive list, so the
trailing case must hold. An empty list (which the elaborator never
produces) is conservatively encoded as `ops.error`. -/
def encodeMatchWith {M : Type} (ops : EncoderOps M)
    (Γ : FunCtx) (δ : VarEnv) (scrut : Term .value) :
    List (Typed.Binder × Typed.Expr) → Nat → (Term .value → M) → M
  | [], _, _ => ops.error "match: non-exhaustive"
  | (b, body) :: rest, i, k =>
    let δ' := VarEnv.bindBinder δ b (.unop .payloadOf scrut)
    match rest with
    | [] => encodeWith ops Γ δ' body k
    | _ :: _ =>
      ops.ite
        (.binop .eq (.unop .tagOf scrut) (.const (.i (i : Int))))
        (encodeWith ops Γ δ' body k)
        (encodeMatchWith ops Γ δ scrut rest (i + 1) k)
end

/-! ## Semantic interpretation of carriers

A semantic predicate `sem : M → Env → Prop` explains how a carrier is
interpreted in an environment. Downstream constructions (e.g. the relational
encoder's least fixpoint) use these notions on top of the traversal. -/

/-- Semantic interpretation of an encoded carrier in an environment. -/
abbrev SemPred (M : Type) := M → Env → Prop

/-- A carrier is monotone when its semantic interpretation is stable under
`Fix.Env.le`. -/
def SemanticMono {M : Type} (sem : SemPred M) (m : M) : Prop :=
  ∀ {ρ ρ' : Env}, Fix.Env.le ρ ρ' → sem m ρ → sem m ρ'

/-! ## Generic carrier predicates

Some properties of encodings are independent of signatures and function-context
well-formedness. `EncoderOpsInd` packages per-operation preservation of
an arbitrary carrier predicate; `encodeWith_ind` lifts those assumptions
through the shared traversal. -/

/-- Per-operation preservation assumptions for an arbitrary carrier predicate. -/
structure EncoderOpsInd {M : Type} (ops : EncoderOps M) (P : M → Prop) where
  /-- Calls preserve the predicate when their continuation does. -/
  call_ind : ∀ {rel arg k},
    (∀ v, P (k v)) → P (ops.call rel arg k)
  /-- Conditionals preserve the predicate when both branches do. -/
  ite_ind : ∀ {cond t e},
    P t → P e → P (ops.ite cond t e)
  /-- The error carrier satisfies the predicate. -/
  error_ind : ∀ {msg}, P (ops.error msg)

/-- Per-expression statement of `encodeWith_ind`. -/
def EncodeWithInd (e : Typed.Expr) : Prop :=
  ∀ {M : Type} {ops : EncoderOps M} {P : M → Prop}
    {Γ : FunCtx} {δ : VarEnv} {k : Term .value → M},
    EncoderOpsInd ops P → (∀ v, P (k v)) →
    P (encodeWith ops Γ δ e k)

/-- Per-list statement of `encodeWith_ind`. -/
def EncodeListWithInd (es : List Typed.Expr) : Prop :=
  ∀ {M : Type} {ops : EncoderOps M} {P : M → Prop}
    {Γ : FunCtx} {δ : VarEnv} {k : List (Term .value) → M},
    EncoderOpsInd ops P → (∀ vs, P (k vs)) →
    P (encodeListWith ops Γ δ es k)

/-- Per-branch-list statement of `encodeWith_ind`, mirroring `EncodeWithInd`
but parametric in the scrutinee value and the index offset. -/
def EncodeMatchWithInd (branches : List (Typed.Binder × Typed.Expr)) : Prop :=
  ∀ {M : Type} {ops : EncoderOps M} {P : M → Prop}
    {Γ : FunCtx} {δ : VarEnv} {scrut : Term .value} {i : Nat}
    {k : Term .value → M},
    EncoderOpsInd ops P → (∀ v, P (k v)) →
    P (encodeMatchWith ops Γ δ scrut branches i k)

/-! ## Per-case helpers for `encodeWith_ind` -/

namespace Ind

theorem const (c : TinyML.Const) : EncodeWithInd (.const c) := by
  intro _ _ _ _ _ _ _ hk; simp only [encodeWith]; exact hk _

theorem var (x : String) (ty : TinyML.Typ) : EncodeWithInd (.var x ty) := by
  intro _ _ _ _ δ _ hops hk
  cases hlookup : δ.lookup x with
  | none => simp only [encodeWith, hlookup]; exact hops.error_ind
  | some v => simp only [encodeWith, hlookup]; exact hk v

theorem unop (op : TinyML.UnOp) (e : Typed.Expr) (ty : TinyML.Typ)
    (ih : EncodeWithInd e) : EncodeWithInd (.unop op e ty) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]
  refine ih hops ?_
  intro v
  cases encodeUnOp op v with
  | error _ => simp; exact hops.error_ind
  | ok _    => simp; exact hk _

theorem binop (op : TinyML.BinOp) (e1 e2 : Typed.Expr) (ty : TinyML.Typ)
    (ih1 : EncodeWithInd e1) (ih2 : EncodeWithInd e2) :
    EncodeWithInd (.binop op e1 e2 ty) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]
  refine ih1 hops ?_
  intro v1
  refine ih2 hops ?_
  intro v2
  cases encodeBinOp op v1 v2 with
  | error _ => simp; exact hops.error_ind
  | ok _    => simp; exact hk _

theorem ifThenElse (c t e : Typed.Expr) (ty : TinyML.Typ)
    (ihc : EncodeWithInd c) (iht : EncodeWithInd t) (ihe : EncodeWithInd e) :
    EncodeWithInd (.ifThenElse c t e ty) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]
  refine ihc hops ?_
  intro _
  exact hops.ite_ind (iht hops hk) (ihe hops hk)

theorem app (fn : Typed.Expr) (args : List Typed.Expr) (ty : TinyML.Typ)
    (ihArgs : ∀ a ∈ args, EncodeWithInd a) : EncodeWithInd (.app fn args ty) := by
  intro _ _ _ Γ _ _ hops hk
  match fn, args with
  | .var f _, [arg] =>
      simp only [encodeWith]
      cases FunCtx.lookup Γ f with
      | none => exact hops.error_ind
      | some _ =>
          simp only
          refine ihArgs arg (List.mem_singleton.mpr rfl) hops ?_
          intro _
          exact hops.call_ind hk
  | .const _, _ | .unop .., _ | .binop .., _ | .fix .., _ | .app .., _
  | .ifThenElse .., _ | .letIn .., _ | .ref .., _ | .deref .., _ | .store .., _
  | .assert _, _ | .tuple _, _ | .inj .., _ | .match_ .., _ | .cast .., _
  | .var _ _, [] | .var _ _, _ :: _ :: _ =>
      simp only [encodeWith]; exact hops.error_ind

theorem cast (e : Typed.Expr) (ty : TinyML.Typ) (ih : EncodeWithInd e) :
    EncodeWithInd (.cast e ty) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]; exact ih hops hk

theorem fix (self : Typed.Binder) (args : List Typed.Binder) (retTy : TinyML.Typ)
    (body : Typed.Expr) : EncodeWithInd (.fix self args retTy body) :=
  fun hops _ => hops.error_ind

theorem letIn (name : Typed.Binder) (bound body : Typed.Expr)
    (ihBound : EncodeWithInd bound) (ihBody : EncodeWithInd body) :
    EncodeWithInd (.letIn name bound body) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]
  exact ihBound hops fun _ => ihBody hops hk

theorem ref (owned : Bool) (e : Typed.Expr) : EncodeWithInd (.ref owned e) :=
  fun hops _ => hops.error_ind

theorem deref (e : Typed.Expr) (ty : TinyML.Typ) : EncodeWithInd (.deref e ty) :=
  fun hops _ => hops.error_ind

theorem store (loc val : Typed.Expr) : EncodeWithInd (.store loc val) :=
  fun hops _ => hops.error_ind

theorem assert (e : Typed.Expr) : EncodeWithInd (.assert e) :=
  fun hops _ => hops.error_ind

theorem tuple (es : List Typed.Expr) (ih : EncodeListWithInd es) :
    EncodeWithInd (.tuple es) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]
  exact ih hops (fun vs => hk (.unop .ofValList (Terms.toValList vs)))

theorem inj (tag arity : Nat) (payload : Typed.Expr)
    (ih : EncodeWithInd payload) : EncodeWithInd (.inj tag arity payload) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]
  refine ih hops ?_
  intro v; exact hk _

theorem match_ (scrut : Typed.Expr) (branches : List (Typed.Binder × Typed.Expr))
    (ty : TinyML.Typ) (ihScrut : EncodeWithInd scrut)
    (ihBranches : EncodeMatchWithInd branches) :
    EncodeWithInd (.match_ scrut branches ty) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeWith]
  refine ihScrut hops ?_
  intro _; exact ihBranches hops hk

theorem match_nil : EncodeMatchWithInd [] := by
  intro _ _ _ _ _ _ _ _ hops _; simp only [encodeMatchWith]; exact hops.error_ind

theorem match_cons (b : Typed.Binder) (body : Typed.Expr)
    (rest : List (Typed.Binder × Typed.Expr))
    (ihBody : EncodeWithInd body) (ihRest : EncodeMatchWithInd rest) :
    EncodeMatchWithInd ((b, body) :: rest) := by
  intro _ _ _ _ _ _ _ _ hops hk
  simp only [encodeMatchWith]
  cases rest with
  | nil =>
    cases b.name <;> exact ihBody hops hk
  | cons _ _ =>
    refine hops.ite_ind ?_ ?_
    · cases b.name <;> exact ihBody hops hk
    · exact ihRest hops hk

theorem list_nil : EncodeListWithInd [] := by
  intro _ _ _ _ _ _ _ hk; simp only [encodeListWith]; exact hk []

theorem list_cons (e : Typed.Expr) (es : List Typed.Expr)
    (ih : EncodeWithInd e) (ihs : EncodeListWithInd es) :
    EncodeListWithInd (e :: es) := by
  intro _ _ _ _ _ _ hops hk
  simp only [encodeListWith]
  refine ih hops ?_
  intro v
  refine ihs hops ?_
  intro vs
  exact hk (v :: vs)

end Ind

mutual
/-- Generic preservation theorem for the shared traversal: under per-operation
preservation assumptions, every encoded expression yields a carrier satisfying
the predicate. -/
theorem encodeWith_ind_def : ∀ (e : Typed.Expr), EncodeWithInd e
  | .const c => Ind.const c
  | .var x ty => Ind.var x ty
  | .unop op e ty => Ind.unop op e ty (encodeWith_ind_def e)
  | .binop op e1 e2 ty =>
      Ind.binop op e1 e2 ty (encodeWith_ind_def e1) (encodeWith_ind_def e2)
  | .ifThenElse c t e ty =>
      Ind.ifThenElse c t e ty (encodeWith_ind_def c)
        (encodeWith_ind_def t) (encodeWith_ind_def e)
  | .app fn args ty =>
      Ind.app fn args ty (fun a _ => encodeWith_ind_def a)
  | .cast e ty => Ind.cast e ty (encodeWith_ind_def e)
  | .fix self args retTy body => Ind.fix self args retTy body
  | .letIn name bound body =>
      Ind.letIn name bound body (encodeWith_ind_def bound) (encodeWith_ind_def body)
  | .ref owned e => Ind.ref owned e
  | .deref e ty => Ind.deref e ty
  | .store loc val => Ind.store loc val
  | .assert e => Ind.assert e
  | .tuple es => Ind.tuple es (encodeListWith_ind_def es)
  | .inj tag arity payload => Ind.inj tag arity payload (encodeWith_ind_def payload)
  | .match_ scrut branches ty =>
      Ind.match_ scrut branches ty
        (encodeWith_ind_def scrut) (encodeMatchWith_ind_def branches)

theorem encodeListWith_ind_def : ∀ (es : List Typed.Expr), EncodeListWithInd es
  | [] => Ind.list_nil
  | e :: es => Ind.list_cons e es (encodeWith_ind_def e) (encodeListWith_ind_def es)

theorem encodeMatchWith_ind_def :
    ∀ (branches : List (Typed.Binder × Typed.Expr)), EncodeMatchWithInd branches
  | [] => Ind.match_nil
  | (b, body) :: rest =>
      Ind.match_cons b body rest (encodeWith_ind_def body)
        (encodeMatchWith_ind_def rest)
end

/-- Compatibility wrapper preserving the original signature. -/
theorem encodeWith_ind {M : Type} {ops : EncoderOps M} {P : M → Prop}
    (hops : EncoderOpsInd ops P)
    {Γ : FunCtx} {δ : VarEnv} (e : Typed.Expr)
    {k : Term .value → M}
    (hk : ∀ v, P (k v)) :
    P (encodeWith ops Γ δ e k) :=
  encodeWith_ind_def e hops hk

/-! ## Signature-indexed induction

Each instance supplies its own signature-indexed carrier predicate `P` and its
own function-context predicate `Pctx`. Given the per-operation assumptions
packaged in `EncoderOpsSig`, the shared traversal preserves `P`. Well-formedness
is the canonical instance; determinism in a designated result variable is
another. -/

/-- Continuation contract for signature-indexed induction: a continuation `k`
takes a value term well-formed in any signature extending `Δ` to a carrier
satisfying `P` in that extension. -/
abbrev SigCont {M : Type} (P : Signature → M → Prop)
    (Δ : Signature) (k : Term .value → M) : Prop :=
  ∀ {Δ'}, Δ.Subset Δ' → Δ'.wf →
    ∀ v, v.wfIn Δ' → P Δ' (k v)

/-- Per-operation closure assumptions for a signature-indexed carrier
predicate `P`, with a function-context predicate `Pctx` for `call`
(instantiated e.g. by `FunCtx.wfIn` for well-formedness, or pinned to a
specific `Γ` for determinism). The shared traversal preserves `P` whenever
`ops` satisfies these (`encodeWith_indWithSig`). -/
structure EncoderOpsSig {M : Type} (ops : EncoderOps M)
    (P : Signature → M → Prop) (Pctx : FunCtx → Signature → Prop) where
  /-- The function-context predicate is stable under signature extension. -/
  ctx_mono : ∀ {Γ Δ Δ'}, Pctx Γ Δ → Δ.Subset Δ' → Pctx Γ Δ'
  /-- A call to a function registered in `Γ` satisfies `P` at `Δ` provided its
  continuation does. -/
  call_ind : ∀ {Γ Δ f rel arg k},
    Δ.wf → Pctx Γ Δ → (f, rel) ∈ Γ → arg.wfIn Δ →
    SigCont P Δ k →
    P Δ (ops.call rel arg k)
  /-- A conditional with a well-formed condition and both branches satisfying
  `P` satisfies `P`. -/
  ite_ind : ∀ {Δ cond t e},
    Δ.wf → cond.wfIn Δ → P Δ t → P Δ e →
    P Δ (ops.ite cond t e)
  /-- The error carrier satisfies `P` at every signature. -/
  error_ind : ∀ {Δ msg}, P Δ (ops.error msg)

/-- Per-expression statement of `encodeWith_indWithSig`. -/
def EncodeWithIndSig (e : Typed.Expr) : Prop :=
  ∀ {M : Type} {ops : EncoderOps M}
    {P : Signature → M → Prop} {Pctx : FunCtx → Signature → Prop}
    {Γ : FunCtx} {Δ Δ' : Signature} {δ : VarEnv} {k : Term .value → M},
    EncoderOpsSig ops P Pctx →
    Δ.Subset Δ' → Δ'.wf → Pctx Γ Δ' → δ.wfIn Δ' →
    SigCont P Δ' k →
    P Δ' (encodeWith ops Γ δ e k)

/-- Per-list statement of `encodeWith_indWithSig`. -/
def EncodeListWithIndSig (es : List Typed.Expr) : Prop :=
  ∀ {M : Type} {ops : EncoderOps M}
    {P : Signature → M → Prop} {Pctx : FunCtx → Signature → Prop}
    {Γ : FunCtx} {Δ Δ' : Signature} {δ : VarEnv} {k : List (Term .value) → M},
    EncoderOpsSig ops P Pctx →
    Δ.Subset Δ' → Δ'.wf → Pctx Γ Δ' → δ.wfIn Δ' →
    (∀ {Δ''}, Δ'.Subset Δ'' → Δ''.wf →
      ∀ vs, (∀ v ∈ vs, v.wfIn Δ'') → P Δ'' (k vs)) →
    P Δ' (encodeListWith ops Γ δ es k)

/-- Per-branch-list statement of `encodeWith_indWithSig`, parametric in the
scrutinee value and starting index. The scrutinee must be well-formed at the
current signature so the tag-check and payload projection are. -/
def EncodeMatchWithIndSig (branches : List (Typed.Binder × Typed.Expr)) : Prop :=
  ∀ {M : Type} {ops : EncoderOps M}
    {P : Signature → M → Prop} {Pctx : FunCtx → Signature → Prop}
    {Γ : FunCtx} {Δ Δ' : Signature} {δ : VarEnv}
    {scrut : Term .value} {i : Nat} {k : Term .value → M},
    EncoderOpsSig ops P Pctx →
    Δ.Subset Δ' → Δ'.wf → Pctx Γ Δ' → δ.wfIn Δ' →
    scrut.wfIn Δ' →
    SigCont P Δ' k →
    P Δ' (encodeMatchWith ops Γ δ scrut branches i k)

/-! ## Per-case helpers for `encodeWith_indWithSig` -/

namespace IndSig

theorem const (c : TinyML.Const) : EncodeWithIndSig (.const c) := by
  intro _ _ _ _ _ _ _ _ _ _ _ hΔ' _ _ hk
  simp only [encodeWith]
  exact hk (Signature.Subset.refl _) hΔ' _ (encodeConst_wfIn c _)

theorem var (x : String) (ty : TinyML.Typ) : EncodeWithIndSig (.var x ty) := by
  intro _ _ _ _ _ _ _ δ _ hops _ hΔ' _ hδ hk
  cases hlookup : δ.lookup x with
  | none => simp only [encodeWith, hlookup]; exact hops.error_ind
  | some v =>
      simp only [encodeWith, hlookup]
      exact hk (Signature.Subset.refl _) hΔ' v (hδ x v hlookup)

theorem unop (op : TinyML.UnOp) (e : Typed.Expr) (ty : TinyML.Typ)
    (ih : EncodeWithIndSig e) : EncodeWithIndSig (.unop op e ty) := by
  intro M ops P Pctx Γ Δ Δ' δ k hops hsub hΔ' hΓ hδ hk
  simp only [encodeWith]
  refine ih hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' v hv
  cases hraw : encodeUnOp op v with
  | error _ => simp [hraw]; exact hops.error_ind
  | ok _ =>
      simp [hraw]
      exact hk hsub'' hΔ'' _ (encodeUnOp_wfIn hraw hv)

theorem binop (op : TinyML.BinOp) (e1 e2 : Typed.Expr) (ty : TinyML.Typ)
    (ih1 : EncodeWithIndSig e1) (ih2 : EncodeWithIndSig e2) :
    EncodeWithIndSig (.binop op e1 e2 ty) := by
  intro _ _ _ _ _ _ _ δ _ hops hsub hΔ' hΓ hδ hk
  simp only [encodeWith]
  refine ih1 hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' v1 hv1
  have hΓ'' := hops.ctx_mono hΓ hsub''
  refine ih2 hops (hsub.trans hsub'') hΔ'' hΓ''
    (fun x v h => Term.wfIn_mono v (hδ x v h) hsub'' hΔ'') ?_
  intro Δ''' hsub''' hΔ''' v2 hv2
  cases hraw : encodeBinOp op v1 v2 with
  | error _ => simp [hraw]; exact hops.error_ind
  | ok _ =>
      simp [hraw]
      have hv1' := Term.wfIn_mono _ hv1 hsub''' hΔ'''
      exact hk (hsub''.trans hsub''') hΔ''' _ (encodeBinOp_wfIn hraw hv1' hv2)

theorem ifThenElse (c t e : Typed.Expr) (ty : TinyML.Typ)
    (ihc : EncodeWithIndSig c) (iht : EncodeWithIndSig t) (ihe : EncodeWithIndSig e) :
    EncodeWithIndSig (.ifThenElse c t e ty) := by
  intro M ops P Pctx Γ Δ Δ' δ k hops hsub hΔ' hΓ hδ hk
  simp only [encodeWith]
  refine ihc hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' b hb
  have hΓ'' := hops.ctx_mono hΓ hsub''
  have hkmono : SigCont P Δ'' k := fun hsub''' hΔ''' v hv =>
    hk (hsub''.trans hsub''') hΔ''' v hv
  have hδ'' : δ.wfIn Δ'' :=
    fun x v h => Term.wfIn_mono v (hδ x v h) hsub'' hΔ''
  have hmtP := iht hops (hsub.trans hsub'') hΔ'' hΓ'' hδ'' hkmono
  have hmeP := ihe hops (hsub.trans hsub'') hΔ'' hΓ'' hδ'' hkmono
  have hbWf : (Term.unop UnOp.toBool b).wfIn Δ'' := ⟨trivial, hb⟩
  exact hops.ite_ind hΔ'' hbWf hmtP hmeP

theorem app (fn : Typed.Expr) (args : List Typed.Expr) (ty : TinyML.Typ)
    (ihArgs : ∀ a ∈ args, EncodeWithIndSig a) : EncodeWithIndSig (.app fn args ty) := by
  intro _ _ _ _ Γ _ _ δ _ hops hsub hΔ' hΓ hδ hk
  match fn, args with
  | .var f _, [arg] =>
      simp only [encodeWith]
      cases hlk : FunCtx.lookup Γ f with
      | none => exact hops.error_ind
      | some _ =>
          simp only
          have hmem := FunCtx.mem_of_lookup hlk
          refine ihArgs arg (List.mem_singleton.mpr rfl) hops hsub hΔ' hΓ hδ ?_
          intro Δ'' hsub'' hΔ'' v hv
          refine hops.call_ind hΔ'' (hops.ctx_mono hΓ hsub'') hmem hv ?_
          intro Δ''' hsub''' hΔ''' v' hv'
          exact hk (hsub''.trans hsub''') hΔ''' v' hv'
  | .const _, _ | .unop .., _ | .binop .., _ | .fix .., _ | .app .., _
  | .ifThenElse .., _ | .letIn .., _ | .ref .., _ | .deref .., _ | .store .., _
  | .assert _, _ | .tuple _, _ | .inj .., _ | .match_ .., _ | .cast .., _
  | .var _ _, [] | .var _ _, _ :: _ :: _ =>
      simp only [encodeWith]; exact hops.error_ind

theorem cast (e : Typed.Expr) (ty : TinyML.Typ) (ih : EncodeWithIndSig e) :
    EncodeWithIndSig (.cast e ty) := by
  intro _ _ _ _ _ _ _ _ _ hops hsub hΔ' hΓ hδ hk
  simpa [encodeWith] using ih hops hsub hΔ' hΓ hδ hk

theorem fix (self : Typed.Binder) (args : List Typed.Binder) (retTy : TinyML.Typ)
    (body : Typed.Expr) : EncodeWithIndSig (.fix self args retTy body) :=
  fun hops _ _ _ _ _ => hops.error_ind

theorem letIn (name : Typed.Binder) (bound body : Typed.Expr)
    (ihBound : EncodeWithIndSig bound) (ihBody : EncodeWithIndSig body) :
    EncodeWithIndSig (.letIn name bound body) := by
  intro _ _ _ _ _ _ _ δ _ hops hsub hΔ' hΓ hδ hk
  simp only [encodeWith]
  refine ihBound hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' v hv
  have hΓ'' := hops.ctx_mono hΓ hsub''
  exact ihBody hops (hsub.trans hsub'') hΔ'' hΓ''
    (VarEnv.wfIn.bindBinder
      (fun y w h => Term.wfIn_mono w (hδ y w h) hsub'' hΔ'') hv)
    (fun hsub''' hΔ''' w hw => hk (hsub''.trans hsub''') hΔ''' w hw)

theorem ref (owned : Bool) (e : Typed.Expr) : EncodeWithIndSig (.ref owned e) :=
  fun hops _ _ _ _ _ => hops.error_ind

theorem deref (e : Typed.Expr) (ty : TinyML.Typ) : EncodeWithIndSig (.deref e ty) :=
  fun hops _ _ _ _ _ => hops.error_ind

theorem store (loc val : Typed.Expr) : EncodeWithIndSig (.store loc val) :=
  fun hops _ _ _ _ _ => hops.error_ind

theorem assert (e : Typed.Expr) : EncodeWithIndSig (.assert e) :=
  fun hops _ _ _ _ _ => hops.error_ind

theorem tuple (es : List Typed.Expr) (ih : EncodeListWithIndSig es) :
    EncodeWithIndSig (.tuple es) := by
  intro _ _ _ _ _ _ _ δ _ hops hsub hΔ' hΓ hδ hk
  simp only [encodeWith]
  refine ih hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' vs hvs
  exact hk hsub'' hΔ'' _ ⟨trivial, Terms.toValList_wfIn hvs⟩

theorem inj (tag arity : Nat) (payload : Typed.Expr)
    (ih : EncodeWithIndSig payload) :
    EncodeWithIndSig (.inj tag arity payload) := by
  intro _ _ _ _ _ _ _ _ _ hops hsub hΔ' hΓ hδ hk
  simp only [encodeWith]
  refine ih hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' v hv
  exact hk hsub'' hΔ'' _ ⟨trivial, hv⟩

theorem match_ (scrut : Typed.Expr) (branches : List (Typed.Binder × Typed.Expr))
    (ty : TinyML.Typ) (ihScrut : EncodeWithIndSig scrut)
    (ihBranches : EncodeMatchWithIndSig branches) :
    EncodeWithIndSig (.match_ scrut branches ty) := by
  intro _ _ _ _ _ _ _ δ k hops hsub hΔ' hΓ hδ hk
  simp only [encodeWith]
  refine ihScrut hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' v hv
  have hΓ'' := hops.ctx_mono hΓ hsub''
  have hδ'' : δ.wfIn Δ'' :=
    fun y w h => Term.wfIn_mono w (hδ y w h) hsub'' hΔ''
  have hkmono : SigCont _ Δ'' k :=
    fun hs hΔ''' v hv => hk (hsub''.trans hs) hΔ''' v hv
  exact ihBranches hops (hsub.trans hsub'') hΔ'' hΓ'' hδ'' hv hkmono

theorem match_nil : EncodeMatchWithIndSig [] := by
  intro _ _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _
  simp only [encodeMatchWith]
  exact hops.error_ind

theorem match_cons (b : Typed.Binder) (body : Typed.Expr)
    (rest : List (Typed.Binder × Typed.Expr))
    (ihBody : EncodeWithIndSig body)
    (ihRest : EncodeMatchWithIndSig rest) :
    EncodeMatchWithIndSig ((b, body) :: rest) := by
  intro _ _ _ _ _ _ Δ' _ scrut _ _ hops hsub hΔ' hΓ hδ hscrut hk
  simp only [encodeMatchWith]
  have hpay : (Term.unop UnOp.payloadOf scrut).wfIn Δ' := ⟨trivial, hscrut⟩
  cases rest with
  | nil => exact ihBody hops hsub hΔ' hΓ (VarEnv.wfIn.bindBinder hδ hpay) hk
  | cons _ _ =>
    exact hops.ite_ind hΔ' ⟨trivial, ⟨trivial, hscrut⟩, trivial⟩
      (ihBody hops hsub hΔ' hΓ (VarEnv.wfIn.bindBinder hδ hpay) hk)
      (ihRest hops hsub hΔ' hΓ hδ hscrut hk)

theorem list_nil : EncodeListWithIndSig [] := by
  intro _ _ _ _ _ _ _ _ _ _ _ hΔ' _ _ hk
  simp only [encodeListWith]
  exact hk (Signature.Subset.refl _) hΔ' [] (by simp)

theorem list_cons (e : Typed.Expr) (es : List Typed.Expr)
    (ih : EncodeWithIndSig e) (ihs : EncodeListWithIndSig es) :
    EncodeListWithIndSig (e :: es) := by
  intro _ _ _ _ Γ Δ Δ' δ k hops hsub hΔ' hΓ hδ hk
  simp only [encodeListWith]
  refine ih hops hsub hΔ' hΓ hδ ?_
  intro Δ'' hsub'' hΔ'' v hv
  have hΓ'' := hops.ctx_mono hΓ hsub''
  refine ihs hops (hsub.trans hsub'') hΔ'' hΓ''
    (fun x v h => Term.wfIn_mono v (hδ x v h) hsub'' hΔ'') ?_
  intro Δ''' hsub''' hΔ''' vs hvs
  have hwfs : ∀ q ∈ v :: vs, q.wfIn Δ''' := by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with hq | hq
    · subst q
      exact Term.wfIn_mono v hv hsub''' hΔ'''
    · exact hvs q hq
  exact hk (hsub''.trans hsub''') hΔ''' (v :: vs) hwfs

end IndSig

mutual
/-- Generic signature-indexed induction theorem for the shared traversal:
under the per-operation closure assumptions in `EncoderOpsSig`, every encoded
expression yields a carrier satisfying `P`. -/
theorem encodeWith_indWithSig_def : ∀ (e : Typed.Expr), EncodeWithIndSig e
  | .const c => IndSig.const c
  | .var x ty => IndSig.var x ty
  | .unop op e ty => IndSig.unop op e ty (encodeWith_indWithSig_def e)
  | .binop op e1 e2 ty =>
      IndSig.binop op e1 e2 ty (encodeWith_indWithSig_def e1) (encodeWith_indWithSig_def e2)
  | .ifThenElse c t e ty =>
      IndSig.ifThenElse c t e ty (encodeWith_indWithSig_def c)
        (encodeWith_indWithSig_def t) (encodeWith_indWithSig_def e)
  | .app fn args ty =>
      IndSig.app fn args ty (fun a _ => encodeWith_indWithSig_def a)
  | .cast e ty => IndSig.cast e ty (encodeWith_indWithSig_def e)
  | .fix self args retTy body => IndSig.fix self args retTy body
  | .letIn name bound body =>
      IndSig.letIn name bound body
        (encodeWith_indWithSig_def bound) (encodeWith_indWithSig_def body)
  | .ref owned e => IndSig.ref owned e
  | .deref e ty => IndSig.deref e ty
  | .store loc val => IndSig.store loc val
  | .assert e => IndSig.assert e
  | .tuple es => IndSig.tuple es (encodeListWith_indWithSig_def es)
  | .inj tag arity payload =>
      IndSig.inj tag arity payload (encodeWith_indWithSig_def payload)
  | .match_ scrut branches ty =>
      IndSig.match_ scrut branches ty
        (encodeWith_indWithSig_def scrut)
        (encodeMatchWith_indWithSig_def branches)

theorem encodeListWith_indWithSig_def : ∀ (es : List Typed.Expr), EncodeListWithIndSig es
  | [] => IndSig.list_nil
  | e :: es =>
      IndSig.list_cons e es (encodeWith_indWithSig_def e) (encodeListWith_indWithSig_def es)

theorem encodeMatchWith_indWithSig_def :
    ∀ (branches : List (Typed.Binder × Typed.Expr)),
      EncodeMatchWithIndSig branches
  | [] => IndSig.match_nil
  | (b, body) :: rest =>
      IndSig.match_cons b body rest
        (encodeWith_indWithSig_def body)
        (encodeMatchWith_indWithSig_def rest)
end

theorem encodeWith_indWithSig {M : Type} {ops : EncoderOps M}
    {P : Signature → M → Prop} {Pctx : FunCtx → Signature → Prop}
    (hops : EncoderOpsSig ops P Pctx)
    {Γ : FunCtx} {Δ Δ' : Signature} {δ : VarEnv} (e : Typed.Expr)
    {k : Term .value → M}
    (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf) (hΓ : Pctx Γ Δ')
    (hδ : δ.wfIn Δ')
    (hk : SigCont P Δ' k) :
    P Δ' (encodeWith ops Γ δ e k) :=
  encodeWith_indWithSig_def e hops hsub hΔ' hΓ hδ hk

/-! ## Generic paired-encoding binary

When two encoders are run on the same TinyML expression, a binary relation `B`
between their carriers can be lifted from operation-level binary data. The
primary theorem is stated in bind position, so recursive continuations remain
in scope throughout the induction. -/

/-- Generic continuation contract for bind-position proofs. The two
continuations are paired by `B` whenever they are fed value terms that are
`Term.eval`-equal in some pair of *future* states extending the base
`(Δ₁, ρ₁)` / `(Δ₂, ρ₂)`. "Future" means the signature only grew
(`Δ.Subset`) and the environment still agrees on the old symbols
(`Env.agreeOn`); the fed terms must be well-formed in the future
signatures. Future quantification is needed because each carrier's `call`
op declares its own fresh symbols as the monad runs, so the two sides may
extend to different signatures. -/
abbrev EncoderContSpec {M₁ M₂ : Type}
    (B : Signature → Signature → Env → Env → M₁ → M₂ → Prop)
    (Δ₁ Δ₂ : Signature) (ρ₁ ρ₂ : Env)
    (k₁ : Term .value → M₁) (k₂ : Term .value → M₂) : Prop :=
  ∀ {Δ₁' Δ₂' : Signature} {ρ₁' ρ₂' : Env},
    Δ₁.Subset Δ₁' → Δ₂.Subset Δ₂' →
    Δ₁'.wf → Δ₂'.wf →
    Env.agreeOn Δ₁ ρ₁ ρ₁' → Env.agreeOn Δ₂ ρ₂ ρ₂' →
    ∀ v₁ v₂,
      v₁.wfIn Δ₁' → v₂.wfIn Δ₂' →
      Term.eval ρ₁' v₁ = Term.eval ρ₂' v₂ →
      B Δ₁' Δ₂' ρ₁' ρ₂' (k₁ v₁) (k₂ v₂)

/-- Weakening of the continuation contract: a contract at base `(Δ₁, ρ₁)` /
`(Δ₂, ρ₂)` restricts to any future state, since futures of the future are
futures of the base. -/
theorem EncoderContSpec.mono {M₁ M₂ : Type}
    {B : Signature → Signature → Env → Env → M₁ → M₂ → Prop}
    {Δ₁ Δ₂ Δ₁' Δ₂' : Signature} {ρ₁ ρ₂ ρ₁' ρ₂' : Env}
    {k₁ : Term .value → M₁} {k₂ : Term .value → M₂}
    (hsub₁ : Δ₁.Subset Δ₁') (hsub₂ : Δ₂.Subset Δ₂')
    (ha₁ : Env.agreeOn Δ₁ ρ₁ ρ₁') (ha₂ : Env.agreeOn Δ₂ ρ₂ ρ₂')
    (hk : EncoderContSpec B Δ₁ Δ₂ ρ₁ ρ₂ k₁ k₂) :
    EncoderContSpec B Δ₁' Δ₂' ρ₁' ρ₂' k₁ k₂ := by
  intro Δ₁'' Δ₂'' ρ₁'' ρ₂'' hs₁ hs₂ hw₁ hw₂ hag₁ hag₂ v₁ v₂ hv₁ hv₂ heval
  exact hk (hsub₁.trans hs₁) (hsub₂.trans hs₂) hw₁ hw₂
    (Env.agreeOn_trans ha₁ (Env.agreeOn_mono hsub₁ hag₁))
    (Env.agreeOn_trans ha₂ (Env.agreeOn_mono hsub₂ hag₂))
    v₁ v₂ hv₁ hv₂ heval

/-- Operation-level binary data for the CPS induction theorem. The relation
`B` is now indexed by the pair of signatures and environments the carriers
are interpreted in. -/
structure EncoderOpsBinary {M₁ M₂ : Type} (Γ : FunCtx)
    (ops₁ : EncoderOps M₁) (ops₂ : EncoderOps M₂)
    (B : Signature → Signature → Env → Env → M₁ → M₂ → Prop) where
  /-- A call to a function registered in `Γ` is related when its (well-formed)
  arguments evaluate equally and its continuations are paired by the
  continuation contract. -/
  call_binary : ∀ {Δ₁ Δ₂ ρ₁ ρ₂ f rel arg₁ arg₂ k₁ k₂}, (f, rel) ∈ Γ →
    arg₁.wfIn Δ₁ → arg₂.wfIn Δ₂ →
    Term.eval ρ₁ arg₁ = Term.eval ρ₂ arg₂ →
    EncoderContSpec B Δ₁ Δ₂ ρ₁ ρ₂ k₁ k₂ →
    B Δ₁ Δ₂ ρ₁ ρ₂ (ops₁.call rel arg₁ k₁) (ops₂.call rel arg₂ k₂)
  /-- Conditionals preserve the binary property when the conditions evaluate
  equally and both branches are related. -/
  ite_binary : ∀ {Δ₁ Δ₂ ρ₁ ρ₂ c₁ c₂ t₁ t₂ e₁ e₂},
    Term.eval ρ₁ c₁ = Term.eval ρ₂ c₂ →
    B Δ₁ Δ₂ ρ₁ ρ₂ t₁ t₂ → B Δ₁ Δ₂ ρ₁ ρ₂ e₁ e₂ →
    B Δ₁ Δ₂ ρ₁ ρ₂ (ops₁.ite c₁ t₁ e₁) (ops₂.ite c₂ t₂ e₂)
  /-- Error carriers are related in every state. -/
  error_binary : ∀ {Δ₁ Δ₂ ρ₁ ρ₂ msg}, B Δ₁ Δ₂ ρ₁ ρ₂ (ops₁.error msg) (ops₂.error msg)

/-- Generic continuation contract for list encodings. It is the list-valued
analogue of `EncoderContSpec`: the continuation may be invoked in any future
state, provided the paired value lists are well-formed and evaluate
pointwise equally. -/
abbrev EncoderListContSpec {M₁ M₂ : Type}
    (B : Signature → Signature → Env → Env → M₁ → M₂ → Prop)
    (Δ₁ Δ₂ : Signature) (ρ₁ ρ₂ : Env)
    (k₁ : List (Term .value) → M₁) (k₂ : List (Term .value) → M₂) : Prop :=
  ∀ {Δ₁' Δ₂' : Signature} {ρ₁' ρ₂' : Env},
    Δ₁.Subset Δ₁' → Δ₂.Subset Δ₂' →
    Δ₁'.wf → Δ₂'.wf →
    Env.agreeOn Δ₁ ρ₁ ρ₁' → Env.agreeOn Δ₂ ρ₂ ρ₂' →
    ∀ vs₁ vs₂,
      (∀ v ∈ vs₁, v.wfIn Δ₁') → (∀ v ∈ vs₂, v.wfIn Δ₂') →
      vs₁.map (fun v => Term.eval ρ₁' v) =
        vs₂.map (fun v => Term.eval ρ₂' v) →
      B Δ₁' Δ₂' ρ₁' ρ₂' (k₁ vs₁) (k₂ vs₂)

/-- Per-expression statement of `encodeWith_bind_binary`. -/
def EncodeWithBindBinary (e : Typed.Expr) : Prop :=
  ∀ {M₁ M₂ : Type} {Γ : FunCtx} {Δ₁ Δ₂ : Signature} {δ₁ δ₂ : VarEnv}
    {ops₁ : EncoderOps M₁} {ops₂ : EncoderOps M₂}
    {B : Signature → Signature → Env → Env → M₁ → M₂ → Prop},
    EncoderOpsBinary Γ ops₁ ops₂ B →
    ∀ {k₁ : Term .value → M₁}
      {Δ₁' Δ₂' : Signature} {ρ₁' ρ₂' : Env} {k₂ : Term .value → M₂},
      Δ₁.Subset Δ₁' → Δ₂.Subset Δ₂' →
      Δ₁'.wf → Δ₂'.wf →
      VarEnv.Agree Δ₁' Δ₂' ρ₁' ρ₂' δ₁ δ₂ →
      EncoderContSpec B Δ₁' Δ₂' ρ₁' ρ₂' k₁ k₂ →
      B Δ₁' Δ₂' ρ₁' ρ₂'
        (encodeWith ops₁ Γ δ₁ e k₁) (encodeWith ops₂ Γ δ₂ e k₂)

/-- Per-list statement of `encodeWith_bind_binary`. -/
def EncodeListWithBindBinary (es : List Typed.Expr) : Prop :=
  ∀ {M₁ M₂ : Type} {Γ : FunCtx} {Δ₁ Δ₂ : Signature} {δ₁ δ₂ : VarEnv}
    {ops₁ : EncoderOps M₁} {ops₂ : EncoderOps M₂}
    {B : Signature → Signature → Env → Env → M₁ → M₂ → Prop},
    EncoderOpsBinary Γ ops₁ ops₂ B →
    ∀ {k₁ : List (Term .value) → M₁}
      {Δ₁' Δ₂' : Signature} {ρ₁' ρ₂' : Env} {k₂ : List (Term .value) → M₂},
      Δ₁.Subset Δ₁' → Δ₂.Subset Δ₂' →
      Δ₁'.wf → Δ₂'.wf →
      VarEnv.Agree Δ₁' Δ₂' ρ₁' ρ₂' δ₁ δ₂ →
      EncoderListContSpec B Δ₁' Δ₂' ρ₁' ρ₂' k₁ k₂ →
      B Δ₁' Δ₂' ρ₁' ρ₂'
        (encodeListWith ops₁ Γ δ₁ es k₁) (encodeListWith ops₂ Γ δ₂ es k₂)

/-- Per-branch-list statement of `encodeWith_bind_binary`, parametric in two
scrutinee values whose evaluations agree, the starting index, and the
continuations. -/
def EncodeMatchWithBindBinary (branches : List (Typed.Binder × Typed.Expr)) : Prop :=
  ∀ {M₁ M₂ : Type} {Γ : FunCtx} {Δ₁ Δ₂ : Signature} {δ₁ δ₂ : VarEnv}
    {ops₁ : EncoderOps M₁} {ops₂ : EncoderOps M₂}
    {B : Signature → Signature → Env → Env → M₁ → M₂ → Prop},
    EncoderOpsBinary Γ ops₁ ops₂ B →
    ∀ {k₁ : Term .value → M₁}
      {Δ₁' Δ₂' : Signature} {ρ₁' ρ₂' : Env} {k₂ : Term .value → M₂}
      {scrut₁ scrut₂ : Term .value} {i : Nat},
      Δ₁.Subset Δ₁' → Δ₂.Subset Δ₂' →
      Δ₁'.wf → Δ₂'.wf →
      VarEnv.Agree Δ₁' Δ₂' ρ₁' ρ₂' δ₁ δ₂ →
      scrut₁.wfIn Δ₁' → scrut₂.wfIn Δ₂' →
      Term.eval ρ₁' scrut₁ = Term.eval ρ₂' scrut₂ →
      EncoderContSpec B Δ₁' Δ₂' ρ₁' ρ₂' k₁ k₂ →
      B Δ₁' Δ₂' ρ₁' ρ₂'
        (encodeMatchWith ops₁ Γ δ₁ scrut₁ branches i k₁)
        (encodeMatchWith ops₂ Γ δ₂ scrut₂ branches i k₂)


/-! ### Eval helpers for the paired-encoding binary -/

/-- `encodeConst` produces closed terms, so their value is environment
independent. -/
private theorem encodeConst_eval (c : TinyML.Const) (ρ ρ' : Env) :
    Term.eval ρ (encodeConst c) = Term.eval ρ' (encodeConst c) :=
  Term.eval_env_agree (encodeConst_wfIn c Signature.empty) (Env.agreeOn_empty ρ ρ')

/-- `encodeUnOp` is a pure syntactic wrapper: equal arguments yield equal
results. -/
private theorem encodeUnOp_eval {op : TinyML.UnOp} {v v' w w' : Term .value}
    {ρ ρ' : Env} (hv : encodeUnOp op v = .ok v') (hw : encodeUnOp op w = .ok w')
    (h : Term.eval ρ v = Term.eval ρ' w) :
    Term.eval ρ v' = Term.eval ρ' w' := by
  cases op with
  | neg | not =>
      simp only [encodeUnOp, Except.ok.injEq] at hv hw
      subst hv; subst hw
      simp only [Term.eval, UnOp.eval]; rw [h]
  | proj n =>
      simp only [encodeUnOp, Except.ok.injEq] at hv hw
      subst hv; subst hw
      simp only [Term.eval, UnOp.eval, vtailN_eval]
      rw [h]

/-- `encodeBinOp` is a pure syntactic wrapper: equal arguments yield equal
results. -/
private theorem encodeBinOp_eval {op : TinyML.BinOp} {a a' b b' c c' : Term .value}
    {ρ ρ' : Env}
    (h1 : encodeBinOp op a b = .ok c) (h2 : encodeBinOp op a' b' = .ok c')
    (ha : Term.eval ρ a = Term.eval ρ' a') (hb : Term.eval ρ b = Term.eval ρ' b') :
    Term.eval ρ c = Term.eval ρ' c' := by
  cases op with
  | add | sub | mul | div | mod | lt | le | gt | ge | eq | and | or =>
      simp only [encodeBinOp, Except.ok.injEq] at h1 h2
      subst h1; subst h2
      simp [Term.eval, UnOp.eval, BinOp.eval, Const.denote, ha, hb, ge_iff_le]

private theorem toValList_eval_eq {ts₁ ts₂ : List (Term .value)} {ρ₁ ρ₂ : Env}
    (h : ts₁.map (fun t => Term.eval ρ₁ t) = ts₂.map (fun t => Term.eval ρ₂ t)) :
    Term.eval ρ₁ (Terms.toValList ts₁) = Term.eval ρ₂ (Terms.toValList ts₂) := by
  induction ts₁ generalizing ts₂ with
  | nil =>
      cases ts₂ <;> simp [Terms.toValList, Term.eval, Const.denote] at h ⊢
  | cons t ts ih =>
      cases ts₂ with
      | nil => simp at h
      | cons u us =>
          simp only [List.map_cons, List.cons.injEq] at h
          rcases h with ⟨hhead, htail⟩
          simp [Terms.toValList, Term.eval, BinOp.eval, hhead, ih htail]

/-- The shape of an `encodeUnOp` result (error, with message) depends only on
the operator, not the argument. -/
private theorem encodeUnOp_error_irrel {op : TinyML.UnOp} {v v' : Term .value}
    {msg : String} (h : encodeUnOp op v = .error msg) :
    encodeUnOp op v' = .error msg := by
  cases op <;> simp_all [encodeUnOp]

/-- The shape of an `encodeUnOp` result (success) depends only on the
operator, not the argument. -/
private theorem encodeUnOp_ok_irrel {op : TinyML.UnOp} {v v' w : Term .value}
    (h : encodeUnOp op v = .ok w) : ∃ w', encodeUnOp op v' = .ok w' := by
  cases op <;> simp_all [encodeUnOp]

/-- The shape of an `encodeBinOp` result (error, with message) depends only on
the operator, not the arguments. -/
private theorem encodeBinOp_error_irrel {op : TinyML.BinOp} {a b a' b' : Term .value}
    {msg : String} (h : encodeBinOp op a b = .error msg) :
    encodeBinOp op a' b' = .error msg := by
  cases op <;> simp_all [encodeBinOp]

/-- The shape of an `encodeBinOp` result (success) depends only on the
operator, not the arguments. -/
private theorem encodeBinOp_ok_irrel {op : TinyML.BinOp} {a b a' b' c : Term .value}
    (h : encodeBinOp op a b = .ok c) : ∃ c', encodeBinOp op a' b' = .ok c' := by
  cases op <;> simp_all [encodeBinOp]

/-! ## Per-case helpers for `encodeWith_bind_binary` -/

namespace BindBinary

theorem const (c : TinyML.Const) : EncodeWithBindBinary (.const c) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ _ hk
  simp only [encodeWith]
  exact hk (Signature.Subset.refl _) (Signature.Subset.refl _) hwf₁ hwf₂
    Env.agreeOn_refl Env.agreeOn_refl (encodeConst c) (encodeConst c)
    (encodeConst_wfIn c _) (encodeConst_wfIn c _) (encodeConst_eval c _ _)

theorem var (x : String) (ty : TinyML.Typ) : EncodeWithBindBinary (.var x ty) := by
  intro _ _ _ _ _ δ₁ δ₂ _ _ _ hops _ _ _ ρ₁' ρ₂' _ _ _ hwf₁ hwf₂ henv hk
  cases h₁ : δ₁.lookup x with
  | none =>
      have h₂ : δ₂.lookup x = none := by
        cases h₂ : δ₂.lookup x with
        | none => rfl
        | some v₂ =>
            have : ∃ v₁, δ₁.lookup x = some v₁ := (henv.sameDomain x).mpr ⟨v₂, h₂⟩
            rcases this with ⟨v₁, hv₁⟩
            rw [h₁] at hv₁
            cases hv₁
      simp only [encodeWith, h₁, h₂]
      exact hops.error_binary
  | some v₁ =>
      obtain ⟨v₂, h₂⟩ := (henv.sameDomain x).mp ⟨v₁, h₁⟩
      rcases henv.agree x v₁ v₂ h₁ h₂ with ⟨hv₁, hv₂, heval⟩
      simp only [encodeWith, h₁, h₂]
      exact hk (Signature.Subset.refl _) (Signature.Subset.refl _) hwf₁ hwf₂
        Env.agreeOn_refl Env.agreeOn_refl v₁ v₂ hv₁ hv₂ heval

theorem unop (op : TinyML.UnOp) (e : Typed.Expr) (ty : TinyML.Typ)
    (ih : EncodeWithBindBinary e) : EncodeWithBindBinary (.unop op e ty) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeWith]
  refine ih hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ v₁ v₂ hv₁ hv₂ hevalv
  cases hraw₁ : encodeUnOp op v₁ with
  | error msg =>
      have hraw₂ := encodeUnOp_error_irrel (v' := v₂) hraw₁
      simp only [hraw₁, hraw₂]
      exact hops.error_binary
  | ok v₁' =>
      obtain ⟨v₂', hraw₂⟩ := encodeUnOp_ok_irrel (v' := v₂) hraw₁
      simp only [hraw₁, hraw₂]
      exact hk hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ v₁' v₂'
        (encodeUnOp_wfIn hraw₁ hv₁) (encodeUnOp_wfIn hraw₂ hv₂)
        (encodeUnOp_eval hraw₁ hraw₂ hevalv)

theorem binop (op : TinyML.BinOp) (e1 e2 : Typed.Expr) (ty : TinyML.Typ)
    (ih1 : EncodeWithBindBinary e1) (ih2 : EncodeWithBindBinary e2) :
    EncodeWithBindBinary (.binop op e1 e2 ty) := by
  intro _ _ _ Δ₁ Δ₂ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeWith]
  refine ih1 hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ v1₁ v1₂ hv1₁ hv1₂ heval1
  refine ih2 hops
    (hsub₁.trans hsa₁) (hsub₂.trans hsa₂) hwa₁ hwa₂
    (VarEnv.Agree.mono hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ henv) ?_
  intro Δb₁ Δb₂ ρb₁ ρb₂ hsb₁ hsb₂ hwb₁ hwb₂ hab₁ hab₂ v2₁ v2₂ hv2₁ hv2₂ heval2
  have hev1 : Term.eval ρb₁ v1₁ = Term.eval ρb₂ v1₂ := by
    rw [← Term.eval_env_agree hv1₁ hab₁, heval1,
        Term.eval_env_agree hv1₂ hab₂]
  cases hraw₁ : encodeBinOp op v1₁ v2₁ with
  | error msg =>
      have hraw₂ := encodeBinOp_error_irrel (a' := v1₂) (b' := v2₂) hraw₁
      simp only [hraw₁, hraw₂]
      exact hops.error_binary
  | ok v₁' =>
      obtain ⟨v₂', hraw₂⟩ := encodeBinOp_ok_irrel (a' := v1₂) (b' := v2₂) hraw₁
      simp only [hraw₁, hraw₂]
      exact hk (hsa₁.trans hsb₁) (hsa₂.trans hsb₂) hwb₁ hwb₂
        (Env.agreeOn_trans haa₁ (Env.agreeOn_mono hsa₁ hab₁))
        (Env.agreeOn_trans haa₂ (Env.agreeOn_mono hsa₂ hab₂))
        v₁' v₂'
        (encodeBinOp_wfIn hraw₁ (Term.wfIn_mono v1₁ hv1₁ hsb₁ hwb₁) hv2₁)
        (encodeBinOp_wfIn hraw₂ (Term.wfIn_mono v1₂ hv1₂ hsb₂ hwb₂) hv2₂)
        (encodeBinOp_eval hraw₁ hraw₂ hev1 heval2)

theorem ifThenElse (c t e : Typed.Expr) (ty : TinyML.Typ)
    (ihc : EncodeWithBindBinary c) (iht : EncodeWithBindBinary t)
    (ihe : EncodeWithBindBinary e) :
    EncodeWithBindBinary (.ifThenElse c t e ty) := by
  intro _ _ _ Δ₁ Δ₂ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeWith]
  refine ihc hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ b₁ b₂ hb₁ hb₂ hevalb
  have hsub₁a : Δ₁.Subset Δa₁ := hsub₁.trans hsa₁
  have hsub₂a : Δ₂.Subset Δa₂ := hsub₂.trans hsa₂
  have henv_a := VarEnv.Agree.mono hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ henv
  have hka : EncoderContSpec _ Δa₁ Δa₂ ρa₁ ρa₂ _ _ :=
    EncoderContSpec.mono hsa₁ hsa₂ haa₁ haa₂ hk
  refine hops.ite_binary ?_
    (iht hops hsub₁a hsub₂a hwa₁ hwa₂ henv_a hka)
    (ihe hops hsub₁a hsub₂a hwa₁ hwa₂ henv_a hka)
  simp only [Term.eval, UnOp.eval]; rw [hevalb]

theorem app (fn : Typed.Expr) (args : List Typed.Expr) (ty : TinyML.Typ)
    (ihArgs : ∀ a ∈ args, EncodeWithBindBinary a) :
    EncodeWithBindBinary (.app fn args ty) := by
  intro _ _ Γ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  match fn, args with
  | .var f _, [arg] =>
      simp only [encodeWith]
      cases hlk : FunCtx.lookup Γ f with
      | none => exact hops.error_binary
      | some _ =>
          simp only
          refine ihArgs arg (List.mem_singleton.mpr rfl) hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
          intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ _ _ haa₁ haa₂ v₁ v₂ hv₁ hv₂ hevalv
          exact hops.call_binary (FunCtx.mem_of_lookup hlk) hv₁ hv₂ hevalv
            (EncoderContSpec.mono hsa₁ hsa₂ haa₁ haa₂ hk)
  | .const _, _ | .unop .., _ | .binop .., _ | .fix .., _ | .app .., _
  | .ifThenElse .., _ | .letIn .., _ | .ref .., _ | .deref .., _ | .store .., _
  | .assert _, _ | .tuple _, _ | .inj .., _ | .match_ .., _ | .cast .., _
  | .var _ _, [] | .var _ _, _ :: _ :: _ =>
      simp only [encodeWith]; exact hops.error_binary

theorem cast (e : Typed.Expr) (ty : TinyML.Typ) (ih : EncodeWithBindBinary e) :
    EncodeWithBindBinary (.cast e ty) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simpa only [encodeWith] using ih hops hsub₁ hsub₂ hwf₁ hwf₂ henv hk

theorem fix (self : Typed.Binder) (args : List Typed.Binder) (retTy : TinyML.Typ)
    (body : Typed.Expr) : EncodeWithBindBinary (.fix self args retTy body) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ _ _ _ _ _ _; exact hops.error_binary

theorem letIn (name : Typed.Binder) (bound body : Typed.Expr)
    (ihBound : EncodeWithBindBinary bound) (ihBody : EncodeWithBindBinary body) :
    EncodeWithBindBinary (.letIn name bound body) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeWith]
  refine ihBound hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ v₁ v₂ hv₁ hv₂ hevalv
  have henv_a := VarEnv.Agree.mono hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ henv
  have hka : EncoderContSpec _ Δa₁ Δa₂ ρa₁ ρa₂ _ _ :=
    EncoderContSpec.mono hsa₁ hsa₂ haa₁ haa₂ hk
  exact ihBody hops (hsub₁.trans hsa₁) (hsub₂.trans hsa₂) hwa₁ hwa₂
    (VarEnv.Agree.bindBinder henv_a hv₁ hv₂ hevalv) hka

theorem ref (owned : Bool) (e : Typed.Expr) : EncodeWithBindBinary (.ref owned e) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ _ _ _ _ _ _; exact hops.error_binary

theorem deref (e : Typed.Expr) (ty : TinyML.Typ) : EncodeWithBindBinary (.deref e ty) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ _ _ _ _ _ _; exact hops.error_binary

theorem store (loc val : Typed.Expr) : EncodeWithBindBinary (.store loc val) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ _ _ _ _ _ _; exact hops.error_binary

theorem assert (e : Typed.Expr) : EncodeWithBindBinary (.assert e) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ _ _ _ _ _ _; exact hops.error_binary

theorem tuple (es : List Typed.Expr) (ih : EncodeListWithBindBinary es) :
    EncodeWithBindBinary (.tuple es) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeWith]
  refine ih hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ vs₁ vs₂ hvs₁ hvs₂ hevals
  exact hk hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂
    (.unop .ofValList (Terms.toValList vs₁)) (.unop .ofValList (Terms.toValList vs₂))
    ⟨trivial, Terms.toValList_wfIn hvs₁⟩
    ⟨trivial, Terms.toValList_wfIn hvs₂⟩
    (by simp [Term.eval, UnOp.eval, toValList_eval_eq hevals])

theorem inj (tag arity : Nat) (payload : Typed.Expr)
    (ih : EncodeWithBindBinary payload) :
    EncodeWithBindBinary (.inj tag arity payload) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeWith]
  refine ih hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ v₁ v₂ hv₁ hv₂ hevalv
  exact hk hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂
    (.unop (.mkInj tag arity) v₁) (.unop (.mkInj tag arity) v₂)
    ⟨trivial, hv₁⟩ ⟨trivial, hv₂⟩
    (by simp [Term.eval, UnOp.eval, hevalv])

theorem match_ (scrut : Typed.Expr) (branches : List (Typed.Binder × Typed.Expr))
    (ty : TinyML.Typ) (ihScrut : EncodeWithBindBinary scrut)
    (ihBranches : EncodeMatchWithBindBinary branches) :
    EncodeWithBindBinary (.match_ scrut branches ty) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeWith]
  refine ihScrut hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ v₁ v₂ hv₁ hv₂ hevalv
  have henv_a := VarEnv.Agree.mono hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ henv
  have hka : EncoderContSpec _ Δa₁ Δa₂ ρa₁ ρa₂ _ _ :=
    EncoderContSpec.mono hsa₁ hsa₂ haa₁ haa₂ hk
  exact ihBranches hops (hsub₁.trans hsa₁) (hsub₂.trans hsa₂) hwa₁ hwa₂
    henv_a hv₁ hv₂ hevalv hka

/-- Empty match branch lists encode as the shared match error. -/
theorem match_nil : EncodeMatchWithBindBinary [] := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [encodeMatchWith]; exact hops.error_binary

/-- Binary preservation for a non-empty match branch list. -/
theorem match_cons (b : Typed.Binder) (body : Typed.Expr)
    (rest : List (Typed.Binder × Typed.Expr))
    (ihBody : EncodeWithBindBinary body)
    (ihRest : EncodeMatchWithBindBinary rest) :
    EncodeMatchWithBindBinary ((b, body) :: rest) := by
  intro _ _ _ _ _ _ _ _ _ _ hops _ Δ₁' Δ₂' ρ₁' ρ₂' _ scrut₁ scrut₂ _
        hsub₁ hsub₂ hwf₁ hwf₂ henv hscrut₁ hscrut₂ hevalScrut hk
  simp only [encodeMatchWith]
  have hpay₁ : (Term.unop UnOp.payloadOf scrut₁).wfIn Δ₁' := ⟨trivial, hscrut₁⟩
  have hpay₂ : (Term.unop UnOp.payloadOf scrut₂).wfIn Δ₂' := ⟨trivial, hscrut₂⟩
  have hpayEval : Term.eval ρ₁' (.unop UnOp.payloadOf scrut₁) =
      Term.eval ρ₂' (.unop UnOp.payloadOf scrut₂) := by
    simp [Term.eval, UnOp.eval, hevalScrut]
  cases rest with
  | nil =>
    exact ihBody hops hsub₁ hsub₂ hwf₁ hwf₂
      (VarEnv.Agree.bindBinder henv hpay₁ hpay₂ hpayEval) hk
  | cons _ _ =>
    refine hops.ite_binary ?_
      (ihBody hops hsub₁ hsub₂ hwf₁ hwf₂
        (VarEnv.Agree.bindBinder henv hpay₁ hpay₂ hpayEval) hk)
      (ihRest hops hsub₁ hsub₂ hwf₁ hwf₂ henv hscrut₁ hscrut₂ hevalScrut hk)
    simp [Term.eval, UnOp.eval, BinOp.eval, hevalScrut]

/-- Empty expression lists feed matching empty value lists to their
continuations. -/
theorem list_nil : EncodeListWithBindBinary [] := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ _ hk
  simp only [encodeListWith]
  exact hk (Signature.Subset.refl _) (Signature.Subset.refl _) hwf₁ hwf₂
    Env.agreeOn_refl Env.agreeOn_refl [] [] (by simp) (by simp) (by simp)

/-- Binary preservation for expression lists, threading the head value into the
tail list continuation. -/
theorem list_cons (e : Typed.Expr) (es : List Typed.Expr)
    (ih : EncodeWithBindBinary e) (ihs : EncodeListWithBindBinary es) :
    EncodeListWithBindBinary (e :: es) := by
  intro _ _ _ Δ₁ Δ₂ _ _ _ _ _ hops _ _ _ _ _ _ hsub₁ hsub₂ hwf₁ hwf₂ henv hk
  simp only [encodeListWith]
  refine ih hops hsub₁ hsub₂ hwf₁ hwf₂ henv ?_
  intro Δa₁ Δa₂ ρa₁ ρa₂ hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ v₁ v₂ hv₁ hv₂ hevalv
  refine ihs hops
    (hsub₁.trans hsa₁) (hsub₂.trans hsa₂) hwa₁ hwa₂
    (VarEnv.Agree.mono hsa₁ hsa₂ hwa₁ hwa₂ haa₁ haa₂ henv) ?_
  intro Δb₁ Δb₂ ρb₁ ρb₂ hsb₁ hsb₂ hwb₁ hwb₂ hab₁ hab₂ vs₁ vs₂ hvs₁ hvs₂ hevals
  have hevHead : Term.eval ρb₁ v₁ = Term.eval ρb₂ v₂ := by
    rw [← Term.eval_env_agree hv₁ hab₁, hevalv,
        Term.eval_env_agree hv₂ hab₂]
  have hwfs₁ : ∀ q ∈ v₁ :: vs₁, q.wfIn Δb₁ := by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with hq | hq
    · subst q
      exact Term.wfIn_mono v₁ hv₁ hsb₁ hwb₁
    · exact hvs₁ q hq
  have hwfs₂ : ∀ q ∈ v₂ :: vs₂, q.wfIn Δb₂ := by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with hq | hq
    · subst q
      exact Term.wfIn_mono v₂ hv₂ hsb₂ hwb₂
    · exact hvs₂ q hq
  exact hk (hsa₁.trans hsb₁) (hsa₂.trans hsb₂) hwb₁ hwb₂
    (Env.agreeOn_trans haa₁ (Env.agreeOn_mono hsa₁ hab₁))
    (Env.agreeOn_trans haa₂ (Env.agreeOn_mono hsa₂ hab₂))
    (v₁ :: vs₁) (v₂ :: vs₂) hwfs₁ hwfs₂ (by simp [hevHead, hevals])

end BindBinary

mutual
/-- Generic paired-encoding theorem for the shared traversal. -/
theorem encodeWith_bind_binary_def : ∀ (e : Typed.Expr), EncodeWithBindBinary e
  | .const c => BindBinary.const c
  | .var x ty => BindBinary.var x ty
  | .unop op e ty => BindBinary.unop op e ty (encodeWith_bind_binary_def e)
  | .binop op e1 e2 ty =>
      BindBinary.binop op e1 e2 ty (encodeWith_bind_binary_def e1)
        (encodeWith_bind_binary_def e2)
  | .ifThenElse c t e ty =>
      BindBinary.ifThenElse c t e ty (encodeWith_bind_binary_def c)
        (encodeWith_bind_binary_def t) (encodeWith_bind_binary_def e)
  | .app fn args ty =>
      BindBinary.app fn args ty (fun a _ => encodeWith_bind_binary_def a)
  | .cast e ty => BindBinary.cast e ty (encodeWith_bind_binary_def e)
  | .fix self args retTy body => BindBinary.fix self args retTy body
  | .letIn name bound body =>
      BindBinary.letIn name bound body
        (encodeWith_bind_binary_def bound) (encodeWith_bind_binary_def body)
  | .ref owned e => BindBinary.ref owned e
  | .deref e ty => BindBinary.deref e ty
  | .store loc val => BindBinary.store loc val
  | .assert e => BindBinary.assert e
  | .tuple es => BindBinary.tuple es (encodeListWith_bind_binary_def es)
  | .inj tag arity payload =>
      BindBinary.inj tag arity payload (encodeWith_bind_binary_def payload)
  | .match_ scrut branches ty =>
      BindBinary.match_ scrut branches ty
        (encodeWith_bind_binary_def scrut)
        (encodeMatchWith_bind_binary_def branches)

theorem encodeListWith_bind_binary_def : ∀ (es : List Typed.Expr), EncodeListWithBindBinary es
  | [] => BindBinary.list_nil
  | e :: es =>
      BindBinary.list_cons e es (encodeWith_bind_binary_def e)
        (encodeListWith_bind_binary_def es)

theorem encodeMatchWith_bind_binary_def :
    ∀ (branches : List (Typed.Binder × Typed.Expr)),
      EncodeMatchWithBindBinary branches
  | [] => BindBinary.match_nil
  | (b, body) :: rest =>
      BindBinary.match_cons b body rest
        (encodeWith_bind_binary_def body)
        (encodeMatchWith_bind_binary_def rest)
end

/-- Bind-position paired-encoding theorem. The two encoders are run on the
same syntax `e` but with independent local environments related by
`VarEnv.Agree`. The conclusion is quantified over arbitrary *states*
`(Δ₁', ρ₁')`, `(Δ₂', ρ₂')` extending the initial signatures, so the induction
can chain inner continuation contracts off the future state reached by the
outer one. -/
theorem encodeWith_bind_binary {M₁ M₂ : Type} {Γ : FunCtx} {Δ₁ Δ₂ : Signature}
    {δ₁ δ₂ : VarEnv}
    {ops₁ : EncoderOps M₁} {ops₂ : EncoderOps M₂}
    {B : Signature → Signature → Env → Env → M₁ → M₂ → Prop}
    (hops : EncoderOpsBinary Γ ops₁ ops₂ B)
    (e : Typed.Expr) {k₁ : Term .value → M₁}
    {Δ₁' Δ₂' : Signature} {ρ₁' ρ₂' : Env} {k₂ : Term .value → M₂}
    (hsub₁ : Δ₁.Subset Δ₁') (hsub₂ : Δ₂.Subset Δ₂')
    (hwf₁ : Δ₁'.wf) (hwf₂ : Δ₂'.wf)
    (henv : VarEnv.Agree Δ₁' Δ₂' ρ₁' ρ₂' δ₁ δ₂)
    (hk : EncoderContSpec B Δ₁' Δ₂' ρ₁' ρ₂' k₁ k₂) :
    B Δ₁' Δ₂' ρ₁' ρ₂' (encodeWith ops₁ Γ δ₁ e k₁) (encodeWith ops₂ Γ δ₂ e k₂) :=
  encodeWith_bind_binary_def e hops hsub₁ hsub₂ hwf₁ hwf₂ henv hk


end Verifier.RelationalEncoding
