-- SUMMARY: Lambda lifting of spec-level bounded quantifiers (Range.all/Range.exists) into axiomatized function symbols.
import Mica.SourceTinyML.Typing
import Mica.Pure.Variables
import Mica.Pure.Guard
import Mica.Verifier.SpecFunctions
import Mica.Pure.Axioms

open Verifier (State)

open Iris Iris.BI

/-!
# Bounded quantifiers

`Range.all lo hi (fun i -> body)` in a specification means
`∀ i, lo ≤ i < hi → body` (vacuously true on an empty range);
`Range.exists` is the dual. The surface forms elaborate to ordinary
applications of the primitives `range-all`/`range-exists`
(`allName`/`existsName`). Their registry entries have false operational and
specification semantics: a rewrite pass lambda-lifts every legitimate spec
occurrence into calls to freshly axiomatized function symbols, while any
occurrence that survives the pass fails verification normally.
-/

namespace Verifier.BoundedQuantifier

/-- Internal primitive name for `Range.all`. -/
def allName : String := "range-all"

/-- Internal primitive name for `Range.exists`. -/
def existsName : String := "range-exists"

/-- Whether `n` is one of the bounded-quantifier primitives. -/
def isPrim (n : String) : Bool :=
  n = allName || n = existsName

/-! ## Registry entries

The quantifier operations are real intrinsics so the ordinary registry is the
single source of surface resolution and typing. Their operational relation,
weakest precondition, and specification precondition are all false: legitimate
specification occurrences are eliminated by this pass, while any occurrence
that survives cannot verify. No FOL symbol or axiom is required. -/

/-- A spec-only bounded-quantifier intrinsic. -/
def intrinsic (name : String) (path : String) : Verifier.Intrinsic where
  arity := .three
  name := name
  path := some ("Range", [path])
  mode := .ghost
  sem := fun _ _ _ _ => False
  pre := fun _ _ => iprop(False)
  argTys := [.int, .int, .arrow [.int] .bool none]
  retTy := .bool
  spec :=
    { args := ["lo", "hi", "body"]
      ghost := []
      pred := .assert .false_ (.ret ⟨"ret", .ret ()⟩) }
  encode := none
  axioms := []

/-- Registry entry for `Range.all`. -/
def allIntrinsic : Verifier.Intrinsic := intrinsic allName "all"

/-- Registry entry for `Range.exists`. -/
def existsIntrinsic : Verifier.Intrinsic := intrinsic existsName "exists"


/-- A forbidden intrinsic is sound: its specification and weakest precondition
are both false, and it contributes no solver symbols or axioms. -/
@[reducible] def intrinsicSound (name path : String) :
    Verifier.IntrinsicSound [] (intrinsic name path) where
  arg_len := rfl
  spec_wf := by
    intro Δ _ _
    simp [intrinsic, Verifier.Intrinsic.specArgs, PredTrans.wfIn, Assertion.wfIn]
    trivial
  spec_sound := by
    intro _ σ Θ vs ρ Φ _
    simp only [intrinsic, PredTrans.apply, Assertion.pre]
    iintro H
    icases H with ⟨_, %hfalse, _⟩
    exact hfalse.elim
  pre_wp := fun h => absurd rfl h
  pre_bupd := by
    intro _ _ vs _
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | [_, _] => exact false_elim
    | [_, _, _] => exact false_elim
    | _ :: _ :: _ :: _ :: _ => exact false_elim
  axioms_wf := by
    intro _ _ _ a ha
    cases ha
  axioms_sound := by
    intro _ _ a ha
    cases ha
  encode_sound := by
    intro f hf
    cases hf

instance : Verifier.IntrinsicSound [] allIntrinsic := intrinsicSound _ _

instance : Verifier.IntrinsicSound [] existsIntrinsic := intrinsicSound _ _

/-! ## The rewrite pass

Lifting is a *leaf* rewrite, so it runs inside the leaf translator that
elaboration calls (`Typed.SpecEnv.translate`), ahead of the FOL encoding, and
accumulates its lifted symbols in the elaboration state. Each occurrence
`Range.all lo hi (fun i -> body)` in a spec leaf is replaced by a plain call
`L (lo, hi, x̄)` of a symbol `L = "range-<digest>"` named after the closure's
content, over the packed bounds and captured variables `x̄`; the closure is recorded as a lifted
function body `let (x̄, i) = arg in body` to be axiomatized when it is declared.
Only spec leaves change — declaration bodies, hence the program's runtime
erasure, are never touched.

The rewrite itself is `partial` and unverified: no proof depends on its
equations. Rewritten leaves are encoded from scratch, and name freshness is
validated operationally when it is declared. -/

/-- State of the leaf rewrite: the lifted symbols in dependency order (inner
occurrences precede outer ones). -/
structure LiftState where
  syms : List LiftedClosure := []

abbrev LiftM := StateT LiftState (Except String)

mutual
  /-- Free program variables of a typed expression, in first-occurrence order.
  A named unary call head is resolved through the function context and is not
  captured as a value variable. -/
  private def freeVars : Typed.Expr → List TinyML.Var
    | .const _ => []
    | .var x _ _ => [x]
    | .prim .. => []
    | .unop _ e _ => freeVars e
    | .binop _ l r _ => freeVars l ++ freeVars r
    | .fix self args _ _ body =>
        (freeVars body).filter fun v =>
          self.name != some v && !args.any (·.name == some v)
    | .app (.var _ _ _) [arg] _ _ => freeVars arg
    | .app fn args gargs _ => freeVars fn ++ args.flatMap freeVars ++ gargs.flatMap freeVars
    | .ifThenElse c t e _ => freeVars c ++ freeVars t ++ freeVars e
    | .letIn _ b bound body =>
        freeVars bound ++ (freeVars body).filter (fun v => b.name != some v)
    | .letProd bs bound body =>
        freeVars bound ++ (freeVars body).filter (fun v => !bs.any (·.name == some v))
    | .ref _ e => freeVars e
    | .deref e _ => freeVars e
    | .store loc val => freeVars loc ++ freeVars val
    | .arrayMake _ len init => freeVars len ++ freeVars init
    | .arrayLen arr => freeVars arr
    | .arrayGet arr idx _ => freeVars arr ++ freeVars idx
    | .arraySet arr idx val => freeVars arr ++ freeVars idx ++ freeVars val
    | .assert e => freeVars e
    | .tuple es => es.flatMap freeVars
    | .inj _ _ payload _ => freeVars payload
    | .match_ scrut branches _ => freeVars scrut ++ branchFreeVars branches

  private def branchFreeVars : List (Typed.Binder × Typed.Expr) → List TinyML.Var
    | [] => []
    | (b, body) :: rest =>
        (freeVars body).filter (fun v => b.name != some v) ++ branchFreeVars rest
end

/-- The lifted symbol's name: a digest of everything that determines its defining
axioms — the quantifier kind, the index binder, the captured variables, and the
closure body — but not the bounds, which are passed as arguments, nor the packed
argument's name, which is derived from this name in turn.

Keying the symbol by content rather than by occurrence means an identical
quantifier written twice, in one specification or in two, lifts to a single
symbol. -/
private def liftedName (all : Bool) (binder : Typed.Binder) (captured : List TinyML.Var)
    (body : Typed.Expr) : String :=
  s!"range-{String.hash (toString (repr (all, binder, captured, body)))}"

/-- Lift one occurrence: allocate the quantifier symbol, record the lifted closure
`let (x̄, i) = arg in body`, and return the plain call replacing the
occurrence — the quantifier symbol applied to the packed `(lo, hi, x̄)` tuple.

Since the symbol is keyed by the closure's content, re-lifting an identical
occurrence reuses the symbol and records nothing new — which is what keeps
`LiftedClosure.validate`'s freshness precondition satisfiable. One name standing for
two *different* closures would axiomatize one of them as the other, so a digest
collision is rejected rather than resolved. -/
private def lift (all : Bool) (binder : Typed.Binder)
    (body lo hi : Typed.Expr) : LiftM Typed.Expr := do
  let captured := ((freeVars body).filter (fun v => binder.name != some v)).eraseDups
  let name := liftedName all binder captured body
  let gBody := Typed.Expr.letProd
    (captured.map (fun x => ⟨some x, .value⟩) ++ [binder]) (.var (name ++ "-x") [] .value) body
  let entry : LiftedClosure := { name, all, captured, arg := name ++ "-x", body := gBody }
  let st ← get
  match st.syms.find? (fun s => s.name == name) with
  | some existing =>
      if existing == entry then pure ()
      else throw s!"bounded-quantifier digest collision on '{name}'"
  | none => set ({ syms := st.syms ++ [entry] } : LiftState)
  pure (.app (.var name [] (.arrow [.value] .bool none))
    [.tuple (lo :: hi :: captured.map (fun x => Typed.Expr.var x [] .value))] [] .bool)

/-- Rewrite every bounded-quantifier occurrence in a spec leaf, bottom-up:
bounds and closure bodies are rewritten first, so inner occurrences are
lifted before — and their calls captured by — outer ones. -/
private partial def rewrite : Typed.Expr → LiftM Typed.Expr
  | .app (.prim n inst pty) args gargs ty => do
      if !gargs.isEmpty then throw "ghost arguments are not supported inside a bounded quantifier"
      else if isPrim n then
        match args with
        | [lo, hi, .fix _ [binder] _ _ body] => do
            let lo' ← rewrite lo
            let hi' ← rewrite hi
            let body' ← rewrite body
            lift (n = allName) binder body' lo' hi'
        | _ => throw "Range.all/Range.exists expect a literal single-argument function"
      else do
        pure (.app (.prim n inst pty) (← args.mapM rewrite) [] ty)
  | .const c => pure (.const c)
  | .var x inst ty => pure (.var x inst ty)
  | .prim n inst ty => pure (.prim n inst ty)
  | .unop op e ty => do pure (.unop op (← rewrite e) ty)
  | .binop op l r ty => do pure (.binop op (← rewrite l) (← rewrite r) ty)
  | .fix self args retTy spec body => do pure (.fix self args retTy spec (← rewrite body))
  | .app fn args gargs ty => do
      if !gargs.isEmpty then throw "ghost arguments are not supported inside a bounded quantifier"
      pure (.app (← rewrite fn) (← args.mapM rewrite) [] ty)
  | .ifThenElse c t e ty => do
      pure (.ifThenElse (← rewrite c) (← rewrite t) (← rewrite e) ty)
  | .letIn m b bound body => do pure (.letIn m b (← rewrite bound) (← rewrite body))
  | .letProd bs bound body => do
      pure (.letProd bs (← rewrite bound) (← rewrite body))
  | .ref ownership e => do pure (.ref ownership (← rewrite e))
  | .deref e ty => do pure (.deref (← rewrite e) ty)
  | .store loc val => do pure (.store (← rewrite loc) (← rewrite val))
  | .arrayMake ownership len init => do
      pure (.arrayMake ownership (← rewrite len) (← rewrite init))
  | .arrayLen arr => do pure (.arrayLen (← rewrite arr))
  | .arrayGet arr idx ty => do pure (.arrayGet (← rewrite arr) (← rewrite idx) ty)
  | .arraySet arr idx val => do
      pure (.arraySet (← rewrite arr) (← rewrite idx) (← rewrite val))
  | .assert e => do pure (.assert (← rewrite e))
  | .tuple es => do pure (.tuple (← es.mapM rewrite))
  | .inj tag arity payload ty => do pure (.inj tag arity (← rewrite payload) ty)
  | .match_ scrut branches ty => do
      pure (.match_ (← rewrite scrut)
        (← branches.mapM fun (b, body) => do pure (b, ← rewrite body)) ty)

/-- Rewrite one typed spec leaf, lifting every bounded-quantifier occurrence in
it. Lifted symbols accumulate in `syms` in dependency order: `rewrite` descends
into bounds and closure bodies first, so inner occurrences are lifted before the
outer ones that capture their calls. -/
def rewriteLeaf (e : Typed.Expr) (st : LiftState) : Except String (Typed.Expr × LiftState) :=
  (rewrite e).run st

end Verifier.BoundedQuantifier

/-! ## Solver-facing symbols and defining axioms

Each lifted occurrence contributes one `SpecFn`-shaped symbol triple for the
quantifier symbol `L`. The lifted closure body is compiled directly under the
matrix variables and inlined into `L`'s two defining axioms.

The canonical interpretations of `L`'s symbols are the evaluations of the
axioms' right-hand sides, so validity is by construction. -/

open PureEncoding

namespace Verifier.LiftedClosure

open BoundedQuantifier

/-- Bound index variable of the defining axioms. -/
def idx (s : LiftedClosure) : String := s.name ++ "-i"

/-- `Δ` extended by the packed argument variable: the scope of the axiom
matrices, which bind the index themselves. -/
abbrev argScope (s : LiftedClosure) (Δ : Signature) : Signature :=
  Δ.declVar ⟨s.arg, .value⟩

/-- `argScope` extended by the bound index: the scope of the compiled body. -/
abbrev matrixScope (s : LiftedClosure) (Δ : Signature) : Signature :=
  (s.argScope Δ).declVar ⟨s.idx, .int⟩

/-- Facts required to compile and declare a quantifier symbol: freshness of all
derived names. Established operationally by `validate`. -/
structure Valid (s : LiftedClosure) (Δ : Signature) : Prop where
  relFresh : SpecFn.relName s.name ∉ Δ.allNames
  funcFresh : SpecFn.funcName s.name ∉ Δ.allNames
  defFresh : SpecFn.defName s.name ∉ Δ.allNames
  argFresh : s.arg ∉ Δ.allNames
  idxFresh : s.idx ∉ Δ.allNames
  idxNeArg : s.idx ≠ s.arg
  argNeRel : s.arg ≠ SpecFn.relName s.name
  argNeFunc : s.arg ≠ SpecFn.funcName s.name
  argNeDef : s.arg ≠ SpecFn.defName s.name
  idxNeRel : s.idx ≠ SpecFn.relName s.name
  idxNeFunc : s.idx ≠ SpecFn.funcName s.name
  idxNeDef : s.idx ≠ SpecFn.defName s.name

/-- Run one decidable validation check, or fail with `msg`. -/
private def check (p : Prop) [Decidable p] (msg : String) : Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error msg

/-- Validate the fresh names required to compile and declare the solver-facing
quantifier symbol over `Δ`. A successful run returns the `Valid` evidence
directly. -/
def validate (s : LiftedClosure) (Δ : Signature) : Except String (PLift (Valid s Δ)) := do
  let L := s.name
  let ⟨relFresh⟩ ← check (SpecFn.relName L ∉ Δ.allNames)
    s!"derived relation name '{SpecFn.relName L}' for a bounded quantifier conflicts with an existing symbol"
  let ⟨funcFresh⟩ ← check (SpecFn.funcName L ∉ Δ.allNames)
    s!"derived value-function name '{SpecFn.funcName L}' for a bounded quantifier conflicts with an existing symbol"
  let ⟨defFresh⟩ ← check (SpecFn.defName L ∉ Δ.allNames)
    s!"derived definedness name '{SpecFn.defName L}' for a bounded quantifier conflicts with an existing symbol"
  let ⟨argFresh⟩ ← check (s.arg ∉ Δ.allNames)
    s!"bounded quantifier argument name '{s.arg}' conflicts with a global symbol"
  let ⟨idxFresh⟩ ← check (s.idx ∉ Δ.allNames)
    s!"bounded quantifier index name '{s.idx}' conflicts with a global symbol"
  let ⟨idxNeArg⟩ ← check (s.idx ≠ s.arg)
    s!"bounded quantifier index name '{s.idx}' clashes with its argument name"
  let ⟨argNeRel⟩ ← check (s.arg ≠ SpecFn.relName L)
    s!"bounded quantifier argument name '{s.arg}' clashes with derived relation name '{SpecFn.relName L}'"
  let ⟨argNeFunc⟩ ← check (s.arg ≠ SpecFn.funcName L)
    s!"bounded quantifier argument name '{s.arg}' clashes with derived value-function name '{SpecFn.funcName L}'"
  let ⟨argNeDef⟩ ← check (s.arg ≠ SpecFn.defName L)
    s!"bounded quantifier argument name '{s.arg}' clashes with derived definedness name '{SpecFn.defName L}'"
  let ⟨idxNeRel⟩ ← check (s.idx ≠ SpecFn.relName L)
    s!"bounded quantifier index name '{s.idx}' clashes with derived relation name '{SpecFn.relName L}'"
  let ⟨idxNeFunc⟩ ← check (s.idx ≠ SpecFn.funcName L)
    s!"bounded quantifier index name '{s.idx}' clashes with derived value-function name '{SpecFn.funcName L}'"
  let ⟨idxNeDef⟩ ← check (s.idx ≠ SpecFn.defName L)
    s!"bounded quantifier index name '{s.idx}' clashes with derived definedness name '{SpecFn.defName L}'"
  .ok ⟨⟨relFresh, funcFresh, defFresh, argFresh, idxFresh, idxNeArg, argNeRel,
    argNeFunc, argNeDef, idxNeRel, idxNeFunc, idxNeDef⟩⟩

/-- The packed axiom variable (also the lifted closure's argument name). -/
private def pvar (s : LiftedClosure) : Term .value := .var .value s.arg

private def ivar (s : LiftedClosure) : Term .int := .var .int s.idx

/-- Lower bound: the packed tuple's first component. -/
private def lo (s : LiftedClosure) : Term .int := .unop .toInt (s.pvar.proj 0)

/-- Upper bound: the packed tuple's second component. -/
private def hi (s : LiftedClosure) : Term .int := .unop .toInt (s.pvar.proj 1)

/-- The bounds premise `lo ≤ i ∧ i < hi`. -/
private def bounds (s : LiftedClosure) : Formula :=
  .and (.binpred .le s.lo s.ivar) (.binpred .lt s.ivar s.hi)

/-- The lifted closure's packed argument: the captured components of `p`
(positions `2..`) followed by the index. Matches the destructuring order of
the closure's `letProd`. -/
private def gpack (s : LiftedClosure) : Term .value :=
  Term.tuple
    ((List.range s.captured.length).map (fun k => s.pvar.proj (k + 2))
      ++ [.unop .ofInt s.ivar])

/-- Compile the lifted closure body under the packed argument and index matrix
variables. Binding the TinyML argument to `gpack` shadows the same-named FOL
variable while retaining that variable inside the packed term. -/
def compile (s : LiftedClosure) (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature) :
    Except String Skolemize.DefVal :=
  let Δpi := s.matrixScope Δ
  let env := (VarEnv.ofSignature Δpi).bind s.arg s.gpack
  Expr.toDefVal .id <$>
    encode primitives Δpi Γ env s.body Δpi.allNames

/-- Matrix of the value axiom: the bounded quantifier over the lifted
closure's truth. -/
def matrix (s : LiftedClosure) (body : Skolemize.DefVal) : Formula :=
  if s.all then .forall_ s.idx .int [] (.implies s.bounds body.value.isTrue)
  else .exists_ s.idx .int (.and s.bounds body.value.isTrue)

/-- Matrix of the definedness axiom: the lifted closure is defined on the
whole range (vacuously on an empty range, giving the vacuity semantics). -/
def defMatrix (s : LiftedClosure) (body : Skolemize.DefVal) : Formula :=
  .forall_ s.idx .int [] (.implies s.bounds body.defined)

/-- Defining definedness axiom: `L-def(p)` iff the closure is defined on the
whole range. Triggered only by the `L-def` application. -/
def defAxiom (s : LiftedClosure) (body : Skolemize.DefVal) : Formula :=
  .forall_ s.arg .value
    [.unpred (.uninterpreted (SpecFn.defName s.name) .value) s.pvar]
    (.iff (SpecFn.isDefined s.name s.pvar) (s.defMatrix body))

/-- Defining value axiom: `L-func(p)` is the boolean truth value of the
bounded quantifier. Stated as the two directions so the solver also learns
booleanness of the result. Triggered only by the `L-func` application. -/
def valAxiom (s : LiftedClosure) (body : Skolemize.DefVal) : Formula :=
  .forall_ s.arg .value
    [.term (SpecFn.call s.name s.pvar)]
    (.and (.implies (s.matrix body) (SpecFn.call s.name s.pvar).isTrue)
          (.implies (.not (s.matrix body)) (SpecFn.call s.name s.pvar).isFalse))

/-- The axioms defining a quantifier symbol; both quantified, hence guarded. -/
def axioms (s : LiftedClosure) (body : Skolemize.DefVal) : List Axiom :=
  [⟨s.defAxiom body, .high⟩, ⟨s.valAxiom body, .high⟩]

/-- Signature after declaring the quantifier relation, value function, and
definedness predicate. -/
def extendSignature (s : LiftedClosure) (Δ : Signature) : Signature :=
  ((Δ.addBinaryRel (SpecFn.rel s.name)).addUnary
    (SpecFn.func s.name)).addUnaryRel (SpecFn.defined s.name)

/-- Declare and axiomatize one validated quantifier symbol. -/
def declare (s : LiftedClosure) (body : Skolemize.DefVal) : SeqM Unit :=
  SpecFn.declare s.name (s.axioms body)

/-- Canonical interpretation of the quantifier symbol's definedness predicate:
the evaluation of the definedness axiom's right-hand side. -/
noncomputable def definterp (s : LiftedClosure) (body : Skolemize.DefVal) (ρ : _root_.Env) :
    Srt.value.denote → Prop :=
  fun v => (s.defMatrix body).eval (ρ.updateConst .value s.arg v)

open Classical in
/-- Canonical interpretation of the quantifier symbol's value function: the
boolean truth value of the value axiom's matrix. -/
noncomputable def funcinterp (s : LiftedClosure) (body : Skolemize.DefVal) (ρ : _root_.Env) :
    Srt.value.denote → Srt.value.denote :=
  fun v =>
    if (s.matrix body).eval (ρ.updateConst .value s.arg v)
    then Runtime.Val.bool true else Runtime.Val.bool false

/-- Canonical interpretation of the quantifier symbol's relation: the graph of the
value function on the definedness domain (single-valued, and in agreement
with the func-form reading, by construction). -/
noncomputable def relinterp (s : LiftedClosure) (body : Skolemize.DefVal) (ρ : _root_.Env) :
    Srt.value.denote → Srt.value.denote → Prop :=
  fun a b => s.definterp body ρ a ∧ s.funcinterp body ρ a = b

/-! ### Well-formedness of the defining axioms -/

private theorem var_wfIn {Δ : Signature} {x : String} {τ : Srt}
    (hΔ : Δ.wf) (hmem : (⟨x, τ⟩ : Var) ∈ Δ.vars) : (Term.var τ x).wfIn Δ :=
  ⟨hmem, fun _ hc => Signature.wf_no_const_of_var hΔ hmem hc,
   fun _ hv => Signature.wf_unique_var hΔ hmem hv⟩

variable {s : LiftedClosure} {Δ : Signature} {body : Skolemize.DefVal}

private theorem gpack_wfIn (hΔ : Δ.wf)
    (hp : (⟨s.arg, .value⟩ : Var) ∈ Δ.vars) (hi : (⟨s.idx, .int⟩ : Var) ∈ Δ.vars) :
    s.gpack.wfIn Δ := by
  refine Term.tuple_wfIn ?_
  intro t ht
  rcases List.mem_append.mp ht with hmem | hmem
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
    exact Term.proj_wfIn (var_wfIn hΔ hp) _
  · simp only [List.mem_singleton] at hmem
    subst hmem
    exact show UnOp.wfIn .ofInt Δ ∧ (Term.var .int s.idx).wfIn Δ from
      ⟨trivial, var_wfIn hΔ hi⟩

/-- The index variable is fresh for the signature extended by the packed
variable, so the nested `declVar` is an extension. -/
private theorem idx_fresh_declVar (harg : s.arg ∉ Δ.allNames)
    (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    s.idx ∉ (s.argScope Δ).allNames := by
  rw [Signature.allNames_declVar_of_not_in harg]
  intro hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact hai h
  · exact hidx h

/-- The signature the matrices are checked in — `Δ` extended by the packed
argument and the index — is well-formed and declares both matrix variables. -/
private theorem matrix_vars (hΔ : Δ.wf)
    (harg : s.arg ∉ Δ.allNames) (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    (s.matrixScope Δ).wf ∧
      (⟨s.arg, .value⟩ : Var) ∈ (s.matrixScope Δ).vars ∧
      (⟨s.idx, .int⟩ : Var) ∈ (s.matrixScope Δ).vars :=
  let hΔp := Signature.wf_declVar hΔ
  let hsubpi := Signature.subset_declVar_of_fresh (idx_fresh_declVar harg hidx hai)
  ⟨Signature.wf_declVar hΔp,
   hsubpi.vars _ (Signature.var_mem_declVar Δ ⟨s.arg, .value⟩),
   Signature.var_mem_declVar _ ⟨s.idx, .int⟩⟩

/-- A successfully compiled lifting body is well-formed under its two matrix
variables. -/
theorem compile_wfIn {primitives : PrimEncodings} (hlaw : primitives.Lawful)
    (hv : s.Valid Δ) (hΔ : Δ.wf) (hΓ : Γ.wfIn Δ)
    (henc : s.compile primitives Γ Δ = .ok body) :
    body.wfIn (s.matrixScope Δ) := by
  let Δp := s.argScope Δ
  let Δpi := s.matrixScope Δ
  have hsubp : Δ.Subset Δp := Signature.subset_declVar_of_fresh hv.argFresh
  have hsubpi : Δp.Subset Δpi :=
    Signature.subset_declVar_of_fresh
      (idx_fresh_declVar hv.argFresh hv.idxFresh hv.idxNeArg)
  obtain ⟨hΔpi, hp, hi⟩ := matrix_vars hΔ hv.argFresh hv.idxFresh hv.idxNeArg
  simp only [compile] at henc
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  exact Expr.toDefVal_wfIn_of_encode s.body hlaw (Signature.Subset.refl _) hΔpi
    (FunCtx.funcWfIn_mono hΓ.func (hsubp.trans hsubpi))
    ((VarEnv.ofSignature_wfIn hΔpi).bind (gpack_wfIn hΔpi hp hi))
    (Covers.allNames _) hc

private theorem bounds_wfIn (hΔ : Δ.wf)
    (hp : (⟨s.arg, .value⟩ : Var) ∈ Δ.vars) (hi : (⟨s.idx, .int⟩ : Var) ∈ Δ.vars) :
    s.bounds.wfIn Δ := by
  have hproj : ∀ k, (s.pvar.proj k).wfIn Δ := fun k => Term.proj_wfIn (var_wfIn hΔ hp) k
  have hlo : s.lo.wfIn Δ :=
    show UnOp.wfIn .toInt Δ ∧ (s.pvar.proj 0).wfIn Δ from ⟨trivial, hproj 0⟩
  have hhi : s.hi.wfIn Δ :=
    show UnOp.wfIn .toInt Δ ∧ (s.pvar.proj 1).wfIn Δ from ⟨trivial, hproj 1⟩
  have hiv : s.ivar.wfIn Δ := var_wfIn hΔ hi
  exact ⟨⟨trivial, hlo, hiv⟩, ⟨trivial, hiv, hhi⟩⟩

/-- Well-formedness of the value-axiom matrix at the packed-variable
signature, given a body compiled under both matrix variables. -/
theorem matrix_wfIn (hΔ : Δ.wf)
    (hbody : body.wfIn (s.matrixScope Δ))
    (harg : s.arg ∉ Δ.allNames) (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    (s.matrix body).wfIn (s.argScope Δ) := by
  obtain ⟨hΔpi, hpvars, hivars⟩ := matrix_vars hΔ harg hidx hai
  have hholds : body.value.isTrue.wfIn _ := ⟨hbody.1, trivial, trivial⟩
  unfold matrix
  split
  · exact ⟨fun _ h => (List.not_mem_nil h).elim,
      bounds_wfIn hΔpi hpvars hivars, hholds⟩
  · exact ⟨bounds_wfIn hΔpi hpvars hivars, hholds⟩

/-- Well-formedness of the definedness-axiom matrix at the packed-variable
signature. -/
theorem defMatrix_wfIn (hΔ : Δ.wf)
    (hbody : body.wfIn (s.matrixScope Δ))
    (harg : s.arg ∉ Δ.allNames) (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    (s.defMatrix body).wfIn (s.argScope Δ) := by
  obtain ⟨hΔpi, hpvars, hivars⟩ := matrix_vars hΔ harg hidx hai
  exact ⟨fun _ h => (List.not_mem_nil h).elim,
    bounds_wfIn hΔpi hpvars hivars,
    hbody.2⟩

/-- Well-formedness of the defining axioms. All hypotheses are discharged
operationally when it is declared (symbol declarations and name checks). -/
theorem axioms_wfIn (hΔ : Δ.wf)
    (hbody : body.wfIn (s.matrixScope Δ))
    (hlfun : SpecFn.func s.name ∈ Δ.unary) (hldef : SpecFn.defined s.name ∈ Δ.unaryRel)
    (harg : s.arg ∉ Δ.allNames) (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    ∀ ax ∈ s.axioms body, ax.formula.wfIn Δ := by
  intro ax hmem
  have hΔp : (s.argScope Δ).wf := Signature.wf_declVar hΔ
  have hsubp : Δ.Subset (s.argScope Δ) :=
    Signature.subset_declVar_of_fresh harg
  have hpwf : (Term.var .value s.arg).wfIn (s.argScope Δ) :=
    var_wfIn hΔp (Signature.var_mem_declVar Δ ⟨s.arg, .value⟩)
  have hlfun_p : SpecFn.func s.name ∈ (s.argScope Δ).unary :=
    hsubp.unary _ hlfun
  have hldef_p : SpecFn.defined s.name ∈ (s.argScope Δ).unaryRel :=
    hsubp.unaryRel _ hldef
  simp only [axioms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · -- defAxiom
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact SpecFn.isDefined_wfIn hldef_p hΔp hpwf
    · exact ⟨⟨SpecFn.isDefined_wfIn hldef_p hΔp hpwf,
        defMatrix_wfIn hΔ hbody harg hidx hai⟩,
        ⟨defMatrix_wfIn hΔ hbody harg hidx hai,
        SpecFn.isDefined_wfIn hldef_p hΔp hpwf⟩⟩
  · -- valAxiom
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact SpecFn.call_wfIn hlfun_p hΔp hpwf
    · exact ⟨⟨matrix_wfIn hΔ hbody harg hidx hai,
        SpecFn.call_wfIn hlfun_p hΔp hpwf, trivial, trivial⟩,
        ⟨matrix_wfIn hΔ hbody harg hidx hai,
        SpecFn.call_wfIn hlfun_p hΔp hpwf, trivial, trivial⟩⟩

/-! ### Validity of the defining axioms under the canonical interpretations -/

/-- The environment carrying the quantifier symbol's canonical interpretations. -/
noncomputable def extend (s : LiftedClosure) (body : Skolemize.DefVal) (ρ : _root_.Env) : _root_.Env :=
  ((ρ.updateBinaryRel .value .value (SpecFn.relName s.name) (s.relinterp body ρ)).updateUnary
      .value .value (SpecFn.funcName s.name) (s.funcinterp body ρ)).updateUnaryRel
    .value (SpecFn.defName s.name) (s.definterp body ρ)

/-- The extension only touches the quantifier symbol's three fresh names. -/
theorem extend_agreeOn {ρ : _root_.Env}
    (hrel : SpecFn.relName s.name ∉ Δ.allNames)
    (hfun : SpecFn.funcName s.name ∉ Δ.allNames)
    (hdef : SpecFn.defName s.name ∉ Δ.allNames) :
    _root_.Env.agreeOn Δ ρ (s.extend body ρ) :=
  _root_.Env.agreeOn_trans
    (_root_.Env.agreeOn_update_fresh_binaryRel (b := SpecFn.rel s.name)
      (f := s.relinterp body ρ) hrel)
    (_root_.Env.agreeOn_trans
      (_root_.Env.agreeOn_update_fresh_unary (u := SpecFn.func s.name)
        (f := s.funcinterp body ρ) hfun)
      (_root_.Env.agreeOn_update_fresh_unaryRel (u := SpecFn.defined s.name)
        (f := s.definterp body ρ) hdef))

@[simp] theorem extend_evalDefined (ρ : _root_.Env) (v : Srt.value.denote) :
    SpecFn.evalDefined s.name (s.extend body ρ) v ↔ s.definterp body ρ v := by
  simp [extend, SpecFn.evalDefined, SpecFn.defined, SpecFn.defName,
    _root_.Env.updateUnaryRel, _root_.Env.updateUnary, _root_.Env.updateBinaryRel]

@[simp] theorem extend_evalCall (ρ : _root_.Env) (v : Srt.value.denote) :
    SpecFn.evalCall s.name (s.extend body ρ) v = s.funcinterp body ρ v := by
  simp [extend, SpecFn.evalCall, SpecFn.func, SpecFn.funcName,
    _root_.Env.updateUnaryRel, _root_.Env.updateUnary, _root_.Env.updateBinaryRel]

@[simp] theorem extend_evalRelates (ρ : _root_.Env) (a b : Srt.value.denote) :
    SpecFn.evalRelates s.name (s.extend body ρ) a b ↔ s.relinterp body ρ a b := by
  simp [extend, SpecFn.evalRelates, SpecFn.rel, SpecFn.relName,
    _root_.Env.updateUnaryRel, _root_.Env.updateUnary, _root_.Env.updateBinaryRel]

/-- The defining axioms hold in the extended environment. Matrix
well-formedness lets their evaluation be transported past the extension. -/
theorem axioms_eval {ρ : _root_.Env}
    (hmat : (s.matrix body).wfIn (s.argScope Δ))
    (hdefmat : (s.defMatrix body).wfIn (s.argScope Δ))
    (hrel : SpecFn.relName s.name ∉ Δ.allNames)
    (hfun : SpecFn.funcName s.name ∉ Δ.allNames)
    (hdef : SpecFn.defName s.name ∉ Δ.allNames) :
    ∀ ax ∈ s.axioms body, ax.formula.eval (s.extend body ρ) := by
  have hagree : _root_.Env.agreeOn Δ ρ (s.extend body ρ) := extend_agreeOn hrel hfun hdef
  have htrans : ∀ (φ : Formula), φ.wfIn (s.argScope Δ) →
      ∀ v, φ.eval ((s.extend body ρ).updateConst .value s.arg v) ↔
        φ.eval (ρ.updateConst .value s.arg v) :=
    fun φ hwf v => (Formula.eval_agreeOn hwf (_root_.Env.agreeOn_declVar hagree)).symm
  intro ax hmem
  simp only [axioms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · -- defAxiom
    simp only [defAxiom, Formula.iff, Formula.eval]
    intro v
    have hA : (SpecFn.isDefined s.name s.pvar).eval
        ((s.extend body ρ).updateConst .value s.arg v) ↔ s.definterp body ρ v := by
      simp [pvar, Term.eval]
    have hB := htrans (s.defMatrix body) hdefmat v
    exact ⟨fun h => hB.mpr (hA.mp h), fun h => hA.mpr (hB.mp h)⟩
  · -- valAxiom
    simp only [valAxiom, Term.isTrue, Term.isFalse, Formula.eval]
    intro v
    have hM := htrans (s.matrix body) hmat v
    have hcall : Term.eval ((s.extend body ρ).updateConst .value s.arg v)
        (SpecFn.call s.name s.pvar) = s.funcinterp body ρ v := by
      simp [pvar, Term.eval]
    constructor
    · intro h
      rw [hcall]
      simp only [funcinterp]
      rw [if_pos (hM.mp h)]
      simp [Term.eval]
    · intro h
      rw [hcall]
      simp only [funcinterp]
      rw [if_neg (fun hm => h (hM.mpr hm))]
      simp [Term.eval]

/-- Declaring a validated quantifier symbol preserves the global
spec-function declaration invariants: the generic triple declaration
(`SpecFn.declare_correct`) instantiated with the canonical interpretations,
whose graph shape holds by construction. -/
theorem declare_correct (s : LiftedClosure) (body : Skolemize.DefVal) (Δ : Signature) (Γ : FunCtx)
    (st : State) (ρ : _root_.Env) {Q : Unit → State → _root_.Env → Prop}
    (hv : Valid s Δ)
    (hbody : body.wfIn (s.matrixScope Δ))
    (hdecls : st.decls = Δ) (howns : st.owns = []) (hvars : st.decls.vars = [])
    (hwf : Δ.wf) (hΓwf : FunCtx.wfIn Γ Δ)
    (hΓagree : FunCtx.Agreement Γ ρ)
    (heval : SeqM.eval (s.declare body) st ρ Q) :
    ∃ st' ρ',
      st'.decls = s.extendSignature Δ ∧ st'.owns = [] ∧ st'.decls.vars = [] ∧
      st'.decls.wf ∧ st.decls.Subset st'.decls ∧
      _root_.Env.agreeOn st.decls ρ ρ' ∧
      FunCtx.wfIn (Γ ++ [(s.name, s.name)]) st'.decls ∧
      FunCtx.Agreement (Γ ++ [(s.name, s.name)]) ρ' ∧
      Q () st' ρ' := by
  have hf : SpecFnFresh Δ s.name s.arg :=
    { symFresh := by
        intro n hn
        simp only [SpecFn.names, List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl
        exacts [hv.relFresh, hv.funcFresh, hv.defFresh]
      argFresh := by
        simp [SpecFn.names, hv.argFresh, hv.argNeRel, hv.argNeFunc, hv.argNeDef] }
  have hh : SpecFnFresh.WithRes Δ s.name s.arg s.idx :=
    { toSpecFnFresh := hf
      resFresh := by
        simp [SpecFn.names, hv.idxFresh, hv.idxNeRel, hv.idxNeFunc, hv.idxNeDef,
          hv.idxNeArg] }
  have hwfext : (s.extendSignature Δ).wf := hf.sigBoth_wf hwf
  have hsub : Δ.Subset (s.extendSignature Δ) :=
    ((Signature.Subset.subset_addBinaryRel _ _).trans
      (Signature.Subset.subset_addUnary _ _)).trans
      (Signature.Subset.subset_addUnaryRel _ _)
  have hargext : s.arg ∉ (s.extendSignature Δ).allNames := hf.argFresh_sigBoth
  have hidxext : s.idx ∉ (s.extendSignature Δ).allNames := by
    intro hmem
    apply hh.resFresh_sigBothArg
    show s.idx ∈ (s.argScope (s.extendSignature Δ)).allNames
    rw [Signature.allNames_declVar_of_not_in hargext]
    exact List.mem_cons_of_mem _ hmem
  have hbodyext : body.wfIn (s.matrixScope (s.extendSignature Δ)) := by
    have hsubpi := Signature.Subset.declVar
      (Signature.Subset.declVar hsub ⟨s.arg, .value⟩) ⟨s.idx, .int⟩
    have hwfpi : (s.matrixScope (s.extendSignature Δ)).wf :=
      Signature.wf_declVar (Signature.wf_declVar hwfext)
    exact ⟨Term.wfIn_mono body.value hbody.1 hsubpi hwfpi,
      Formula.wfIn_mono body.defined hbody.2 hsubpi hwfpi⟩
  have haxwf : ∀ ax ∈ s.axioms body, ax.formula.wfIn (s.extendSignature Δ) :=
    s.axioms_wfIn hwfext hbodyext (List.Mem.head _) (List.Mem.head _)
      hargext hidxext hv.idxNeArg
  have haxeval : ∀ ax ∈ s.axioms body,
      ax.formula.eval (SpecFn.Env.both ρ s.name
        (s.relinterp body ρ) (s.definterp body ρ) (s.funcinterp body ρ)) :=
    s.axioms_eval (Δ := Δ)
      (s.matrix_wfIn hwf hbody hv.argFresh hv.idxFresh hv.idxNeArg)
      (s.defMatrix_wfIn hwf hbody hv.argFresh hv.idxFresh hv.idxNeArg)
      hv.relFresh hv.funcFresh hv.defFresh
  obtain ⟨st', ρ', _, hrest⟩ :=
    SpecFn.declare_correct s.name s.name (s.axioms body)
      (s.relinterp body ρ) (s.funcinterp body ρ) (s.definterp body ρ) Δ Γ st ρ
      hv.relFresh hv.funcFresh hv.defFresh (fun _ _ => Iff.rfl)
      hdecls howns hvars hwfext hΓwf hΓagree haxwf haxeval heval
  exact ⟨st', ρ', hrest⟩

end Verifier.LiftedClosure

/-! ## Declaring the lifted closures of a declaration -/

namespace Verifier.Env

open PureEncoding

/-- Declare a bounded quantifier's solver-facing triple and its defining
axioms. All freshness and membership conditions needed by the soundness proof
are checked operationally by `validate`. -/
private def declareLifting (env : Env) (s : Verifier.LiftedClosure) : SeqM Env :=
  match s.validate env.signature with
  | .error msg => SeqM.fatal msg
  | .ok _ =>
      match s.compile env.registry.primitives env.specFunctions env.signature with
      | .error msg => SeqM.fatal msg
      | .ok body => do
          s.declare body
          pure { env with
                 specFunctions := env.specFunctions ++ [(s.name, s.name)],
                 signature := s.extendSignature env.signature }

/-- Compile and declare the lifted bounded quantifiers in lift order. Earlier
symbols are available while compiling later bodies, which supports nesting. -/
def declareLiftings : Env → List Verifier.LiftedClosure → SeqM Env
  | env, [] => pure env
  | env, s :: ss => do
      let env' ← declareLifting env s
      declareLiftings env' ss

/-- Compiling and declaring one lifted bounded quantifier preserves `SpecInv`. -/
private theorem declareLifting_correct {reg : Registry} {Θ : TinyML.TypeEnv}
    (hlaw : reg.primitives.Lawful) (s : Verifier.LiftedClosure)
    (env : Env) (st : State) (ρ : _root_.Env)
    {Q : Env → State → _root_.Env → Prop}
    (hinv : SpecInv reg Θ env st ρ)
    (heval : SeqM.eval (declareLifting env s) st ρ Q) :
    ∃ env' st' ρ', SpecInv reg Θ env' st' ρ' ∧
      st.decls.Subset st'.decls ∧ Env.agreeOn st.decls ρ ρ' ∧
      Q env' st' ρ' := by
  obtain ⟨hreg, htypes, hacc, howns, hvars, hwf, hΓwf, hΓagree, hu⟩ := hinv
  simp only [declareLifting] at heval
  cases hvalid : s.validate env.signature with
  | error msg =>
    simp only [hvalid] at heval
    exact (SeqM.eval_fatal heval).elim
  | ok v =>
    simp only [hvalid] at heval
    cases hcompile : s.compile env.registry.primitives env.specFunctions env.signature with
    | error msg =>
      simp only [hcompile] at heval
      exact (SeqM.eval_fatal heval).elim
    | ok body =>
      simp only [hcompile] at heval
      have hbody := Verifier.LiftedClosure.compile_wfIn (hreg ▸ hlaw)
        v.down (hacc ▸ hwf) (hacc ▸ hΓwf) hcompile
      obtain ⟨st4, ρ4, hdelta, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hΓagree4, hcont⟩ :=
        Verifier.LiftedClosure.declare_correct s body env.signature
          env.specFunctions st ρ v.down hbody hacc.symm howns hvars
          (hacc ▸ hwf) (hacc ▸ hΓwf) hΓagree (SeqM.eval_bind heval)
      exact ⟨{ env with
               specFunctions := env.specFunctions ++ [(s.name, s.name)],
               signature := s.extendSignature env.signature }, st4, ρ4,
        ⟨hreg, htypes, hdelta.symm, howns4, hvars4, hwf4, hΓwf4, hΓagree4, hu.mono hsub4 hagree4 hwf4⟩,
        hsub4, hagree4, SeqM.eval_ret hcont⟩

theorem declareLiftings_correct {reg : Registry} {Θ : TinyML.TypeEnv}
    (hlaw : reg.primitives.Lawful) (ss : List Verifier.LiftedClosure) :
    ∀ (env : Env) (st : State) (ρ : _root_.Env)
      {Q : Env → State → _root_.Env → Prop},
      SpecInv reg Θ env st ρ →
      SeqM.eval (declareLiftings env ss) st ρ Q →
      ∃ result stRel ρRel, SpecInv reg Θ result stRel ρRel ∧
        st.decls.Subset stRel.decls ∧ Env.agreeOn st.decls ρ ρRel ∧
        Q result stRel ρRel := by
  induction ss with
  | nil =>
    intro env st ρ Q hinv heval
    simp only [declareLiftings] at heval
    exact ⟨env, st, ρ, hinv, Signature.Subset.refl _, Env.agreeOn_refl,
      SeqM.eval_ret heval⟩
  | cons s ss ih =>
    intro env st ρ Q hinv heval
    simp only [declareLiftings] at heval
    obtain ⟨env1, st1, ρ1, hinv1, hsub1, hag1, hcont1⟩ :=
      declareLifting_correct hlaw s env st ρ hinv (SeqM.eval_bind heval)
    obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ :=
      ih env1 st1 ρ1 hinv1 hcont1
    exact ⟨result, stRel, ρRel, hinvRel, hsub1.trans hsubRel,
      Env.agreeOn_trans hag1 (Env.agreeOn_mono hsub1 hagRel), hQ⟩

end Verifier.Env
