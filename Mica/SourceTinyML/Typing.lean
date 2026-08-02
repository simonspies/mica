-- SUMMARY: Elaboration and typechecking from the untyped IR to the typed IR.
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.Untyped
import Mica.SourceTinyML.Typed
import Mica.TinyML.RuntimeExpr
import Mica.SourceTinyML.Assertions
import Mica.SourceTinyML.TypeConstraints
import Mica.SourceTinyML.Printer
import Mica.Base.Except

namespace TinyML

/-! ## Type contexts -/

abbrev TyCtx := TinyML.Var → Option Typ

def TyCtx.empty : TyCtx := fun _ => none

def TyCtx.extend (Γ : TyCtx) (x : TinyML.Var) (t : Typ) : TyCtx :=
  fun y => if y == x then some t else Γ y

def TyCtx.extendBinder (Γ : TyCtx) (b : Typed.Binder) (t : Typ) : TyCtx :=
  match b.name with
  | none => Γ
  | some x => Γ.extend x t

@[simp] theorem TyCtx.extend_eq (Γ : TyCtx) (x : TinyML.Var) (t : Typ) :
    (Γ.extend x t) x = some t := by simp [TyCtx.extend]

@[simp] theorem TyCtx.extend_ne (Γ : TyCtx) (x y : TinyML.Var) (t : Typ) (h : y ≠ x) :
    (Γ.extend x t) y = Γ y := by
  simp [TyCtx.extend, h]

/-- Extending a context along a list of name/type pairs leaves every name
    outside that list untouched. -/
theorem TyCtx.foldl_extend_of_not_mem (Γ : TyCtx) (ps : List (TinyML.Var × Typ))
    (y : TinyML.Var) (hy : y ∉ ps.map Prod.fst) :
    (ps.foldl (fun ctx (p : TinyML.Var × Typ) => ctx.extend p.1 p.2) Γ) y = Γ y := by
  induction ps generalizing Γ with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    rw [List.foldl_cons, ih _ (by simpa using hy.2), TyCtx.extend_ne _ _ _ _ hy.1]

/-- Γ ≤ Γ': Γ' extends Γ pointwise. -/
def TyCtx.le (Γ Γ' : TyCtx) : Prop := ∀ x t, Γ x = some t → Γ' x = some t

instance : LE TyCtx := ⟨TyCtx.le⟩

theorem TyCtx.le_refl (Γ : TyCtx) : Γ ≤ Γ := fun _ _ h => h

theorem TyCtx.le_trans {Γ₁ Γ₂ Γ₃ : TyCtx} (h12 : Γ₁ ≤ Γ₂) (h23 : Γ₂ ≤ Γ₃) : Γ₁ ≤ Γ₃ :=
  fun x t h => h23 x t (h12 x t h)

/-- Monotonicity of `extendBinder` w.r.t. context ordering. -/
theorem TyCtx.le_extendBinder_congr {Γ Γ' : TyCtx} (b : Typed.Binder) (t : Typ)
    (hle : Γ ≤ Γ') : Γ.extendBinder b t ≤ Γ'.extendBinder b t := by
  intro y ty hy
  cases hname : b.name with
  | none =>
    simp [TyCtx.extendBinder, hname] at hy ⊢
    exact hle y ty hy
  | some x =>
    simp only [TyCtx.extendBinder, hname, TyCtx.extend] at hy ⊢
    by_cases h : y == x
    · simp [h] at hy ⊢; exact hy
    · simp [h] at hy ⊢; exact hle y ty hy

-- foldl extend doesn't change the value at x if x doesn't appear in the list.
theorem TyCtx.foldl_extend_stable
    (args : List (TinyML.Var × Typ)) (Γ : TyCtx) (x : TinyML.Var)
    (hx : ∀ a ∈ args, a.1 ≠ x) :
    (args.foldl (fun ctx a => ctx.extend a.1 a.2) Γ) x = Γ x := by
  induction args generalizing Γ with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons]
    have := ih (Γ.extend a.1 a.2) (fun a' ha' => hx a' (.tail _ ha'))
    rw [this]
    have hne := hx a (.head _)
    simp [TyCtx.extend, beq_iff_eq, Ne.symm hne]

end TinyML

namespace Typed

open TinyML

inductive TypeError where
  | undefinedVar (name : TinyML.Var)
  | duplicateType (name : TypeName)
  | operatorMismatch (op : BinOp) (lhs rhs : Typ)
  | unaryMismatch (op : UnOp) (arg : Typ)
  | notAFunction (ty : Typ)
  | arityMismatch (expected actual : Nat)
  | typeMismatch (expected actual : Typ)
  | notASum (ty : Typ)
  | notARef (ty : Typ)
  | notAnArray (ty : Typ)
  | missingReturnType
  | subsumptionFailure (sub super : Typ)
  | spec (msg : String)
  | unknownPrimitive (name : String)
  | cannotInstantiate (name : String) (msg : String)
  | unboundTypeVar (name : TyVar)
  deriving Repr, Inhabited, DecidableEq

instance : ToString TypeError where
  toString
    | .undefinedVar name => s!"undefined variable: {name}"
    | .duplicateType name => s!"duplicate type: {name}"
    | .operatorMismatch op lhs rhs =>
        s!"operator {repr op} cannot be applied to {lhs.print} and {rhs.print}"
    | .unaryMismatch op arg =>
        s!"operator {repr op} cannot be applied to {arg.print}"
    | .notAFunction ty => s!"not a function: {ty.print}"
    | .arityMismatch expected actual =>
        s!"arity mismatch: expected {expected}, got {actual}"
    | .typeMismatch expected actual =>
        s!"type mismatch: expected {expected.print}, got {actual.print}"
    | .notASum ty => s!"not a sum type: {ty.print}"
    | .notARef ty => s!"not a ref type: {ty.print}"
    | .notAnArray ty => s!"not an array type: {ty.print}"
    | .missingReturnType => "missing return type"
    | .subsumptionFailure sub super =>
        s!"subsumption failed: {sub.print} is not a subtype of {super.print}"
    | .spec msg => s!"specification error: {msg}"
    | .unknownPrimitive name => s!"unknown primitive: {name}"
    | .cannotInstantiate name msg =>
        s!"cannot instantiate primitive {name}: {msg}"
    | .unboundTypeVar name => s!"unbound type variable '{name}"

def Binder.ofUntyped (b : Untyped.Binder) (ty : Typ) : Typed.Binder :=
  match b with
  | .none => .none ty
  | .named x _ => .named x ty

def extendTyped (Γ : TinyML.TyCtx) (b : Typed.Binder) : TinyML.TyCtx :=
  match b.name with
  | none => Γ
  | some x => Γ.extend x b.ty

def extendTypedList (Γ : TinyML.TyCtx) (bs : List Typed.Binder) : TinyML.TyCtx :=
  bs.foldl extendTyped Γ

def joinAll (Θ : TypeEnv) : List Typ → Typ
  | [] => .value
  | t :: ts => ts.foldl (Typ.join Θ) t

def extendTypeEnv (Θ : TypeEnv) (name : TypeName) (body : DataDecl) : Except TypeError TypeEnv :=
  match Θ name with
  | some _ => .error (.duplicateType name)
  | none => .ok (fun query => if query == name then some body else Θ query)

/-- What typing needs to know about a built-in primitive: its (possibly
    polymorphic) arrow scheme and the typing function computing the type-variable
    instantiation from the inferred argument types. The typing function is
    untrusted — the elaborator re-checks arguments against the instantiated
    scheme, so a wrong instantiation is rejected, never unsound. -/
structure PrimSig where
  scheme : SchemaTyp
  typing : TypeEnv → List Typ → Except String (List (TyVar × Typ))

/-! ## The typing monad

Typing has exactly one effect of its own — failure. The state is there only to
carry whatever effect the ambient environment's callbacks need, and typing never
reads or writes it: it merely threads it through. -/

abbrev TypeM (σ : Type) := StateT σ (Except TypeError)

/-- Fail with a type error, discarding the state. -/
def TypeM.error (e : TypeError) : TypeM σ α := fun _ => .error e

@[simp] theorem TypeM.error_apply (e : TypeError) (s : σ) :
    (TypeM.error e : TypeM σ α) s = .error e := rfl

@[simp] theorem TypeM.pure_apply (a : α) (s : σ) :
    (pure a : TypeM σ α) s = .ok (a, s) := rfl

@[simp] theorem TypeM.error_bind (e : TypeError) (g : α → TypeM σ β) :
    (TypeM.error e >>= g : TypeM σ β) = TypeM.error e := by
  funext s; rfl

/-- Run a pure `Except` computation in `TypeM`, leaving the state untouched. -/
def TypeM.ofExcept : Except TypeError α → TypeM σ α
  | .ok a => fun s => .ok (a, s)
  | .error e => fun _ => .error e

@[simp] theorem TypeM.ofExcept_pure (a : α) :
    (TypeM.ofExcept (.ok a) : TypeM σ α) = pure a := rfl

@[simp] theorem TypeM.ofExcept_error (e : TypeError) :
    (TypeM.ofExcept (.error e) : TypeM σ α) = TypeM.error e := rfl

@[simp] theorem TypeM.ofExcept_ok {r : Except TypeError α} {s s' : σ} {a : α} :
    (TypeM.ofExcept r : TypeM σ α) s = .ok (a, s') ↔ r = .ok a ∧ s' = s := by
  cases r <;> simp [TypeM.ofExcept, eq_comm]

/-- The built-in primitives, the translation of a single typed specification
    expression into its value term and definedness condition, and the globals a
    specification nested in a type is elaborated against — the program's
    bindings as of the declaration whose type carries it. Typing propagates
    whatever effect the translation carries in `σ`. -/
structure SpecEnv (σ : Type) where
  primitive : String → Option PrimSig
  translate : List String → Typed.Expr → TypeM σ (Term .value × Formula)
  globals : TinyML.TyCtx

/-- The domain and result types of `ty` applied to `arity` arguments.
    Applications are n-ary and saturated: a wrong argument count is an arity
    error, not a partial application. -/
def domains (ty : Typ) (arity : Nat) : Except TypeError (List Typ × Typ) :=
  match ty with
  | .arrow doms ret _ =>
      if doms.length == arity then .ok (doms, ret)
      else .error (.arityMismatch doms.length arity)
  | _ => .error (.notAFunction ty)

/-- Subsume an already-inferred argument list against the domain types,
    inserting casts. Used for primitive applications, whose arrow type is only
    known after the instantiation is solved from the inferred argument types. -/
def checkInferred (Θ : TypeEnv) :
    List Typ → List (Typ × Typed.Expr) → Except TypeError (List Typed.Expr)
  | [], [] => .ok []
  | dom :: doms, (argTy, arg) :: rest =>
      if argTy == dom then do
        let args' ← checkInferred Θ doms rest
        .ok (arg :: args')
      else if Typ.sub Θ argTy dom then do
        let args' ← checkInferred Θ doms rest
        .ok (Expr.cast arg dom :: args')
      else .error (.subsumptionFailure argTy dom)
  | doms, rest => .error (.arityMismatch doms.length rest.length)

/-- `checkInferred` preserves erasure: casts are transparent at runtime. -/
theorem checkInferred_runtime (Θ : TypeEnv) :
    (pairs : List (Typ × Typed.Expr)) → ∀ doms result,
      checkInferred Θ doms pairs = .ok result →
      result.map Expr.WithTypeVars.runtime = (pairs.map Prod.snd).map Expr.WithTypeVars.runtime
  | [] => by
      intro doms result h
      cases doms <;> simp [checkInferred] at h
      case nil => cases h; rfl
  | (argTy, arg) :: rest => by
      intro doms result h
      cases doms with
      | nil => simp [checkInferred] at h
      | cons dom doms =>
        simp only [checkInferred] at h
        split at h
        · have ⟨args', hrest, hcont⟩ := Except.bind_ok h
          simp at hcont
          cases hcont
          simp only [List.map]
          rw [checkInferred_runtime Θ rest doms _ hrest]
        · split at h
          · have ⟨args', hrest, hcont⟩ := Except.bind_ok h
            simp at hcont
            cases hcont
            simp only [List.map, Expr.WithTypeVars.runtime]
            rw [checkInferred_runtime Θ rest doms _ hrest]
          · simp at h

/-- Assert all formulas in order before continuing with the assertion body.

Used only to spell out the type constraints of a name a spec binds. That does
not belong here: an `Assertion` binder should carry the type it binds at, and
the constraints should be emitted where the assertion is elaborated, which is
also the layer that knows how a type constrains a term. Until the binders carry
their types, typing expands the constraints on the spot. -/
private def assertAll (φs : List Formula) (k : Assertion Typ α) : Assertion Typ α :=
  φs.foldr .assert k

/-- The formula stating that a leaf's value term is the boolean `true`. -/
private def holds (v : Term .value) : Formula :=
  .eq .bool (.unop .toBool v) (.const (.b true))

/-- Resolve a spec-level variable. The leaf translator represents each spec-level
name by the value-sorted variable of the same name, so resolving one is just a
scope check. -/
private def specVar (names : List String) (x : String) : TypeM σ (Term .value) :=
  if x ∈ names then pure (.var .value x)
  else TypeM.error (.spec s!"unbound spec variable '{x}'")

/-- Elaborate a spec predicate into the atom binding its payload, checking the
scrutinee against both the type context and the spec-level scope. -/
private def elabPred (Γ : TyCtx) (names : List String) (ty : Typ) :
    Spec.Pred → TypeM σ (Atom Typ .value)
  | .isinj tag arity scrut => do pure (.isinj tag arity (← specVar names scrut))
  | .own loc =>
    match Γ loc with
    | some (.owned innerTy) =>
      if innerTy == ty then do pure (.own (← specVar names loc) ty)
      else TypeM.error (.spec s!"own {loc} must bind {repr innerTy}, not {repr ty}")
    | some other => TypeM.error (.spec s!"own {loc} requires an owned reference, got {repr other}")
    | none => TypeM.error (.spec s!"unknown ownership variable '{loc}'")
  | .arr loc =>
    match Γ loc with
    | some (.ownedArray innerTy) =>
      if (.vec innerTy) == ty then do pure (.arr (← specVar names loc) innerTy)
      else TypeM.error (.spec s!"arr {loc} must bind a vector snapshot of type {repr (TinyML.Typ.vec innerTy)}, not {repr ty}")
    | some other => TypeM.error (.spec s!"arr {loc} requires an owned array, got {repr other}")
    | none => TypeM.error (.spec s!"unknown ownership variable '{loc}'")

/-- Match the spec's bound names against the typed function binders to recover
each argument's type. -/
private def specArgTypes : List Typed.Binder → List String → Except TypeError (List (String × Typ))
  | _, [] => .ok []
  | [], _ :: _ => .error (.spec "more arguments than the function declares")
  | b :: bs, n :: ns => do
    let rest ← specArgTypes bs ns
    .ok ((n, b.ty) :: rest)

-- Every function below walks one piece of the declaration being elaborated —
-- a type, a binder, an expression, an assertion — and every call it makes is on
-- a piece nested inside its own, so the size of that piece is the measure.
-- `check` is the one exception: it hands its expression to `infer` unchanged,
-- so it takes the tag that orders it above the others at equal size.
mutual
  /-- Translate a type of the untyped IR into the core type it denotes,
  elaborating every specification it carries. A specification's leaves are
  typechecked in the program's global context extended with the arrow's own
  arguments — never with the binders surrounding the annotation, which the
  function the type describes cannot mention. -/
  def translate (env : SpecEnv σ) (Θ : TypeEnv) : Untyped.Typ → TypeM σ Typ
    | .core t => pure t
    | .tvar v => TypeM.error (.unboundTypeVar v)
    | .sum ts => do pure (.sum (← translateList env Θ ts))
    | .arrow args ret spec => do
        let args' ← translateList env Θ args
        let ret' ← translate env Θ ret
        match spec with
        | none => pure (.arrow args' ret' none)
        | some rb => do
            let s ← elabSpecBody env Θ env.globals (args'.map Typed.Binder.none) ret' rb
            pure (.arrow args' ret' (some s))
    | .ref t => do pure (.ref (← translate env Θ t))
    | .array t => do pure (.array (← translate env Θ t))
    | .ownedArray t => do pure (.ownedArray (← translate env Θ t))
    | .vec t => do pure (.vec (← translate env Θ t))
    | .owned t => do pure (.owned (← translate env Θ t))
    | .tuple ts => do pure (.tuple (← translateList env Θ ts))
    | .named n args => do pure (.named n (← translateList env Θ args))
  termination_by ty => (sizeOf ty, 0)

  def translateList (env : SpecEnv σ) (Θ : TypeEnv) : List Untyped.Typ → TypeM σ (List Typ)
    | [] => pure []
    | t :: ts => do pure ((← translate env Θ t) :: (← translateList env Θ ts))
  termination_by ts => (sizeOf ts, 0)

  def translateOpt (env : SpecEnv σ) (Θ : TypeEnv) : Option Untyped.Typ → TypeM σ (Option Typ)
    | none => pure none
    | some t => do pure (some (← translate env Θ t))
  termination_by t => (sizeOf t, 0)

  /-- The type a binder is checked at: its own annotation, translated, or the
  fallback its context supplies. -/
  def Binder.expectedTy (env : SpecEnv σ) (Θ : TypeEnv) (b : Untyped.Binder) (fallback : Typ) :
      TypeM σ Typ :=
    match b with
    | .named _ (some ty) => translate env Θ ty
    | _ => pure fallback
  termination_by (sizeOf b, 0)

  /-- Type a function's argument binders, defaulting an unannotated argument to
  `value`. -/
  def typedBinders (env : SpecEnv σ) (Θ : TypeEnv) :
      List Untyped.Binder → TypeM σ (List Typed.Binder)
    | [] => pure []
    | b :: bs => do
        let ty ← Binder.expectedTy env Θ b .value
        pure (Typed.Binder.ofUntyped b ty :: (← typedBinders env Θ bs))
  termination_by bs => (sizeOf bs, 0)

  /-- Type the binders of a product pattern against the component types the
  bound expression supplies. -/
  def inferProductBinders (env : SpecEnv σ) (Θ : TypeEnv) :
      List Untyped.Binder → List Typ → TypeM σ (List Typed.Binder)
    | [], [] => pure []
    | binder :: binders, ty :: tys => do
        let binderTy ← Binder.expectedTy env Θ binder ty
        if Typ.sub Θ ty binderTy then do
          let rest ← inferProductBinders env Θ binders tys
          pure (Typed.Binder.ofUntyped binder binderTy :: rest)
        else
          TypeM.error (.subsumptionFailure ty binderTy)
    | binders, tys => TypeM.error (.arityMismatch tys.length binders.length)
  termination_by bs _ => (sizeOf bs, 0)

  def infer (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) : Untyped.Expr → TypeM σ (Typ × Typed.Expr)
    | .const c => pure (Typed.Const.ty c, .const c)
    | .var x =>
        match Γ x with
        | some ty => pure (ty, .var x ty)
        | none => TypeM.error (.undefinedVar x)
    | .prim n =>
        match env.primitive n with
        | none => TypeM.error (.unknownPrimitive n)
        | some sig =>
          match SchemaTyp.close (fun _ => none) sig.scheme with
          | .ok ty => pure (ty, .prim n [] ty)
          | .error _ =>
            TypeM.error (.cannotInstantiate n "a polymorphic primitive must be applied")
    | .unop op e => do
        let (argTy, e') ← infer env Θ Γ e
        match TinyML.UnOp.typeOf op argTy with
        | some ty => pure (ty, .unop op e' ty)
        | none => TypeM.error (.unaryMismatch op argTy)
    | .binop op lhs rhs => do
        let (lhsTy, lhs') ← infer env Θ Γ lhs
        let (rhsTy, rhs') ← infer env Θ Γ rhs
        match TinyML.BinOp.typeOf op lhsTy rhsTy with
        | some ty => pure (ty, .binop op lhs' rhs' ty)
        | none => TypeM.error (.operatorMismatch op lhsTy rhsTy)
    | .fix self args retTy body => do
        let retTy := (← translateOpt env Θ retTy).getD .value
        let typedArgs ← typedBinders env Θ args
        let selfTy := Typ.arrow (typedArgs.map Binder.WithTypeVars.ty) retTy none
        let typedSelf := Typed.Binder.ofUntyped self selfTy
        let Γ' := typedArgs.foldl extendTyped (extendTyped Γ typedSelf)
        let body' ← check env Θ Γ' body retTy
        pure (selfTy, .fix typedSelf typedArgs retTy none body')
    | .app fn args =>
        match fn.primName? with
        | some n =>
          match env.primitive n with
          | none => TypeM.error (.unknownPrimitive n)
          | some sig => do
            let inferred ← inferList env Θ Γ args
            match sig.typing Θ (inferred.map Prod.fst) with
            | .error msg => TypeM.error (.cannotInstantiate n msg)
            | .ok inst =>
              match SchemaTyp.close (fun v => inst.lookup v) sig.scheme with
              | .ok ty => do
                let (doms, retTy) ← TypeM.ofExcept (domains ty inferred.length)
                let args' ← TypeM.ofExcept (checkInferred Θ doms inferred)
                pure (retTy, .app (.prim n inst ty) args' retTy)
              | .error v =>
                TypeM.error (.cannotInstantiate n s!"unresolved type variable '{v}")
        | none => do
            let (fnTy, fn') ← infer env Θ Γ fn
            let (doms, retTy) ← TypeM.ofExcept (domains fnTy args.length)
            let args' ← checkArgs env Θ Γ doms args
            pure (retTy, .app fn' args' retTy)
    | .ifThenElse cond thn els => do
        let cond' ← check env Θ Γ cond .bool
        let (thnTy, thn') ← infer env Θ Γ thn
        let (elsTy, els') ← infer env Θ Γ els
        let ty := Typ.join Θ thnTy elsTy
        let thn'' := if thnTy == ty then thn' else .cast thn' ty
        let els'' := if elsTy == ty then els' else .cast els' ty
        pure (ty, .ifThenElse cond' thn'' els'' ty)
    | .letIn name bound body => do
        let (boundTy, bound') ←
          match name with
          | .named _ (some ty) => do
              let ty' ← translate env Θ ty
              let e' ← check env Θ Γ bound ty'
              pure (ty', e')
          | _ => infer env Θ Γ bound
        let typedName := Typed.Binder.ofUntyped name boundTy
        let (bodyTy, body') ← infer env Θ (extendTyped Γ typedName) body
        pure (bodyTy, .letIn typedName bound' body')
    | .letProd names bound body => do
        let (boundTy, bound') ← infer env Θ Γ bound
        let tys ← match boundTy with
          | .tuple tys => pure tys
          | _ => TypeM.error (.typeMismatch (.tuple []) boundTy)
        let typedNames ← inferProductBinders env Θ names tys
        let (bodyTy, body') ← infer env Θ (extendTypedList Γ typedNames) body
        pure (bodyTy, .letProd typedNames bound' body')
    | .ref ownership e => do
        let (ty, e') ← infer env Θ Γ e
        let refTy := match ownership with
          | .owned => .owned ty
          | .shared => .ref ty
        pure (refTy, .ref ownership e')
    | .deref e => do
        let (ty, e') ← infer env Θ Γ e
        match ty with
        | .ref inner | .owned inner => pure (inner, .deref e' inner)
        | _ => TypeM.error (.notARef ty)
    | .store loc val => do
        let (locTy, loc') ← infer env Θ Γ loc
        match locTy with
        | .ref inner | .owned inner =>
            let val' ← check env Θ Γ val inner
            pure (.unit, .store loc' val')
        | _ => TypeM.error (.notARef locTy)
    | .arrayMake ownership len init => do
        let len' ← check env Θ Γ len .int
        let (elemTy, init') ← infer env Θ Γ init
        let arrayTy := match ownership with
          | .owned => .ownedArray elemTy
          | .shared => .array elemTy
        pure (arrayTy, .arrayMake ownership len' init')
    | .arrayLen arr => do
        let (arrTy, arr') ← infer env Θ Γ arr
        match arrTy with
        | .array _ | .ownedArray _ => pure (.int, .arrayLen arr')
        | _ => TypeM.error (.notAnArray arrTy)
    | .arrayGet arr idx => do
        let (arrTy, arr') ← infer env Θ Γ arr
        let idx' ← check env Θ Γ idx .int
        match arrTy with
        | .array elemTy | .ownedArray elemTy => pure (elemTy, .arrayGet arr' idx' elemTy)
        | _ => TypeM.error (.notAnArray arrTy)
    | .arraySet arr idx val => do
        let (arrTy, arr') ← infer env Θ Γ arr
        let idx' ← check env Θ Γ idx .int
        match arrTy with
        | .array elemTy | .ownedArray elemTy =>
            let val' ← check env Θ Γ val elemTy
            pure (.unit, .arraySet arr' idx' val')
        | _ => TypeM.error (.notAnArray arrTy)
    | .assert e => do
        let e' ← check env Θ Γ e .bool
        pure (.unit, .assert e')
    | .tuple es => do
        let pairs ← inferList env Θ Γ es
        pure (.tuple (pairs.map Prod.fst), .tuple (pairs.map Prod.snd))
    | .inj tag arity payload => do
        let (ty, payload') ← infer env Θ Γ payload
        pure (.sum ((List.replicate arity .empty).set tag ty), .inj tag arity payload')
    | .match_ scrutinee branches => do
        let (scrutTy, scrut') ← infer env Θ Γ scrutinee
        -- Resolve the scrutinee type: accept sum directly, or unfold a named type and insert a cast.
        match scrutTy with
        | .sum ts =>
                if _h : ts.length = branches.length then
                  let branches' ← inferBranches env Θ Γ ts branches
                  let ty := joinAll Θ (branches'.map (fun p => p.2.ty))
                  let branches'' := branches'.map fun
                    | (binder, body) =>
                        (binder, if body.ty == ty then body else .cast body ty)
                  pure (ty, .match_ scrut' branches'' ty)
                else
                  TypeM.error (.arityMismatch ts.length branches.length)
        | .named T args =>
                match TypeName.unfold Θ T args with
                | some (.sum ts) =>
                    if _h : ts.length = branches.length then
                      let branches' ← inferBranches env Θ Γ ts branches
                      let ty := joinAll Θ (branches'.map (fun p => p.2.ty))
                      let branches'' := branches'.map fun
                        | (binder, body) =>
                            (binder, if body.ty == ty then body else .cast body ty)
                      -- Insert a cast to unfold the named type before matching.
                      pure (ty, .match_ (.cast scrut' (.sum ts)) branches'' ty)
                    else
                      TypeM.error (.arityMismatch ts.length branches.length)
                | _ => TypeM.error (.notASum scrutTy)
        | _ => TypeM.error (.notASum scrutTy)
  termination_by e => (sizeOf e, 0)

  def check (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      Untyped.Expr → Typ → TypeM σ Typed.Expr
    -- A function literal checked against a specified arrow is elaborated at that
    -- arrow: it takes the expected signature, records the specification, and its
    -- self-reference is typed at the specified arrow — the same shape a specified
    -- declaration gets. Inferring the literal first could never reach a specified
    -- arrow, since those are invariant and an inferred literal carries no spec.
    | .fix self args retTy body, .arrow doms ret (some s) => do
        let typedArgs ← checkBinders env Θ args doms
        let ann ← translateOpt env Θ retTy
        if ann.any (· != ret) then
          TypeM.error (.subsumptionFailure ret (ann.getD ret))
        else
          -- The self-reference is typed at the specified arrow, so a recursive
          -- call goes through the specification.
          let typedSelf :=
            Typed.Binder.ofUntyped self (.arrow (typedArgs.map Binder.WithTypeVars.ty) ret (some s))
          let Γ' := typedArgs.foldl extendTyped (extendTyped Γ typedSelf)
          let body' ← check env Θ Γ' body ret
          pure (.fix typedSelf typedArgs ret (some s) body')
    -- A tuple checked against a tuple type is checked componentwise. A record
    -- literal is a tuple, so this is how a field declared at a specified arrow
    -- receives one: inference alone could never produce a specified arrow, and
    -- subsumption cannot repair that, since a specified arrow is invariant.
    --
    -- Tuples are the only type former that pushes the expected type inward.
    -- Every other one that can hold a function has the same gap: a constructor
    -- payload (`Fn (fun x -> ...)`), a reference (`ref (fun x -> ...)`), an
    -- array element. Each needs its own rule here, and unlike this one they are
    -- not exact — the type they build subsumes into the expected type rather
    -- than matching it — so they also need the subsumption step below.
    | .tuple es, .tuple tys => do
        pure (.tuple (← checkArgs env Θ Γ tys es))
    -- Everything else is checked by inference, subsuming into the expected type.
    | e, expected => do
        let (actual, e') ← infer env Θ Γ e
        if actual == expected then
          pure e'
        else if Typ.sub Θ actual expected then
          pure (.cast e' expected)
        else
          TypeM.error (.subsumptionFailure actual expected)
  termination_by e => (sizeOf e, 1)

  /-- Type a function literal's binders at the domains its expected arrow
  supplies. An annotation is allowed, but it has to agree: a specified arrow is
  invariant, so there is nothing to subsume. -/
  def checkBinders (env : SpecEnv σ) (Θ : TypeEnv) :
      List Untyped.Binder → List Typ → TypeM σ (List Typed.Binder)
    | [], [] => pure []
    | b :: bs, ty :: tys => do
        let annotated ← Binder.expectedTy env Θ b ty
        if annotated == ty then do
          let rest ← checkBinders env Θ bs tys
          pure (Typed.Binder.ofUntyped b ty :: rest)
        else
          TypeM.error (.subsumptionFailure ty annotated)
    | bs, tys => TypeM.error (.arityMismatch tys.length bs.length)
  termination_by bs _ => (sizeOf bs, 0)

  def inferList (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) : List Untyped.Expr → TypeM σ (List (Typ × Typed.Expr))
    | [] => pure []
    | e :: es => do
        let head ← infer env Θ Γ e
        let tail ← inferList env Θ Γ es
        pure (head :: tail)
  termination_by es => (sizeOf es, 0)

  /-- Check an argument list against the domain types of the function applied. -/
  def checkArgs (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      List Typ → List Untyped.Expr → TypeM σ (List Typed.Expr)
    | [], [] => pure []
    | dom :: doms, arg :: args => do
        let arg' ← check env Θ Γ arg dom
        let args' ← checkArgs env Θ Γ doms args
        pure (arg' :: args')
    | doms, args => TypeM.error (.arityMismatch doms.length args.length)
  termination_by _ args => (sizeOf args, 0)

  def inferBranches (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      List Typ → List (Untyped.Binder × Untyped.Expr) → TypeM σ (List (Typed.Binder × Typed.Expr))
    | [], [] => pure []
    | ty :: tys, (binder, body) :: rest => do
        let binderTy ← Binder.expectedTy env Θ binder ty
        if Typ.sub Θ ty binderTy then
          let typedBinder := Typed.Binder.ofUntyped binder binderTy
          let (_bodyTy, body') ← infer env Θ (extendTyped Γ typedBinder) body
          let rest' ← inferBranches env Θ Γ tys rest
          pure ((typedBinder, body') :: rest')
        else
          TypeM.error (.subsumptionFailure ty binderTy)
    | tys, bs => TypeM.error (.arityMismatch tys.length bs.length)
  termination_by _ bs => (sizeOf bs, 0)

  /-- Elaborate a postcondition into a verifier assertion in one walk: each leaf
  is typechecked and then translated, and its definedness condition is asserted
  before the value it guards is bound or tested. -/
  def elabPost (env : SpecEnv σ) (Θ : TypeEnv) :
      TyCtx → List String → Spec.Assert Untyped.Expr Untyped.Typ Unit →
        TypeM σ (Assertion Typ Unit)
    | _, _, .ret () => pure (.ret ())
    | Γ, ns, .assert cond rest => do
      let cond' ← check env Θ Γ cond .bool
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.assert (holds v) (← elabPost env Θ Γ ns rest)))
    | Γ, ns, .let_ x e rest => do
      let (ty, e') ← infer env Θ Γ e
      let (v, defd) ← env.translate ns e'
      pure (.assert defd (.let_ ⟨x, .value⟩ v
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← elabPost env Θ (Γ.extend x ty) (ns ++ [x]) rest))))
    | Γ, ns, .bind p x ty rest => do
      let ty ← translate env Θ ty
      let atom ← elabPred Γ ns ty p
      pure (.pred ⟨x, .value⟩ atom
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← elabPost env Θ (Γ.extend x ty) (ns ++ [x]) rest)))
    | Γ, ns, .ite cond thn els => do
      let cond' ← check env Θ Γ cond .bool
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.ite (holds v)
        (← elabPost env Θ Γ ns thn) (← elabPost env Θ Γ ns els)))
  termination_by _ _ a => (sizeOf a, 0)

  /-- Elaborate a precondition the same way, ending in the postcondition the
  result must satisfy — elaborated with the result name bound at the function's
  return type. -/
  def elabPre (env : SpecEnv σ) (Θ : TypeEnv) (retTy : Typ) :
      TyCtx → List String → Spec.Pre Untyped.Expr Untyped.Typ → TypeM σ (PredTrans Typ)
    | Γ, ns, .ret post => do
      let body' ← elabPost env Θ (Γ.extend post.name retTy) (ns ++ [post.name]) post.body
      pure (.ret ⟨post.name, body'⟩)
    | Γ, ns, .assert cond rest => do
      let cond' ← check env Θ Γ cond .bool
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.assert (holds v) (← elabPre env Θ retTy Γ ns rest)))
    | Γ, ns, .let_ x e rest => do
      let (ty, e') ← infer env Θ Γ e
      let (v, defd) ← env.translate ns e'
      pure (.assert defd (.let_ ⟨x, .value⟩ v
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← elabPre env Θ retTy (Γ.extend x ty) (ns ++ [x]) rest))))
    | Γ, ns, .bind p x ty rest => do
      let ty ← translate env Θ ty
      let atom ← elabPred Γ ns ty p
      pure (.pred ⟨x, .value⟩ atom
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← elabPre env Θ retTy (Γ.extend x ty) (ns ++ [x]) rest)))
    | Γ, ns, .ite cond thn els => do
      let cond' ← check env Θ Γ cond .bool
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.ite (holds v)
        (← elabPre env Θ retTy Γ ns thn) (← elabPre env Θ retTy Γ ns els)))
  termination_by _ _ a => (sizeOf a, 0)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (obtain ⟨name, body⟩ := post; simp; omega)

  /-- Elaborate a spec body against its function's typed signature, layering the
  spec's arguments on top of the program's global bindings `Γbase`. The argument
  and return types recovered here type the spec's leaf expressions; the `Spec`
  itself keeps only the argument names, since the types belong to the function's
  arrow. -/
  def elabSpecBody (env : SpecEnv σ) (Θ : TypeEnv) (Γbase : TyCtx)
      (argBinders : List Typed.Binder) (retTy : Typ)
      (rb : Untyped.SpecBody) : TypeM σ (Spec Typ) := do
    let names := rb.args
    let argTys ← TypeM.ofExcept (specArgTypes argBinders names)
    let Γ₀ : TyCtx := argTys.foldl (fun Γ p => Γ.extend p.1 p.2) Γbase
    let pred ← elabPre env Θ retTy Γ₀ names rb.pre
    pure { args := names, pred := pred }
  termination_by (sizeOf rb, 0)
  decreasing_by obtain ⟨args, pre⟩ := rb; simp; omega
end

mutual

/-- Translate a payload type, keeping the declaration's own type parameters as
variables. A payload that carries a specification has no variables to keep —
`translate` rejects them everywhere else — so it is translated as an ordinary
type and embedded. -/
def translateSchema (env : SpecEnv σ) (Θ : TypeEnv) : Untyped.Typ → TypeM σ SchemaTyp
  | .core t => pure (Typ.subst Empty.elim t)
  | .tvar v => pure (.tvar v)
  | .sum ts => do pure (.sum (← translateSchemaList env Θ ts))
  | .arrow args ret none => do
      pure (.arrow (← translateSchemaList env Θ args) (← translateSchema env Θ ret) none)
  | t@(.arrow _ _ (some _)) => do pure (Typ.subst Empty.elim (← translate env Θ t))
  | .ref t => do pure (.ref (← translateSchema env Θ t))
  | .array t => do pure (.array (← translateSchema env Θ t))
  | .ownedArray t => do pure (.ownedArray (← translateSchema env Θ t))
  | .vec t => do pure (.vec (← translateSchema env Θ t))
  | .owned t => do pure (.owned (← translateSchema env Θ t))
  | .tuple ts => do pure (.tuple (← translateSchemaList env Θ ts))
  | .named n args => do pure (.named n (← translateSchemaList env Θ args))
termination_by t => sizeOf t

def translateSchemaList (env : SpecEnv σ) (Θ : TypeEnv) :
    List Untyped.Typ → TypeM σ (List SchemaTyp)
  | [] => pure []
  | t :: ts => do
      pure ((← translateSchema env Θ t) :: (← translateSchemaList env Θ ts))
termination_by ts => sizeOf ts

end

/-- Lower a data declaration's payloads, elaborating any specification they
carry. A constructor payload is a type like any other, so it may describe a
specified function; its specification is elaborated once, against the bindings
in scope where the declaration stands. (A record's fields take a different
route: the frontend inlines a record type as a tuple, so a field's
specification is elaborated at each mention of the record type instead.) -/
def translateDataDecl (env : SpecEnv σ) (Θ : TypeEnv) (d : Untyped.DataDecl) :
    TypeM σ TinyML.DataDecl := do
  pure { tparams := d.tparams, payloads := ← translateSchemaList env Θ d.payloads }

theorem Binder.ofUntyped_runtime (b : Untyped.Binder) (ty : Typ) :
    (Typed.Binder.ofUntyped b ty).runtime = b.runtime := by
  cases b <;> rfl

theorem typedBinders_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    ∀ (binders : List Untyped.Binder) (typed : List Typed.Binder) (s s' : σ),
      typedBinders env Θ binders s = .ok (typed, s') →
        typed.map Typed.Binder.WithTypeVars.runtime = binders.map Untyped.Binder.runtime
  | [], typed, s, s', h => by
      simp [typedBinders] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | b :: bs, typed, s, s', h => by
      unfold typedBinders at h
      have ⟨ty, s₀, _hty, hcont⟩ := StateT.bind_ok h
      have ⟨rest, s₁, hrest, hcont⟩ := StateT.bind_ok hcont
      rcases (by simpa using hcont) with ⟨rfl, rfl⟩
      simp [Binder.ofUntyped_runtime, typedBinders_runtime env Θ bs rest s₀ s₁ hrest]

theorem checkBinders_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    ∀ (binders : List Untyped.Binder) (tys : List Typ) (typed : List Typed.Binder) (s s' : σ),
      checkBinders env Θ binders tys s = .ok (typed, s') →
        typed.map Typed.Binder.WithTypeVars.runtime = binders.map Untyped.Binder.runtime
  | [], [], typed, s, s', h => by
      simp [checkBinders] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | b :: bs, ty :: tys, typed, s, s', h => by
      unfold checkBinders at h
      have ⟨annotated, s₀, _hty, hcont⟩ := StateT.bind_ok h
      split at hcont
      · have ⟨rest, s₁, hrest, hcont⟩ := StateT.bind_ok hcont
        rcases (by simpa using hcont) with ⟨rfl, rfl⟩
        simp [Binder.ofUntyped_runtime, checkBinders_runtime env Θ bs tys rest s₀ s₁ hrest]
      · simp at hcont
  | [], _ :: _, typed, s, s', h => by
      simp [checkBinders] at h
  | _ :: _, [], typed, s, s', h => by
      simp [checkBinders] at h

theorem inferProductBinders_runtime (env : SpecEnv σ) (Θ : TypeEnv) :
    ∀ (binders : List Untyped.Binder) (tys : List Typ) (typed : List Typed.Binder) (s s' : σ),
      inferProductBinders env Θ binders tys s = .ok (typed, s') →
        typed.map Typed.Binder.WithTypeVars.runtime = binders.map Untyped.Binder.runtime
  | [], [], typed, s, s', h => by
      simp [inferProductBinders] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | b :: bs, ty :: tys, typed, s, s', h => by
      unfold inferProductBinders at h
      have ⟨binderTy, s₀, _hty, hcont⟩ := StateT.bind_ok h
      split at hcont
      · have ⟨rest, s₁, hrest, hcont⟩ := StateT.bind_ok hcont
        rcases (by simpa using hcont) with ⟨rfl, rfl⟩
        simp [Binder.ofUntyped_runtime,
          inferProductBinders_runtime env Θ bs tys rest s₀ s₁ hrest]
      · simp at hcont
  | [], _ :: _, typed, s, s', h => by
      simp [inferProductBinders] at h
  | _ :: _, [], typed, s, s', h => by
      simp [inferProductBinders] at h

/-! ## Specification elaboration

A spec is elaborated alongside the declaration it annotates, in a single walk.
Its leaf expressions go through the ordinary `infer`/`check` judgments — with the
spec's arguments taking the function's argument types, `bind` binders their
annotated types, and the postcondition result the return type — and each typed
leaf is handed straight to `env.translate`, so the walk produces a `Spec`
directly rather than an intermediate typed spec body. This reuses the global
context from `Program.elaborate`, so a spec may refer to earlier definitions. -/

/-- Elaborate a specified function literal: its signature and specification
first, then its body. Doing the spec before the body is what lets the recursive
self-reference — and hence every call in the body — be typed at the specified
arrow, so a recursive call resolves through the type it is annotated with rather
than through a side table. -/
def elabSpecifiedFix (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (rb : Untyped.SpecBody) : Untyped.Expr → TypeM σ (Spec Typ × Typed.Expr)
  | e@(.fix _ args retTy _) => do
      -- The specification needs the literal's signature, and checking the
      -- literal needs the specification, so the signature is elaborated first
      -- and the literal is then checked at the arrow the two describe.
      let ret := (← translateOpt env Θ retTy).getD .value
      let typedArgs ← typedBinders env Θ args
      let s ← elabSpecBody env Θ Γ typedArgs ret rb
      pure (s, ← check env Θ Γ e (.arrow (typedArgs.map Binder.WithTypeVars.ty) ret (some s)))
  | _ => TypeM.error (.spec "attached to a non-function declaration")

/-- A declaration is specified once. `[@@spec]` and a specification on the
declaration's own type are the same mechanism, so giving both would ask for two
specifications of one function. -/
private def checkSingleSpec (b : Untyped.Binder) : TypeM σ Unit :=
  match b with
  | .named _ (some ann) =>
      if ann.isSpecified then
        TypeM.error (.spec
          "a declaration carries either [@@spec] or a specification on its own type, not both")
      else pure ()
  | _ => pure ()

/-- Check a declaration binder's annotation against the type elaborated for its
body. A specified declaration's type carries its specification, which no
annotation mentions, so the annotation is matched against the bare type. -/
private def checkDeclAnnotation (env : SpecEnv σ) (Θ : TypeEnv) (b : Untyped.Binder) (ty : Typ) :
    TypeM σ Unit :=
  match b with
  | .named _ (some ann) => do
      let ann' ← translate env Θ ann
      if Typ.unspec ty == ann' then pure () else TypeM.error (.subsumptionFailure ty ann')
  | _ => pure ()

def ValDecl.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (d : Untyped.ValDecl Untyped.SpecBody) :
    TypeM σ Typed.ValDecl := do
  match d.spec with
  | some rb => do
      checkSingleSpec d.name
      -- A specified declaration's literal records its specification, so the
      -- declaration's own type — and hence the type every later use is
      -- annotated with — is the specified arrow.
      let (_, body') ← elabSpecifiedFix env Θ Γ rb d.body
      checkDeclAnnotation env Θ d.name body'.ty
      pure { name := Typed.Binder.ofUntyped d.name body'.ty, body := body',
             relation := d.relation }
  | none => do
      let (bodyTy, body') ←
        match d.name with
        | .named _ (some ty) => do
            let ty' ← translate env Θ ty
            let body' ← check env Θ Γ d.body ty'
            pure (ty', body')
        | _ => infer env Θ Γ d.body
      pure { name := Typed.Binder.ofUntyped d.name bodyTy, body := body',
             relation := d.relation }

def Program.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
    Untyped.Program Untyped.SpecBody → TypeM σ (TypeEnv × Typed.Program)
  | [] => pure (Θ, [])
  | d :: ds => do
      match d with
      | .type_ dty =>
          let body ← translateDataDecl { env with globals := Γ } Θ dty.body
          let Θ' ← TypeM.ofExcept (extendTypeEnv Θ dty.name body)
          Program.elaborate env Θ' Γ ds
      | .val_ dval =>
          let d' ← ValDecl.elaborate { env with globals := Γ } Θ Γ dval
          let Γ' := match d'.name.name with
            | some x => Γ.extend x d'.name.ty
            | none => Γ
          let (Θ', ds') ← Program.elaborate env Θ Γ' ds
          pure (Θ', d' :: ds')

private theorem branchListRuntime_cast_joinAll
    (Θ : TypeEnv) (branches' : List (Typed.Binder × Typed.Expr)) :
    Expr.WithTypeVars.branchListRuntime
      (branches'.map fun x =>
        (x.1, if x.2.ty = joinAll Θ (branches'.map (fun p => p.2.ty)) then x.2
              else Expr.cast x.2 (joinAll Θ (branches'.map (fun p => p.2.ty))))) =
    Expr.WithTypeVars.branchListRuntime branches' := by
  simpa [BEq.beq] using
    Typed.Expr.branchListRuntime_castBodies
      (joinAll Θ (branches'.map (fun p => p.2.ty))) branches'

-- The main issue in this block is not the mathematical argument, but convincing
-- Lean's termination checker that the mutual proof recursion is well-founded.
-- The right high-level strategy is to follow the structure of the recursive
-- functions themselves: recurse on the same syntax arguments that `infer`,
-- `check`, `inferList`, `checkArgs`, and `inferBranches` recurse on.
-- However, that alone is not enough. If we phrase the proofs directly as
-- `∀ result, infer Γ e = .ok result → ...` (and similarly for the other
-- mutually recursive judgments), then unpack that equality only afterward,
-- Lean no longer sees the recursive calls as being driven directly by the
-- structurally smaller arguments, and it rejects the mutual definition.
-- The workaround is a lifted continuation style: match on the structural
-- argument immediately, make recursive calls only on the smaller subexpressions
-- or sublists exposed by that match, and let each branch return the implication
-- over successful elaboration results. Once those recursive implications have
-- been obtained in the branch, they can be used freely afterward.
mutual
  theorem infer_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (e : Untyped.Expr) → ∀ s result s', Typed.infer env Θ Γ e s = .ok (result, s') →
        result.2.runtime = e.runtime
    | .const c => by
        intro s result s' h
        simp [Typed.infer] at h
        rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime]
    | .var x => by
        intro s result s' h
        unfold Typed.infer at h
        cases hΓ : Γ x with
        | none => simp [hΓ] at h
        | some ty =>
          simp [hΓ] at h
          rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime]
    | .prim n => by
        intro s result s' h
        unfold Typed.infer at h
        cases hp : env.primitive n with
        | none => simp [hp] at h
        | some sig =>
          cases hc : SchemaTyp.close (fun _ => none) sig.scheme with
          | error _ => simp [hp, hc] at h
          | ok ty =>
            simp [hp, hc] at h
            rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime]
    | .unop op e => by
        let ih := infer_runtime env Θ Γ e
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hinfer, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk argTy e1 =>
          cases hty : TinyML.UnOp.typeOf op argTy with
          | none =>
            simp [hty] at hcont
          | some resTy =>
            rcases (by simpa [hty] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
    | .binop op lhs rhs => by
        let ihL := infer_runtime env Θ Γ lhs
        let ihR := infer_runtime env Θ Γ rhs
        intro s result s' h
        unfold Typed.infer at h
        have ⟨lp, s₀, hlhs, hcont⟩ := StateT.bind_ok h
        cases lp with
        | mk lhsTy lhs' =>
          have ⟨rp, s₁, hrhs, hcont⟩ := StateT.bind_ok hcont
          cases rp with
          | mk rhsTy rhs' =>
            cases hty : TinyML.BinOp.typeOf op lhsTy rhsTy with
            | none =>
              simp [hty] at hcont
            | some resTy =>
              rcases (by simpa [hty] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
              simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihL _ _ _ hlhs, ihR _ _ _ hrhs]
    | .fix self args retTy body => by
        intro s result s' h
        unfold Typed.infer at h
        have ⟨retTy', s₀, _hret, hcont⟩ := StateT.bind_ok h
        have ⟨typedArgs, s₁, hargs, hcont⟩ := StateT.bind_ok hcont
        have ⟨body', s₂, hbody, hcont⟩ := StateT.bind_ok hcont
        let ih := check_runtime env Θ
          (typedArgs.foldl extendTyped
            (extendTyped Γ (Typed.Binder.ofUntyped self
              (Typ.arrow (typedArgs.map Binder.WithTypeVars.ty) (retTy'.getD .value) none))))
          body (retTy'.getD .value)
        rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ hbody, Binder.ofUntyped_runtime,
          typedBinders_runtime env Θ args typedArgs s₀ s₁ hargs]
    | .app fn args => by
        let ihFn := infer_runtime env Θ Γ fn
        let ihArgs := checkArgs_runtime env Θ Γ args
        let ihList := inferList_runtime env Θ Γ args
        intro s result s' h
        unfold Typed.infer at h
        cases hpn : fn.primName? with
        | some n =>
          simp only [hpn] at h
          cases hp : env.primitive n with
          | none => simp [hp] at h
          | some sig =>
            simp only [hp] at h
            have ⟨inferred, s₀, hinf, hcont⟩ := StateT.bind_ok h
            cases hty : sig.typing Θ (inferred.map Prod.fst) with
            | error msg => simp [hty] at hcont
            | ok inst =>
              simp only [hty] at hcont
              cases hinst : SchemaTyp.close (fun v => inst.lookup v) sig.scheme with
              | error v => simp [hinst] at hcont
              | ok ty =>
                simp only [hinst] at hcont
                have ⟨dr, s₁, hdoms, hcont⟩ := StateT.bind_ok hcont
                cases dr with
                | mk doms retTy =>
                  have ⟨args', s₂, hchk, hcont⟩ := StateT.bind_ok hcont
                  rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
                  simp only [Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
                    Untyped.Expr.primName?_runtime hpn]
                  rw [checkInferred_runtime Θ inferred _ _ (TypeM.ofExcept_ok.mp hchk).1,
                    ihList _ _ _ hinf]
        | none =>
          simp only [hpn] at h
          obtain ⟨fp, s₀, hfn, hcont⟩ := StateT.bind_ok h
          obtain ⟨fnTy, fn'⟩ := fp
          obtain ⟨dr, s₁, hdoms, hcont⟩ := StateT.bind_ok hcont
          obtain ⟨doms, retTy⟩ := dr
          obtain ⟨args', s₂, hargs, hcont⟩ := StateT.bind_ok hcont
          rcases (by simpa [hargs] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihFn _ _ _ hfn, ihArgs doms _ _ _ hargs]
    | .ifThenElse cond thn els => by
        let ihCond := check_runtime env Θ Γ cond .bool
        let ihThn := infer_runtime env Θ Γ thn
        let ihEls := infer_runtime env Θ Γ els
        intro s result s' h
        unfold Typed.infer at h
        have ⟨cond', s₀, hcond, hcont⟩ := StateT.bind_ok h
        have ⟨tp, s₁, hthn, hcont⟩ := StateT.bind_ok hcont
        cases tp with
        | mk thnTy thn' =>
          have ⟨ep, s₂, hels, hcont⟩ := StateT.bind_ok hcont
          cases ep with
          | mk elsTy els' =>
            rcases (by simpa [hels] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihCond _ _ _ hcond]
            constructor
            · by_cases hj : thnTy = Typ.join Θ thnTy elsTy
              · rw [if_pos hj]
                exact ihThn _ _ _ hthn
              · rw [if_neg hj]
                simpa [Typed.Expr.WithTypeVars.runtime] using ihThn _ _ _ hthn
            · by_cases hj : elsTy = Typ.join Θ thnTy elsTy
              · rw [if_pos hj]
                exact ihEls _ _ _ hels
              · rw [if_neg hj]
                simpa [Typed.Expr.WithTypeVars.runtime] using ihEls _ _ _ hels
    | .letIn name bound body => by
        intro s result s' h
        cases name with
        | none =>
          unfold Typed.infer at h
          have ⟨p, s₀, hbound, hcont⟩ := StateT.bind_ok h
          cases p with
          | mk boundTy bound' =>
            let typedName := Typed.Binder.ofUntyped .none boundTy
            let ihBound := infer_runtime env Θ Γ bound
            let ihBody := infer_runtime env Θ (extendTyped Γ typedName) body
            have ⟨q, s₁, hbody, hcont⟩ := StateT.bind_ok hcont
            cases q with
            | mk bodyTy body' =>
              rcases (by simpa [typedName, hbody] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
              simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
                Binder.ofUntyped_runtime]
        | named x ann =>
          cases ann with
          | none =>
            unfold Typed.infer at h
            have ⟨p, s₀, hbound, hcont⟩ := StateT.bind_ok h
            cases p with
            | mk boundTy bound' =>
              let typedName := Typed.Binder.ofUntyped (.named x .none) boundTy
              let ihBound := infer_runtime env Θ Γ bound
              let ihBody := infer_runtime env Θ (extendTyped Γ typedName) body
              have ⟨q, s₁, hbody, hcont⟩ := StateT.bind_ok hcont
              cases q with
              | mk bodyTy body' =>
                rcases (by simpa [typedName, hbody] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
                simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
                  Binder.ofUntyped_runtime]
          | some ty =>
            unfold Typed.infer at h
            have ⟨ty', s₀, _hty, hcont⟩ := StateT.bind_ok h
            have ⟨bound', s₁, hbound, hcont⟩ := StateT.bind_ok hcont
            let typedName := Typed.Binder.ofUntyped (.named x (.some ty)) ty'
            let ihBound := check_runtime env Θ Γ bound ty'
            let ihBody := infer_runtime env Θ (extendTyped Γ typedName) body
            have hcont' :
                (do
                  let p ← infer env Θ (extendTyped Γ typedName) body
                  pure (p.1, Expr.letIn typedName bound' p.2)) s₁ = .ok (result, s') := by
              simpa [typedName] using hcont
            have ⟨p, s₂, hbody, hcont⟩ := StateT.bind_ok hcont'
            cases p with
            | mk bodyTy body' =>
              rcases (by simpa [hbody] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
              have hname_rt :
                  typedName.runtime = (Untyped.Binder.named x (some ty)).runtime := by
                simp [typedName, Binder.ofUntyped_runtime]
              simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
                hname_rt]
    | .letProd names bound body => by
        let ihBound := infer_runtime env Θ Γ bound
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hbound, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk boundTy bound' =>
          cases boundTy with
          | tuple tys =>
            have hcont' :
                (do
                  let typedNames ← inferProductBinders env Θ names tys
                  let p ← infer env Θ (extendTypedList Γ typedNames) body
                  pure (p.1, Expr.letProd typedNames bound' p.2)) s₀ = .ok (result, s') := by
              simpa using hcont
            have ⟨typedNames, s₁, hnames, hcont⟩ := StateT.bind_ok hcont'
            let ihBody := infer_runtime env Θ (extendTypedList Γ typedNames) body
            have ⟨q, s₂, hbody, hcont⟩ := StateT.bind_ok hcont
            cases q with
            | mk bodyTy body' =>
              rcases (by simpa [hbody] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
              simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
                inferProductBinders_runtime env Θ names tys typedNames s₀ s₁ hnames]
          | _ =>
            simp at hcont
    | .ref ownership e => by
        let ih := infer_runtime env Θ Γ e
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hinfer, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk innerTy e1 =>
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
    | .deref e => by
        let ih := infer_runtime env Θ Γ e
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hinfer, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk innerTy e1 =>
          cases innerTy <;> simp at hcont
          case ref ty =>
            rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
          case owned ty =>
            rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
    | .store loc val => by
        let ihLoc := infer_runtime env Θ Γ loc
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hloc, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk locTy loc' =>
          -- `bind_pure_comp` would fold the remaining bind into a `<$>`, which
          -- `StateT.bind_ok` no longer matches.
          cases locTy <;> simp [-bind_pure_comp] at hcont
          case ref inner =>
            let ihVal := check_runtime env Θ Γ val inner
            have ⟨val', s₁, hval, hcont⟩ := StateT.bind_ok hcont
            rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihLoc _ _ _ hloc, ihVal _ _ _ hval]
          case owned inner =>
            let ihVal := check_runtime env Θ Γ val inner
            have ⟨val', s₁, hval, hcont⟩ := StateT.bind_ok hcont
            rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihLoc _ _ _ hloc, ihVal _ _ _ hval]
    | .arrayMake ownership len init => by
        let ihLen := check_runtime env Θ Γ len .int
        let ihInit := infer_runtime env Θ Γ init
        intro s result s' h
        unfold Typed.infer at h
        have ⟨len', s₀, hlen, hcont⟩ := StateT.bind_ok h
        have ⟨p, s₁, hinit, hcont⟩ := StateT.bind_ok hcont
        cases p with
        | mk elemTy init' =>
          rcases (by simpa [hinit] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihLen _ _ _ hlen, ihInit _ _ _ hinit]
    | .arrayLen arr => by
        let ih := infer_runtime env Θ Γ arr
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, harr, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk arrTy arr' =>
          cases arrTy <;> simp at hcont
          case array elemTy | ownedArray elemTy =>
            rcases hcont with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ harr]
    | .arrayGet arr idx => by
        let ihArr := infer_runtime env Θ Γ arr
        let ihIdx := check_runtime env Θ Γ idx .int
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, harr, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk arrTy arr' =>
          have ⟨idx', s₁, hidx, hcont⟩ := StateT.bind_ok hcont
          cases arrTy <;> simp at hcont
          case array elemTy | ownedArray elemTy =>
            rcases hcont with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihArr _ _ _ harr, ihIdx _ _ _ hidx]
    | .arraySet arr idx val => by
        let ihArr := infer_runtime env Θ Γ arr
        let ihIdx := check_runtime env Θ Γ idx .int
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, harr, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk arrTy arr' =>
          have ⟨idx', s₁, hidx, hcont⟩ := StateT.bind_ok hcont
          cases arrTy <;> simp [-bind_pure_comp] at hcont
          case array | ownedArray =>
            have ⟨val', s₂, hval, hcont⟩ := StateT.bind_ok hcont
            rcases hcont with ⟨⟨rfl, rfl⟩, rfl⟩
            have hval_rt := check_runtime env Θ Γ val _ _ val' _ hval
            simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihArr _ _ _ harr, ihIdx _ _ _ hidx, hval_rt]
    | .assert e => by
        let ih := check_runtime env Θ Γ e .bool
        intro s result s' h
        unfold Typed.infer at h
        have ⟨e1, s₀, he, hcont⟩ := StateT.bind_ok h
        rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ he]
    | .tuple es => by
        let ih := inferList_runtime env Θ Γ es
        intro s result s' h
        unfold Typed.infer at h
        have ⟨pairs, s₀, hpairs, hcont⟩ := StateT.bind_ok h
        rcases (by simpa [hpairs] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ hpairs]
    | .inj tag arity payload => by
        let ih := infer_runtime env Θ Γ payload
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hpayload, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk payloadTy payload' =>
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ih _ _ _ hpayload]
    | .match_ scrutinee branches => by
        let ihScrut := infer_runtime env Θ Γ scrutinee
        let ihBranches := inferBranches_runtime env Θ Γ branches
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hscrut, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk scrutTy scrut' =>
          cases scrutTy with
          | sum ts =>
            by_cases hlen : ts.length = branches.length
            · simp [-bind_pure_comp, hlen] at hcont
              have ⟨branches', s₁, hbranches, hcont⟩ := StateT.bind_ok hcont
              rcases (by simpa [hbranches] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
              simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime]
              constructor
              · exact ihScrut _ _ _ hscrut
              · exact (branchListRuntime_cast_joinAll Θ branches').trans
                  (ihBranches ts _ _ _ hbranches)
            · simp [hlen] at hcont
          | named T args =>
            cases hunfold : TypeName.unfold Θ T args with
            | none => simp [hunfold] at hcont
            | some body =>
              cases body with
              | sum ts =>
                simp only [hunfold] at hcont
                by_cases hlen : ts.length = branches.length
                · simp [-bind_pure_comp, hlen] at hcont
                  have ⟨branches', s₁, hbranches, hcont⟩ := StateT.bind_ok hcont
                  rcases (by simpa [hbranches] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
                  simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, ihScrut _ _ _ hscrut]
                  exact (branchListRuntime_cast_joinAll Θ branches').trans
                    (ihBranches ts _ _ _ hbranches)
                · simp [hlen] at hcont
              | _ => simp [hunfold] at hcont
          | _ =>
            simp at hcont

  theorem check_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) (e : Untyped.Expr) :
      ∀ (expected : Typ) s e' s',
        Typed.check env Θ Γ e expected s = .ok (e', s') → e'.runtime = e.runtime := by
    intro expected s e' s' h
    rw [Typed.check.eq_def] at h
    split at h
    -- A function literal at a specified arrow. Its binders are checked against
    -- the arrow's domains, so they erase to the literal's own; the arrow and the
    -- specification leave no trace.
    case _ self args retTy body doms ret sp =>
      have ⟨typedArgs, s₀, hargs, hcont⟩ := StateT.bind_ok h
      have ⟨ann, s₁, _hret, hcont⟩ := StateT.bind_ok hcont
      by_cases hann : ann.any (· != ret)
      · simp [hann] at hcont
      · simp only [hann, if_false, Bool.false_eq_true] at hcont
        have ⟨body', s₂, hbody, hcont⟩ := StateT.bind_ok hcont
        rcases (by simpa using hcont) with ⟨rfl, rfl⟩
        simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime, Binder.ofUntyped_runtime,
          check_runtime env Θ _ body ret _ _ _ hbody,
          checkBinders_runtime env Θ args doms typedArgs s s₀ hargs]
    -- A tuple against a tuple type: the components erase one by one.
    case _ es tys =>
      have ⟨es', s₀, hes, hcont⟩ := StateT.bind_ok h
      rcases (by simpa using hcont) with ⟨rfl, rfl⟩
      simp [Expr.WithTypeVars.runtime, Untyped.Expr.runtime,
        checkArgs_runtime env Θ Γ es tys s es' s₀ hes]
    -- Everything else is inference followed by subsumption.
    case _ =>
      have ⟨p, s₀, hinfer, hcont⟩ := StateT.bind_ok h
      cases p with
      | mk actual e1 =>
        by_cases heq : actual == expected
        · simp [heq] at hcont
          rcases hcont with ⟨rfl, rfl⟩
          exact infer_runtime env Θ Γ e _ _ _ hinfer
        · by_cases hsub : Typ.sub Θ actual expected
          · simp [heq, hsub] at hcont
            rcases hcont with ⟨rfl, rfl⟩
            simp [Expr.WithTypeVars.runtime, infer_runtime env Θ Γ e _ _ _ hinfer]
          · simp [heq, hsub] at hcont

  theorem inferList_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (es : List Untyped.Expr) → ∀ s pairs s', Typed.inferList env Θ Γ es s = .ok (pairs, s') →
        (pairs.map Prod.snd).map Expr.WithTypeVars.runtime = es.map Untyped.Expr.runtime
    | [] => by
        intro s pairs s' h
        simp [Typed.inferList] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
    | e :: es => by
        let ihHead := infer_runtime env Θ Γ e
        let ihTail := inferList_runtime env Θ Γ es
        intro s pairs s' h
        unfold Typed.inferList at h
        have ⟨head, s₀, hinfer, hcont⟩ := StateT.bind_ok h
        have ⟨tail, s₁, htail, hcont⟩ := StateT.bind_ok hcont
        cases head with
        | mk ty e' =>
          simp at hcont
          rcases hcont with ⟨rfl, rfl⟩
          simp [ihHead _ _ _ hinfer, ihTail _ _ _ htail]

  theorem checkArgs_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (args : List Untyped.Expr) → ∀ doms s result s',
        Typed.checkArgs env Θ Γ doms args s = .ok (result, s') →
        result.map Expr.WithTypeVars.runtime = args.map Untyped.Expr.runtime
    | [] => by
        intro doms s result s' h
        cases doms <;> simp [Typed.checkArgs] at h
        case nil => rcases h with ⟨rfl, rfl⟩; rfl
    | arg :: args => by
        let ihRest := checkArgs_runtime env Θ Γ args
        intro doms s result s' h
        cases doms with
        | nil => simp [Typed.checkArgs] at h
        | cons dom doms =>
          simp only [Typed.checkArgs] at h
          have ⟨arg', s₀, harg, hcont⟩ := StateT.bind_ok h
          have ⟨args', s₁, hrest, hcont⟩ := StateT.bind_ok hcont
          simp at hcont
          rcases hcont with ⟨rfl, rfl⟩
          simp only [List.map]
          rw [check_runtime env Θ Γ arg dom _ _ _ harg, ihRest doms _ _ _ hrest]

  theorem inferBranches_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (branches : List (Untyped.Binder × Untyped.Expr)) →
      ∀ tys s branches' s', Typed.inferBranches env Θ Γ tys branches s = .ok (branches', s') →
        Expr.WithTypeVars.branchListRuntime branches' =
          Untyped.Expr.runtime.branchListRuntime branches
    | [] => by
        intro tys s branches' s' h
        cases tys <;> simp [Typed.inferBranches] at h
        case nil =>
          rcases h with ⟨rfl, rfl⟩
          simp [Expr.WithTypeVars.branchListRuntime, Untyped.Expr.runtime.branchListRuntime]
    | br :: rest => by
        let ihRest := inferBranches_runtime env Θ Γ rest
        intro tys s branches' s' h
        cases tys with
        | nil =>
          simp [Typed.inferBranches] at h
        | cons ty tys =>
          obtain ⟨binder, body⟩ := br
          unfold Typed.inferBranches at h
          have ⟨binderTy, s₀, _hty, hcont⟩ := StateT.bind_ok h
          by_cases hsub : Typ.sub Θ ty binderTy
          · simp [-bind_pure_comp, hsub] at hcont
            let ihBody :=
              infer_runtime env Θ (extendTyped Γ (Typed.Binder.ofUntyped binder binderTy)) body
            have ⟨p, s₁, hbody, hcont⟩ := StateT.bind_ok hcont
            cases p with
            | mk bodyTy body' =>
              have ⟨rest', s₂, hrest, hcont⟩ := StateT.bind_ok hcont
              simp at hcont
              rcases hcont with ⟨rfl, rfl⟩
              simp [Expr.WithTypeVars.branchListRuntime, Untyped.Expr.runtime.branchListRuntime,
                Binder.ofUntyped_runtime, ihBody _ _ _ hbody, ihRest tys _ _ _ hrest]
          · simp [hsub] at hcont
end

/-- The specification a function literal is elaborated against does not change
what it runs. -/
theorem elabSpecifiedFix_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (rb : Untyped.SpecBody) (e : Untyped.Expr) :
    ∀ {s : σ} {r : Spec Typ × Typed.Expr} {s' : σ},
      Typed.elabSpecifiedFix env Θ Γ rb e s = .ok (r, s') →
      r.2.runtime = e.runtime := by
  intro s r s' h
  cases e
  case fix self args retTy body =>
    simp only [elabSpecifiedFix] at h
    -- The signature and the spec's own elaboration stay opaque: `StateT.bind_ok`
    -- recovers them without naming what they are applied to. The literal is then
    -- checked as it stands, so erasure is exactly `check_runtime`.
    have ⟨_retTy, s₀, _hret, hcont⟩ := StateT.bind_ok h
    have ⟨_typedArgs, s₁, _hargs, hcont⟩ := StateT.bind_ok hcont
    have ⟨_spec, s₂, _hspec, hcont⟩ := StateT.bind_ok hcont
    have ⟨body', s₃, hchecked, hcont⟩ := StateT.bind_ok hcont
    rcases hcont with ⟨rfl, rfl⟩
    exact check_runtime env Θ Γ _ _ _ _ _ hchecked
  all_goals simp [elabSpecifiedFix, TypeM.error] at h

theorem ValDecl.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (d : Untyped.ValDecl Untyped.SpecBody) :
    ∀ {s : σ} {d' : Typed.ValDecl} {s' : σ},
      Typed.ValDecl.elaborate env Θ Γ d s = .ok (d', s') →
      d'.runtime = d.runtime := by
  intro s d' s' helab
  -- Split on whether there is a specification, and then — in its absence — only
  -- on whether there is an annotation; the unannotated cases are identical.
  match hspec : d.spec with
  | some rb =>
    simp only [ValDecl.elaborate, hspec] at helab
    have ⟨_, sg, _, helab'⟩ := StateT.bind_ok helab
    have ⟨r, s₀, hfix, hcont⟩ := StateT.bind_ok helab'
    have ⟨_, s₁, _, hcont⟩ := StateT.bind_ok hcont
    rcases hcont with ⟨rfl, rfl⟩
    simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime, Binder.ofUntyped_runtime,
      elabSpecifiedFix_runtime env Θ Γ rb d.body hfix]
  | none =>
    match hname : d.name with
    | .named x (some ty) =>
      simp only [ValDecl.elaborate, hspec, hname] at helab
      have ⟨ty', s₀, _hty, hcont⟩ := StateT.bind_ok helab
      have ⟨body', s₁, hcheck, hcont⟩ := StateT.bind_ok hcont
      have ⟨y, s₂, hy, hcont⟩ := StateT.bind_ok hcont
      rcases (by simpa using hy) with ⟨rfl, rfl⟩
      rcases hcont with ⟨rfl, rfl⟩
      simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime,
        check_runtime env Θ Γ d.body ty' _ _ _ hcheck, Binder.ofUntyped_runtime, hname]
    | .none | .named _ none =>
      simp only [ValDecl.elaborate, hspec, hname] at helab
      have ⟨p, s₀, hinfer, hcont⟩ := StateT.bind_ok helab
      obtain ⟨bodyTy, body'⟩ := p
      rcases hcont with ⟨rfl, rfl⟩
      simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime,
        infer_runtime env Θ Γ d.body _ _ _ hinfer, Binder.ofUntyped_runtime, hname]

theorem Program.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (prog : Untyped.Program Untyped.SpecBody) :
    ∀ {s : σ} {Θ' : TypeEnv} {prog' : Typed.Program} {s' : σ},
      Typed.Program.elaborate env Θ Γ prog s = .ok ((Θ', prog'), s') →
      prog'.runtime = prog.runtime := by
  induction prog generalizing Θ Γ with
  | nil =>
    intro s Θ' prog' s' h
    simp [Typed.Program.elaborate] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [Typed.Program.runtime, Untyped.Program.runtime]
  | cons d ds ih =>
    intro s Θ' prog' s' h
    cases d with
    | type_ dty =>
      unfold Typed.Program.elaborate at h
      -- The payloads' own elaboration stays opaque; a type declaration
      -- contributes nothing to the runtime program either way.
      have ⟨body, s₀, _hbody, hcont⟩ := StateT.bind_ok h
      cases hext : extendTypeEnv Θ dty.name body with
      | error err =>
        simp [hext] at hcont
      | ok Θ1 =>
        simp [hext] at hcont
        exact ih Θ1 Γ hcont
    | val_ dval =>
      unfold Typed.Program.elaborate at h
      have ⟨dval', s₀, hdecl, hcont⟩ := StateT.bind_ok h
      let Γ' := match dval'.name.name with
        | some x => Γ.extend x dval'.name.ty
        | none => Γ
      have ⟨tail, s₁, htail, hcont⟩ := StateT.bind_ok hcont
      rcases tail with ⟨Θ'', ds'⟩
      simp at hcont
      rcases hcont with ⟨⟨rfl, rfl⟩, rfl⟩
      have hdecl_rt : dval'.runtime = dval.runtime :=
        ValDecl.elaborate_runtime _ Θ Γ dval hdecl
      simp [Typed.Program.runtime, Untyped.Program.runtime, hdecl_rt]
      exact congrArg (List.cons dval.runtime) (ih Θ Γ' htail)
