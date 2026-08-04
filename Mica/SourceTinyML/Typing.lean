-- SUMMARY: Elaboration from the untyped IR to the typed IR, by unification.
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.Unification
import Mica.SourceTinyML.Untyped
import Mica.SourceTinyML.Typed
import Mica.TinyML.RuntimeExpr
import Mica.SourceTinyML.Assertions
import Mica.SourceTinyML.TypeConstraints
import Mica.SourceTinyML.Printer
import Mica.Base.Except

namespace Typed

open TinyML

def Binder.ofUntyped (b : Untyped.Binder) (ty : Typ) : Typed.Binder :=
  match b with
  | .none => .none ty
  | .named x _ => .named x ty

def extendTypeEnv (Θ : TypeEnv) (name : TypeName) (body : DataDecl) : Except TypeError TypeEnv :=
  match Θ name with
  | some _ => .error (.duplicateType name)
  | none => .ok (fun query => if query == name then some body else Θ query)

/-! ## The specification environment -/

/-- The arrow scheme of each built-in primitive, the translation of a single
    typed specification expression into its value term and definedness
    condition, and the globals a specification nested in a type is elaborated
    against — the program's bindings as of the declaration whose type carries
    it. Typing propagates whatever effect the translation carries in `σ`.

    A primitive's scheme is instantiated at Infer.fresh metavariables at every use
    site, so the ordinary unifier solves its type variables from the
    arguments. -/
structure SpecEnv (σ : Type) where
  primitive : String → Option SchemaTyp
  translate : List String → Typed.Expr → TypeM σ (Term .value × Formula)
  globals : TinyML.TyCtx

/-- Assert all formulas in order before continuing with the assertion body.

Used only to spell out the type constraints of a name a spec binds. This
functionality does not belong here: an `Assertion` binder should carry the type
it binds at, and the constraints should be emitted where the assertion is
elaborated, which is also the layer that knows how a type constrains a term.
Until the binders carry their types, typing expands the constraints on the spot.
-/
private def assertAll (φs : List Formula) (k : Assertion Typ α) : Assertion Typ α :=
  φs.foldr .assert k

/-- The formula stating that a leaf's value term is the boolean `true`. -/
private def holds (v : Term .value) : Formula :=
  .eq .bool (.unop .toBool v) (.const (.b true))

private def resolveSpecVar (names : List String) (x : String) : TypeM σ (Term .value) :=
  if x ∈ names then pure (.var .value x)
  else TypeM.error (.spec s!"unbound spec variable '{x}'")

/-- Match the spec's bound names against the typed function binders to recover
each argument's type. -/
private def extractSpecArgTypes : List Typed.Binder → List String → Except TypeError (List (String × Typ))
  | _, [] => .ok []
  | [], _ :: _ => .error (.spec "more arguments than the function declares")
  | b :: bs, n :: ns => do
    let rest ← extractSpecArgTypes bs ns
    .ok ((n, b.ty) :: rest)

/-- Elaborate a spec predicate into the atom binding its payload, checking the
scrutinee against both the type context and the spec-level scope. -/
private def Spec.Pred.elaborate (Γ : TyCtx) (names : List String) (ty : Typ) :
    Spec.Pred → TypeM σ (Atom Typ .value)
  | .isinj tag arity scrut => do pure (.isinj tag arity (← resolveSpecVar names scrut))
  | .own loc =>
    match Γ loc with
    | some (.owned innerTy) =>
      if innerTy == ty then do pure (.own (← resolveSpecVar names loc) ty)
      else TypeM.error (.spec s!"own {loc} must bind {repr innerTy}, not {repr ty}")
    | some other => TypeM.error (.spec s!"own {loc} requires an owned reference, got {repr other}")
    | none => TypeM.error (.spec s!"unknown ownership variable '{loc}'")
  | .arr loc =>
    match Γ loc with
    | some (.ownedArray innerTy) =>
      if (.vec innerTy) == ty then do pure (.arr (← resolveSpecVar names loc) innerTy)
      else TypeM.error (.spec s!"arr {loc} must bind a vector snapshot of type {repr (TinyML.Typ.vec innerTy)}, not {repr ty}")
    | some other => TypeM.error (.spec s!"arr {loc} requires an owned array, got {repr other}")
    | none => TypeM.error (.spec s!"unknown ownership variable '{loc}'")


/-! ## Elaboration -/

-- Every function below walks one piece of the declaration being elaborated — a
-- type, a binder, an expression, an assertion — and every call it makes is on a
-- piece nested inside its own, so the size of that piece is the measure. The
-- exceptions are the three that hand their own argument on unchanged:
-- `Infer.Typ.elaborate` to `Typ.elaborate`, `Infer.Binder.elaborateAt` to
-- `Infer.Binder.elaborate`, and `Expr.elaborate` to `Infer.Expr.elaborate`. They
-- take the tag that orders them above the others at equal size.
mutual
  /-- Translate a type of the untyped IR into the core type it denotes,
  elaborating every specification it carries. A specification's leaves are
  typechecked in the program's global context extended with the arrow's own
  arguments — never with the binders surrounding the annotation, which the
  function the type describes cannot mention. -/
  def Typ.elaborate (env : SpecEnv σ) (Θ : TypeEnv) : Untyped.Typ → TypeM σ Typ
    | .core t => pure t
    | .tvar v => TypeM.error (.unboundTypeVar v)
    | .sum ts => do pure (.sum (← Typ.elaborateList env Θ ts))
    | .arrow args ret spec => do
        let args' ← Typ.elaborateList env Θ args
        let ret' ← Typ.elaborate env Θ ret
        match spec with
        | none => pure (.arrow args' ret' none)
        | some rb => do
            let s ← Spec.Body.elaborate env Θ env.globals (args'.map Typed.Binder.none) ret' rb
            pure (.arrow args' ret' (some s))
    | .ref t => do pure (.ref (← Typ.elaborate env Θ t))
    | .array t => do pure (.array (← Typ.elaborate env Θ t))
    | .ownedArray t => do pure (.ownedArray (← Typ.elaborate env Θ t))
    | .vec t => do pure (.vec (← Typ.elaborate env Θ t))
    | .owned t => do pure (.owned (← Typ.elaborate env Θ t))
    | .tuple ts => do pure (.tuple (← Typ.elaborateList env Θ ts))
    | .named n args => do pure (.named n (← Typ.elaborateList env Θ args))
  termination_by ty => (sizeOf ty, 0)

  def Typ.elaborateList (env : SpecEnv σ) (Θ : TypeEnv) : List Untyped.Typ → TypeM σ (List Typ)
    | [] => pure []
    | t :: ts => do pure ((← Typ.elaborate env Θ t) :: (← Typ.elaborateList env Θ ts))
  termination_by ts => (sizeOf ts, 0)

  def Typ.elaborateOpt (env : SpecEnv σ) (Θ : TypeEnv) : Option Untyped.Typ → TypeM σ (Option Typ)
    | none => pure none
    | some t => do pure (some (← Typ.elaborate env Θ t))

  def Infer.Typ.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (ty : Untyped.Typ) : Infer.M σ Infer.Typ := do
    pure (Infer.Typ.ofTyp (← StateT.lift (Typ.elaborate env Θ ty)))
  termination_by (sizeOf ty, 1)

  /-- A binder at its annotation, or at a Infer.fresh metavariable if it has none. -/
  def Infer.Binder.elaborate (env : SpecEnv σ) (Θ : TypeEnv) : Untyped.Binder → Infer.M σ Infer.Binder
    | .none => do pure { name := none, ty := ← Infer.fresh }
    | .named x ann => do
        let ty ← match ann with
          | some t => Infer.Typ.elaborate env Θ t
          | none => Infer.fresh
        pure { name := some x, ty }
  termination_by b => (sizeOf b, 0)

  def Infer.Binder.elaborateAt (env : SpecEnv σ) (Θ : TypeEnv) (b : Untyped.Binder)
      (expected : Infer.Typ) : Infer.M σ Infer.Binder := do
    let b' ← Infer.Binder.elaborate env Θ b
    Infer.unify Θ b'.ty expected
    pure b'
  termination_by (sizeOf b, 1)

  def Infer.Binder.elaborateList (env : SpecEnv σ) (Θ : TypeEnv) :
      List Untyped.Binder → Infer.M σ (List Infer.Binder)
    | [] => pure []
    | b :: bs => do pure ((← Infer.Binder.elaborate env Θ b) :: (← Infer.Binder.elaborateList env Θ bs))
  termination_by bs => (sizeOf bs, 0)

  def Infer.Binder.elaborateListAt (env : SpecEnv σ) (Θ : TypeEnv) :
      List Untyped.Binder → List Infer.Typ → Infer.M σ (List Infer.Binder)
    | [], [] => pure []
    | b :: bs, ty :: tys => do
        pure ((← Infer.Binder.elaborateAt env Θ b ty) :: (← Infer.Binder.elaborateListAt env Θ bs tys))
    | bs, tys => Infer.error (.arityMismatch tys.length bs.length)
  termination_by bs => (sizeOf bs, 1)

  /-- A return annotation as an inference type, when there is one. -/
  def Infer.Typ.elaborateOpt (env : SpecEnv σ) (Θ : TypeEnv) :
      Option Untyped.Typ → Infer.M σ (Option Infer.Typ)
    | none => pure none
    | some t => do pure (some (← Infer.Typ.elaborate env Θ t))
  termination_by t => (sizeOf t, 1)

  /-- The signature a function literal is elaborated at. -/
  def Infer.fixSignature (env : SpecEnv σ) (Θ : TypeEnv) (args : List Untyped.Binder)
      (retTy : Option Infer.Typ) (exp : Infer.Typ) :
      Infer.M σ (List Infer.Binder × Infer.Typ × Option (Spec Infer.Typ)) := do
    let (doms, ret, spec) ← Infer.Constraint.arrow Θ exp args.length
    let args' ← Infer.Binder.elaborateListAt env Θ args doms
    match retTy with
    | some ann => Infer.unify Θ ann ret
    | none => pure ()
    pure (args', ret, spec)
  termination_by (sizeOf args, 2)

  /-- Elaborate an expression at the type expected of it. -/
  def Infer.Expr.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γ : Infer.Ctx) :
      Untyped.Expr → Infer.Typ → Infer.M σ Infer.Expr
    | .const c, exp => do
        Infer.unify Θ (Typed.Const.ty c) exp
        pure (.const c)
    | .var x, exp => match Γ x with
        | some ty => do Infer.unify Θ ty exp; pure (.var x ty)
        | none => Infer.error (.undefinedVar x)
    | .prim n, exp => match env.primitive n with
        | none => Infer.error (.unknownPrimitive n)
        | some scheme => do
            let (ty, inst) ← Infer.instantiate scheme
            Infer.unify Θ ty exp
            pure (.prim n inst ty)
    | .unop op e, exp => do
        match op with
        | .neg => do
            let e' ← Infer.Expr.elaborate env Θ Γ e .int
            Infer.unify Θ .int exp
            pure (.unop op e' .int)
        | .not => do
            let e' ← Infer.Expr.elaborate env Θ Γ e .bool
            Infer.unify Θ .bool exp
            pure (.unop op e' .bool)
        | .proj n => do
            let argTy ← Infer.fresh
            let e' ← Infer.Expr.elaborate env Θ Γ e argTy
            let ty ← Infer.Constraint.tuple Θ argTy n
            Infer.unify Θ ty exp
            pure (.unop op e' ty)
    | .binop op lhs rhs, exp => do
        let argTy : Infer.Typ := match op with | .and | .or => .bool | _ => .int
        let retTy : Infer.Typ := match op with
          | .eq | .lt | .le | .gt | .ge | .and | .or => .bool
          | _ => .int
        let lhs' ← Infer.Expr.elaborate env Θ Γ lhs argTy
        let rhs' ← Infer.Expr.elaborate env Θ Γ rhs argTy
        Infer.unify Θ retTy exp
        pure (.binop op lhs' rhs' retTy)
    | .fix self args retAnn body, exp => do
        let retTy ← Infer.Typ.elaborateOpt env Θ retAnn
        let (args', ret, spec) ← Infer.fixSignature env Θ args retTy exp
        let fnTy : Infer.Typ := .arrow (args'.map (·.ty)) ret spec
        let self' ← Infer.Binder.elaborateAt env Θ self fnTy
        let Γ' := Infer.Ctx.extendList (Γ.extendBinder self') args'
        pure (.fix self' args' ret spec (← Infer.Expr.elaborate env Θ Γ' body ret))
    | .app fn args, exp => do
        let fnTy ← Infer.fresh
        let fn' ← Infer.Expr.elaborate env Θ Γ fn fnTy
        let (doms, ret, _) ← Infer.Constraint.arrow Θ fnTy args.length
        let args' ← Infer.Expr.elaborateList env Θ Γ args doms
        Infer.unify Θ ret exp
        pure (.app fn' args' ret)
    | .ifThenElse cond thn els, exp => do
        -- Both branches are elaborated at the expected type rather than the
        -- first fixing the type of the second, so a branch that does not return
        -- — a call to `failwith`, whose result type is its own variable —
        -- leaves the result to the other branch.
        let cond' ← Infer.Expr.elaborate env Θ Γ cond .bool
        let thn' ← Infer.Expr.elaborate env Θ Γ thn exp
        let els' ← Infer.Expr.elaborate env Θ Γ els exp
        pure (.ifThenElse cond' thn' els' exp)
    | .letIn name bound body, exp => do
        let name' ← Infer.Binder.elaborate env Θ name
        let bound' ← Infer.Expr.elaborate env Θ Γ bound name'.ty
        pure (.letIn name' bound' (← Infer.Expr.elaborate env Θ (Γ.extendBinder name') body exp))
    | .letProd names bound body, exp => do
        let names' ← Infer.Binder.elaborateList env Θ names
        let bound' ← Infer.Expr.elaborate env Θ Γ bound (.tuple (names'.map (·.ty)))
        pure (.letProd names' bound'
          (← Infer.Expr.elaborate env Θ (Infer.Ctx.extendList Γ names') body exp))
    | .ref ownership e, exp => do
        let ty ← Infer.fresh
        let e' ← Infer.Expr.elaborate env Θ Γ e ty
        Infer.unify Θ (match ownership with | .owned => .owned ty | .shared => .ref ty) exp
        pure (.ref ownership e')
    | .deref e, exp => do
        let refTy ← Infer.fresh
        let e' ← Infer.Expr.elaborate env Θ Γ e refTy
        let inner ← Infer.Constraint.ref Θ refTy
        Infer.unify Θ inner exp
        pure (.deref e' inner)
    | .store loc val, exp => do
        let refTy ← Infer.fresh
        let loc' ← Infer.Expr.elaborate env Θ Γ loc refTy
        let inner ← Infer.Constraint.ref Θ refTy
        let val' ← Infer.Expr.elaborate env Θ Γ val inner
        Infer.unify Θ .unit exp
        pure (.store loc' val')
    | .arrayMake ownership len init, exp => do
        let len' ← Infer.Expr.elaborate env Θ Γ len .int
        let ty ← Infer.fresh
        let init' ← Infer.Expr.elaborate env Θ Γ init ty
        Infer.unify Θ (match ownership with | .owned => .ownedArray ty | .shared => .array ty) exp
        pure (.arrayMake ownership len' init')
    | .arrayLen arr, exp => do
        let arrTy ← Infer.fresh
        let arr' ← Infer.Expr.elaborate env Θ Γ arr arrTy
        let _ ← Infer.Constraint.array Θ arrTy
        Infer.unify Θ .int exp
        pure (.arrayLen arr')
    | .arrayGet arr idx, exp => do
        let arrTy ← Infer.fresh
        let arr' ← Infer.Expr.elaborate env Θ Γ arr arrTy
        let idx' ← Infer.Expr.elaborate env Θ Γ idx .int
        let ty ← Infer.Constraint.array Θ arrTy
        Infer.unify Θ ty exp
        pure (.arrayGet arr' idx' ty)
    | .arraySet arr idx val, exp => do
        let arrTy ← Infer.fresh
        let arr' ← Infer.Expr.elaborate env Θ Γ arr arrTy
        let idx' ← Infer.Expr.elaborate env Θ Γ idx .int
        let ty ← Infer.Constraint.array Θ arrTy
        let val' ← Infer.Expr.elaborate env Θ Γ val ty
        Infer.unify Θ .unit exp
        pure (.arraySet arr' idx' val')
    | .assert e, exp => do
        let e' ← Infer.Expr.elaborate env Θ Γ e .bool
        Infer.unify Θ .unit exp
        pure (.assert e')
    | .tuple es, exp => do
        match ← Infer.resolve exp with
        | .tuple tys => pure (.tuple (← Infer.Expr.elaborateList env Θ Γ es tys))
        | _ => do
            let tys ← Infer.freshList es.length
            let es' ← Infer.Expr.elaborateList env Θ Γ es tys
            Infer.unify Θ (.tuple tys) exp
            pure (.tuple es')
    | .inj tag arity payload T, exp => do
        -- Constraining the expectation before elaborating the payload is what
        -- lets the use site decide the arguments, as in `[]`.
        let args ← Infer.Constraint.named Θ T exp
        let payloadTy ← Infer.Constraint.payloadOf Θ T args tag arity
        let payload' ← Infer.Expr.elaborate env Θ Γ payload payloadTy
        pure (.inj tag arity payload' (.named T args))
    | .match_ scrut branches, exp => do
        let scrutTy ← Infer.fresh
        let scrut' ← Infer.Expr.elaborate env Θ Γ scrut scrutTy
        let payloads ← Infer.Constraint.sum Θ scrutTy branches.length
        let branches' ← Infer.Expr.elaborateBranches env Θ Γ payloads branches exp
        pure (.match_ scrut' branches' exp)
  termination_by e => (sizeOf e, 0)

  def Infer.Expr.elaborateList (env : SpecEnv σ) (Θ : TypeEnv) (Γ : Infer.Ctx) :
      List Untyped.Expr → List Infer.Typ → Infer.M σ (List Infer.Expr)
    | [], [] => pure []
    | e :: es, ty :: tys => do
        pure ((← Infer.Expr.elaborate env Θ Γ e ty) :: (← Infer.Expr.elaborateList env Θ Γ es tys))
    | es, tys => Infer.error (.arityMismatch tys.length es.length)
  termination_by es => (sizeOf es, 0)

  def Infer.Expr.elaborateBranches (env : SpecEnv σ) (Θ : TypeEnv) (Γ : Infer.Ctx) :
      List Infer.Typ → List (Untyped.Binder × Untyped.Expr) → Infer.Typ →
        Infer.M σ (List (Infer.Binder × Infer.Expr))
    | [], [], _ => pure []
    | ty :: tys, (b, body) :: bs, exp => do
        let b' ← Infer.Binder.elaborateAt env Θ b ty
        let body' ← Infer.Expr.elaborate env Θ (Γ.extendBinder b') body exp
        pure ((b', body') :: (← Infer.Expr.elaborateBranches env Θ Γ tys bs exp))
    | tys, bs, _ => Infer.error (.arityMismatch tys.length bs.length)
  termination_by _ bs => (sizeOf bs, 0)


  def Expr.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TyCtx)
      (e : Untyped.Expr) (expected : Option Typ) : TypeM σ Typed.Expr :=
    Infer.run (fun ty => Infer.Expr.elaborate env Θ (Infer.Ctx.ofTyCtx Γ) e ty) expected
  termination_by (sizeOf e, 1)

  /-- Elaborate a postcondition into a verifier assertion in one walk: each leaf
  is typechecked and then translated, and its definedness condition is asserted
  before the value it guards is bound or tested.

  Each leaf is its own elaboration boundary, so a type one leaf leaves open is
  an error there rather than something a later leaf could solve. Sharing one
  inference state across the leaves is worth doing, but it is not a local
  change: translation needs a closed expression, and the context a leaf extends
  holds closed types, so the walk would have to build a pending assertion over
  `Infer.Typ` and translate it only after closing the whole specification. -/
  def Spec.Post.elaborate (env : SpecEnv σ) (Θ : TypeEnv) :
      TyCtx → List String → Spec.Assert Untyped.Expr Untyped.Typ Unit →
        TypeM σ (Assertion Typ Unit)
    | _, _, .ret () => pure (.ret ())
    | Γ, ns, .assert cond rest => do
      let cond' ← Expr.elaborate env Θ Γ cond (some .bool)
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.assert (holds v) (← Spec.Post.elaborate env Θ Γ ns rest)))
    | Γ, ns, .let_ x e rest => do
      let e' ← Expr.elaborate env Θ Γ e none
      let ty := e'.ty
      let (v, defd) ← env.translate ns e'
      pure (.assert defd (.let_ ⟨x, .value⟩ v
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← Spec.Post.elaborate env Θ (Γ.extend x ty) (ns ++ [x]) rest))))
    | Γ, ns, .bind p x ty rest => do
      let ty ← Typ.elaborate env Θ ty
      let atom ← Spec.Pred.elaborate Γ ns ty p
      pure (.pred ⟨x, .value⟩ atom
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← Spec.Post.elaborate env Θ (Γ.extend x ty) (ns ++ [x]) rest)))
    | Γ, ns, .ite cond thn els => do
      let cond' ← Expr.elaborate env Θ Γ cond (some .bool)
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.ite (holds v)
        (← Spec.Post.elaborate env Θ Γ ns thn) (← Spec.Post.elaborate env Θ Γ ns els)))
  termination_by _ _ a => (sizeOf a, 0)

  /-- Elaborate a precondition the same way, ending in the postcondition the
  result must satisfy — elaborated with the result name bound at the function's
  return type. -/
  def Spec.Pre.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (retTy : Typ) :
      TyCtx → List String → Spec.Pre Untyped.Expr Untyped.Typ → TypeM σ (PredTrans Typ)
    | Γ, ns, .ret post => do
      let body' ← Spec.Post.elaborate env Θ (Γ.extend post.name retTy) (ns ++ [post.name]) post.body
      pure (.ret ⟨post.name, body'⟩)
    | Γ, ns, .assert cond rest => do
      let cond' ← Expr.elaborate env Θ Γ cond (some .bool)
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.assert (holds v) (← Spec.Pre.elaborate env Θ retTy Γ ns rest)))
    | Γ, ns, .let_ x e rest => do
      let e' ← Expr.elaborate env Θ Γ e none
      let ty := e'.ty
      let (v, defd) ← env.translate ns e'
      pure (.assert defd (.let_ ⟨x, .value⟩ v
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← Spec.Pre.elaborate env Θ retTy (Γ.extend x ty) (ns ++ [x]) rest))))
    | Γ, ns, .bind p x ty rest => do
      let ty ← Typ.elaborate env Θ ty
      let atom ← Spec.Pred.elaborate Γ ns ty p
      pure (.pred ⟨x, .value⟩ atom
        (assertAll (TinyML.typeConstraints ty (.var .value x))
          (← Spec.Pre.elaborate env Θ retTy (Γ.extend x ty) (ns ++ [x]) rest)))
    | Γ, ns, .ite cond thn els => do
      let cond' ← Expr.elaborate env Θ Γ cond (some .bool)
      let (v, defd) ← env.translate ns cond'
      pure (.assert defd (.ite (holds v)
        (← Spec.Pre.elaborate env Θ retTy Γ ns thn) (← Spec.Pre.elaborate env Θ retTy Γ ns els)))
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
  def Spec.Body.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γbase : TyCtx)
      (argBinders : List Typed.Binder) (retTy : Typ)
      (rb : Untyped.SpecBody) : TypeM σ (Spec Typ) := do
    let names := rb.args
    let argTys ← TypeM.ofExcept (extractSpecArgTypes argBinders names)
    let Γ₀ : TyCtx := argTys.foldl (fun Γ p => Γ.extend p.1 p.2) Γbase
    let pred ← Spec.Pre.elaborate env Θ retTy Γ₀ names rb.pre
    pure { args := names, pred := pred }
  termination_by (sizeOf rb, 0)
  decreasing_by obtain ⟨args, pre⟩ := rb; simp; omega
end

mutual

/-- Translate a payload type, keeping the declaration's own type parameters as
variables. A payload that carries a specification has no variables to keep —
`Typ.elaborate` rejects them everywhere else — so it is translated as an ordinary
type and embedded. -/
def SchemaTyp.elaborate (env : SpecEnv σ) (Θ : TypeEnv) : Untyped.Typ → TypeM σ SchemaTyp
  | .core t => pure (Typ.subst Empty.elim t)
  | .tvar v => pure (.tvar v)
  | .sum ts => do pure (.sum (← SchemaTyp.elaborateList env Θ ts))
  | .arrow args ret none => do
      pure (.arrow (← SchemaTyp.elaborateList env Θ args) (← SchemaTyp.elaborate env Θ ret) none)
  | t@(.arrow _ _ (some _)) => do pure (Typ.subst Empty.elim (← Typ.elaborate env Θ t))
  | .ref t => do pure (.ref (← SchemaTyp.elaborate env Θ t))
  | .array t => do pure (.array (← SchemaTyp.elaborate env Θ t))
  | .ownedArray t => do pure (.ownedArray (← SchemaTyp.elaborate env Θ t))
  | .vec t => do pure (.vec (← SchemaTyp.elaborate env Θ t))
  | .owned t => do pure (.owned (← SchemaTyp.elaborate env Θ t))
  | .tuple ts => do pure (.tuple (← SchemaTyp.elaborateList env Θ ts))
  | .named n args => do pure (.named n (← SchemaTyp.elaborateList env Θ args))
termination_by t => sizeOf t

def SchemaTyp.elaborateList (env : SpecEnv σ) (Θ : TypeEnv) :
    List Untyped.Typ → TypeM σ (List SchemaTyp)
  | [] => pure []
  | t :: ts => do
      pure ((← SchemaTyp.elaborate env Θ t) :: (← SchemaTyp.elaborateList env Θ ts))
termination_by ts => sizeOf ts

end

/-- Translate a specified function's argument binders. `ValDecl.elaborateSpecified`
checks that every one of them is annotated before calling this. -/
def Binder.elaborateList (env : SpecEnv σ) (Θ : TypeEnv) :
    List Untyped.Binder → TypeM σ (List Typed.Binder)
  | [] => pure []
  | b :: bs => do
      let ty ← match b with
        | .named _ (some ty) => Typ.elaborate env Θ ty
        | _ => pure .value
      pure (Typed.Binder.ofUntyped b ty :: (← Binder.elaborateList env Θ bs))

/-- Elaborate a data declaration's payloads. -/
def DataDecl.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (d : Untyped.DataDecl) :
    TypeM σ TinyML.DataDecl := do
  pure { tparams := d.tparams, payloads := ← SchemaTyp.elaborateList env Θ d.payloads }

/-! ## Specification elaboration

A spec is elaborated alongside the declaration it annotates, in a single walk.
Its leaf expressions go through the ordinary `elaborate` judgment — with the
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
def ValDecl.elaborateSpecified (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (rb : Untyped.SpecBody) : Untyped.Expr → TypeM σ (Spec Typ × Typed.Expr)
  | e@(.fix _ args (some retAnn) _) => do
      -- A specified signature has to be complete: the specification is written
      -- against these types, so leaving one to inference would let the body
      -- decide what the specification means.
      if args.any fun b => match b with | .named _ (some _) => false | _ => true then
        TypeM.error (.spec "specified functions require every argument type annotation")
      else
        -- The specification needs the literal's signature, and checking the
        -- literal needs the specification, so the signature is elaborated first
        -- and the literal is then checked at the arrow the two describe.
        let ret ← Typ.elaborate env Θ retAnn
        let typedArgs ← Binder.elaborateList env Θ args
        let s ← Spec.Body.elaborate env Θ Γ typedArgs ret rb
        let body' ← Expr.elaborate env Θ Γ e
          (some (.arrow (typedArgs.map Binder.WithTypeVars.ty) ret (some s)))
        pure (s, body')
  | .fix _ _ none _ =>
      TypeM.error (.spec "specified functions require a return type annotation")
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
      let ann' ← Typ.elaborate env Θ ann
      if Typ.unspec ty == ann' then pure () else TypeM.error (.typeMismatch ann' (Typ.unspec ty))
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
      let (_, body') ← ValDecl.elaborateSpecified env Θ Γ rb d.body
      checkDeclAnnotation env Θ d.name body'.ty
      pure { name := Typed.Binder.ofUntyped d.name body'.ty, body := body',
             relation := d.relation }
  | none => do
      -- The declaration's own annotation, if it has one, is the only type the
      -- body is expected at; without one the body decides its own.
      let expected ← Typ.elaborateOpt env Θ (match d.name with
        | .named _ (some ty) => some ty
        | _ => none)
      let body' ← Expr.elaborate env Θ Γ d.body expected
      pure { name := Typed.Binder.ofUntyped d.name body'.ty, body := body',
             relation := d.relation }

def Program.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
    Untyped.Program Untyped.SpecBody → TypeM σ (TypeEnv × Typed.Program)
  | [] => pure (Θ, [])
  | d :: ds => do
      match d with
      | .type_ dty =>
          let body ← DataDecl.elaborate { env with globals := Γ } Θ dty.body
          let Θ' ← TypeM.ofExcept (extendTypeEnv Θ dty.name body)
          Program.elaborate env Θ' Γ ds
      | .val_ dval =>
          let d' ← ValDecl.elaborate { env with globals := Γ } Θ Γ dval
          let Γ' := match d'.name.name with
            | some x => Γ.extend x d'.name.ty
            | none => Γ
          let (Θ', ds') ← Program.elaborate env Θ Γ' ds
          pure (Θ', d' :: ds')

end Typed
