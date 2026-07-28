-- SUMMARY: Elaboration and typechecking from the untyped IR to the typed IR.
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.Untyped
import Mica.SourceTinyML.Typed
import Mica.TinyML.RuntimeExpr
import Mica.SourceTinyML.Spec
import Mica.SourceTinyML.Assertions
import Mica.SourceTinyML.TypeConstraints
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
  deriving Repr, Inhabited, DecidableEq

instance : ToString TypeError where
  toString
    | .undefinedVar name => s!"undefined variable: {name}"
    | .duplicateType name => s!"duplicate type: {name}"
    | .operatorMismatch op lhs rhs =>
        s!"operator {repr op} cannot be applied to {repr lhs} and {repr rhs}"
    | .unaryMismatch op arg =>
        s!"operator {repr op} cannot be applied to {repr arg}"
    | .notAFunction ty => s!"not a function: {repr ty}"
    | .arityMismatch expected actual =>
        s!"arity mismatch: expected {expected}, got {actual}"
    | .typeMismatch expected actual =>
        s!"type mismatch: expected {repr expected}, got {repr actual}"
    | .notASum ty => s!"not a sum type: {repr ty}"
    | .notARef ty => s!"not a ref type: {repr ty}"
    | .notAnArray ty => s!"not an array type: {repr ty}"
    | .missingReturnType => "missing return type"
    | .subsumptionFailure sub super =>
        s!"subsumption failed: {repr sub} is not a subtype of {repr super}"
    | .spec msg => s!"specification error: {msg}"
    | .unknownPrimitive name => s!"unknown primitive: {name}"
    | .cannotInstantiate name msg =>
        s!"cannot instantiate primitive {name}: {msg}"

def Binder.ofUntyped (b : Untyped.Binder) (ty : Typ) : Typed.Binder :=
  match b with
  | .none => .none ty
  | .named x _ => .named x ty

def Binder.expectedTy (b : Untyped.Binder) (fallback : Typ) : Typ :=
  match b with
  | .none => fallback
  | .named _ (some ty) => ty
  | .named _ .none => fallback

def extendTyped (Γ : TinyML.TyCtx) (b : Typed.Binder) : TinyML.TyCtx :=
  match b.name with
  | none => Γ
  | some x => Γ.extend x b.ty

def extendTypedList (Γ : TinyML.TyCtx) (bs : List Typed.Binder) : TinyML.TyCtx :=
  bs.foldl extendTyped Γ

def inferProductBinders (Θ : TypeEnv) :
    List Untyped.Binder → List Typ → Except TypeError (List Typed.Binder)
  | [], [] => .ok []
  | binder :: binders, ty :: tys => do
      let binderTy := Typed.Binder.expectedTy binder ty
      if Typ.sub Θ ty binderTy then
        let typedBinder := Typed.Binder.ofUntyped binder binderTy
        let rest ← inferProductBinders Θ binders tys
        .ok (typedBinder :: rest)
      else
        .error (.subsumptionFailure ty binderTy)
  | binders, tys => .error (.arityMismatch tys.length binders.length)

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
  scheme : Typ
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

/-- The built-in primitives, and the translation of a single typed
    specification expression into its value term and definedness condition.
    Typing propagates whatever effect the translation carries in `σ`. -/
structure SpecEnv (σ : Type) where
  primitive : String → Option PrimSig
  translate : List String → Typed.Expr → TypeM σ (Term .value × Formula)

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
        .ok (arg.cast dom :: args')
      else .error (.subsumptionFailure argTy dom)
  | doms, rest => .error (.arityMismatch doms.length rest.length)

/-- `checkInferred` preserves erasure: casts are transparent at runtime. -/
theorem checkInferred_runtime (Θ : TypeEnv) :
    (pairs : List (Typ × Typed.Expr)) → ∀ doms result,
      checkInferred Θ doms pairs = .ok result →
      result.map Expr.runtime = (pairs.map Prod.snd).map Expr.runtime
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
            simp only [List.map, Expr.runtime]
            rw [checkInferred_runtime Θ rest doms _ hrest]
          · simp at h

mutual
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
          if sig.scheme.closed then pure (sig.scheme, .prim n [] sig.scheme)
          else TypeM.error (.cannotInstantiate n "a polymorphic primitive must be applied")
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
        let retTy := retTy.getD .value
        let typedArgs := args.map (fun b => Typed.Binder.ofUntyped b (Typed.Binder.expectedTy b .value))
        let selfTy := Typ.arrow (typedArgs.map Binder.ty) retTy none
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
              let ty := sig.scheme.subst fun v => (inst.lookup v).getD (.tvar v)
              if ty.closed then do
                let (doms, retTy) ← TypeM.ofExcept (domains ty inferred.length)
                let args' ← TypeM.ofExcept (checkInferred Θ doms inferred)
                pure (retTy, .app (.prim n inst ty) args' retTy)
              else
                TypeM.error (.cannotInstantiate n "unresolved type variables")
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
          | .named _ (some ty) => do let e' ← check env Θ Γ bound ty; pure (ty, e')
          | _ => infer env Θ Γ bound
        let typedName := Typed.Binder.ofUntyped name (match name with | .named _ (some ty) => ty | _ => boundTy)
        let (bodyTy, body') ← infer env Θ (extendTyped Γ typedName) body
        pure (bodyTy, .letIn typedName bound' body')
    | .letProd names bound body => do
        let (boundTy, bound') ← infer env Θ Γ bound
        let tys ← match boundTy with
          | .tuple tys => pure tys
          | _ => TypeM.error (.typeMismatch (.tuple []) boundTy)
        let typedNames ← TypeM.ofExcept (inferProductBinders Θ names tys)
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

  def check (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) (e : Untyped.Expr) (expected : Typ) : TypeM σ Typed.Expr := do
    let (actual, e') ← infer env Θ Γ e
    if actual == expected then
      pure e'
    else if Typ.sub Θ actual expected then
      pure (.cast e' expected)
    else
      TypeM.error (.subsumptionFailure actual expected)

  def inferList (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) : List Untyped.Expr → TypeM σ (List (Typ × Typed.Expr))
    | [] => pure []
    | e :: es => do
        let head ← infer env Θ Γ e
        let tail ← inferList env Θ Γ es
        pure (head :: tail)

  /-- Check an argument list against the domain types of the function applied. -/
  def checkArgs (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      List Typ → List Untyped.Expr → TypeM σ (List Typed.Expr)
    | [], [] => pure []
    | dom :: doms, arg :: args => do
        let arg' ← check env Θ Γ arg dom
        let args' ← checkArgs env Θ Γ doms args
        pure (arg' :: args')
    | doms, args => TypeM.error (.arityMismatch doms.length args.length)

  def inferBranches (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      List Typ → List (Untyped.Binder × Untyped.Expr) → TypeM σ (List (Typed.Binder × Typed.Expr))
    | [], [] => pure []
    | ty :: tys, (binder, body) :: rest => do
        let binderTy := Typed.Binder.expectedTy binder ty
        if Typ.sub Θ ty binderTy then
          let typedBinder := Typed.Binder.ofUntyped binder binderTy
          let (_bodyTy, body') ← infer env Θ (extendTyped Γ typedBinder) body
          let rest' ← inferBranches env Θ Γ tys rest
          pure ((typedBinder, body') :: rest')
        else
          TypeM.error (.subsumptionFailure ty binderTy)
    | tys, bs => TypeM.error (.arityMismatch tys.length bs.length)
end

theorem Binder.ofUntyped_runtime (b : Untyped.Binder) (ty : Typ) :
    (Typed.Binder.ofUntyped b ty).runtime = b.runtime := by
  cases b <;> rfl

theorem inferProductBinders_runtime (Θ : TypeEnv) :
    ∀ (binders : List Untyped.Binder) (tys : List Typ) (typed : List Typed.Binder),
      inferProductBinders Θ binders tys = .ok typed →
        typed.map Typed.Binder.runtime = binders.map Untyped.Binder.runtime
  | [], [], typed, h => by
      simp [inferProductBinders] at h
      subst h
      rfl
  | b :: bs, ty :: tys, typed, h => by
      simp [inferProductBinders] at h
      split at h
      · have ⟨rest, hrest, hcont⟩ := Except.bind_ok h
        cases hcont
        simp [Binder.ofUntyped_runtime, inferProductBinders_runtime Θ bs tys rest hrest]
      · cases h
  | [], _ :: _, typed, h => by
      simp [inferProductBinders] at h
  | _ :: _, [], typed, h => by
      simp [inferProductBinders] at h

/-! ## Specification elaboration

A spec is elaborated alongside the declaration it annotates, in a single walk.
Its leaf expressions go through the ordinary `infer`/`check` judgments — with the
spec's arguments taking the function's argument types, `bind` binders their
annotated types, and the postcondition result the return type — and each typed
leaf is handed straight to `env.translate`, so the walk produces a `Spec`
directly rather than an intermediate typed spec body. This reuses the global
context from `Program.elaborate`, so a spec may refer to earlier definitions. -/

/-- Assert all formulas in order before continuing with the assertion body. -/
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

/-- Elaborate a spec assertion into a verifier assertion in one walk: each leaf
is typechecked and then translated, and its definedness condition is asserted
before the value it guards is bound or tested. The `inner` callback elaborates
the return payload in the current type context and spec-level scope. -/
def elabAssert (env : SpecEnv σ) (Θ : TypeEnv) (inner : TyCtx → List String → α → TypeM σ β) :
    TyCtx → List String → Spec.Assert Untyped.Expr α → TypeM σ (Assertion Typ β)
  | Γ, ns, .ret a => do pure (.ret (← inner Γ ns a))
  | Γ, ns, .assert cond rest => do
    let cond' ← check env Θ Γ cond .bool
    let (v, defd) ← env.translate ns cond'
    pure (.assert defd (.assert (holds v) (← elabAssert env Θ inner Γ ns rest)))
  | Γ, ns, .let_ x e rest => do
    let (ty, e') ← infer env Θ Γ e
    let (v, defd) ← env.translate ns e'
    pure (.assert defd (.let_ ⟨x, .value⟩ v
      (assertAll (TinyML.typeConstraints ty (.var .value x))
        (← elabAssert env Θ inner (Γ.extend x ty) (ns ++ [x]) rest))))
  | Γ, ns, .bind p x ty rest => do
    let atom ← elabPred Γ ns ty p
    pure (.pred ⟨x, .value⟩ atom
      (assertAll (TinyML.typeConstraints ty (.var .value x))
        (← elabAssert env Θ inner (Γ.extend x ty) (ns ++ [x]) rest)))
  | Γ, ns, .ite cond thn els => do
    let cond' ← check env Θ Γ cond .bool
    let (v, defd) ← env.translate ns cond'
    pure (.assert defd (.ite (holds v)
      (← elabAssert env Θ inner Γ ns thn) (← elabAssert env Θ inner Γ ns els)))

private def elabPost (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TyCtx) (ns : List String)
    (post : Spec.Post Untyped.Expr) : TypeM σ (Assertion Typ Unit) :=
  elabAssert env Θ (fun _ _ () => pure ()) Γ ns post

/-- Match the spec's bound names against the typed function binders to recover
each argument's type. -/
private def specArgTypes : List Typed.Binder → List String → Except TypeError (List (String × Typ))
  | _, [] => .ok []
  | [], _ :: _ => .error (.spec "more arguments than the function declares")
  | b :: bs, n :: ns => do
    let rest ← specArgTypes bs ns
    .ok ((n, b.ty) :: rest)

/-- Elaborate a spec body against its function's typed signature, layering the
spec's arguments on top of the program's global bindings `Γbase`. The argument
and return types recovered here type the spec's leaf expressions; the `Spec`
itself keeps only the argument names, since the types belong to the function's
arrow. -/
def elabSpecBody (env : SpecEnv σ) (Θ : TypeEnv) (Γbase : TyCtx) (body : Typed.Expr)
    (rb : Spec.Body Untyped.Expr) : TypeM σ (Spec Typ) := do
  let (names, pre) := rb
  let (argBinders, retTy) ← match body with
    | .fix _ args retTy _ _ => pure (args, retTy)
    | _ => TypeM.error (.spec "attached to a non-function declaration")
  let argTys ← TypeM.ofExcept (specArgTypes argBinders names)
  let Γ₀ : TyCtx := argTys.foldl (fun Γ p => Γ.extend p.1 p.2) Γbase
  let pred ← elabAssert env Θ
    (fun Γ ns (vname, post) => do
      let post' ← elabPost env Θ (Γ.extend vname retTy) (ns ++ [vname]) post
      pure ⟨vname, post'⟩)
    Γ₀ names pre
  pure { args := names, pred := pred }

/-- Elaborate a declaration's optional spec against the typed function `body`. -/
def elabSpec (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TyCtx) (body : Typed.Expr) :
    Option (Spec.Body Untyped.Expr) → TypeM σ (Option (Spec Typ))
  | none => pure none
  | some rb => do
    let s ← elabSpecBody env Θ Γ body rb
    pure (some s)

def ValDecl.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (d : Untyped.ValDecl (Spec.Body Untyped.Expr)) :
    TypeM σ (Typed.ValDecl (Spec Typ)) := do
  let (bodyTy, body') ←
    match d.name with
    | .named _ (some ty) => do
        let body' ← check env Θ Γ d.body ty
        pure (ty, body')
    | _ => infer env Θ Γ d.body
  let nameTy := match d.name with
    | .named _ (some ty) => ty
    | _ => bodyTy
  let spec' ← elabSpec env Θ Γ body' d.declMeta.spec
  pure { name := Typed.Binder.ofUntyped d.name nameTy, body := body',
         declMeta := { spec := spec', relation := d.declMeta.relation } }

def Program.elaborate (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
    Untyped.Program (Spec.Body Untyped.Expr) → TypeM σ (TypeEnv × Typed.Program (Spec Typ))
  | [] => pure (Θ, [])
  | d :: ds => do
      match d with
      | .type_ dty =>
          let Θ' ← TypeM.ofExcept (extendTypeEnv Θ dty.name dty.body)
          Program.elaborate env Θ' Γ ds
      | .val_ dval =>
          let d' ← ValDecl.elaborate env Θ Γ dval
          let Γ' := match d'.name.name with
            | some x => Γ.extend x d'.name.ty
            | none => Γ
          let (Θ', ds') ← Program.elaborate env Θ Γ' ds
          pure (Θ', d' :: ds')

private theorem branchListRuntime_cast_joinAll
    (Θ : TypeEnv) (branches' : List (Typed.Binder × Typed.Expr)) :
    Expr.branchListRuntime
      (branches'.map fun x =>
        (x.1, if x.2.ty = joinAll Θ (branches'.map (fun p => p.2.ty)) then x.2
              else x.2.cast (joinAll Θ (branches'.map (fun p => p.2.ty))))) =
    Expr.branchListRuntime branches' := by
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
        simp [Expr.runtime, Untyped.Expr.runtime]
    | .var x => by
        intro s result s' h
        unfold Typed.infer at h
        cases hΓ : Γ x with
        | none => simp [hΓ] at h
        | some ty =>
          simp [hΓ] at h
          rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.runtime, Untyped.Expr.runtime]
    | .prim n => by
        intro s result s' h
        unfold Typed.infer at h
        cases hp : env.primitive n with
        | none => simp [hp] at h
        | some sig =>
          by_cases hc : sig.scheme.closed
          · simp [hp, hc] at h
            rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime]
          · simp [hp, hc] at h
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
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
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
              simp [Expr.runtime, Untyped.Expr.runtime, ihL _ _ _ hlhs, ihR _ _ _ hrhs]
    | .fix self args retTy body => by
        let retTy' := retTy.getD .value
        let typedArgs := args.map (fun b => Typed.Binder.ofUntyped b (Typed.Binder.expectedTy b .value))
        let selfTy := Typ.arrow (typedArgs.map Binder.ty) retTy' none
        let typedSelf := Typed.Binder.ofUntyped self selfTy
        let Γ' := typedArgs.foldl extendTyped (extendTyped Γ typedSelf)
        let ih := check_runtime env Θ Γ' body retTy'
        intro s result s' h
        unfold Typed.infer at h
        have ⟨body', s₀, hbody, hcont⟩ := StateT.bind_ok h
        rcases (by simpa [retTy', typedArgs, selfTy, typedSelf, Γ', hbody] using hcont)
          with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ hbody, Binder.ofUntyped_runtime]
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
              split at hcont
              · have ⟨dr, s₁, hdoms, hcont⟩ := StateT.bind_ok hcont
                cases dr with
                | mk doms retTy =>
                  have ⟨args', s₂, hchk, hcont⟩ := StateT.bind_ok hcont
                  rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
                  simp only [Expr.runtime, Untyped.Expr.runtime,
                    Untyped.Expr.primName?_runtime hpn]
                  rw [checkInferred_runtime Θ inferred _ _ (TypeM.ofExcept_ok.mp hchk).1,
                    ihList _ _ _ hinf]
              · simp at hcont
        | none =>
          simp only [hpn] at h
          obtain ⟨fp, s₀, hfn, hcont⟩ := StateT.bind_ok h
          obtain ⟨fnTy, fn'⟩ := fp
          obtain ⟨dr, s₁, hdoms, hcont⟩ := StateT.bind_ok hcont
          obtain ⟨doms, retTy⟩ := dr
          obtain ⟨args', s₂, hargs, hcont⟩ := StateT.bind_ok hcont
          rcases (by simpa [hargs] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.runtime, Untyped.Expr.runtime, ihFn _ _ _ hfn, ihArgs doms _ _ _ hargs]
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
            simp [Expr.runtime, Untyped.Expr.runtime, ihCond _ _ _ hcond]
            constructor
            · by_cases hj : thnTy = Typ.join Θ thnTy elsTy
              · rw [if_pos hj]
                exact ihThn _ _ _ hthn
              · rw [if_neg hj]
                simpa [Typed.Expr.runtime] using ihThn _ _ _ hthn
            · by_cases hj : elsTy = Typ.join Θ thnTy elsTy
              · rw [if_pos hj]
                exact ihEls _ _ _ hels
              · rw [if_neg hj]
                simpa [Typed.Expr.runtime] using ihEls _ _ _ hels
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
              simp [Expr.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
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
                simp [Expr.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
                  Binder.ofUntyped_runtime]
          | some ty =>
            unfold Typed.infer at h
            have ⟨bound', s₀, hbound, hcont⟩ := StateT.bind_ok h
            let typedName := Typed.Binder.ofUntyped (.named x (.some ty)) ty
            let ihBound := check_runtime env Θ Γ bound ty
            let ihBody := infer_runtime env Θ (extendTyped Γ typedName) body
            have hcont' :
                (do
                  let p ← infer env Θ (extendTyped Γ typedName) body
                  pure (p.1, Expr.letIn typedName bound' p.2)) s₀ = .ok (result, s') := by
              simpa [typedName] using hcont
            have ⟨p, s₁, hbody, hcont⟩ := StateT.bind_ok hcont'
            cases p with
            | mk bodyTy body' =>
              rcases (by simpa [hbody] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
              have hname_rt :
                  typedName.runtime = (Untyped.Binder.named x (some ty)).runtime := by
                simp [typedName, Binder.ofUntyped_runtime]
              simp [Expr.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
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
                  let typedNames ← TypeM.ofExcept (inferProductBinders Θ names tys)
                  let p ← infer env Θ (extendTypedList Γ typedNames) body
                  pure (p.1, Expr.letProd typedNames bound' p.2)) s₀ = .ok (result, s') := by
              simpa using hcont
            have ⟨typedNames, s₁, hnames, hcont⟩ := StateT.bind_ok hcont'
            let ihBody := infer_runtime env Θ (extendTypedList Γ typedNames) body
            have ⟨q, s₂, hbody, hcont⟩ := StateT.bind_ok hcont
            cases q with
            | mk bodyTy body' =>
              rcases (by simpa [hbody] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
              simp [Expr.runtime, Untyped.Expr.runtime, ihBound _ _ _ hbound, ihBody _ _ _ hbody,
                inferProductBinders_runtime Θ names tys typedNames
                  (TypeM.ofExcept_ok.mp hnames).1]
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
          simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
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
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
          case owned ty =>
            rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ hinfer]
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
            simp [Expr.runtime, Untyped.Expr.runtime, ihLoc _ _ _ hloc, ihVal _ _ _ hval]
          case owned inner =>
            let ihVal := check_runtime env Θ Γ val inner
            have ⟨val', s₁, hval, hcont⟩ := StateT.bind_ok hcont
            rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ihLoc _ _ _ hloc, ihVal _ _ _ hval]
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
          simp [Expr.runtime, Untyped.Expr.runtime, ihLen _ _ _ hlen, ihInit _ _ _ hinit]
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
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ harr]
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
            simp [Expr.runtime, Untyped.Expr.runtime, ihArr _ _ _ harr, ihIdx _ _ _ hidx]
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
            simp [Expr.runtime, Untyped.Expr.runtime, ihArr _ _ _ harr, ihIdx _ _ _ hidx, hval_rt]
    | .assert e => by
        let ih := check_runtime env Θ Γ e .bool
        intro s result s' h
        unfold Typed.infer at h
        have ⟨e1, s₀, he, hcont⟩ := StateT.bind_ok h
        rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ he]
    | .tuple es => by
        let ih := inferList_runtime env Θ Γ es
        intro s result s' h
        unfold Typed.infer at h
        have ⟨pairs, s₀, hpairs, hcont⟩ := StateT.bind_ok h
        rcases (by simpa [hpairs] using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ hpairs]
    | .inj tag arity payload => by
        let ih := infer_runtime env Θ Γ payload
        intro s result s' h
        unfold Typed.infer at h
        have ⟨p, s₀, hpayload, hcont⟩ := StateT.bind_ok h
        cases p with
        | mk payloadTy payload' =>
          rcases (by simpa using hcont) with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Expr.runtime, Untyped.Expr.runtime, ih _ _ _ hpayload]
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
              simp [Expr.runtime, Untyped.Expr.runtime]
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
                  simp [Expr.runtime, Untyped.Expr.runtime, ihScrut _ _ _ hscrut]
                  exact (branchListRuntime_cast_joinAll Θ branches').trans
                    (ihBranches ts _ _ _ hbranches)
                · simp [hlen] at hcont
              | _ => simp [hunfold] at hcont
          | _ =>
            simp at hcont

  theorem check_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) (e : Untyped.Expr)
      (expected : Typ) :
      ∀ s e' s', Typed.check env Θ Γ e expected s = .ok (e', s') → e'.runtime = e.runtime := by
      intro s e' s' h
      unfold Typed.check at h
      have ⟨p, s₀, hinfer, hcont⟩ := StateT.bind_ok h
      cases p with
      | mk actual e1 =>
        by_cases heq : actual == expected
        · simp [heq] at hcont
          rcases hcont with ⟨rfl, rfl⟩
          simpa using infer_runtime env Θ Γ e _ _ _ hinfer
        · by_cases hsub : Typ.sub Θ actual expected
          · simp [heq, hsub] at hcont
            rcases hcont with ⟨rfl, rfl⟩
            simp [Expr.runtime, infer_runtime env Θ Γ e _ _ _ hinfer]
          · simp [heq, hsub] at hcont

  theorem inferList_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (es : List Untyped.Expr) → ∀ s pairs s', Typed.inferList env Θ Γ es s = .ok (pairs, s') →
        (pairs.map Prod.snd).map Expr.runtime = es.map Untyped.Expr.runtime
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
        result.map Expr.runtime = args.map Untyped.Expr.runtime
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
        Expr.branchListRuntime branches' =
          Untyped.Expr.runtime.branchListRuntime branches
    | [] => by
        intro tys s branches' s' h
        cases tys <;> simp [Typed.inferBranches] at h
        case nil =>
          rcases h with ⟨rfl, rfl⟩
          simp [Expr.branchListRuntime, Untyped.Expr.runtime.branchListRuntime]
    | br :: rest => by
        let ihRest := inferBranches_runtime env Θ Γ rest
        intro tys s branches' s' h
        cases tys with
        | nil =>
          simp [Typed.inferBranches] at h
        | cons ty tys =>
          obtain ⟨binder, body⟩ := br
          let binderTy := Typed.Binder.expectedTy binder ty
          by_cases hsub : Typ.sub Θ ty binderTy
          · unfold Typed.inferBranches at h
            simp [-bind_pure_comp, binderTy, hsub] at h
            let typedBinder := Typed.Binder.ofUntyped binder binderTy
            let ihBody := infer_runtime env Θ (extendTyped Γ typedBinder) body
            have ⟨p, s₀, hbody, hcont⟩ := StateT.bind_ok h
            cases p with
            | mk bodyTy body' =>
              have ⟨rest', s₁, hrest, hcont⟩ := StateT.bind_ok hcont
              simp at hcont
              rcases hcont with ⟨rfl, rfl⟩
              simp [Expr.branchListRuntime, Untyped.Expr.runtime.branchListRuntime,
                Binder.ofUntyped_runtime, ihBody _ _ _ hbody, ihRest tys _ _ _ hrest]
          · simp [Typed.inferBranches, binderTy, hsub] at h
end

theorem ValDecl.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (d : Untyped.ValDecl (Spec.Body Untyped.Expr)) :
    ∀ {s : σ} {d' : Typed.ValDecl (Spec Typ)} {s' : σ},
      Typed.ValDecl.elaborate env Θ Γ d s = .ok (d', s') →
      d'.runtime = d.runtime := by
  intro s d' s' helab
  -- Split only on whether there is an annotation; the unannotated cases are identical.
  -- The spec's own elaboration stays opaque: `StateT.bind_ok` recovers it without
  -- naming the arguments `elabSpec` is applied to.
  match hname : d.name with
  | .named x (some ty) =>
    simp only [ValDecl.elaborate, hname] at helab
    have ⟨body', s₀, hcheck, hcont⟩ := StateT.bind_ok helab
    have ⟨y, s₂, hy, hcont⟩ := StateT.bind_ok hcont
    rcases (by simpa using hy) with ⟨rfl, rfl⟩
    have ⟨spec', s₁, hspec, hcont⟩ := StateT.bind_ok hcont
    rcases hcont with ⟨rfl, rfl⟩
    simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime,
      check_runtime env Θ Γ d.body ty _ _ _ hcheck, Binder.ofUntyped_runtime, hname]
  | .none | .named _ none =>
    simp only [ValDecl.elaborate, hname] at helab
    have ⟨p, s₀, hinfer, hcont⟩ := StateT.bind_ok helab
    obtain ⟨bodyTy, body'⟩ := p
    have ⟨spec', s₁, hspec, hcont⟩ := StateT.bind_ok hcont
    rcases hcont with ⟨rfl, rfl⟩
    simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime,
      infer_runtime env Θ Γ d.body _ _ _ hinfer, Binder.ofUntyped_runtime, hname]

theorem Program.elaborate_runtime (env : SpecEnv σ) (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (prog : Untyped.Program (Spec.Body Untyped.Expr)) :
    ∀ {s : σ} {Θ' : TypeEnv} {prog' : Typed.Program (Spec Typ)} {s' : σ},
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
      cases hext : extendTypeEnv Θ dty.name dty.body with
      | error err =>
        simp [hext] at h
      | ok Θ1 =>
        simp [hext] at h
        exact ih Θ1 Γ h
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
        ValDecl.elaborate_runtime env Θ Γ dval hdecl
      simp [Typed.Program.runtime, Untyped.Program.runtime, hdecl_rt]
      exact congrArg (List.cons dval.runtime) (ih Θ Γ' htail)
