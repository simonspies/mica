-- SUMMARY: Elaboration and typechecking from the untyped IR to the typed IR.
import Mica.TinyML.Types
import Mica.TinyML.Untyped
import Mica.TinyML.Typed
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.Spec
import Mica.Base.Except

namespace TinyML

/-! ## Type contexts -/

abbrev TyCtx := Var → Option Typ

def TyCtx.empty : TyCtx := fun _ => none

def TyCtx.extend (Γ : TyCtx) (x : Var) (t : Typ) : TyCtx :=
  fun y => if y == x then some t else Γ y

def TyCtx.extendBinder (Γ : TyCtx) (b : Typed.Binder) (t : Typ) : TyCtx :=
  match b.name with
  | none => Γ
  | some x => Γ.extend x t

@[simp] theorem TyCtx.extend_eq (Γ : TyCtx) (x : Var) (t : Typ) :
    (Γ.extend x t) x = some t := by simp [TyCtx.extend]

@[simp] theorem TyCtx.extend_ne (Γ : TyCtx) (x y : Var) (t : Typ) (h : y ≠ x) :
    (Γ.extend x t) y = Γ y := by
  simp [TyCtx.extend, h]

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
    (args : List (Var × Typ)) (Γ : TyCtx) (x : Var)
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
  | undefinedVar (name : Var)
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

def joinAll (Θ : TypeEnv) : List Typ → Typ
  | [] => .value
  | t :: ts => ts.foldl (Typ.join Θ) t

def extendTypeEnv (Θ : TypeEnv) (name : TypeName) (body : DataDecl) : Except TypeError TypeEnv :=
  match Θ name with
  | some _ => .error (.duplicateType name)
  | none => .ok (fun query => if query == name then some body else Θ query)

mutual
  def infer (Θ : TypeEnv) (Γ : TinyML.TyCtx) : Untyped.Expr → Except TypeError (Typ × Typed.Expr)
    | .const c => .ok (Typed.Const.ty c, .const c)
    | .var x =>
        match Γ x with
        | some ty => .ok (ty, .var x ty)
        | none => .error (.undefinedVar x)
    | .prim n ty => .ok (ty, .prim n ty)
    | .unop op e => do
        let (argTy, e') ← infer Θ Γ e
        match TinyML.UnOp.typeOf op argTy with
        | some ty => .ok (ty, .unop op e' ty)
        | none => .error (.unaryMismatch op argTy)
    | .binop op lhs rhs => do
        let (lhsTy, lhs') ← infer Θ Γ lhs
        let (rhsTy, rhs') ← infer Θ Γ rhs
        match TinyML.BinOp.typeOf op lhsTy rhsTy with
        | some ty => .ok (ty, .binop op lhs' rhs' ty)
        | none => .error (.operatorMismatch op lhsTy rhsTy)
    | .fix self args retTy body => do
        let retTy := retTy.getD .value
        let typedArgs := args.map (fun b => Typed.Binder.ofUntyped b (Typed.Binder.expectedTy b .value))
        let selfTy := Typed.arrowOfArgs typedArgs retTy
        let typedSelf := Typed.Binder.ofUntyped self selfTy
        let Γ' := typedArgs.foldl extendTyped (extendTyped Γ typedSelf)
        let body' ← check Θ Γ' body retTy
        .ok (selfTy, .fix typedSelf typedArgs retTy body')
    | .app fn args => do
        let (fnTy, fn') ← infer Θ Γ fn
        let (args', retTy) ← checkArgs Θ Γ fnTy args
        .ok (retTy, .app fn' args' retTy)
    | .ifThenElse cond thn els => do
        let cond' ← check Θ Γ cond .bool
        let (thnTy, thn') ← infer Θ Γ thn
        let (elsTy, els') ← infer Θ Γ els
        let ty := Typ.join Θ thnTy elsTy
        let thn'' := if thnTy == ty then thn' else .cast thn' ty
        let els'' := if elsTy == ty then els' else .cast els' ty
        .ok (ty, .ifThenElse cond' thn'' els'' ty)
    | .letIn name bound body => do
        let (boundTy, bound') ←
          match name with
          | .named _ (some ty) => do let e' ← check Θ Γ bound ty; .ok (ty, e')
          | _ => infer Θ Γ bound
        let typedName := Typed.Binder.ofUntyped name (match name with | .named _ (some ty) => ty | _ => boundTy)
        let (bodyTy, body') ← infer Θ (extendTyped Γ typedName) body
        .ok (bodyTy, .letIn typedName bound' body')
    | .ref owned e => do
        let (ty, e') ← infer Θ Γ e
        .ok ((if owned then .owned ty else .ref ty), .ref owned e')
    | .deref e => do
        let (ty, e') ← infer Θ Γ e
        match ty with
        | .ref inner | .owned inner => .ok (inner, .deref e' inner)
        | _ => .error (.notARef ty)
    | .store loc val => do
        let (locTy, loc') ← infer Θ Γ loc
        match locTy with
        | .ref inner | .owned inner =>
            let val' ← check Θ Γ val inner
            .ok (.unit, .store loc' val')
        | _ => .error (.notARef locTy)
    | .arrayMake len init => do
        let len' ← check Θ Γ len .int
        let (elemTy, init') ← infer Θ Γ init
        .ok (.array elemTy, .arrayMake len' init')
    | .arrayLen arr => do
        let (arrTy, arr') ← infer Θ Γ arr
        match arrTy with
        | .array _ => .ok (.int, .arrayLen arr')
        | _ => .error (.notAnArray arrTy)
    | .arrayGet arr idx => do
        let (arrTy, arr') ← infer Θ Γ arr
        let idx' ← check Θ Γ idx .int
        match arrTy with
        | .array elemTy => .ok (elemTy, .arrayGet arr' idx' elemTy)
        | _ => .error (.notAnArray arrTy)
    | .arraySet arr idx val => do
        let (arrTy, arr') ← infer Θ Γ arr
        let idx' ← check Θ Γ idx .int
        match arrTy with
        | .array elemTy =>
            let val' ← check Θ Γ val elemTy
            .ok (.unit, .arraySet arr' idx' val')
        | _ => .error (.notAnArray arrTy)
    | .assert e => do
        let e' ← check Θ Γ e .bool
        .ok (.unit, .assert e')
    | .tuple es => do
        let pairs ← inferList Θ Γ es
        .ok (.tuple (pairs.map Prod.fst), .tuple (pairs.map Prod.snd))
    | .inj tag arity payload => do
        let (ty, payload') ← infer Θ Γ payload
        .ok (.sum ((List.replicate arity .empty).set tag ty), .inj tag arity payload')
    | .match_ scrutinee branches => do
        let (scrutTy, scrut') ← infer Θ Γ scrutinee
        -- Resolve the scrutinee type: accept sum directly, or unfold a named type and insert a cast.
        match scrutTy with
        | .sum ts =>
                if _h : ts.length = branches.length then
                  let branches' ← inferBranches Θ Γ ts branches
                  let ty := joinAll Θ (branches'.map (fun p => p.2.ty))
                  let branches'' := branches'.map fun
                    | (binder, body) =>
                        (binder, if body.ty == ty then body else .cast body ty)
                  .ok (ty, .match_ scrut' branches'' ty)
                else
                  .error (.arityMismatch ts.length branches.length)
        | .named T args =>
                match TypeName.unfold Θ T args with
                | some (.sum ts) =>
                    if _h : ts.length = branches.length then
                      let branches' ← inferBranches Θ Γ ts branches
                      let ty := joinAll Θ (branches'.map (fun p => p.2.ty))
                      let branches'' := branches'.map fun
                        | (binder, body) =>
                            (binder, if body.ty == ty then body else .cast body ty)
                      -- Insert a cast to unfold the named type before matching.
                      .ok (ty, .match_ (.cast scrut' (.sum ts)) branches'' ty)
                    else
                      .error (.arityMismatch ts.length branches.length)
                | _ => .error (.notASum scrutTy)
        | _ => .error (.notASum scrutTy)

  def check (Θ : TypeEnv) (Γ : TinyML.TyCtx) (e : Untyped.Expr) (expected : Typ) : Except TypeError Typed.Expr := do
    let (actual, e') ← infer Θ Γ e
    if actual == expected then
      .ok e'
    else if Typ.sub Θ actual expected then
      .ok (.cast e' expected)
    else
      .error (.subsumptionFailure actual expected)

  def inferList (Θ : TypeEnv) (Γ : TinyML.TyCtx) : List Untyped.Expr → Except TypeError (List (Typ × Typed.Expr))
    | [] => .ok []
    | e :: es => do
        let head ← infer Θ Γ e
        let tail ← inferList Θ Γ es
        .ok (head :: tail)

  def checkArgs (Θ : TypeEnv) (Γ : TinyML.TyCtx) : Typ → List Untyped.Expr → Except TypeError (List Typed.Expr × Typ)
    | ty, [] => .ok ([], ty)
    | .arrow dom cod, arg :: args => do
        let arg' ← check Θ Γ arg dom
        let (args', retTy) ← checkArgs Θ Γ cod args
        .ok (arg' :: args', retTy)
    | _ty, args => .error (.arityMismatch 0 args.length)

  def inferBranches (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      List Typ → List (Untyped.Binder × Untyped.Expr) → Except TypeError (List (Typed.Binder × Typed.Expr))
    | [], [] => .ok []
    | ty :: tys, (binder, body) :: rest => do
        let binderTy := Typed.Binder.expectedTy binder ty
        if Typ.sub Θ ty binderTy then
          let typedBinder := Typed.Binder.ofUntyped binder binderTy
          let (_bodyTy, body') ← infer Θ (extendTyped Γ typedBinder) body
          let rest' ← inferBranches Θ Γ tys rest
          .ok ((typedBinder, body') :: rest')
        else
          .error (.subsumptionFailure ty binderTy)
    | tys, bs => .error (.arityMismatch tys.length bs.length)
end

theorem Binder.ofUntyped_runtime (b : Untyped.Binder) (ty : Typ) :
    (Typed.Binder.ofUntyped b ty).runtime = b.runtime := by
  cases b <;> rfl

/-! ## Specification elaboration

A spec is elaborated alongside the declaration it annotates: its leaf
expressions go through the ordinary `infer`/`check` judgments, with the spec's
arguments taking the function's argument types, `bind` binders their annotated
types, and the postcondition result the return type. This reuses the global
context from `Program.elaborate`, so a spec may refer to earlier definitions. -/

/-- Elaborate a spec assertion through `infer`/`check`. The `inner` callback
elaborates the return payload in the current type context. -/
def elabAssert (Θ : TypeEnv) (inner : TyCtx → α → Except TypeError β) :
    TyCtx → Spec.Assert Untyped.Expr α → Except TypeError (Spec.Assert Typed.Expr β)
  | Γ, .ret a => do .ok (.ret (← inner Γ a))
  | Γ, .assert cond rest => do
    let cond' ← check Θ Γ cond .bool
    .ok (.assert cond' (← elabAssert Θ inner Γ rest))
  | Γ, .let_ x e rest => do
    let (ty, e') ← infer Θ Γ e
    .ok (.let_ x e' (← elabAssert Θ inner (Γ.extend x ty) rest))
  | Γ, .bind p x ty rest => do
    .ok (.bind p x ty (← elabAssert Θ inner (Γ.extend x ty) rest))
  | Γ, .ite cond thn els => do
    let cond' ← check Θ Γ cond .bool
    .ok (.ite cond' (← elabAssert Θ inner Γ thn) (← elabAssert Θ inner Γ els))

private def elabPost (Θ : TypeEnv) (Γ : TyCtx) (post : Spec.Post Untyped.Expr) :
    Except TypeError (Spec.Post Typed.Expr) :=
  elabAssert Θ (fun _ () => .ok ()) Γ post

/-- Match the spec's bound names against the typed function binders to recover
each argument's type. -/
private def specArgTypes : List Typed.Binder → List String → Except TypeError (List (String × Typ))
  | _, [] => .ok []
  | [], _ :: _ => .error (.spec "more arguments than the function declares")
  | b :: bs, n :: ns => do
    let rest ← specArgTypes bs ns
    .ok ((n, b.ty) :: rest)

/-- Elaborate a spec body against its function's typed signature, layering the
spec's arguments on top of the program's global bindings `Γbase`. -/
def elabSpecBody (Θ : TypeEnv) (Γbase : TyCtx) (body : Typed.Expr) (rb : Spec.Body Untyped.Expr) :
    Except TypeError (Spec.Body Typed.Expr) := do
  let (names, pre) := rb
  let (argBinders, retTy) ← match body with
    | .fix _ args retTy _ => .ok (args, retTy)
    | _ => .error (.spec "attached to a non-function declaration")
  let argTys ← specArgTypes argBinders names
  let Γ₀ : TyCtx := argTys.foldl (fun Γ p => Γ.extend p.1 p.2) Γbase
  let pre' ← elabAssert Θ
    (fun Γ (vname, post) => do
      let post' ← elabPost Θ (Γ.extend vname retTy) post
      .ok (vname, post'))
    Γ₀ pre
  .ok (names, pre')

/-- Elaborate a declaration's optional spec against the typed function `body`. -/
def elabSpec (Θ : TypeEnv) (Γ : TyCtx) (body : Typed.Expr) :
    Option (Spec.Body Untyped.Expr) → Except TypeError (Option (Spec.Body Typed.Expr))
  | none => .ok none
  | some rb => do
    let cb ← elabSpecBody Θ Γ body rb
    .ok (some cb)

def ValDecl.elaborate (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (d : Untyped.ValDecl (Spec.Body Untyped.Expr)) :
    Except TypeError (Typed.ValDecl (Spec.Body Typed.Expr)) := do
  let (bodyTy, body') ←
    match d.name with
    | .named _ (some ty) => do
        let body' ← check Θ Γ d.body ty
        .ok (ty, body')
    | _ => infer Θ Γ d.body
  let nameTy := match d.name with
    | .named _ (some ty) => ty
    | _ => bodyTy
  let spec' ← elabSpec Θ Γ body' d.declMeta.spec
  .ok { name := Typed.Binder.ofUntyped d.name nameTy, body := body',
        declMeta := { spec := spec', relation := d.declMeta.relation } }

def Program.elaborate (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
    Untyped.Program (Spec.Body Untyped.Expr) → Except TypeError (TypeEnv × Typed.Program (Spec.Body Typed.Expr))
  | [] => .ok (Θ, [])
  | d :: ds => do
      match d with
      | .type_ dty =>
          let Θ' ← extendTypeEnv Θ dty.name dty.body
          Program.elaborate Θ' Γ ds
      | .val_ dval =>
          let d' ← ValDecl.elaborate Θ Γ dval
          let Γ' := match d'.name.name with
            | some x => Γ.extend x d'.name.ty
            | none => Γ
          let (Θ', ds') ← Program.elaborate Θ Γ' ds
          .ok (Θ', d' :: ds')

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
  theorem infer_runtime (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (e : Untyped.Expr) → ∀ result, Typed.infer Θ Γ e = .ok result → result.2.runtime = e.runtime
    | .const c => by
        intro result h
        simp [Typed.infer] at h
        rcases h with ⟨rfl, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime]
    | .var x => by
        intro result h
        simp [Typed.infer] at h
        split at h <;> cases h
        simp [Expr.runtime, Untyped.Expr.runtime]
    | .prim n ty => by
        intro result h
        simp [Typed.infer] at h
        rcases h with ⟨rfl, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime]
    | .unop op e => by
        let ih := infer_runtime Θ Γ e
        intro result h
        unfold Typed.infer at h
        have ⟨p, hinfer, hcont⟩ := Except.bind_ok h
        cases p with
        | mk argTy e1 =>
          cases hty : TinyML.UnOp.typeOf op argTy with
          | none =>
            simp [hty] at hcont
          | some resTy =>
            rcases (by simpa [hty] using hcont) with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ hinfer]
    | .binop op lhs rhs => by
        let ihL := infer_runtime Θ Γ lhs
        let ihR := infer_runtime Θ Γ rhs
        intro result h
        unfold Typed.infer at h
        have ⟨lp, hlhs, hcont⟩ := Except.bind_ok h
        cases lp with
        | mk lhsTy lhs' =>
          have ⟨rp, hrhs, hcont⟩ := Except.bind_ok hcont
          cases rp with
          | mk rhsTy rhs' =>
            cases hty : TinyML.BinOp.typeOf op lhsTy rhsTy with
            | none =>
              simp [hty] at hcont
            | some resTy =>
              rcases (by simpa [hty] using hcont) with ⟨rfl, rfl⟩
              simp [Expr.runtime, Untyped.Expr.runtime, ihL _ hlhs, ihR _ hrhs]
    | .fix self args retTy body => by
        let retTy' := retTy.getD .value
        let typedArgs := args.map (fun b => Typed.Binder.ofUntyped b (Typed.Binder.expectedTy b .value))
        let selfTy := Typed.arrowOfArgs typedArgs retTy'
        let typedSelf := Typed.Binder.ofUntyped self selfTy
        let Γ' := typedArgs.foldl extendTyped (extendTyped Γ typedSelf)
        let ih := check_runtime Θ Γ' body retTy'
        intro result h
        unfold Typed.infer at h
        have ⟨body', hbody, hcont⟩ := Except.bind_ok h
        rcases (by simpa [retTy', typedArgs, selfTy, typedSelf, Γ', hbody] using hcont) with ⟨rfl, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime, ih _ hbody, Binder.ofUntyped_runtime]
    | .app fn args => by
        let ihFn := infer_runtime Θ Γ fn
        let ihArgs := checkArgs_runtime Θ Γ args
        intro result h
        unfold Typed.infer at h
        have ⟨fp, hfn, hcont⟩ := Except.bind_ok h
        cases fp with
        | mk fnTy fn' =>
          have ⟨result, hargs, hcont⟩ := Except.bind_ok hcont
          cases result with
          | mk args' retTy =>
            rcases (by simpa [hargs] using hcont) with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ihFn _ hfn, ihArgs fnTy _ hargs]
    | .ifThenElse cond thn els => by
        let ihCond := check_runtime Θ Γ cond .bool
        let ihThn := infer_runtime Θ Γ thn
        let ihEls := infer_runtime Θ Γ els
        intro result h
        unfold Typed.infer at h
        have ⟨cond', hcond, hcont⟩ := Except.bind_ok h
        have ⟨tp, hthn, hcont⟩ := Except.bind_ok hcont
        cases tp with
        | mk thnTy thn' =>
          have ⟨ep, hels, hcont⟩ := Except.bind_ok hcont
          cases ep with
          | mk elsTy els' =>
            rcases (by simpa [hels] using hcont) with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ihCond _ hcond]
            constructor
            · by_cases h : thnTy = Typ.join Θ thnTy elsTy
              · rw [if_pos h]
                exact ihThn _ hthn
              · rw [if_neg h]
                simpa [Typed.Expr.runtime] using ihThn _ hthn
            · by_cases h : elsTy = Typ.join Θ thnTy elsTy
              · rw [if_pos h]
                exact ihEls _ hels
              · rw [if_neg h]
                simpa [Typed.Expr.runtime] using ihEls _ hels
    | .letIn name bound body => by
        intro result h
        cases name with
        | none =>
          unfold Typed.infer at h
          have ⟨p, hbound, hcont⟩ := Except.bind_ok h
          cases p with
          | mk boundTy bound' =>
            let typedName := Typed.Binder.ofUntyped .none boundTy
            let ihBound := infer_runtime Θ Γ bound
            let ihBody := infer_runtime Θ (extendTyped Γ typedName) body
            have ⟨p, hbody, hcont⟩ := Except.bind_ok hcont
            cases p with
            | mk bodyTy body' =>
              rcases (by simpa [typedName, hbody] using hcont) with ⟨rfl, rfl⟩
              simp [Expr.runtime, Untyped.Expr.runtime, ihBound _ hbound, ihBody _ hbody,
                Binder.ofUntyped_runtime]
        | named x ann =>
          cases ann with
          | none =>
            unfold Typed.infer at h
            have ⟨p, hbound, hcont⟩ := Except.bind_ok h
            cases p with
            | mk boundTy bound' =>
              let typedName := Typed.Binder.ofUntyped (.named x .none) boundTy
              let ihBound := infer_runtime Θ Γ bound
              let ihBody := infer_runtime Θ (extendTyped Γ typedName) body
              have ⟨p, hbody, hcont⟩ := Except.bind_ok hcont
              cases p with
              | mk bodyTy body' =>
                rcases (by simpa [typedName, hbody] using hcont) with ⟨rfl, rfl⟩
                simp [Expr.runtime, Untyped.Expr.runtime, ihBound _ hbound, ihBody _ hbody,
                  Binder.ofUntyped_runtime]
          | some ty =>
            unfold Typed.infer at h
            have ⟨bound', hbound, hcont⟩ := Except.bind_ok h
            let typedName := Typed.Binder.ofUntyped (.named x (.some ty)) ty
            let ihBound := check_runtime Θ Γ bound ty
            let ihBody := infer_runtime Θ (extendTyped Γ typedName) body
            have hcont' :
                (do
                  let p ← infer Θ (extendTyped Γ typedName) body
                  Except.ok (p.1, Expr.letIn typedName bound' p.2)) = .ok result := by
              simpa [typedName] using hcont
            have ⟨p, hbody, hcont⟩ := Except.bind_ok hcont'
            cases p with
            | mk bodyTy body' =>
              rcases (by simpa [hbody] using hcont) with ⟨rfl, rfl⟩
              have hname_rt :
                  typedName.runtime = (Untyped.Binder.named x (some ty)).runtime := by
                simp [typedName, Binder.ofUntyped_runtime]
              simp [Expr.runtime, Untyped.Expr.runtime, ihBound _ hbound, ihBody _ hbody,
                hname_rt]
    | .ref owned e => by
        let ih := infer_runtime Θ Γ e
        intro result h
        unfold Typed.infer at h
        have ⟨p, hinfer, hcont⟩ := Except.bind_ok h
        cases p with
        | mk innerTy e1 =>
          rcases (by simpa using hcont) with ⟨rfl, rfl⟩
          simp [Expr.runtime, Untyped.Expr.runtime, ih _ hinfer]
    | .deref e => by
        let ih := infer_runtime Θ Γ e
        intro result h
        unfold Typed.infer at h
        have ⟨p, hinfer, hcont⟩ := Except.bind_ok h
        cases p with
        | mk innerTy e1 =>
          cases innerTy <;> simp at hcont
          case ref ty =>
            rcases (by simpa using hcont) with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ hinfer]
          case owned ty =>
            rcases (by simpa using hcont) with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ hinfer]
    | .store loc val => by
        let ihLoc := infer_runtime Θ Γ loc
        intro result h
        unfold Typed.infer at h
        have ⟨p, hloc, hcont⟩ := Except.bind_ok h
        cases p with
        | mk locTy loc' =>
          cases locTy <;> simp at hcont
          case ref inner =>
            let ihVal := check_runtime Θ Γ val inner
            have ⟨val', hval, hcont⟩ := Except.bind_ok hcont
            rcases (by simpa using hcont) with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ihLoc _ hloc, ihVal _ hval]
          case owned inner =>
            let ihVal := check_runtime Θ Γ val inner
            have ⟨val', hval, hcont⟩ := Except.bind_ok hcont
            rcases (by simpa using hcont) with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ihLoc _ hloc, ihVal _ hval]
    | .arrayMake len init => by
        let ihLen := check_runtime Θ Γ len .int
        let ihInit := infer_runtime Θ Γ init
        intro result h
        unfold Typed.infer at h
        have ⟨len', hlen, hcont⟩ := Except.bind_ok h
        have ⟨p, hinit, hcont⟩ := Except.bind_ok hcont
        cases p with
        | mk elemTy init' =>
          rcases (by simpa [hinit] using hcont) with ⟨rfl, rfl⟩
          simp [Expr.runtime, Untyped.Expr.runtime, ihLen _ hlen, ihInit _ hinit]
    | .arrayLen arr => by
        let ih := infer_runtime Θ Γ arr
        intro result h
        unfold Typed.infer at h
        have ⟨p, harr, hcont⟩ := Except.bind_ok h
        cases p with
        | mk arrTy arr' =>
          cases arrTy <;> simp at hcont
          case array elemTy =>
            rcases hcont with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ih _ harr]
    | .arrayGet arr idx => by
        let ihArr := infer_runtime Θ Γ arr
        let ihIdx := check_runtime Θ Γ idx .int
        intro result h
        unfold Typed.infer at h
        have ⟨p, harr, hcont⟩ := Except.bind_ok h
        cases p with
        | mk arrTy arr' =>
          have ⟨idx', hidx, hcont⟩ := Except.bind_ok hcont
          cases arrTy <;> simp at hcont
          case array elemTy =>
            rcases hcont with ⟨rfl, rfl⟩
            simp [Expr.runtime, Untyped.Expr.runtime, ihArr _ harr, ihIdx _ hidx]
    | .arraySet arr idx val => by
        let ihArr := infer_runtime Θ Γ arr
        let ihIdx := check_runtime Θ Γ idx .int
        intro result h
        unfold Typed.infer at h
        have ⟨p, harr, hcont⟩ := Except.bind_ok h
        cases p with
        | mk arrTy arr' =>
          have ⟨idx', hidx, hcont⟩ := Except.bind_ok hcont
          cases arrTy <;> simp at hcont
          case array =>
            have ⟨val', hval, hcont⟩ := Except.bind_ok hcont
            rcases hcont with ⟨rfl, rfl⟩
            have hval_rt := check_runtime Θ Γ val _ val' hval
            simp [Expr.runtime, Untyped.Expr.runtime, ihArr _ harr, ihIdx _ hidx, hval_rt]
    | .assert e => by
        let ih := check_runtime Θ Γ e .bool
        intro result h
        unfold Typed.infer at h
        have ⟨e1, he, hcont⟩ := Except.bind_ok h
        rcases (by simpa using hcont) with ⟨rfl, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime, ih _ he]
    | .tuple es => by
        let ih := inferList_runtime Θ Γ es
        intro result h
        unfold Typed.infer at h
        have ⟨pairs, hpairs, hcont⟩ := Except.bind_ok h
        rcases (by simpa [hpairs] using hcont) with ⟨rfl, rfl⟩
        simp [Expr.runtime, Untyped.Expr.runtime, ih _ hpairs]
    | .inj tag arity payload => by
        let ih := infer_runtime Θ Γ payload
        intro result h
        unfold Typed.infer at h
        have ⟨p, hpayload, hcont⟩ := Except.bind_ok h
        cases p with
        | mk payloadTy payload' =>
          rcases (by simpa using hcont) with ⟨rfl, rfl⟩
          simp [Expr.runtime, Untyped.Expr.runtime, ih _ hpayload]
    | .match_ scrutinee branches => by
        let ihScrut := infer_runtime Θ Γ scrutinee
        let ihBranches := inferBranches_runtime Θ Γ branches
        intro result h
        unfold Typed.infer at h
        have ⟨p, hscrut, hcont⟩ := Except.bind_ok h
        cases p with
        | mk scrutTy scrut' =>
          cases scrutTy with
          | sum ts =>
            by_cases hlen : ts.length = branches.length
            · simp [hlen] at hcont
              have ⟨branches', hbranches, hcont⟩ := Except.bind_ok hcont
              rcases (by simpa [hbranches] using hcont) with ⟨rfl, rfl⟩
              simp [Expr.runtime, Untyped.Expr.runtime]
              constructor
              · exact ihScrut _ hscrut
              · exact (branchListRuntime_cast_joinAll Θ branches').trans (ihBranches ts _ hbranches)
            · simp [hlen] at hcont
          | named T args =>
            cases hunfold : TypeName.unfold Θ T args with
            | none => simp [hunfold] at hcont
            | some body =>
              cases body with
              | sum ts =>
                simp only [hunfold] at hcont
                by_cases hlen : ts.length = branches.length
                · simp [hlen] at hcont
                  have ⟨branches', hbranches, hcont⟩ := Except.bind_ok hcont
                  rcases (by simpa [hbranches] using hcont) with ⟨rfl, rfl⟩
                  simp [Expr.runtime, Untyped.Expr.runtime, ihScrut _ hscrut]
                  exact (branchListRuntime_cast_joinAll Θ branches').trans (ihBranches ts _ hbranches)
                · simp [hlen] at hcont
              | _ => simp [hunfold] at hcont
          | _ =>
            simp at hcont

  theorem check_runtime (Θ : TypeEnv) (Γ : TinyML.TyCtx) (e : Untyped.Expr) (expected : Typ) :
      ∀ e', Typed.check Θ Γ e expected = .ok e' → e'.runtime = e.runtime := by
      intro e' h
      unfold Typed.check at h
      have ⟨p, hinfer, hcont⟩ := Except.bind_ok h
      cases p with
      | mk actual e1 =>
        by_cases heq : actual == expected
        · simp [heq] at hcont
          cases hcont
          simpa using infer_runtime Θ Γ e _ hinfer
        · by_cases hsub : Typ.sub Θ actual expected
          · simp [heq, hsub] at hcont
            cases hcont
            simp [Expr.runtime, infer_runtime Θ Γ e _ hinfer]
          · simp [heq, hsub] at hcont

  theorem inferList_runtime (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (es : List Untyped.Expr) → ∀ pairs, Typed.inferList Θ Γ es = .ok pairs →
        (pairs.map Prod.snd).map Expr.runtime = es.map Untyped.Expr.runtime
    | [] => by
        intro pairs h
        simp [Typed.inferList] at h
        cases h
        rfl
    | e :: es => by
        let ihHead := infer_runtime Θ Γ e
        let ihTail := inferList_runtime Θ Γ es
        intro pairs h
        unfold Typed.inferList at h
        have ⟨head, hinfer, hcont⟩ := Except.bind_ok h
        have ⟨tail, htail, hcont⟩ := Except.bind_ok hcont
        cases head with
        | mk ty e' =>
          simp at hcont
          cases hcont
          simp [ihHead _ hinfer, ihTail _ htail]

  theorem checkArgs_runtime (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (args : List Untyped.Expr) → ∀ ty result, Typed.checkArgs Θ Γ ty args = .ok result →
        result.1.map Expr.runtime = args.map Untyped.Expr.runtime
    | [] => by
        intro ty result h
        simp [Typed.checkArgs] at h
        cases h
        rfl
    | arg :: args => by
        let ihRest := checkArgs_runtime Θ Γ args
        intro ty result h
        cases ty <;> simp [Typed.checkArgs] at h
        case arrow dom cod =>
          have ⟨arg', harg, hcont⟩ := Except.bind_ok h
          have ⟨rest, hrest, hcont⟩ := Except.bind_ok hcont
          cases rest with
          | mk args' retTy =>
            simp at hcont
            cases hcont
            simp only [List.map]
            rw [check_runtime Θ Γ arg dom _ harg, ihRest cod _ hrest]

  theorem inferBranches_runtime (Θ : TypeEnv) (Γ : TinyML.TyCtx) :
      (branches : List (Untyped.Binder × Untyped.Expr)) →
      ∀ tys branches', Typed.inferBranches Θ Γ tys branches = .ok branches' →
        Expr.branchListRuntime branches' =
          Untyped.Expr.runtime.branchListRuntime branches
    | [] => by
        intro tys branches' h
        cases tys <;> simp [Typed.inferBranches] at h
        case nil =>
          cases h
          simp [Expr.branchListRuntime, Untyped.Expr.runtime.branchListRuntime]
    | br :: rest => by
        let ihRest := inferBranches_runtime Θ Γ rest
        intro tys branches' h
        cases tys with
        | nil =>
          simp [Typed.inferBranches] at h
        | cons ty tys =>
          obtain ⟨binder, body⟩ := br
          let binderTy := Typed.Binder.expectedTy binder ty
          by_cases hsub : Typ.sub Θ ty binderTy
          · unfold Typed.inferBranches at h
            simp [binderTy, hsub] at h
            let typedBinder := Typed.Binder.ofUntyped binder binderTy
            let ihBody := infer_runtime Θ (extendTyped Γ typedBinder) body
            have ⟨p, hbody, hcont⟩ := Except.bind_ok h
            cases p with
            | mk bodyTy body' =>
              have ⟨rest', hrest, hcont⟩ := Except.bind_ok hcont
              simp at hcont
              cases hcont
              simp [Expr.branchListRuntime, Untyped.Expr.runtime.branchListRuntime,
                Binder.ofUntyped_runtime, ihBody _ hbody, ihRest tys _ hrest]
          · simp [Typed.inferBranches, binderTy, hsub] at h
end

theorem ValDecl.elaborate_runtime (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (d : Untyped.ValDecl (Spec.Body Untyped.Expr)) :
    ∀ {d' : Typed.ValDecl (Spec.Body Typed.Expr)},
      Typed.ValDecl.elaborate Θ Γ d = .ok d' →
      d'.runtime = d.runtime := by
  intro d' helab
  -- Split only on whether there is an annotation; the unannotated cases are identical.
  match hname : d.name with
  | .named x (some ty) =>
    cases hcheck : Typed.check Θ Γ d.body ty with
    | error err => simp [ValDecl.elaborate, hname, hcheck, bind, Except.bind] at helab
    | ok body' =>
      cases hspec : elabSpec Θ Γ body' d.declMeta.spec with
      | error e => simp [ValDecl.elaborate, hname, hcheck, hspec, bind, Except.bind] at helab
      | ok spec' =>
        simp [ValDecl.elaborate, hname, hcheck, hspec, bind, Except.bind] at helab
        cases helab
        simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime,
          check_runtime Θ Γ d.body ty _ hcheck, Binder.ofUntyped_runtime, hname]
  | .none | .named _ none =>
    cases hinfer : Typed.infer Θ Γ d.body with
    | error err => simp [ValDecl.elaborate, hname, hinfer, bind, Except.bind] at helab
    | ok p =>
      cases p with
      | mk bodyTy body' =>
        cases hspec : elabSpec Θ Γ body' d.declMeta.spec with
        | error e => simp [ValDecl.elaborate, hname, hinfer, hspec, bind, Except.bind] at helab
        | ok spec' =>
          simp [ValDecl.elaborate, hname, hinfer, hspec, bind, Except.bind] at helab
          cases helab
          simp [Typed.ValDecl.runtime, Untyped.ValDecl.runtime,
            infer_runtime Θ Γ d.body _ hinfer, Binder.ofUntyped_runtime, hname]

theorem Program.elaborate_runtime (Θ : TypeEnv) (Γ : TinyML.TyCtx)
    (prog : Untyped.Program (Spec.Body Untyped.Expr)) :
    ∀ {Θ' : TypeEnv} {prog' : Typed.Program (Spec.Body Typed.Expr)},
      Typed.Program.elaborate Θ Γ prog = .ok (Θ', prog') →
      prog'.runtime = prog.runtime := by
  induction prog generalizing Θ Γ with
  | nil =>
    intro Θ' prog' h
    simp [Typed.Program.elaborate] at h
    rcases h with ⟨rfl, rfl⟩
    simp [Typed.Program.runtime, Untyped.Program.runtime]
  | cons d ds ih =>
    intro Θ' prog' h
    cases d with
    | type_ dty =>
      unfold Typed.Program.elaborate at h
      cases hext : extendTypeEnv Θ dty.name dty.body with
      | error err =>
        simp [hext] at h
        cases h
      | ok Θ1 =>
        simp [hext] at h
        exact ih Θ1 Γ h
    | val_ dval =>
      unfold Typed.Program.elaborate at h
      have ⟨dval', hdecl, hcont⟩ := Except.bind_ok h
      let Γ' := match dval'.name.name with
        | some x => Γ.extend x dval'.name.ty
        | none => Γ
      have ⟨tail, htail, hcont⟩ := Except.bind_ok hcont
      rcases tail with ⟨Θ'', ds'⟩
      simp at hcont
      cases hcont
      have hdecl_rt : dval'.runtime = dval.runtime := ValDecl.elaborate_runtime Θ Γ dval hdecl
      subst prog'
      simp [Typed.Program.runtime, Untyped.Program.runtime, hdecl_rt]
      exact congrArg (List.cons dval.runtime) (ih Θ Γ' htail)
