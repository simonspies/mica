-- SUMMARY: Elaboration of surface syntax into the verifier's core language, with frontend-specific checks.
import Mica.Frontend.AST
import Mica.Frontend.Resolver
import Mica.Frontend.SpecParser
import Mica.TinyML.Common
import Mica.TinyML.Untyped

/-!
This file elaborates frontend AST programs into TinyML untyped core terms and
declarations, resolving constructors and record metadata from an elaboration
environment. It is the semantic lowering step after parsing.
-/

namespace Frontend

-- ---------------------------------------------------------------------------
-- Elaboration errors

inductive ElaborateErrorKind where
  | unknownConstructor (name : String)
  | unknownType (name : String)
  | unknownField (name : String)
  | duplicateConstructor (name : String)
  | duplicateType (name : String)
  | duplicateField (name : String)
  | unsupportedChar
  | unsupportedRecordUpdate
  | unsupportedPattern (desc : String)
  | unsupportedFeature (desc : String)
  | arityMismatch (expected got : Nat)
  | bareSpecialIdentifier (name : String)
  | missingMatchBranch (tag : Nat) (arity : Nat)
  | emptyMatch
  | unsupportedPath (path : Path)
  | internalError (desc : String)
  deriving Inhabited

structure ElaborateError where
  loc  : Location
  kind : ElaborateErrorKind
  deriving Inhabited

def ElaborateErrorKind.toString : ElaborateErrorKind → String
  | .unknownConstructor name => s!"unknown constructor '{name}'"
  | .unknownType name => s!"unknown type '{name}'"
  | .unknownField name => s!"unknown field '{name}'"
  | .duplicateConstructor name => s!"duplicate constructor '{name}'"
  | .duplicateType name => s!"duplicate type name '{name}'"
  | .duplicateField name =>
    s!"duplicate field '{name}' (shadowing fields from a previous type is not supported)"
  | .unsupportedChar => "char literals are not supported"
  | .unsupportedRecordUpdate => "record update expressions are not supported"
  | .unsupportedPattern desc => s!"unsupported pattern: {desc}"
  | .unsupportedFeature desc => s!"unsupported feature: {desc}"
  | .arityMismatch expected got => s!"arity mismatch: expected {expected}, got {got}"
  | .bareSpecialIdentifier name => s!"'{name}' cannot be used as a variable; it must be applied"
  | .missingMatchBranch tag arity =>
    s!"missing match branch for constructor {tag} (of {arity})"
  | .emptyMatch => "empty match expression"
  | .unsupportedPath path => s!"unsupported qualified path '{path}'"
  | .internalError desc => s!"internal error: {desc}"

def ElaborateError.toString (e : ElaborateError) : String :=
  let loc := s!"{e.loc.start.file}:{e.loc.start.line}:{e.loc.start.col}"
  s!"{loc}: {e.kind.toString}"

instance : ToString ElaborateError := ⟨ElaborateError.toString⟩

-- ---------------------------------------------------------------------------
-- Elaboration environment (association lists)


structure ElabEnv where
  types    : List TypeConstructor                            := []
  ctors    : List (Constructor × (Nat × Nat))                := []
  fields   : List (FieldName × (TypeConstructor × Nat))      := []
  records  : List (TypeConstructor × List FieldName)         := []
  resolver : Resolver

-- ---------------------------------------------------------------------------
-- Helpers

private abbrev ElabM := Except ElaborateError

private def err (loc : Location) (kind : ElaborateErrorKind) : ElabM α :=
  .error { loc, kind }

-- ---------------------------------------------------------------------------
-- Type elaboration

/-- Apply a single type attribute to an already-elaborated core type. `[@owned]`
turns a shared `ref A` into an owned `owned A`; unknown names are rejected
(mirroring how the expression-level `[@owned]` validates `ref`). -/
private def applyTypAttr (loc : Location) (t : TinyML.Typ) : String → ElabM TinyML.Typ
  | "owned" =>
    match t with
    | .ref inner => .ok (.owned inner)
    | .array _ => err loc (.unsupportedFeature "[@owned] arrays are not supported")
    | _ => err loc (.unsupportedFeature "[@owned] only applies to a 'ref' type")
  | name => err loc (.unsupportedFeature s!"unknown type attribute [@{name}]")

mutual
def TypKind.elaborate (env : ElabEnv) (loc : Location) : TypKind → ElabM TinyML.Typ
  | .var v => .ok (.tvar v)
  | .con path args => do
    let args' ← Typ.elaborateList env args
    -- Qualified paths route through the resolver; an alias must point to a
    -- single-segment target (avoids unbounded chasing).
    let name ← if path.isQualified then
      match env.resolver.type_ path with
      | some (.alias aliasPath) =>
        if aliasPath.isQualified then
          err loc (.unsupportedPath path)
        else .ok aliasPath.head
      | none => err loc (.unsupportedPath path)
    else .ok path.head
    match name with
    | "int"  => if args'.isEmpty then .ok .int  else err loc (.arityMismatch 0 args'.length)
    | "bool" => if args'.isEmpty then .ok .bool else err loc (.arityMismatch 0 args'.length)
    | "unit" => if args'.isEmpty then .ok .unit else err loc (.arityMismatch 0 args'.length)
    | "string" => if args'.isEmpty then .ok .string else err loc (.arityMismatch 0 args'.length)
    | "float" => if args'.isEmpty then .ok .float else err loc (.arityMismatch 0 args'.length)
    | "ref" =>
      match args' with
      | [arg] => .ok (.ref arg)
      | _ => err loc (.arityMismatch 1 args'.length)
    | "array" =>
      match args' with
      | [arg] => .ok (.array arg)
      | _ => err loc (.arityMismatch 1 args'.length)
    | _ =>
      if env.types.elem name then .ok (.named name args')
      else err loc (.unknownType name)
  | .arrow dom cod => do
    let dom' ← Typ.elaborate env dom
    let cod' ← Typ.elaborate env cod
    .ok (.arrow dom' cod')
  | .tuple ts => do
    let ts' ← Typ.elaborateList env ts
    .ok (.tuple ts')
termination_by k => sizeOf k

/-- Elaborate a surface type: lower its kind, then apply any type attributes
(`T [@name]`) left-to-right. Single entry point for every type position. -/
def Typ.elaborate (env : ElabEnv) (ty : Typ) : ElabM TinyML.Typ := do
  let t ← TypKind.elaborate env ty.loc ty.kind
  ty.attrs.foldlM (applyTypAttr ty.loc) t
termination_by sizeOf ty
decreasing_by cases ty; simp_wf; omega

def Typ.elaborateList (env : ElabEnv) : List Typ → ElabM (List TinyML.Typ)
  | [] => .ok []
  | ty :: ts => do
    let t' ← Typ.elaborate env ty
    let ts' ← Typ.elaborateList env ts
    .ok (t' :: ts')
termination_by ts => sizeOf ts
end

private def elaborateOptTyp (env : ElabEnv) : Option Typ → ElabM (Option TinyML.Typ)
  | none => .ok none
  | some ty => do let ty' ← Typ.elaborate env ty; .ok (some ty')

-- ---------------------------------------------------------------------------
-- Pattern helpers

private def patternToBinder (pat : Pattern) : ElabM Untyped.Binder :=
  match pat.kind with
  | .wildcard => .ok .none
  | .binder (some name) _ => .ok (.named name none)
  | .binder none _ => .ok .none
  | _ => err pat.loc (.unsupportedPattern "expected a simple binder (variable or wildcard)")

private def patternToBinderTyped (env : ElabEnv) (pat : Pattern) : ElabM Untyped.Binder :=
  match pat.kind with
  | .wildcard => .ok .none
  | .binder none _ => .ok .none
  | .binder (some n) ty => do
    let ty' ← elaborateOptTyp env ty
    .ok (.named n ty')
  | _ => err pat.loc (.unsupportedPattern "expected a simple binder (variable or wildcard)")

-- ---------------------------------------------------------------------------
-- Match branch assembly

private def checkAllBranches (loc : Location) :
    List (Option (Untyped.Binder × Untyped.Expr)) → Nat → Nat → ElabM (List (Untyped.Binder × Untyped.Expr))
  | [], _, _ => .ok []
  | none :: _, arity, tag => err loc (.missingMatchBranch tag arity)
  | some branch :: rest, arity, tag => do
    let rest' ← checkAllBranches loc rest arity (tag + 1)
    .ok (branch :: rest')

private def listSet (l : List α) (idx : Nat) (val : α) : List α :=
  match l, idx with
  | [], _ => []
  | _ :: rest, 0 => val :: rest
  | x :: rest, n + 1 => x :: listSet rest n val

private def insertBranch (env : ElabEnv) (loc : Location) (arity : Nat)
    (acc : List (Option (Untyped.Binder × Untyped.Expr)))
    (name : Constructor) (binder : Option Untyped.Binder) (body : Untyped.Expr)
    : ElabM (List (Option (Untyped.Binder × Untyped.Expr))) :=
  match List.lookup name env.ctors with
  | none => .error { loc, kind := .unknownConstructor name }
  | some (tag, arity') =>
    if arity' != arity then
      .error { loc, kind := .arityMismatch arity arity' }
    else
      let b := binder.getD .none
      .ok (listSet acc tag (some (b, body)))

-- ---------------------------------------------------------------------------
-- Record helpers (outside mutual block — no recursion into Expr)

private def reorderElaborated (loc : Location) (elaborated : List (FieldName × Untyped.Expr))
    : List FieldName → ElabM (List Untyped.Expr)
  | [] => .ok []
  | fieldName :: rest => do
    match elaborated.find? (fun (n, _) => n == fieldName) with
    | some (_, e) =>
      let rest' ← reorderElaborated loc elaborated rest
      .ok (e :: rest')
    | none => err loc (.unknownField fieldName)

-- ---------------------------------------------------------------------------
-- Expression elaboration

private def elaborateBinOp (loc : Location) : BinOp → ElabM TinyML.BinOp
  | .add => .ok .add | .sub => .ok .sub | .mul => .ok .mul
  | .div => .ok .div | .mod => .ok .mod
  | .eq => .ok .eq | .lt => .ok .lt | .le => .ok .le | .gt => .ok .gt | .ge => .ok .ge
  | .and => .ok .and | .or => .ok .or
  | .neq | .semi | .pipeRight | .atAt | .assign | .concat
  | .fadd | .fsub | .fmul | .fdiv =>
    err loc (.internalError "desugared operator reached elaborateBinOp")

-- Helper to elaborate a constructor lookup (not recursive)
private def elaborateCtorLookup (env : ElabEnv) (loc : Location) (name : String)
    (arg : Option Untyped.Expr) : ElabM Untyped.Expr :=
  match List.lookup name env.ctors with
  | some (tag, arity) => .ok (.inj tag arity (arg.getD (.const .unit)))
  | none => err loc (.unknownConstructor name)

/-- Apply a single expression attribute to an already-elaborated term. One arm
per supported expression attribute; unknown names are rejected here (mirroring
how `[@@...]` names are validated). -/
private def applyAttr (loc : Location) (e : Untyped.Expr) : Attribute → ElabM Untyped.Expr
  | { name := "owned", payload := none } =>
      match e with
      | .ref _ inner => .ok (.ref true inner)
      | _ => err loc (.unsupportedFeature "[@owned] only applies to 'ref'")
  | { name, .. } => err loc (.unsupportedFeature s!"unknown expression attribute [@{name}]")

private def bareSpecial (loc : Location) (path : Path) : ElabM Untyped.Expr :=
  err loc (.bareSpecialIdentifier path.toString)

mutual
/-- Elaborate an expression: lower its kind, then apply any expression
attributes (`e [@name payload]`) left-to-right. This is the single entry point
for every expression position, so attributes are honored everywhere. -/
def Expr.elaborate (env : ElabEnv) : Expr → ElabM Untyped.Expr
  | ⟨loc, kind, attrs⟩ => do
      let e ← ExprKind.elaborate env loc kind
      attrs.foldlM (applyAttr loc) e

def ExprKind.elaborate (env : ElabEnv) (loc : Location) : ExprKind → ElabM Untyped.Expr
  | .const (.int n)  => .ok (.const (.int n))
  | .const (.float f) => .ok (.const (.float f.toBits))
  | .const (.bool b) => .ok (.const (.bool b))
  | .const (.string s) => .ok (.const (.string s))
  | .const .unit     => .ok (.const .unit)
  | .const (.char _) => err loc .unsupportedChar

  | .var path =>
    if path.isQualified then
      match env.resolver.value path with
      | some (.userVar n) => .ok (.var n)
      | some (.primitive n ty) =>
        (match ty with
        | .arrow _ _ => .ok (.prim n ty)
        | _ => .ok (.app (.prim n ty) []))
      | some (.special _) => bareSpecial loc path
      | none => err loc (.unsupportedPath path)
    else
      let name := path.head
      match name with
      | "ref" | "not" => err loc (.bareSpecialIdentifier name)
      | _ =>
        match List.lookup name env.ctors with
        | some (tag, arity) => .ok (.inj tag arity (.const .unit))
        | none => .ok (.var name)

  | .ctor path =>
    if path.isQualified then
      match env.resolver.ctor path with
      | some (.aliased n) => elaborateCtorLookup env loc n none
      | none => err loc (.unsupportedPath path)
    else
      elaborateCtorLookup env loc path.head none

  | .app fn args =>
    match fn.kind with
    | .var path =>
      if !path.isQualified && path.head == "not" then
        match args with
        | [arg] => do
          let arg' ← Expr.elaborate env arg
          .ok (.unop .not arg')
        | _ => err loc (.arityMismatch 1 args.length)
      else if !path.isQualified && path.head == "ref" then
        match args with
        | [arg] => do
          let arg' ← Expr.elaborate env arg
          .ok (.ref false arg')
        | _ => err loc (.arityMismatch 1 args.length)
      else if path.isQualified then
        match env.resolver.value path with
        | some (.userVar n) => do
          let args' ← Expr.elaborateList env args
          .ok (.app (.var n) args')
        | some (.primitive n ty) => do
          let args' ← Expr.elaborateList env args
          .ok (.app (.prim n ty) args')
        | some (.special .arrayMake) =>
            match args with
            | [len, init] => do
              let len' ← Expr.elaborate env len
              let init' ← Expr.elaborate env init
              .ok (.arrayMake len' init')
            | _ => err loc (.arityMismatch 2 args.length)
        | some (.special .arrayLength) =>
            match args with
            | [arr] => do
              let arr' ← Expr.elaborate env arr
              .ok (.arrayLen arr')
            | _ => err loc (.arityMismatch 1 args.length)
        | some (.special .arrayGet) =>
            match args with
            | [arr, idx] => do
              let arr' ← Expr.elaborate env arr
              let idx' ← Expr.elaborate env idx
              .ok (.arrayGet arr' idx')
            | _ => err loc (.arityMismatch 2 args.length)
        | some (.special .arraySet) =>
            match args with
            | [arr, idx, val] => do
              let arr' ← Expr.elaborate env arr
              let idx' ← Expr.elaborate env idx
              let val' ← Expr.elaborate env val
              .ok (.arraySet arr' idx' val')
            | _ => err loc (.arityMismatch 3 args.length)
        | none => do
          let fn' ← Expr.elaborate env fn
          let args' ← Expr.elaborateList env args
          .ok (.app fn' args')
      else do
        let fn' ← Expr.elaborate env fn
        let args' ← Expr.elaborateList env args
        .ok (.app fn' args')
    | .ctor path => do
      let name ← if path.isQualified then
        match env.resolver.ctor path with
        | some (.aliased n) => .ok n
        | none => err loc (.unsupportedPath path)
      else .ok path.head
      match args with
      | [arg] => do
        let arg' ← Expr.elaborate env arg
        elaborateCtorLookup env loc name (some arg')
      | _ =>
        match List.lookup name env.ctors with
        | some _ => err loc (.arityMismatch 1 args.length)
        | none => err loc (.unknownConstructor name)
    | _ => do
      let fn' ← Expr.elaborate env fn
      let args' ← Expr.elaborateList env args
      .ok (.app fn' args')

  | .binop .semi l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.letIn .none l' r')
  | .binop .pipeRight a f
  | .binop .atAt f a => do
    let fn' ← Expr.elaborate env f
    let arg' ← Expr.elaborate env a
    .ok (.app fn' [arg'])
  | .binop .assign l v => do
    let loc' ← Expr.elaborate env l
    let val' ← Expr.elaborate env v
    .ok (.store loc' val')
  | .arrayGet arr idx => do
    let arr' ← Expr.elaborate env arr
    let idx' ← Expr.elaborate env idx
    .ok (.arrayGet arr' idx')
  | .arraySet arr idx val => do
    let val' ← Expr.elaborate env val
    let arr' ← Expr.elaborate env arr
    let idx' ← Expr.elaborate env idx
    .ok (.arraySet arr' idx' val')
  | .binop .neq l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.unop .not (.binop .eq l' r'))
  | .binop .concat l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "string_cat" (.arrow .string (.arrow .string .string))) [l', r'])
  | .binop .fadd l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_add" (.arrow .float (.arrow .float .float))) [l', r'])
  | .binop .fsub l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_sub" (.arrow .float (.arrow .float .float))) [l', r'])
  | .binop .fmul l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_mul" (.arrow .float (.arrow .float .float))) [l', r'])
  | .binop .fdiv l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_div" (.arrow .float (.arrow .float .float))) [l', r'])
  | .binop op l r => do
    let op' ← elaborateBinOp loc op
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.binop op' l' r')

  | .unop .neg e => do
    let e' ← Expr.elaborate env e
    .ok (.unop .neg e')
  | .unop .deref e => do
    let e' ← Expr.elaborate env e
    .ok (.deref e')
  | .unop .assert e => do
    let e' ← Expr.elaborate env e
    .ok (.assert e')
  | .unop (.proj n) e => do
    -- Surface projections are 1-based (`.1` is the first component); TinyML
    -- projections are 0-based. The parser guarantees `n ≥ 1`.
    let e' ← Expr.elaborate env e
    .ok (.unop (.proj (n - 1)) e')
  | .unop (.field name) e =>
    match List.lookup name env.fields with
    | some (_, idx) => do
      let e' ← Expr.elaborate env e
      .ok (.unop (.proj idx) e')
    | none => err loc (.unknownField name)

  | .ite c t e => do
    let c' ← Expr.elaborate env c
    let t' ← Expr.elaborate env t
    let e' ← Expr.elaborate env e
    .ok (.ifThenElse c' t' e')

  | .letIn isRec binders bound body =>
    match binders with
    | [] => err loc (.unsupportedFeature "let with no binders")
    | [pat] => do
      let name ← patternToBinder pat
      let bound' ← Expr.elaborate env bound
      let body' ← Expr.elaborate env body
      if isRec then
        err loc (.unsupportedFeature "let rec requires function arguments")
      else
        .ok (.letIn name bound' body')
    | pat :: args => do
      let name ← patternToBinder pat
      let args' ← Pattern.toAnnotatedBinders env args
      let self := if isRec then name else .none
      let bound' ← Expr.elaborate env bound
      let body' ← Expr.elaborate env body
      .ok (.letIn name (.fix self args' none bound') body')

  | .fun_ args retTy body => do
    let args' ← Pattern.toAnnotatedBinders env args
    let retTy' ← elaborateOptTyp env retTy
    let body' ← Expr.elaborate env body
    .ok (.fix .none args' retTy' body')

  | .match_ scrut arms => do
    let scrut' ← Expr.elaborate env scrut
    let arms' ← MatchArm.elaborateList env arms
    match arms' with
    | [] => err loc .emptyMatch
    | (ctorName, _, _) :: _ =>
      match List.lookup ctorName env.ctors with
      | none => err loc (.unknownConstructor ctorName)
      | some (_, arity) => do
        let init : List (Option (Untyped.Binder × Untyped.Expr)) := List.replicate arity none
        let filled ← arms'.foldlM
          (fun acc (name, binder, body) => insertBranch env loc arity acc name binder body)
          init
        let branches ← checkAllBranches loc filled arity 0
        .ok (.match_ scrut' branches)

  | .tuple es => do
    let es' ← Expr.elaborateList env es
    .ok (.tuple es')

  | .record flds =>
    match flds with
    | [] => err loc (.unsupportedFeature "empty record")
    | (name, _) :: _ =>
      match List.lookup name env.fields with
      | none => err loc (.unknownField name)
      | some (tyName, _) =>
        match List.lookup tyName env.records with
        | none => err loc (.unknownType tyName)
        | some fieldOrder => do
          let elaborated ← Expr.elaborateRecordFields env flds
          let es' ← reorderElaborated loc elaborated fieldOrder
          .ok (.tuple es')

  | .recordUpdate _ _ => err loc .unsupportedRecordUpdate

  | .annot e _ => Expr.elaborate env e

def Expr.elaborateList (env : ElabEnv) : List Expr → ElabM (List Untyped.Expr)
  | [] => .ok []
  | e :: es => do
    let e' ← Expr.elaborate env e
    let es' ← Expr.elaborateList env es
    .ok (e' :: es')

def Expr.elaborateRecordFields (env : ElabEnv)
    : List (FieldName × Expr) → ElabM (List (FieldName × Untyped.Expr))
  | [] => .ok []
  | (name, e) :: rest => do
    let e' ← Expr.elaborate env e
    let rest' ← Expr.elaborateRecordFields env rest
    .ok ((name, e') :: rest')

def MatchArm.elaborateList (env : ElabEnv)
    : List MatchArm → ElabM (List (Constructor × Option Untyped.Binder × Untyped.Expr))
  | [] => .ok []
  | ⟨pat, body⟩ :: arms => do
    let body' ← Expr.elaborate env body
    let (ctorName, binder) ← match pat.kind with
      | .ctor path payload => do
        let name ← if path.isQualified then
          match env.resolver.ctor path with
          | some (.aliased n) => .ok n
          | none => err pat.loc (.unsupportedPath path)
        else .ok path.head
        let binder ← match payload with
          | some p => do
            let b ← patternToBinder p
            pure (some b)
          | none => pure none
        pure (name, binder)
      | _ => err pat.loc (.unsupportedPattern "only constructor patterns are allowed in match")
    let rest ← MatchArm.elaborateList env arms
    .ok ((ctorName, binder, body') :: rest)

def Pattern.toAnnotatedBinders (env : ElabEnv)
    : List Pattern → ElabM (List Untyped.Binder)
  | [] => .ok []
  | p :: ps => do
    let b ← patternToBinderTyped env p
    let bs ← Pattern.toAnnotatedBinders env ps
    .ok (b :: bs)
end

-- ---------------------------------------------------------------------------
-- Type declaration elaboration

private def elaborateCtorDefs (env : ElabEnv) (loc : Location)
    (ctorDefs : List (Constructor × Option Typ)) (tag : Nat) (arity : Nat)
    : ElabM (List TinyML.Typ × List (Constructor × (Nat × Nat))) :=
  match ctorDefs with
  | [] => .ok ([], [])
  | (ctorName, payloadTy) :: rest => do
    if (List.lookup ctorName env.ctors).isSome then
      err loc (.duplicateConstructor ctorName)
    else do
    let payloadTy' ← match payloadTy with
      | some ty => Typ.elaborate env ty
      | none => .ok .unit
    let (restTypes, restCtors) ← elaborateCtorDefs env loc rest (tag + 1) arity
    .ok (payloadTy' :: restTypes,
         (ctorName, (tag, arity)) :: restCtors)

private def elaborateVariant (env : ElabEnv) (loc : Location) (name : TypeConstructor)
    (tparams : List TinyML.TyVar) (ctorDefs : List (Constructor × Option Typ))
    : ElabM (ElabEnv × Untyped.TypeDecl) := do
  if env.types.elem name then
    return ← err loc (.duplicateType name)
  let arity := ctorDefs.length
  -- Register the type name as a named reference so both recursive self-references in
  -- constructor payloads and later uses resolve to the named type (not the inlined sum).
  let envWithSelf := { env with types := name :: env.types }
  let (payloadTypes, newCtors) ← elaborateCtorDefs envWithSelf loc ctorDefs 0 arity
  let env' := { envWithSelf with ctors := newCtors ++ env.ctors }
  let decl : Untyped.TypeDecl := { name, body := { tparams, payloads := payloadTypes } }
  .ok (env', decl)

private def elaborateFieldDefs (env : ElabEnv) (loc : Location) (tyName : TypeConstructor)
    (fieldDefs : List (FieldName × Typ)) (idx : Nat)
    : ElabM (List (FieldName × (TypeConstructor × Nat))) :=
  match fieldDefs with
  | [] => .ok []
  | (fieldName, _) :: rest => do
    if (List.lookup fieldName env.fields).isSome then
      err loc (.duplicateField fieldName)
    else do
    let restFields ← elaborateFieldDefs env loc tyName rest (idx + 1)
    .ok ((fieldName, (tyName, idx)) :: restFields)

private def elaborateRecordDecl (env : ElabEnv) (loc : Location) (name : TypeConstructor)
    (fieldDefs : List (FieldName × Typ)) : ElabM ElabEnv := do
  if env.types.elem name then
    return ← err loc (.duplicateType name)
  let newFields ← elaborateFieldDefs env loc name fieldDefs 0
  let fieldNames := fieldDefs.map Prod.fst
  .ok { env with
    types := name :: env.types
    records := (name, fieldNames) :: env.records
    fields := newFields ++ env.fields }

def TypeDecl.elaborate (env : ElabEnv) (loc : Location) (decl : TypeDecl)
    : ElabM (ElabEnv × Option Untyped.TypeDecl) :=
  match decl.body with
  | .variant ctors => do
      let (env', decl') ← elaborateVariant env loc decl.name decl.params ctors
      .ok (env', some decl')
  | .record fields => do
      let env' ← elaborateRecordDecl env loc decl.name fields
      .ok (env', none)

-- ---------------------------------------------------------------------------
-- Value declaration elaboration

def ValDecl.elaborate (env : ElabEnv) (loc : Location)
    (isRec : Bool) (binders : List Pattern) (retTy : Option Typ) (body : Expr)
    (md : TinyML.DeclMeta (Spec.Body Untyped.Expr))
    : ElabM (Untyped.ValDecl (Spec.Body Untyped.Expr)) := do
  match binders with
  | [] => err loc (.unsupportedFeature "declaration with no binders")
  | [pat] =>
    let name ← patternToBinder pat
    let body' ← Expr.elaborate env body
    if isRec then
      err loc (.unsupportedFeature "let rec requires function arguments")
    else
      .ok { name, body := body', declMeta := md }
  | pat :: args =>
    let name ← patternToBinder pat
    let self := if isRec then name else .none
    let args' ← Pattern.toAnnotatedBinders env args
    let retTy' ← elaborateOptTyp env retTy
    let body' ← Expr.elaborate env body
    .ok { name, body := .fix self args' retTy' body', declMeta := md }

-- ---------------------------------------------------------------------------
-- Program elaboration

private def elaborateAttrSpec (env : ElabEnv) (attrs : List Attribute)
    : ElabM (Option (Spec.Body Untyped.Expr)) :=
  match attrs.find? (·.name == "spec") with
  | none => .ok none
  | some attr =>
    match attr.payload with
    | none => err default (.unsupportedFeature "[@@spec] expects a specification payload")
    | some payload => do
      let e ← Expr.elaborate env payload
      match Spec.parse e with
      | .ok spec => .ok (some spec)
      | .error msg => err payload.loc (.unsupportedFeature s!"invalid [@@spec]: {msg}")

/-- Whether the declaration is marked `[@@fn]`, registering it as a spec-level
    function. The attribute carries no payload; the function's own name is used
    for the derived relation. -/
private def hasAttrRelation (attrs : List Attribute) : ElabM Bool :=
  match attrs.find? (·.name == "fn") with
  | none => .ok false
  | some attr =>
    match attr.payload with
    | none => .ok true
    | some payload => err payload.loc (.unsupportedFeature
        "[@@fn] takes no payload; the function's own name is used for the relation")

def Decl.elaborate (env : ElabEnv) (decl : Decl)
    : ElabM (ElabEnv × Option (Untyped.Decl (Spec.Body Untyped.Expr))) := do
  match decl.kind with
  | .type_ tdecl => do
    let (env', tdecl') ← TypeDecl.elaborate env decl.loc tdecl
    .ok (env', tdecl'.map Untyped.Decl.type_)
  | .val_ isRec binders retTy body => do
    let spec ← elaborateAttrSpec env decl.attrs
    let fn ← hasAttrRelation decl.attrs
    let d ← ValDecl.elaborate env decl.loc isRec binders retTy body { spec }
    -- A `[@@fn]` declaration uses its own name for the derived relation.
    let relation ← if fn then
      match d.name with
      | .named x _ => .ok (some x)
      | .none => err decl.loc (.unsupportedFeature "[@@fn] requires a named declaration")
    else .ok none
    .ok (env, some (.val_ { d with declMeta := { d.declMeta with relation } }))

private def elaborateDecls (env : ElabEnv) :
    List Decl → ElabM (List (Untyped.Decl (Spec.Body Untyped.Expr)))
  | [] => .ok []
  | d :: ds => do
    let (env', optDecl) ← Decl.elaborate env d
    let rest ← elaborateDecls env' ds
    match optDecl with
    | some decl => .ok (decl :: rest)
    | none => .ok rest

def Program.elaborate (resolver : Resolver) (prog : Frontend.Program) :
    ElabM (Untyped.Program (Spec.Body Untyped.Expr)) :=
  elaborateDecls { resolver } prog

end Frontend
