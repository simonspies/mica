-- SUMMARY: Elaboration of surface syntax into the verifier's core language, with frontend-specific checks.
import Mica.Frontend.AST
import Mica.Frontend.Resolver
import Mica.Frontend.SpecParser
import Mica.TinyML.Common
import Mica.SourceTinyML.Untyped

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
  | missingField (name : String)
  | unsupportedRecordUpdate
  | unsupportedPattern (desc : String)
  | unsupportedFeature (desc : String)
  | arityMismatch (expected got : Nat)
  | bareSpecialIdentifier (name : String)
  | missingMatchBranch (tag : Nat) (arity : Nat)
  | emptyMatch
  | missingOpenMica
  | unsupportedOpen (path : Path)
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
  | .missingField name => s!"missing field '{name}'"
  | .duplicateConstructor name => s!"duplicate constructor '{name}'"
  | .duplicateType name => s!"duplicate type name '{name}'"
  | .duplicateField name =>
    s!"duplicate field '{name}' (shadowing fields from a previous type is not supported)"
  | .unsupportedRecordUpdate => "record update expressions are not supported"
  | .unsupportedPattern desc => s!"unsupported pattern: {desc}"
  | .unsupportedFeature desc => s!"unsupported feature: {desc}"
  | .arityMismatch expected got => s!"arity mismatch: expected {expected}, got {got}"
  | .bareSpecialIdentifier name => s!"'{name}' cannot be used as a variable; it must be applied"
  | .missingMatchBranch tag arity =>
    s!"missing match branch for constructor {tag} (of {arity})"
  | .emptyMatch => "empty match expression"
  | .missingOpenMica => "source files must begin with `open Mica`"
  | .unsupportedOpen path => s!"unsupported open '{path}' (only `open Mica` is supported)"
  | .unsupportedPath path => s!"unsupported qualified path '{path}'"
  | .internalError desc => s!"internal error: {desc}"

def ElaborateError.toString (e : ElaborateError) : String :=
  let loc := s!"{e.loc.start.file}:{e.loc.start.line}:{e.loc.start.col}"
  s!"{loc}: {e.kind.toString}"

instance : ToString ElaborateError := ⟨ElaborateError.toString⟩

-- ---------------------------------------------------------------------------
-- Elaboration environment (association lists)


private structure TypeInfo where
  core  : TinyML.TypeName
  arity : Nat

/-- What a constructor resolves to: its tag among the `arity` constructors of
`owner`, and the payload it carries. -/
structure CtorInfo where
  tag     : Nat
  arity   : Nat
  owner   : TinyML.TypeName
  payload : Untyped.Typ

structure ElabEnv where
  types    : List (TypeConstructor × TypeInfo)                := []
  ctors    : List (Constructor × CtorInfo)                    := []
  fields   : List (FieldName × (TypeConstructor × Nat))      := []
  records  : List (TypeConstructor × List (FieldName × Untyped.Typ)) := []
  locals   : List Var                                        := []
  resolver : Resolver

-- ---------------------------------------------------------------------------
-- Helpers

private abbrev ElabM := Except ElaborateError

private def err (loc : Location) (kind : ElaborateErrorKind) : ElabM α :=
  .error { loc, kind }

private def Pattern.binderName? (pat : Pattern) : Option Var :=
  match pat.kind with
  | .binder (some name) _ => some name
  | _ => none

private def Pattern.productBoundNames (pat : Pattern) : List Var :=
  match pat.kind with
  | .tuple pats => pats.filterMap Pattern.binderName?
  | .record fields => fields.filterMap (fun (_, field) => field.binderName?)
  | _ => []

private partial def Pattern.boundNames (pat : Pattern) : List Var :=
  match pat.kind with
  | .binder (some name) _ => [name]
  | .ctor _ (some payload) =>
      match payload.binderName? with
      | some name => [name]
      | none => payload.productBoundNames
  | .cons head tail => head.boundNames ++ tail.boundNames
  | .tuple _ | .record _ => pat.productBoundNames
  | _ => []

private def ElabEnv.bindPattern (env : ElabEnv) (pat : Pattern) : ElabEnv :=
  { env with locals := pat.boundNames ++ env.locals }

private def ElabEnv.bindPatterns (env : ElabEnv) (pats : List Pattern) : ElabEnv :=
  { env with locals := pats.flatMap Pattern.boundNames ++ env.locals }

private def ElabEnv.bindBinder (env : ElabEnv) : Untyped.Binder → ElabEnv
  | .none => env
  | .named name _ => { env with locals := name :: env.locals }

private def ElabEnv.isLocal (env : ElabEnv) (name : Var) : Bool :=
  env.locals.elem name

private def checkRecordFieldSet (loc : Location) (fieldOrder : List FieldName) :
    List (FieldName × α) → ElabM Unit
  | [] => .ok ()
  | (name, _) :: rest =>
      if !fieldOrder.any (· == name) then
        err loc (.unknownField name)
      else if rest.any (fun (other, _) => other == name) then
        err loc (.duplicateField name)
      else
        checkRecordFieldSet loc fieldOrder rest

private def reorderFields (loc : Location) (provided : List (FieldName × α)) :
    List FieldName → ElabM (List α)
  | [] => .ok []
  | fieldName :: rest => do
    match provided.find? (fun (n, _) => n == fieldName) with
    | some (_, a) =>
      let rest' ← reorderFields loc provided rest
      .ok (a :: rest')
    | none => err loc (.missingField fieldName)

private def recordFieldsFor (env : ElabEnv) (loc : Location) (fields : List (FieldName × α)) :
    ElabM (List (FieldName × Untyped.Typ)) :=
  match fields with
  | [] => err loc (.unsupportedFeature "empty record pattern")
  | (name, _) :: _ =>
      match List.lookup name env.fields with
      | none => err loc (.unknownField name)
      | some (tyName, _) =>
          match List.lookup tyName env.records with
          | none => err loc (.unknownType tyName)
          | some fieldInfo => do
              checkRecordFieldSet loc (fieldInfo.map Prod.fst) fields
              .ok fieldInfo

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
  | some info =>
    if info.arity != arity then
      .error { loc, kind := .arityMismatch arity info.arity }
    else
      let b := binder.getD .none
      .ok (listSet acc info.tag (some (b, body)))

-- ---------------------------------------------------------------------------
-- Expression elaboration

private def elaborateBinOp (loc : Location) : BinOp → ElabM TinyML.BinOp
  | .add => .ok .add | .sub => .ok .sub | .mul => .ok .mul
  | .div => .ok .div | .mod => .ok .mod
  | .eq => .ok .eq | .lt => .ok .lt | .le => .ok .le | .gt => .ok .gt | .ge => .ok .ge
  | .and => .ok .and | .or => .ok .or
  | .neq | .semi | .pipeRight | .atAt | .assign | .concat | .append | .cons
  | .fadd | .fsub | .fmul | .fdiv =>
    err loc (.internalError "desugared operator reached elaborateBinOp")

-- Helper to elaborate a constructor lookup (not recursive)
private def elaborateCtorLookup (env : ElabEnv) (loc : Location) (name : String)
    (arg : Option Untyped.Expr) : ElabM Untyped.Expr :=
  match List.lookup name env.ctors with
  | some info => .ok (.inj info.tag info.arity (arg.getD (.const .unit)) info.owner)
  | none => err loc (.unknownConstructor name)

/-- Apply a single expression attribute to an already-elaborated term. One arm
per supported expression attribute; unknown names are rejected here (mirroring
how `[@@...]` names are validated). -/
private def applyAttr (e : Untyped.Expr) (attr : Attribute) : ElabM Untyped.Expr :=
  match attr.name, attr.payload with
  | .owned, none =>
      match e with
      | .ref _ inner => .ok (.ref .owned inner)
      | .arrayMake _ len init => .ok (.arrayMake .owned len init)
      | _ => err attr.loc (.unsupportedFeature "[@owned] only applies to 'ref' or 'Array.make'")
  | .owned, some payload => err payload.loc (.unsupportedFeature "[@owned] takes no payload")
  | name, _ => err attr.loc (.unsupportedFeature s!"unknown expression attribute [@{name}]")

private def bareSpecial (loc : Location) (path : Path) : ElabM Untyped.Expr :=
  err loc (.bareSpecialIdentifier path.toString)

private partial def Pattern.lowerLists (pat : Pattern) : Pattern :=
  let kind := match pat.kind with
    | .nil => .ctor (Path.single "[]") none
    | .cons head tail =>
        let head := head.lowerLists
        let tail := tail.lowerLists
        .ctor (Path.single "::") (some { loc := pat.loc, kind := .tuple [head, tail] })
    | .ctor path payload => .ctor path (payload.map Pattern.lowerLists)
    | .tuple pats => .tuple (pats.map Pattern.lowerLists)
    | .record fields => .record (fields.map fun (name, p) => (name, p.lowerLists))
    | kind => kind
  { pat with kind }

private def isProductPattern (pat : Pattern) : Bool :=
  match pat.kind with
  | .tuple (_ :: _) | .record _ => true
  | _ => false

private def productArgumentName (stem : String) (idx : Nat) : String :=
  s!"{stem}{idx}"

/-- The name of a `let` that takes arguments — just the name, since there is no
type to put on it: with arguments the annotation is the function's return type,
written after them. An annotation here is rejected rather than silently dropped.
(OCaml rejects the syntax outright.) -/
def patternToName (pat : Pattern) : ElabM (Option Var) :=
  match pat.kind with
  | .wildcard => .ok none
  | .binder _ (some _) =>
    err pat.loc (.unsupportedFeature "a let with arguments cannot annotate its name")
  | .binder name none => .ok name
  | _ => err pat.loc (.unsupportedPattern "expected a simple binder (variable or wildcard)")

/-- The binder a `let`'s name becomes: unannotated, by `patternToName`. -/
private def nameBinder : Option Var → Untyped.Binder
  | none => .none
  | some name => .named name none

/-- A `let` with no arguments has two places to write its type — on the binder
pattern and after it — and they mean the same thing, so at most one may be
used. -/
private def annotateBinder (loc : Location) :
    Untyped.Binder → Option Untyped.Typ → ElabM Untyped.Binder
  | b, none => .ok b
  | .named n none, some ty => .ok (.named n (some ty))
  | .named _ (some _), some _ =>
    err loc (.unsupportedFeature "a let is annotated once: on its binder or after it")
  | .none, some _ => .ok .none

mutual
partial def elaborateOptTyp (env : ElabEnv) : Option Typ → ElabM (Option Untyped.Typ)
  | none => .ok none
  | some ty => do let ty' ← Typ.elaborate env ty; .ok (some ty')

-- ---------------------------------------------------------------------------
-- Pattern helpers

/-- A binder pattern together with the type it annotates, if any. -/
partial def patternToBinder (env : ElabEnv) (pat : Pattern) : ElabM Untyped.Binder :=
  match pat.kind with
  | .wildcard => .ok .none
  | .binder none _ => .ok .none
  | .binder (some n) ty => do
    let ty' ← elaborateOptTyp env ty
    .ok (.named n ty')
  | _ => err pat.loc (.unsupportedPattern "expected a simple binder (variable or wildcard)")

partial def patternListToAnnotatedBinders (env : ElabEnv) :
    List Pattern → ElabM (List Untyped.Binder)
  | [] => .ok []
  | p :: ps => do
    let b ← patternToBinder env p
    let bs ← patternListToAnnotatedBinders env ps
    .ok (b :: bs)

partial def patternRecordFieldsToBinders (env : ElabEnv)
    : List (FieldName × Pattern) → ElabM (List (FieldName × Untyped.Binder))
  | [] => .ok []
  | (name, pat) :: rest => do
      let binder ← patternToBinder env pat
      let binders ← patternRecordFieldsToBinders env rest
      .ok ((name, binder) :: binders)

partial def patternToProductBinders (env : ElabEnv) (pat : Pattern) :
    ElabM (List Untyped.Binder) :=
  match pat.kind with
  | .tuple pats => patternListToAnnotatedBinders env pats
  | .record fields => do
      let fieldInfo ← recordFieldsFor env pat.loc fields
      let binders ← patternRecordFieldsToBinders env fields
      reorderFields pat.loc binders (fieldInfo.map Prod.fst)
  | _ => err pat.loc (.unsupportedPattern "expected a flat product binder")

partial def patternComponentType? (env : ElabEnv) (pat : Pattern) : ElabM (Option Untyped.Typ) :=
  match pat.kind with
  | .binder _ (some ty) => do
      let ty' ← Typ.elaborate env ty
      .ok (some ty')
  | .binder _ none | .wildcard => .ok none
  | _ => err pat.loc (.unsupportedPattern "expected a flat tuple binder")

partial def patternComponentTypes? (env : ElabEnv) :
    List Pattern → ElabM (Option (List Untyped.Typ))
  | [] => .ok (some [])
  | p :: ps => do
      let ty? ← patternComponentType? env p
      let tys? ← patternComponentTypes? env ps
      match ty?, tys? with
      | some ty, some tys => .ok (some (ty :: tys))
      | _, _ => .ok none

partial def patternToProductType (env : ElabEnv) (pat : Pattern) : ElabM Untyped.Typ :=
  match pat.kind with
  | .tuple pats => do
      match ← patternComponentTypes? env pats with
      | some tys => .ok (Untyped.Typ.tuple tys)
      | none =>
          err pat.loc (.unsupportedPattern "tuple function arguments must annotate each component")
  | .record fields => do
      let fieldInfo ← recordFieldsFor env pat.loc fields
      .ok (Untyped.Typ.tuple (fieldInfo.map Prod.snd))
  | _ => err pat.loc (.unsupportedPattern "expected a flat product binder")

partial def elaborateFunctionArgs (env : ElabEnv) (stem : String) :
    Nat → List Pattern → Untyped.Expr → ElabM (List Untyped.Binder × Untyped.Expr)
  | _, [], body => .ok ([], body)
  | idx, pat :: pats, body => do
      let (restArgs, restBody) ← elaborateFunctionArgs env stem (idx + 1) pats body
      if isProductPattern pat then
        let argName := productArgumentName stem idx
        let argTy ← patternToProductType env pat
        let names ← patternToProductBinders env pat
        .ok (.named argName (some argTy) :: restArgs, .letProd names (.var argName) restBody)
      else
        let arg ← patternToBinder env pat
        .ok (arg :: restArgs, restBody)

/-- Elaborate a surface type into the untyped IR's type language: lower its
kind, then apply any type attributes (`T [@name payload]`) left-to-right.
Single entry point for every type position, so `[@spec]` is honored wherever a
type may be written. -/
partial def Typ.elaborate (env : ElabEnv) : Typ → ElabM Untyped.Typ
  | ⟨loc, kind, attrs⟩ => do
      let t ← TypKind.elaborate env loc kind
      Typ.applyAttrs env t attrs

partial def Typ.applyAttrs (env : ElabEnv) (t : Untyped.Typ) :
    List Attribute → ElabM Untyped.Typ
  | [] => .ok t
  | attr :: attrs => do
    let t' ← Typ.applyAttr env t attr
    Typ.applyAttrs env t' attrs

/-- Apply a single type attribute. `[@owned]` turns a shared `ref A` into an
owned `owned A` (mirroring how the expression-level `[@owned]` validates
`ref`); `[@spec]` records a specification on the arrow it annotates, exactly as
`[@@spec]` does on a declaration. -/
partial def Typ.applyAttr (env : ElabEnv) (t : Untyped.Typ) (attr : Attribute) :
    ElabM Untyped.Typ :=
  match attr.name, attr.payload with
  | .owned, none =>
    match t with
    | .ref inner => .ok (.owned inner)
    | .array inner => .ok (.ownedArray inner)
    | _ => err attr.loc (.unsupportedFeature "[@owned] only applies to a 'ref' or 'array' type")
  | .owned, some payload => err payload.loc (.unsupportedFeature "[@owned] takes no payload")
  | .spec, none => err attr.loc (.unsupportedFeature "[@spec] expects a specification payload")
  | .spec, some payload => do
    let e ← Expr.elaborate env payload
    match Spec.parse e with
    | .error msg => err payload.loc (.unsupportedFeature s!"invalid [@spec]: {msg}")
    | .ok body =>
      match t with
      | .arrow args ret none => .ok (.arrow args ret (some body))
      | .arrow _ _ (some _) =>
        err attr.loc (.unsupportedFeature "a function type carries at most one [@spec]")
      | _ => err attr.loc (.unsupportedFeature "[@spec] only applies to a function type")
  | name, _ => err attr.loc (.unsupportedFeature s!"unknown type attribute [@{name}]")

partial def TypKind.elaborate (env : ElabEnv) (loc : Location) : TypKind → ElabM Untyped.Typ
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
    | "int"  => if args'.isEmpty then .ok (.core .int)  else err loc (.arityMismatch 0 args'.length)
    | "bool" => if args'.isEmpty then .ok (.core .bool) else err loc (.arityMismatch 0 args'.length)
    | "unit" => if args'.isEmpty then .ok (.core .unit) else err loc (.arityMismatch 0 args'.length)
    | "char" => if args'.isEmpty then .ok (.core .char) else err loc (.arityMismatch 0 args'.length)
    | "string" => if args'.isEmpty then .ok (.core .string) else err loc (.arityMismatch 0 args'.length)
    | "float" => if args'.isEmpty then .ok (.core .float) else err loc (.arityMismatch 0 args'.length)
    | "ref" =>
      match args' with
      | [arg] => .ok (.ref arg)
      | _ => err loc (.arityMismatch 1 args'.length)
    | "array" =>
      match args' with
      | [arg] => .ok (.array arg)
      | _ => err loc (.arityMismatch 1 args'.length)
    | "vec" =>
      match args' with
      | [arg] => .ok (.vec arg)
      | _ => err loc (.arityMismatch 1 args'.length)
    | _ =>
      match List.lookup name env.records with
      | some fields =>
          if args'.isEmpty then .ok (.tuple (fields.map Prod.snd))
          else err loc (.arityMismatch 0 args'.length)
      | none =>
      match List.lookup name env.types with
      | some info =>
          if args'.length = info.arity then .ok (.named info.core args')
          else err loc (.arityMismatch info.arity args'.length)
      | none => err loc (.unknownType name)
  | .arrow dom cod => do
    let dom' ← Typ.elaborate env dom
    let cod' ← Typ.elaborate env cod
    match cod' with
    | .arrow args ret none => .ok (.arrow (dom' :: args) ret none)
    | _ => .ok (.arrow [dom'] cod' none)
  | .tuple ts => do
    let ts' ← Typ.elaborateList env ts
    .ok (.tuple ts')

partial def Typ.elaborateList (env : ElabEnv) : List Typ → ElabM (List Untyped.Typ)
  | [] => .ok []
  | ty :: ts => do
    let t' ← Typ.elaborate env ty
    let ts' ← Typ.elaborateList env ts
    .ok (t' :: ts')

/-- Elaborate an expression: lower its kind, then apply any expression
attributes (`e [@name payload]`) left-to-right. This is the single entry point
for every expression position, so attributes are honored everywhere. -/
partial def Expr.elaborate (env : ElabEnv) : Expr → ElabM Untyped.Expr
  | ⟨loc, kind, attrs⟩ => do
      let e ← ExprKind.elaborate env loc kind
      attrs.foldlM applyAttr e

partial def ExprKind.elaborate (env : ElabEnv) (loc : Location) : ExprKind → ElabM Untyped.Expr
  | .const (.int n)  => .ok (.const (.int n))
  | .const (.float f) => .ok (.const (.float f.toBits))
  | .const (.bool b) => .ok (.const (.bool b))
  | .const (.char c) =>
      if c.toNat < 256 then .ok (.const (.char (UInt8.ofNat c.toNat)))
      else err loc (.unsupportedFeature "char literals must be byte-sized")
  | .const (.string s) => .ok (.const (.string s))
  | .const .unit     => .ok (.const .unit)

  | .var path =>
    if path.isQualified then
      match env.resolver.value path with
      | some (.userVar n) => .ok (.var n)
      | some (.primitive n kind) =>
        (match kind with
        | .function => .ok (.prim n)
        | .nullary => .ok (.app (.prim n) []))
      | some (.special _) => bareSpecial loc path
      | none => err loc (.unsupportedPath path)
    else
      let name := path.head
      if env.isLocal name then
        .ok (.var name)
      else
        match name with
        | "ref" | "not" => err loc (.bareSpecialIdentifier name)
        | _ =>
          match List.lookup name env.ctors with
          | some info => .ok (.inj info.tag info.arity (.const .unit) info.owner)
          | none =>
            -- Bare prelude values resolve only when no lexical binder shadows
            -- them; qualified paths always resolve through the resolver.
            match env.resolver.value path with
            | some (.primitive n .function) => .ok (.prim n)
            | some (.primitive n .nullary) => .ok (.app (.prim n) [])
            | _ => .ok (.var name)

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
      if !path.isQualified && !env.isLocal path.head && path.head == "not" then
        match args with
        | [arg] => do
          let arg' ← Expr.elaborate env arg
          .ok (.unop .not arg')
        | _ => err loc (.arityMismatch 1 args.length)
      else if !path.isQualified && !env.isLocal path.head && path.head == "ref" then
        match args with
        | [arg] => do
          let arg' ← Expr.elaborate env arg
          .ok (.ref .shared arg')
        | _ => err loc (.arityMismatch 1 args.length)
      else if path.isQualified then
        match env.resolver.value path with
        | some (.userVar n) => do
          let args' ← Expr.elaborateList env args
          .ok (.app (.var n) args')
        | some (.primitive n _) => do
          let args' ← Expr.elaborateList env args
          .ok (.app (.prim n) args')
        | some (.special .arrayMake) =>
            match args with
            | [len, init] => do
              let len' ← Expr.elaborate env len
              let init' ← Expr.elaborate env init
              .ok (.arrayMake .shared len' init')
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
    let arr' ← Expr.elaborate env arr
    let idx' ← Expr.elaborate env idx
    let val' ← Expr.elaborate env val
    .ok (.arraySet arr' idx' val')
  | .binop .neq l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.unop .not (.binop .eq l' r'))
  | .binop .concat l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "string_cat") [l', r'])
  | .binop .append l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "list_append") [l', r'])
  | .binop .cons head tail => do
    let head' ← Expr.elaborate env head
    let tail' ← Expr.elaborate env tail
    elaborateCtorLookup env loc "::" (some (.tuple [head', tail']))
  | .binop .fadd l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_add") [l', r'])
  | .binop .fsub l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_sub") [l', r'])
  | .binop .fmul l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_mul") [l', r'])
  | .binop .fdiv l r => do
    let l' ← Expr.elaborate env l
    let r' ← Expr.elaborate env r
    .ok (.app (.prim "float_div") [l', r'])
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

  | .letIn isRec binders retTy bound body =>
    match binders with
    | [] => err loc (.unsupportedFeature "let with no binders")
    | [pat] =>
      if isRec then do
        -- `let rec f : T = fun x -> ... in ...`: the literal's self-reference
        -- is the let's own name, so recursive calls go through its type. The
        -- same shape a recursive declaration gets.
        let name ← patternToBinder env pat
        let name ← annotateBinder loc name (← elaborateOptTyp env retTy)
        let bound' ← Expr.elaborate (env.bindPattern pat) bound
        match bound' with
        | .fix .none args retTy' inner => do
          let body' ← Expr.elaborate (env.bindPattern pat) body
          .ok (.letIn name (.fix name args retTy' inner) body')
        | _ => err loc (.unsupportedFeature "let rec requires a function")
      else do
        let bound' ← Expr.elaborate env bound
        let body' ← Expr.elaborate (env.bindPattern pat) body
        if isProductPattern pat then
          if retTy.isSome then
            err loc (.unsupportedFeature "a destructuring let cannot be annotated")
          else do
            let names ← patternToProductBinders env pat
            .ok (.letProd names bound' body')
        else do
          -- With no arguments the annotation is the bound value's own type, so
          -- it lands on the binder and the bound expression is checked at it.
          let name ← patternToBinder env pat
          let name ← annotateBinder loc name (← elaborateOptTyp env retTy)
          .ok (.letIn name bound' body')
    | pat :: args => do
      let name := nameBinder (← patternToName pat)
      let self := if isRec then name else .none
      let boundEnv := env.bindPatterns args
      let boundEnv := if isRec then boundEnv.bindPattern pat else boundEnv
      let bound' ← Expr.elaborate boundEnv bound
      let (args', bound'') ← elaborateFunctionArgs env "$param" 0 args bound'
      let body' ← Expr.elaborate (env.bindPattern pat) body
      -- With arguments the annotation is the function's return type.
      let retTy' ← elaborateOptTyp env retTy
      .ok (.letIn name (.fix self args' retTy' bound'') body')

  | .fun_ [] _ _ =>
    err loc (.unsupportedFeature "function expressions require at least one argument")
  | .fun_ args retTy body => do
    let retTy' ← elaborateOptTyp env retTy
    let body' ← Expr.elaborate (env.bindPatterns args) body
    let (args', body'') ← elaborateFunctionArgs env "$param" 0 args body'
    .ok (.fix .none args' retTy' body'')

  | .match_ scrut arms => do
    let scrut' ← Expr.elaborate env scrut
    let arms' ← MatchArm.elaborateList env arms
    match arms' with
    | [] => err loc .emptyMatch
    | (ctorName, _, _) :: _ =>
      match List.lookup ctorName env.ctors with
      | none => err loc (.unknownConstructor ctorName)
      | some info => do
        let arity := info.arity
        let init : List (Option (Untyped.Binder × Untyped.Expr)) := List.replicate arity none
        let filled ← arms'.foldlM
          (fun acc (name, binder, body) => insertBranch env loc arity acc name binder body)
          init
        let branches ← checkAllBranches loc filled arity 0
        .ok (.match_ scrut' branches)

  | .tuple es => do
    let es' ← Expr.elaborateList env es
    .ok (.tuple es')

  | .list es => do
    let es' ← Expr.elaborateList env es
    let nil ← elaborateCtorLookup env loc "[]" none
    match List.lookup "::" env.ctors with
    | some info =>
        .ok (es'.foldr
          (fun head tail => .inj info.tag info.arity (.tuple [head, tail]) info.owner) nil)
    | none => err loc (.unknownConstructor "::")

  | .record flds => do
    let fieldInfo ← recordFieldsFor env loc flds
    let elaborated ← Expr.elaborateRecordFields env flds
    let es' ← reorderFields loc elaborated (fieldInfo.map Prod.fst)
    .ok (.tuple es')

  | .recordUpdate _ _ => err loc .unsupportedRecordUpdate

  | .annot e _ => Expr.elaborate env e

partial def Expr.elaborateList (env : ElabEnv) : List Expr → ElabM (List Untyped.Expr)
  | [] => .ok []
  | e :: es => do
    let e' ← Expr.elaborate env e
    let es' ← Expr.elaborateList env es
    .ok (e' :: es')

partial def Expr.elaborateRecordFields (env : ElabEnv)
    : List (FieldName × Expr) → ElabM (List (FieldName × Untyped.Expr))
  | [] => .ok []
  | (name, e) :: rest => do
    let e' ← Expr.elaborate env e
    let rest' ← Expr.elaborateRecordFields env rest
    .ok ((name, e') :: rest')

partial def MatchArm.elaborateList (env : ElabEnv)
    : List MatchArm → ElabM (List (Constructor × Option Untyped.Binder × Untyped.Expr))
  | [] => .ok []
  | ⟨pat, body⟩ :: arms => do
    let pat := pat.lowerLists
    let (ctorName, binder, body'') ← match pat.kind with
      | .ctor path payload => do
        let name ← if path.isQualified then
          match env.resolver.ctor path with
          | some (.aliased n) => .ok n
          | none => err pat.loc (.unsupportedPath path)
        else .ok path.head
        let payloadTy ← match List.lookup name env.ctors with
          | some info => .ok info.payload
          | none => err pat.loc (.unknownConstructor name)
        let (binder, body'') ← match payload with
          | some p =>
            let body' ← Expr.elaborate (env.bindPattern p) body
            match payloadTy with
            | .tuple _ | .core (.tuple _) =>
                if isProductPattern p then do
                  let names ← patternToProductBinders env p
                  let argName := "$arg0"
                  pure (some (.named argName none), .letProd names (.var argName) body')
                else
                  err p.loc (.unsupportedPattern
                    "constructor tuple or record payload must be destructured in the constructor pattern")
            | _ =>
                if isProductPattern p then
                  err p.loc (.unsupportedPattern "constructor payload is not a product")
                else do
                  let b ← patternToBinder env p
                  pure (some b, body')
          | none =>
            let body' ← Expr.elaborate env body
            match payloadTy with
            | .core .unit => pure (none, body')
            | _ => err pat.loc (.unsupportedPattern "constructor payload must be matched")
        pure (name, binder, body'')
      | _ => err pat.loc (.unsupportedPattern "only constructor patterns are allowed in match")
    let rest ← MatchArm.elaborateList env arms
    .ok ((ctorName, binder, body'') :: rest)

end

-- ---------------------------------------------------------------------------
-- Type declaration elaboration

private def elaborateCtorDefs (env : ElabEnv) (loc : Location) (owner : TinyML.TypeName)
    (ctorDefs : List (Constructor × Option Typ)) (tag : Nat) (arity : Nat)
    : ElabM (List Untyped.Typ × List (Constructor × CtorInfo)) :=
  match ctorDefs with
  | [] => .ok ([], [])
  | (ctorName, payloadTy) :: rest => do
    if (List.lookup ctorName env.ctors).isSome then
      err loc (.duplicateConstructor ctorName)
    else do
    let payloadTy' ← match payloadTy with
      | some ty => Typ.elaborate env ty
      | none => .ok (.core .unit)
    let (restTypes, restCtors) ← elaborateCtorDefs env loc owner rest (tag + 1) arity
    .ok (payloadTy' :: restTypes,
         (ctorName, ⟨tag, arity, owner, payloadTy'⟩) :: restCtors)

private def elaborateVariant (env : ElabEnv) (loc : Location) (name : TypeConstructor)
    (tparams : List TinyML.TyVar) (ctorDefs : List (Constructor × Option Typ))
    : ElabM (ElabEnv × Untyped.TypeDecl) := do
  if (List.lookup name env.types).isSome then
    return ← err loc (.duplicateType name)
  let arity := ctorDefs.length
  -- Register the type name as a named reference so both recursive self-references in
  -- constructor payloads and later uses resolve to the named type (not the inlined sum).
  let coreName := TinyML.TypeName.user name
  let envWithSelf := { env with types := (name, ⟨coreName, tparams.length⟩) :: env.types }
  let (payloadTypes, newCtors) ← elaborateCtorDefs envWithSelf loc coreName ctorDefs 0 arity
  let env' := { envWithSelf with ctors := newCtors ++ env.ctors }
  let decl : Untyped.TypeDecl := { name := coreName, body := { tparams, payloads := payloadTypes } }
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
  if (List.lookup name env.types).isSome then
    return ← err loc (.duplicateType name)
  let coreName := TinyML.TypeName.user name
  let envWithSelf := { env with types := (name, ⟨coreName, 0⟩) :: env.types }
  let newFields ← elaborateFieldDefs env loc name fieldDefs 0
  let fieldTypes ← fieldDefs.mapM (fun (fieldName, ty) => do
    let ty' ← Typ.elaborate envWithSelf ty
    pure (fieldName, ty'))
  .ok { env with
    types := (name, ⟨coreName, 0⟩) :: env.types
    records := (name, fieldTypes) :: env.records
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
    (spec : Option Untyped.SpecBody)
    : ElabM (Untyped.ValDecl Untyped.SpecBody) := do
  match binders with
  | [] => err loc (.unsupportedFeature "declaration with no binders")
  | [pat] =>
    -- A declaration with no arguments: its annotation is the declaration's own
    -- type, which is where a `[@spec]` on it belongs.
    let name ← patternToBinder env pat
    let name ← annotateBinder loc name (← elaborateOptTyp env retTy)
    if isRec then
      -- `let rec f : T = fun x -> ...`: the literal's self-reference is the
      -- declaration's own name, so recursive calls go through its type.
      let body' ← Expr.elaborate (env.bindPattern pat) body
      match body' with
      | .fix .none args retTy' inner =>
        .ok { name, body := .fix name args retTy' inner, spec }
      | _ => err loc (.unsupportedFeature "let rec requires a function")
    else do
      let body' ← Expr.elaborate env body
      .ok { name, body := body', spec }
  | pat :: args =>
    let name := nameBinder (← patternToName pat)
    let self := if isRec then name else .none
    let retTy' ← elaborateOptTyp env retTy
    let bodyEnv := env.bindPatterns args
    let bodyEnv := if isRec then bodyEnv.bindPattern pat else bodyEnv
    let body' ← Expr.elaborate bodyEnv body
    let (args', body'') ← elaborateFunctionArgs env "$param" 0 args body'
    .ok { name, body := .fix self args' retTy' body'', spec }

-- ---------------------------------------------------------------------------
-- Program elaboration

/-- What a value declaration's attributes say about it. -/
private structure ValAttrs where
  /-- The specification `[@@spec]` carries. -/
  spec : Option Untyped.SpecBody := none
  /-- Whether `[@@fn]` registers it as a spec-level function. The attribute
  takes no payload; the function's own name is used for the derived relation. -/
  fn : Bool := false

/-- Read a value declaration's attributes. Every attribute is accounted for —
an unknown name is rejected, and neither may be written twice — so none is
silently ignored. -/
private def elaborateValAttrs (env : ElabEnv) (acc : ValAttrs) :
    List Attribute → ElabM ValAttrs
  | [] => .ok acc
  | attr :: attrs =>
    match attr.name, attr.payload with
    | .spec, some payload =>
      if acc.spec.isSome then
        err attr.loc (.unsupportedFeature "a declaration carries at most one [@@spec]")
      else do
        let e ← Expr.elaborate env payload
        match Spec.parse e with
        | .ok spec => elaborateValAttrs env { acc with spec := some spec } attrs
        | .error msg => err payload.loc (.unsupportedFeature s!"invalid [@@spec]: {msg}")
    | .spec, none =>
      err attr.loc (.unsupportedFeature "[@@spec] expects a specification payload")
    | .fn, none =>
      if acc.fn then err attr.loc (.unsupportedFeature "a declaration carries at most one [@@fn]")
      else elaborateValAttrs env { acc with fn := true } attrs
    | .fn, some payload => err payload.loc (.unsupportedFeature
        "[@@fn] takes no payload; the function's own name is used for the relation")
    | name, _ =>
      err attr.loc (.unsupportedFeature s!"unknown declaration attribute [@@{name}]")

/-- Attributes are meaningful on a value declaration only. The parser accepts
`[@@...]` after any declaration, so every other kind rejects them here rather
than dropping them silently. -/
def Decl.noAttrs (decl : Decl) (what : String) : ElabM Unit :=
  match decl.attrs with
  | [] => .ok ()
  | attr :: _ =>
    err attr.loc (.unsupportedFeature s!"{what} declaration takes no attributes, \
      but carries [@@{attr.name}]")

def Decl.elaborate (env : ElabEnv) (decl : Decl)
    : ElabM (ElabEnv × Option (Untyped.Decl Untyped.SpecBody)) := do
  match decl.kind with
  | .open_ path =>
    if path == Path.single "Mica" then
      err decl.loc (.unsupportedFeature "`open Mica` must be the first declaration")
    else
      err decl.loc (.unsupportedOpen path)
  | .type_ tdecl => do
    Decl.noAttrs decl "a type"
    let (env', tdecl') ← TypeDecl.elaborate env decl.loc tdecl
    .ok (env', tdecl'.map Untyped.Decl.type_)
  | .val_ isRec binders retTy body => do
    let attrs ← elaborateValAttrs env {} decl.attrs
    let d ← ValDecl.elaborate env decl.loc isRec binders retTy body attrs.spec
    -- A `[@@fn]` declaration uses its own name for the derived relation.
    let relation ← if attrs.fn then
      match d.name with
      | .named x _ => .ok (some x)
      | .none => err decl.loc (.unsupportedFeature "[@@fn] requires a named declaration")
    else .ok none
    .ok (env.bindBinder d.name, some (.val_ { d with relation }))

private def elaborateDecls (env : ElabEnv) :
    List Decl → ElabM (List (Untyped.Decl Untyped.SpecBody))
  | [] => .ok []
  | d :: ds => do
    let (env', optDecl) ← Decl.elaborate env d
    let rest ← elaborateDecls env' ds
    match optDecl with
    | some decl => .ok (decl :: rest)
    | none => .ok rest

private def requireOpenMica : List Decl → ElabM (List Decl)
  | [] => err default .missingOpenMica
  | d :: ds =>
    match d.kind with
    | .open_ path =>
      if path == Path.single "Mica" then do Decl.noAttrs d "an open"; .ok ds
      else err d.loc (.unsupportedOpen path)
    | _ => err d.loc .missingOpenMica

-- ---------------------------------------------------------------------------
-- Predefined types

/-- Embed a schema type into the annotation language. Lossy: an arrow's
specification is dropped, since a source specification is untyped expression
syntax that a core one cannot be turned back into. Only the predefined
constructor payloads go through here, and they carry none. -/
private def schemaAnnotation : TinyML.SchemaTyp → Untyped.Typ
  | .prim p => .core (.prim p)
  | .sum ts => .sum (ts.map schemaAnnotation)
  | .arrow args ret _ =>
      .arrow (args.map schemaAnnotation) (schemaAnnotation ret) none
  | .ref t => .ref (schemaAnnotation t)
  | .array t => .array (schemaAnnotation t)
  | .ownedArray t => .ownedArray (schemaAnnotation t)
  | .vec t => .vec (schemaAnnotation t)
  | .owned t => .owned (schemaAnnotation t)
  | .empty => .core .empty
  | .value => .core .value
  | .tuple ts => .tuple (ts.map schemaAnnotation)
  | .tvar v => .tvar v
  | .named n args => .named n (args.map schemaAnnotation)

private def predefCtorEntries (p : TinyML.Predef) : List (Constructor × CtorInfo) :=
  let arity := p.ctors.length
  let owner := TinyML.TypeName.predef p
  let rec go : List (String × TinyML.SchemaTyp) → Nat → List (Constructor × CtorInfo)
    | [], _ => []
    | (name, payload) :: rest, tag =>
        (name, ⟨tag, arity, owner, schemaAnnotation payload⟩) :: go rest (tag + 1)
  go p.ctors 0

/-- The initial frontend environment derived from the canonical predef catalog.
Predefs participate in name and constructor resolution but are not emitted as
program declarations. -/
private def predefEnv (resolver : Resolver) : ElabEnv :=
  { resolver
    types := TinyML.Predef.all.map fun p =>
      (p.name, ⟨.predef p, p.arity⟩)
    ctors := TinyML.Predef.all.flatMap predefCtorEntries }

def Program.elaborate (resolver : Resolver) (prog : Frontend.Program) :
    ElabM (Untyped.Program Untyped.SpecBody) := do
  let decls ← requireOpenMica prog
  elaborateDecls (predefEnv resolver) decls

end Frontend
