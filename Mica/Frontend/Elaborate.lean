-- SUMMARY: Elaboration of surface syntax into the verifier's core language, with frontend-specific checks.
import Mica.Frontend.AST
import Mica.TinyML.Untyped

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
  | .internalError desc => s!"internal error: {desc}"

def ElaborateError.toString (e : ElaborateError) : String :=
  let loc := s!"{e.loc.start.file}:{e.loc.start.line}:{e.loc.start.col}"
  s!"{loc}: {e.kind.toString}"

instance : ToString ElaborateError := ⟨ElaborateError.toString⟩

-- ---------------------------------------------------------------------------
-- Elaboration environment (association lists)


structure ElabEnv where
  types   : List TypeConstructor                             := []
  ctors   : List (Constructor × (Nat × Nat))                := []
  fields  : List (FieldName × (TypeConstructor × Nat))      := []
  records : List (TypeConstructor × List FieldName)         := []

-- ---------------------------------------------------------------------------
-- Helpers

private abbrev ElabM := Except ElaborateError

private def err (loc : Location) (kind : ElaborateErrorKind) : ElabM α :=
  .error { loc, kind }

-- ---------------------------------------------------------------------------
-- Type elaboration

mutual
def TypKind.elaborate (env : ElabEnv) (loc : Location) : TypKind → ElabM TinyML.Typ
  | .var v => .ok (.tvar v)
  | .con name args => do
    let args' ← Typ.elaborateList env args
    match name with
    | "int"  => if args'.isEmpty then .ok .int  else err loc (.arityMismatch 0 args'.length)
    | "bool" => if args'.isEmpty then .ok .bool else err loc (.arityMismatch 0 args'.length)
    | "unit" => if args'.isEmpty then .ok .unit else err loc (.arityMismatch 0 args'.length)
    | "ref" =>
      match args' with
      | [arg] => .ok (.ref arg)
      | _ => err loc (.arityMismatch 1 args'.length)
    | _ =>
      if env.types.elem name then .ok (.named name args')
      else err loc (.unknownType name)
  | .arrow ⟨dloc, dkind⟩ ⟨cloc, ckind⟩ => do
    let dom' ← TypKind.elaborate env dloc dkind
    let cod' ← TypKind.elaborate env cloc ckind
    .ok (.arrow dom' cod')
  | .tuple ts => do
    let ts' ← Typ.elaborateList env ts
    .ok (.tuple ts')

def Typ.elaborateList (env : ElabEnv) : List Typ → ElabM (List TinyML.Typ)
  | [] => .ok []
  | ⟨loc, kind⟩ :: ts => do
    let t' ← TypKind.elaborate env loc kind
    let ts' ← Typ.elaborateList env ts
    .ok (t' :: ts')
end

def Typ.elaborate (env : ElabEnv) (ty : Typ) : ElabM TinyML.Typ :=
  TypKind.elaborate env ty.loc ty.kind

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
  | .neq | .semi | .pipeRight | .atAt | .assign =>
    err loc (.internalError "desugared operator reached elaborateBinOp")

-- Helper to elaborate a constructor lookup (not recursive)
private def elaborateCtorLookup (env : ElabEnv) (loc : Location) (name : String)
    (arg : Option Untyped.Expr) : ElabM Untyped.Expr :=
  match List.lookup name env.ctors with
  | some (tag, arity) => .ok (.inj tag arity (arg.getD (.const .unit)))
  | none => err loc (.unknownConstructor name)

mutual
def ExprKind.elaborate (env : ElabEnv) (loc : Location) : ExprKind → ElabM Untyped.Expr
  | .const (.int n)  => .ok (.const (.int n))
  | .const (.bool b) => .ok (.const (.bool b))
  | .const .unit     => .ok (.const .unit)
  | .const (.char _) => err loc .unsupportedChar

  | .var name =>
    match name with
    | "ref" | "not" => err loc (.bareSpecialIdentifier name)
    | _ =>
      match List.lookup name env.ctors with
      | some (tag, arity) => .ok (.inj tag arity (.const .unit))
      | none => .ok (.var name)

  | .ctor name => elaborateCtorLookup env loc name none

  | .app ⟨_, .var "not"⟩ [⟨al, ak⟩] => do
    let arg' ← ExprKind.elaborate env al ak
    .ok (.unop .not arg')
  | .app ⟨_, .var "not"⟩ args => err loc (.arityMismatch 1 args.length)
  | .app ⟨_, .var "ref"⟩ [⟨al, ak⟩] => do
    let arg' ← ExprKind.elaborate env al ak
    .ok (.ref arg')
  | .app ⟨_, .var "ref"⟩ args => err loc (.arityMismatch 1 args.length)
  | .app ⟨_, .ctor name⟩ [⟨al, ak⟩] => do
    let arg' ← ExprKind.elaborate env al ak
    elaborateCtorLookup env loc name (some arg')
  | .app ⟨_, .ctor name⟩ args =>
    match List.lookup name env.ctors with
    | some _ => err loc (.arityMismatch 1 args.length)
    | none => err loc (.unknownConstructor name)
  | .app ⟨fnLoc, fnKind⟩ args => do
    let fn' ← ExprKind.elaborate env fnLoc fnKind
    let args' ← Expr.elaborateList env args
    .ok (.app fn' args')

  | .binop .semi ⟨ll, lk⟩ ⟨rl, rk⟩ => do
    let l' ← ExprKind.elaborate env ll lk
    let r' ← ExprKind.elaborate env rl rk
    .ok (.letIn .none l' r')
  | .binop .pipeRight ⟨al, ak⟩ ⟨fl, fk⟩
  | .binop .atAt ⟨fl, fk⟩ ⟨al, ak⟩ => do
    let fn' ← ExprKind.elaborate env fl fk
    let arg' ← ExprKind.elaborate env al ak
    .ok (.app fn' [arg'])
  | .binop .assign ⟨ll, lk⟩ ⟨vl, vk⟩ => do
    let loc' ← ExprKind.elaborate env ll lk
    let val' ← ExprKind.elaborate env vl vk
    .ok (.store loc' val')
  | .binop .neq ⟨ll, lk⟩ ⟨rl, rk⟩ => do
    let l' ← ExprKind.elaborate env ll lk
    let r' ← ExprKind.elaborate env rl rk
    .ok (.unop .not (.binop .eq l' r'))
  | .binop op ⟨ll, lk⟩ ⟨rl, rk⟩ => do
    let op' ← elaborateBinOp loc op
    let l' ← ExprKind.elaborate env ll lk
    let r' ← ExprKind.elaborate env rl rk
    .ok (.binop op' l' r')

  | .unop .neg ⟨el, ek⟩ => do
    let e' ← ExprKind.elaborate env el ek
    .ok (.unop .neg e')
  | .unop .deref ⟨el, ek⟩ => do
    let e' ← ExprKind.elaborate env el ek
    .ok (.deref e')
  | .unop .assert ⟨el, ek⟩ => do
    let e' ← ExprKind.elaborate env el ek
    .ok (.assert e')
  | .unop (.proj n) ⟨el, ek⟩ => do
    let e' ← ExprKind.elaborate env el ek
    .ok (.unop (.proj n) e')
  | .unop (.field name) ⟨el, ek⟩ =>
    match List.lookup name env.fields with
    | some (_, idx) => do
      let e' ← ExprKind.elaborate env el ek
      .ok (.unop (.proj idx) e')
    | none => err loc (.unknownField name)

  | .ite ⟨cl, ck⟩ ⟨tl, tk⟩ ⟨el, ek⟩ => do
    let c' ← ExprKind.elaborate env cl ck
    let t' ← ExprKind.elaborate env tl tk
    let e' ← ExprKind.elaborate env el ek
    .ok (.ifThenElse c' t' e')

  | .letIn isRec binders ⟨bl, bk⟩ ⟨dl, dk⟩ =>
    match binders with
    | [] => err loc (.unsupportedFeature "let with no binders")
    | [pat] => do
      let name ← patternToBinder pat
      let bound' ← ExprKind.elaborate env bl bk
      let body' ← ExprKind.elaborate env dl dk
      if isRec then
        err loc (.unsupportedFeature "let rec requires function arguments")
      else
        .ok (.letIn name bound' body')
    | pat :: args => do
      let name ← patternToBinder pat
      let args' ← Pattern.toAnnotatedBinders env args
      let self := if isRec then name else .none
      let bound' ← ExprKind.elaborate env bl bk
      let body' ← ExprKind.elaborate env dl dk
      .ok (.letIn name (.fix self args' none bound') body')

  | .fun_ args retTy ⟨bl, bk⟩ => do
    let args' ← Pattern.toAnnotatedBinders env args
    let retTy' ← elaborateOptTyp env retTy
    let body' ← ExprKind.elaborate env bl bk
    .ok (.fix .none args' retTy' body')

  | .match_ ⟨sl, sk⟩ arms => do
    let scrut' ← ExprKind.elaborate env sl sk
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

  | .annot ⟨il, ik⟩ _ => ExprKind.elaborate env il ik

def Expr.elaborateList (env : ElabEnv) : List Expr → ElabM (List Untyped.Expr)
  | [] => .ok []
  | ⟨l, k⟩ :: es => do
    let e' ← ExprKind.elaborate env l k
    let es' ← Expr.elaborateList env es
    .ok (e' :: es')

def Expr.elaborateRecordFields (env : ElabEnv)
    : List (FieldName × Expr) → ElabM (List (FieldName × Untyped.Expr))
  | [] => .ok []
  | (name, ⟨l, k⟩) :: rest => do
    let e' ← ExprKind.elaborate env l k
    let rest' ← Expr.elaborateRecordFields env rest
    .ok ((name, e') :: rest')

def MatchArm.elaborateList (env : ElabEnv)
    : List MatchArm → ElabM (List (Constructor × Option Untyped.Binder × Untyped.Expr))
  | [] => .ok []
  | ⟨pat, ⟨bl, bk⟩⟩ :: arms => do
    let body' ← ExprKind.elaborate env bl bk
    let (ctorName, binder) ← match pat.kind with
      | .ctor name payload => do
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

def Expr.elaborate (env : ElabEnv) (e : Expr) : ElabM Untyped.Expr :=
  ExprKind.elaborate env e.loc e.kind

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
    (spec : Option Untyped.Expr)
    : ElabM (Untyped.ValDecl Untyped.Expr) := do
  match binders with
  | [] => err loc (.unsupportedFeature "declaration with no binders")
  | [pat] =>
    let name ← patternToBinder pat
    let body' ← Expr.elaborate env body
    if isRec then
      err loc (.unsupportedFeature "let rec requires function arguments")
    else
      .ok { name, body := body', spec }
  | pat :: args =>
    let name ← patternToBinder pat
    let self := if isRec then name else .none
    let args' ← Pattern.toAnnotatedBinders env args
    let retTy' ← elaborateOptTyp env retTy
    let body' ← Expr.elaborate env body
    .ok { name, body := .fix self args' retTy' body', spec }

-- ---------------------------------------------------------------------------
-- Program elaboration

private def elaborateSpec (env : ElabEnv) (attrs : List Attribute)
    : ElabM (Option Untyped.Expr) :=
  match attrs.find? (·.name == "spec") with
  | none => .ok none
  | some attr => do
    let e ← Expr.elaborate env attr.payload
    .ok (some e)

def Decl.elaborate (env : ElabEnv) (decl : Decl)
    : ElabM (ElabEnv × Option (Untyped.Decl Untyped.Expr)) := do
  match decl.kind with
  | .type_ tdecl => do
    let (env', tdecl') ← TypeDecl.elaborate env decl.loc tdecl
    .ok (env', tdecl'.map Untyped.Decl.type_)
  | .val_ isRec binders retTy body => do
    let spec ← elaborateSpec env decl.attrs
    let d ← ValDecl.elaborate env decl.loc isRec binders retTy body spec
    .ok (env, some (.val_ d))

private def elaborateDecls (env : ElabEnv) :
    List Decl → ElabM (List (Untyped.Decl Untyped.Expr))
  | [] => .ok []
  | d :: ds => do
    let (env', optDecl) ← Decl.elaborate env d
    let rest ← elaborateDecls env' ds
    match optDecl with
    | some decl => .ok (decl :: rest)
    | none => .ok rest

def Program.elaborate (prog : Frontend.Program) : ElabM (Untyped.Program Untyped.Expr) :=
  elaborateDecls {} prog

end Frontend
