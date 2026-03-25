import Mica.Frontend.AST
import Mica.TinyML.Expr

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
  | polymorphicTypeDecl (name : String)
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
  | .polymorphicTypeDecl name => s!"polymorphic type declarations are not supported: '{name}'"
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

private def alookup [BEq α] (key : α) : List (α × β) → Option β
  | [] => none
  | (k, v) :: rest => if k == key then some v else alookup key rest

private def acontains [BEq α] (key : α) (m : List (α × β)) : Bool :=
  (alookup key m).isSome

structure ElabEnv where
  types   : List (TypeConstructor × TinyML.Type_)                      := []
  ctors   : List (Constructor × (Nat × Nat × Option TinyML.Type_))    := []
  fields  : List (FieldName × (TypeConstructor × Nat))                 := []
  records : List (TypeConstructor × List FieldName)                    := []

-- ---------------------------------------------------------------------------
-- Helpers

private abbrev ElabM := Except ElaborateError

private def err (loc : Location) (kind : ElaborateErrorKind) : ElabM α :=
  .error { loc, kind }

-- ---------------------------------------------------------------------------
-- Type elaboration

mutual
def TypKind.elaborate (env : ElabEnv) (loc : Location) : TypKind → ElabM TinyML.Type_
  | .var _ => err loc (.polymorphicTypeDecl "type variable")
  | .con name args =>
    match args with
    | [] =>
      match name with
      | "int"  => .ok .int
      | "bool" => .ok .bool
      | "unit" => .ok .unit
      | _      =>
        match alookup name env.types with
        | some ty => .ok ty
        | none => err loc (.unknownType name)
    | _ => err loc (.polymorphicTypeDecl name)
  | .arrow ⟨dloc, dkind⟩ ⟨cloc, ckind⟩ => do
    let dom' ← TypKind.elaborate env dloc dkind
    let cod' ← TypKind.elaborate env cloc ckind
    .ok (.arrow dom' cod')
  | .tuple ts => do
    let ts' ← TypList.elaborate env ts
    .ok (.tuple ts')

def TypList.elaborate (env : ElabEnv) : List Typ → ElabM (List TinyML.Type_)
  | [] => .ok []
  | ⟨loc, kind⟩ :: ts => do
    let t' ← TypKind.elaborate env loc kind
    let ts' ← TypList.elaborate env ts
    .ok (t' :: ts')
end

def Typ.elaborate (env : ElabEnv) (ty : Typ) : ElabM TinyML.Type_ :=
  TypKind.elaborate env ty.loc ty.kind

private def elaborateOptTyp (env : ElabEnv) : Option Typ → ElabM (Option TinyML.Type_)
  | none => .ok none
  | some ty => do let ty' ← Typ.elaborate env ty; .ok (some ty')

-- ---------------------------------------------------------------------------
-- Pattern helpers

private def patternToBinder (pat : Pattern) : ElabM TinyML.Binder :=
  match pat.kind with
  | .wildcard => .ok .none
  | .binder (some name) _ => .ok (.named name)
  | .binder none _ => .ok .none
  | _ => err pat.loc (.unsupportedPattern "expected a simple binder (variable or wildcard)")

private def patternToBinderTyped (env : ElabEnv) (pat : Pattern)
    : ElabM (TinyML.Binder × Option TinyML.Type_) :=
  match pat.kind with
  | .wildcard => .ok (.none, none)
  | .binder name ty => do
    let binder := match name with | some n => TinyML.Binder.named n | none => .none
    let ty' ← elaborateOptTyp env ty
    .ok (binder, ty')
  | _ => err pat.loc (.unsupportedPattern "expected a simple binder (variable or wildcard)")

-- ---------------------------------------------------------------------------
-- Match branch assembly

private def checkAllBranches (loc : Location) :
    List (Option TinyML.Expr) → Nat → Nat → ElabM (List TinyML.Expr)
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
    (acc : List (Option TinyML.Expr))
    (name : Constructor) (binder : Option TinyML.Binder) (body : TinyML.Expr)
    : ElabM (List (Option TinyML.Expr)) :=
  match alookup name env.ctors with
  | none => .error { loc, kind := .unknownConstructor name }
  | some (tag, arity', _) =>
    if arity' != arity then
      .error { loc, kind := .arityMismatch arity arity' }
    else
      let b := binder.getD .none
      let branch := TinyML.Expr.fix .none [(b, none)] none body
      .ok (listSet acc tag (some branch))

-- ---------------------------------------------------------------------------
-- Record helpers (outside mutual block — no recursion into Expr)

private def reorderElaborated (loc : Location) (elaborated : List (FieldName × TinyML.Expr))
    : List FieldName → ElabM (List TinyML.Expr)
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
    (arg : Option TinyML.Expr) : ElabM TinyML.Expr :=
  match alookup name env.ctors with
  | some (tag, arity, _) => .ok (.inj tag arity (arg.getD (.val .unit)))
  | none => err loc (.unknownConstructor name)

mutual
def ExprKind.elaborate (env : ElabEnv) (loc : Location) : ExprKind → ElabM TinyML.Expr
  | .const (.int n)  => .ok (.val (.int n))
  | .const (.bool b) => .ok (.val (.bool b))
  | .const .unit     => .ok (.val .unit)
  | .const (.char _) => err loc .unsupportedChar

  | .var name =>
    match name with
    | "ref" | "not" => err loc (.bareSpecialIdentifier name)
    | _ =>
      match alookup name env.ctors with
      | some (tag, arity, _) => .ok (.inj tag arity (.val .unit))
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
    match alookup name env.ctors with
    | some _ => err loc (.arityMismatch 1 args.length)
    | none => err loc (.unknownConstructor name)
  | .app ⟨fnLoc, fnKind⟩ args => do
    let fn' ← ExprKind.elaborate env fnLoc fnKind
    let args' ← ExprList.elaborate env args
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
    match alookup name env.fields with
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
      let args' ← PatternList.toBindersTyped env args
      let self := if isRec then name else .none
      let bound' ← ExprKind.elaborate env bl bk
      let body' ← ExprKind.elaborate env dl dk
      .ok (.letIn name (.fix self args' none bound') body')

  | .fun_ args retTy ⟨bl, bk⟩ => do
    let args' ← PatternList.toBindersTyped env args
    let retTy' ← elaborateOptTyp env retTy
    let body' ← ExprKind.elaborate env bl bk
    .ok (.fix .none args' retTy' body')

  | .match_ ⟨sl, sk⟩ arms => do
    let scrut' ← ExprKind.elaborate env sl sk
    let arms' ← MatchArmList.elaborate env arms
    match arms' with
    | [] => err loc .emptyMatch
    | (ctorName, _, _) :: _ =>
      match alookup ctorName env.ctors with
      | none => err loc (.unknownConstructor ctorName)
      | some (_, arity, _) => do
        let init : List (Option TinyML.Expr) := List.replicate arity none
        let filled ← arms'.foldlM
          (fun acc (name, binder, body) => insertBranch env loc arity acc name binder body)
          init
        let branches ← checkAllBranches loc filled arity 0
        .ok (.match_ scrut' branches)

  | .tuple es => do
    let es' ← ExprList.elaborate env es
    .ok (.tuple es')

  | .record flds =>
    match flds with
    | [] => err loc (.unsupportedFeature "empty record")
    | (name, _) :: _ =>
      match alookup name env.fields with
      | none => err loc (.unknownField name)
      | some (tyName, _) =>
        match alookup tyName env.records with
        | none => err loc (.unknownType tyName)
        | some fieldOrder => do
          let elaborated ← RecordFieldList.elaborate env flds
          let es' ← reorderElaborated loc elaborated fieldOrder
          .ok (.tuple es')

  | .recordUpdate _ _ => err loc .unsupportedRecordUpdate

  | .annot ⟨il, ik⟩ ty => do
    let _ ← Typ.elaborate env ty
    ExprKind.elaborate env il ik

def ExprList.elaborate (env : ElabEnv) : List Expr → ElabM (List TinyML.Expr)
  | [] => .ok []
  | ⟨l, k⟩ :: es => do
    let e' ← ExprKind.elaborate env l k
    let es' ← ExprList.elaborate env es
    .ok (e' :: es')

def RecordFieldList.elaborate (env : ElabEnv)
    : List (FieldName × Expr) → ElabM (List (FieldName × TinyML.Expr))
  | [] => .ok []
  | (name, ⟨l, k⟩) :: rest => do
    let e' ← ExprKind.elaborate env l k
    let rest' ← RecordFieldList.elaborate env rest
    .ok ((name, e') :: rest')

def MatchArmList.elaborate (env : ElabEnv)
    : List MatchArm → ElabM (List (Constructor × Option TinyML.Binder × TinyML.Expr))
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
    let rest ← MatchArmList.elaborate env arms
    .ok ((ctorName, binder, body') :: rest)

def PatternList.toBindersTyped (env : ElabEnv)
    : List Pattern → ElabM (List (TinyML.Binder × Option TinyML.Type_))
  | [] => .ok []
  | p :: ps => do
    let b ← patternToBinderTyped env p
    let bs ← PatternList.toBindersTyped env ps
    .ok (b :: bs)
end

def Expr.elaborate (env : ElabEnv) (e : Expr) : ElabM TinyML.Expr :=
  ExprKind.elaborate env e.loc e.kind

-- ---------------------------------------------------------------------------
-- Type declaration elaboration

private def elaborateCtorDefs (env : ElabEnv) (loc : Location)
    (ctorDefs : List (Constructor × Option Typ)) (tag : Nat) (arity : Nat)
    : ElabM (List TinyML.Type_ × List (Constructor × (Nat × Nat × Option TinyML.Type_))) :=
  match ctorDefs with
  | [] => .ok ([], [])
  | (ctorName, payloadTy) :: rest => do
    if acontains ctorName env.ctors then
      err loc (.duplicateConstructor ctorName)
    else do
    let payloadTy' ← match payloadTy with
      | some ty => Typ.elaborate env ty
      | none => .ok .unit
    let (restTypes, restCtors) ← elaborateCtorDefs env loc rest (tag + 1) arity
    .ok (payloadTy' :: restTypes,
         (ctorName, (tag, arity, some payloadTy')) :: restCtors)

private def elaborateVariant (env : ElabEnv) (loc : Location) (name : TypeConstructor)
    (ctorDefs : List (Constructor × Option Typ)) : ElabM ElabEnv := do
  if acontains name env.types then
    return ← err loc (.duplicateType name)
  let arity := ctorDefs.length
  let (payloadTypes, newCtors) ← elaborateCtorDefs env loc ctorDefs 0 arity
  let sumTy := TinyML.Type_.sum payloadTypes
  .ok { env with
    types := (name, sumTy) :: env.types
    ctors := newCtors ++ env.ctors }

private def elaborateFieldDefs (env : ElabEnv) (loc : Location) (tyName : TypeConstructor)
    (fieldDefs : List (FieldName × Typ)) (idx : Nat)
    : ElabM (List TinyML.Type_ × List (FieldName × (TypeConstructor × Nat))) :=
  match fieldDefs with
  | [] => .ok ([], [])
  | (fieldName, ty) :: rest => do
    if acontains fieldName env.fields then
      err loc (.duplicateField fieldName)
    else do
    let ty' ← Typ.elaborate env ty
    let (restTypes, restFields) ← elaborateFieldDefs env loc tyName rest (idx + 1)
    .ok (ty' :: restTypes, (fieldName, (tyName, idx)) :: restFields)

private def elaborateRecordDecl (env : ElabEnv) (loc : Location) (name : TypeConstructor)
    (fieldDefs : List (FieldName × Typ)) : ElabM ElabEnv := do
  if acontains name env.types then
    return ← err loc (.duplicateType name)
  let (fieldTypes, newFields) ← elaborateFieldDefs env loc name fieldDefs 0
  let tupleTy := TinyML.Type_.tuple fieldTypes
  let fieldNames := fieldDefs.map Prod.fst
  .ok { env with
    types := (name, tupleTy) :: env.types
    records := (name, fieldNames) :: env.records
    fields := newFields ++ env.fields }

def TypeDecl.elaborate (env : ElabEnv) (loc : Location) (decl : TypeDecl)
    : ElabM ElabEnv := do
  if !decl.params.isEmpty then
    return ← err loc (.polymorphicTypeDecl decl.name)
  match decl.body with
  | .variant ctors => elaborateVariant env loc decl.name ctors
  | .record fields => elaborateRecordDecl env loc decl.name fields

-- ---------------------------------------------------------------------------
-- Value declaration elaboration

def ValDecl.elaborate (env : ElabEnv) (loc : Location)
    (isRec : Bool) (binders : List Pattern) (retTy : Option Typ) (body : Expr)
    : ElabM (TinyML.Decl TinyML.Expr) := do
  match binders with
  | [] => err loc (.unsupportedFeature "declaration with no binders")
  | [pat] =>
    let name ← patternToBinder pat
    let body' ← Expr.elaborate env body
    if isRec then
      err loc (.unsupportedFeature "let rec requires function arguments")
    else
      .ok { name, body := body', spec := none }
  | pat :: args =>
    let name ← patternToBinder pat
    let self := if isRec then name else .none
    let args' ← PatternList.toBindersTyped env args
    let retTy' ← elaborateOptTyp env retTy
    let body' ← Expr.elaborate env body
    .ok { name, body := .fix self args' retTy' body', spec := none }

-- ---------------------------------------------------------------------------
-- Program elaboration

def Decl.elaborate (env : ElabEnv) (decl : Decl)
    : ElabM (ElabEnv × Option (TinyML.Decl TinyML.Expr)) := do
  match decl.kind with
  | .type_ tdecl => do
    let env' ← TypeDecl.elaborate env decl.loc tdecl
    .ok (env', none)
  | .val_ isRec binders retTy body => do
    let d ← ValDecl.elaborate env decl.loc isRec binders retTy body
    .ok (env, some d)

private def elaborateDecls (env : ElabEnv) :
    List Decl → ElabM (List (TinyML.Decl TinyML.Expr))
  | [] => .ok []
  | d :: ds => do
    let (env', optDecl) ← Decl.elaborate env d
    let rest ← elaborateDecls env' ds
    match optDecl with
    | some decl => .ok (decl :: rest)
    | none => .ok rest

def Program.elaborate (prog : Frontend.Program) : ElabM TinyML.Program :=
  elaborateDecls {} prog

end Frontend
