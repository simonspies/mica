import Mica.TinyML.Lexer
import Mica.TinyML.Expr

namespace TinyML

/-- Maps constructor name to (tag, total number of constructors). -/
abbrev CtorMap := List (String × Nat × Nat)

private def ctorLookup : CtorMap → String → Option (Nat × Nat)
  | [], _ => none
  | (n, v) :: rest, name => if n == name then some v else ctorLookup rest name

abbrev TypeAliasMap := List (String × Type_)

private def typeAliasLookup : TypeAliasMap → String → Option Type_
  | [], _ => none
  | (n, t) :: rest, name => if n == name then some t else typeAliasLookup rest name

structure ParserState where
  tokens : Array Token
  pos : Nat
  ctors : CtorMap := []
  typeAliases : TypeAliasMap := []

abbrev Parser (α : Type) := ParserState → Except String (α × ParserState)

private def peek (st : ParserState) : Token :=
  st.tokens.getD st.pos .eof

private def advance (st : ParserState) : ParserState :=
  { st with pos := st.pos + 1 }

private def expect (tok : Token) (st : ParserState) : Except String ParserState :=
  if peek st == tok then .ok (advance st)
  else .error s!"expected {tok}, got {peek st}"

private def expectIdent (st : ParserState) : Except String (String × ParserState) :=
  match peek st with
  | .ident name => .ok (name, advance st)
  | t => .error s!"expected identifier, got {t}"

private def parseBinder (st : ParserState) : Except String (Binder × ParserState) :=
  match peek st with
  | .ident name => .ok (.named name, advance st)
  | .underscore => .ok (.none, advance st)
  | t => .error s!"expected binder, got {t}"

private partial def parseLAssocLoop
    (ops : List (Token × BinOp)) (sub : Parser Expr) (e : Expr) : Parser Expr := fun st =>
  match ops.find? (·.1 == peek st) with
  | some (_, op) => do
    let (rhs, st) ← sub (advance st)
    parseLAssocLoop ops sub (.binop op e rhs) st
  | none => .ok (e, st)

private partial def parseLAssoc (ops : List (Token × BinOp)) (sub : Parser Expr) : Parser Expr :=
  fun st => do
    let (e, st) ← sub st
    parseLAssocLoop ops sub e st

/-- Parse a type.

   Extensibility: to add new type constructors, either add atoms to `parseTypeAtom`
   (for nullary constructors) or new postfix rules to `parseTypeApp`. -/
private partial def parseType : Parser Type_ := fun st =>
  parseTypeArrow st
where
  parseTypeArrow : Parser Type_ := fun st => do
    let (t, st) ← parseTypeProd st
    match peek st with
    | .arrow => do
      let (t2, st) ← parseTypeArrow (advance st)
      .ok (.arrow t t2, st)
    | _ => .ok (t, st)

  parseTypeProd : Parser Type_ := fun st => do
    let (t, st) ← parseTypeApp st
    match peek st with
    | .star => do
      let (rest, st) ← parseTypeProdRest (advance st)
      .ok (.tuple (t :: rest), st)
    | _ => .ok (t, st)

  parseTypeProdRest : Parser (List Type_) := fun st => do
    let (t, st) ← parseTypeApp st
    match peek st with
    | .star => do
      let (rest, st) ← parseTypeProdRest (advance st)
      .ok (t :: rest, st)
    | _ => .ok ([t], st)

  parseTypeApp : Parser Type_ := fun st => do
    let (t, st) ← parseTypeAtom st
    match peek st with
    | .kw_ref => .ok (.ref t, advance st)
    | _ => .ok (t, st)

  parseTypeAtom : Parser Type_ := fun st =>
    match peek st with
    | .ident "int"  => .ok (.int,  advance st)
    | .ident "bool" => .ok (.bool, advance st)
    | .ident "unit" => .ok (.unit, advance st)
    | .lparen => do
      let st' := advance st
      -- `()` is unit
      if peek st' == .rparen then
        .ok (.unit, advance st')
      else do
        let (t1, st') ← parseType st'
        match peek st' with
        | .rparen => .ok (t1, advance st')
        | .comma => do
          -- `(T1, T2) Either.t`
          let (t2, st') ← parseType (advance st')
          let st' ← expect .rparen st'
          let st' ← expect (.ident "Either") st'
          let st' ← expect .dot st'
          let st' ← expect (.ident "t") st'
          .ok (.sum [t1, t2], st')
        | t => .error s!"expected ')' or ',' in type, got {t}"
    | .ident name =>
      match typeAliasLookup st.typeAliases name with
      | .some t => .ok (t, advance st)
      | .none => .error s!"expected type, got {repr (Token.ident name)}"
    | t => .error s!"expected type, got {t}"

/-- Parse an expression. -/
partial def parseExpr : Parser Expr := fun st =>
  match peek st with
  | .kw_let => parseLet st
  | .kw_fun => parseFun st
  | .kw_if => parseIf st
  | .kw_match => parseMatch st
  | _ => parseSemi st

where
  parseLet : Parser Expr := fun st => do
    let st ← expect .kw_let st
    let isRec := peek st == .kw_rec
    let st := if isRec then advance st else st
    let (binder, st) ← parseBinder st
    -- collect argument binders for `let f x y = e`
    let (args, st) ← parseLetArgs st
    -- optional return type annotation `: T` before `=`
    let (retTy, st) ← parseOptRetTy st
    let st ← expect .eq st
    let (bound, st) ← parseExpr st
    let st ← expect .kw_in st
    let (body, st) ← parseExpr st
    let self := match binder with
      | .named name => if isRec then Binder.named name else Binder.none
      | .none => Binder.none
    -- wrap bound in fix for each argument (right to left), retTy on innermost
    if args.isEmpty && isRec then
      .error "let rec without arguments is not supported"
    else
      let bound := wrapFix self args retTy bound
      .ok (.letIn binder bound body, st)

  parseLetArgs (st : ParserState) : Except String (List (Binder × Option Type_) × ParserState) :=
    match peek st with
    | .ident _ | .underscore => do
      let (b, st) ← parseBinder st
      let (bs, st) ← parseLetArgs st
      .ok ((b, none) :: bs, st)
    | .lparen => do
      let st' := advance st
      match peek st' with
      | .ident _ | .underscore => do
        let (b, st') ← parseBinder st'
        match peek st' with
        | .colon => do
          let (ty, st') ← parseType (advance st')
          let st' ← expect .rparen st'
          let (bs, st') ← parseLetArgs st'
          .ok ((b, some ty) :: bs, st')
        | .rparen => do
          let (bs, st') ← parseLetArgs (advance st')
          .ok ((b, none) :: bs, st')
        | t => .error s!"expected ':' or ')' in annotated binder, got {t}"
      | _ => .ok ([], st)
    | _ => .ok ([], st)

  parseFun : Parser Expr := fun st => do
    let st ← expect .kw_fun st
    let (args, st) ← parseFunArgs st
    -- optional return type annotation `: T` before `->`
    let (retTy, st) ← parseOptRetTy st
    let st ← expect .arrow st
    let (body, st) ← parseExpr st
    let e := wrapFix .none args retTy body
    .ok (e, st)

  parseFunArgs (st : ParserState) : Except String (List (Binder × Option Type_) × ParserState) :=
    match peek st with
    | .ident _ | .underscore => do
      let (b, st) ← parseBinder st
      let (bs, st) ← parseFunArgs st
      .ok ((b, none) :: bs, st)
    | .lparen => do
      let st' := advance st
      match peek st' with
      | .ident _ | .underscore => do
        let (b, st') ← parseBinder st'
        match peek st' with
        | .colon => do
          let (ty, st') ← parseType (advance st')
          let st' ← expect .rparen st'
          let (bs, st') ← parseFunArgs st'
          .ok ((b, some ty) :: bs, st')
        | .rparen => do
          let (bs, st') ← parseFunArgs (advance st')
          .ok ((b, none) :: bs, st')
        | t => .error s!"expected ':' or ')' in annotated binder, got {t}"
      | _ => .ok ([], st)
    | _ => .ok ([], st)

  -- Optional `: T` return type annotation (consumed only if `:` follows).
  parseOptRetTy (st : ParserState) : Except String (Option Type_ × ParserState) :=
    match peek st with
    | .colon => do
      let (ty, st) ← parseType (advance st)
      .ok (some ty, st)
    | _ => .ok (none, st)

  -- Produce a single fix node with the full args list.
  wrapFix (self : Binder) (args : List (Binder × Option Type_)) (retTy : Option Type_)
      (body : Expr) : Expr :=
    match args with
    | [] => body
    | _ => .fix self args retTy body

  parseIf : Parser Expr := fun st => do
    let st ← expect .kw_if st
    let (cond, st) ← parseExpr st
    let st ← expect .kw_then st
    let (thn, st) ← parseExpr st
    let st ← expect .kw_else st
    let (els, st) ← parseExpr st
    .ok (.ifThenElse cond thn els, st)

  -- `match e with | C1 x -> e1 | C2 y -> e2 | ...`
  -- Desugars each arm into a lambda at the constructor's tag position.
  parseMatch : Parser Expr := fun st => do
    let st ← expect .kw_match st
    let (scrut, st) ← parseExpr st
    let st ← expect .kw_with st
    let (arms, st) ← parseMatchArms st
    -- arms is a list of (tag, arity, binder, body)
    match arms with
    | [] => .error "match with no arms"
    | (_, arity, _, _) :: _ =>
      -- Build branches array indexed by tag, fill with lambdas
      let branches := buildBranches arms arity
      match branches with
      | .error msg => .error msg
      | .ok bs => .ok (.match_ scrut bs, st)

  buildBranches (arms : List (Nat × Nat × Binder × Expr)) (arity : Nat)
      : Except String (List Expr) :=
    -- Build a list of length `arity` with branches at their tag positions
    let init : List (Option Expr) := List.replicate arity .none
    let filled := arms.foldl (fun acc (tag, _, binder, body) =>
      acc.set tag (.some (.fix .none [(binder, .none)] .none body))) init
    let rec collect : List (Option Expr) → Except String (List Expr)
      | [] => .ok []
      | .some e :: rest => do let rs ← collect rest; .ok (e :: rs)
      | .none :: _ => .error "incomplete match: missing branch for some constructor"
    collect filled

  -- Parse `| CtorName binder -> expr` arms
  parseMatchArms (st : ParserState) :
      Except String (List (Nat × Nat × Binder × Expr) × ParserState) :=
    match peek st with
    | .pipe => do
      let st := advance st
      -- Expect a constructor name
      let (ctorName, st) ← expectIdent st
      match ctorLookup st.ctors ctorName with
      | .none => .error s!"unknown constructor '{ctorName}'"
      | .some (tag, arity) =>
        -- Optional binder for the payload
        let (binder, st) ← match peek st with
          | .ident _ | .underscore | .lparen => parseBinder st
          | _ => .ok (Binder.none, st)  -- nullary constructor
        let st ← expect .arrow st
        let (body, st) ← parseExpr st
        let (rest, st) ← parseMatchArms st
        .ok ((tag, arity, binder, body) :: rest, st)
    | _ => .ok ([], st)

  -- `;` sequences: `e1; e2` → `let _ = e1 in e2`
  parseSemi : Parser Expr := fun st => do
    let (lhs, st) ← parsePipeGt st
    parseSemiRest lhs st

  parseSemiRest (lhs : Expr) : Parser Expr := fun st =>
    match peek st with
    | .semi => do
      let (rhs, st) ← parseSemi (advance st)  -- right-assoc: e1; e2; e3 = e1; (e2; e3)
      .ok (.letIn .none lhs rhs, st)
    | _ => .ok (lhs, st)

  -- `|>` reverse application (left-assoc): `x |> f` → `f x`
  parsePipeGt : Parser Expr := fun st => do
    let (lhs, st) ← parseAtAt st
    parsePipeGtRest lhs st

  parsePipeGtRest (lhs : Expr) : Parser Expr := fun st =>
    match peek st with
    | .pipe_gt => do
      let (rhs, st) ← parseAtAt (advance st)
      parsePipeGtRest (.app rhs [lhs]) st
    | _ => .ok (lhs, st)

  -- `@@` application (right-assoc): `f @@ x` → `f x`
  -- The RHS uses full parseExpr so that `f @@ fun x -> e` works without parens.
  parseAtAt : Parser Expr := fun st => do
    let (lhs, st) ← parseStore st
    match peek st with
    | .atat => do
      let (rhs, st) ← parseExpr (advance st)
      .ok (.app lhs [rhs], st)
    | _ => .ok (lhs, st)

  -- `:=` store (right-assoc)
  parseStore : Parser Expr := fun st => do
    let (lhs, st) ← parseOr st
    match peek st with
    | .colonEq => do
      let (rhs, st) ← parseStore (advance st)
      .ok (.store lhs rhs, st)
    | _ => .ok (lhs, st)

  parseOr  := parseLAssoc [(.pipepipe, .or)]  parseAnd
  parseAnd := parseLAssoc [(.ampamp,   .and)] parseCmp

  parseCmp := parseLAssoc
    [(.eq, .eq), (.lt, .lt), (.le, .le), (.gt, .gt), (.ge, .ge)] parseAdd

  parseAdd := parseLAssoc [(.plus, .add), (.minus, .sub)] parseMul
  parseMul := parseLAssoc [(.star, .mul), (.slash, .div), (.kw_mod, .mod)] parseApp

  parseApp : Parser Expr := fun st => do
    let (e, st) ← parseUnary st
    parseAppRest e st

  parseAppRest (fn : Expr) : Parser Expr := fun st => do
    let (args, st) ← collectArgs st
    if args.isEmpty then .ok (fn, st)
    else .ok (.app fn args, st)

  collectArgs : Parser (List Expr) := fun st =>
    match peek st with
    | .intLit _ | .ident _ | .lparen | .kw_true | .kw_false
    | .bang | .kw_not | .kw_ref => do
      let (arg, st) ← parseUnary st
      let (rest, st) ← collectArgs st
      .ok (arg :: rest, st)
    | _ => .ok ([], st)

  parseUnary : Parser Expr := fun st =>
    let kwUnary : List (Token × UnOp) :=
      [(Token.kw_not, UnOp.not)]
    match kwUnary.find? (·.1 == peek st) with
    | some (_, op) => do
      let (e, st) ← parseUnary (advance st)
      .ok (.unop op e, st)
    | none =>
      match peek st with
      | .minus => do
        let (e, st) ← parseUnary (advance st)
        .ok (.unop .neg e, st)
      | .kw_ref => do
        let (e, st) ← parseUnary (advance st)
        .ok (.ref e, st)
      | .kw_assert => do
        let (e, st) ← parseUnary (advance st)
        .ok (.assert e, st)
      | .bang => do
        let (e, st) ← parseUnary (advance st)
        .ok (.deref e, st)
      | _ => parseAtom st

  parseAtom : Parser Expr := fun st => do
    let (e, st) ← parseAtomBase st
    parsePostfix e st

  parseAtomBase : Parser Expr := fun st =>
    match peek st with
    | .intLit n  => .ok (.val (.int n), advance st)
    | .kw_true   => .ok (.val (.bool true), advance st)
    | .kw_false  => .ok (.val (.bool false), advance st)
    | .ident "inj" =>
      -- `inj <tag:int> <arity:int> <payload>` — explicit injection syntax (used in specs)
      let st := advance st
      match peek st with
      | .intLit tag =>
        let st := advance st
        match peek st with
        | .intLit arity => do
          let st := advance st
          let (payload, st) ← parseAtom st
          .ok (.inj tag.toNat arity.toNat payload, st)
        | t => .error s!"expected arity after 'inj {tag}', got {t}"
      | t => .error s!"expected tag after 'inj', got {t}"
    | .ident name =>
      match ctorLookup st.ctors name with
      | .some (tag, arity) =>
        let st := advance st
        -- Try to parse an argument for the constructor
        match peek st with
        | .intLit _ | .ident _ | .lparen | .kw_true | .kw_false => do
          let (arg, st) ← parseAtom st
          .ok (.inj tag arity arg, st)
        | _ =>
          -- Nullary constructor: payload is unit
          .ok (.inj tag arity (.val .unit), st)
      | .none => .ok (.var name, advance st)
    | .lparen => do
      let st' := advance st
      -- `()` is unit
      if peek st' == .rparen then
        .ok (.val .unit, advance st')
      else do
        let (e, st') ← parseExpr st'
        if peek st' == .comma then do
          let (rest, st') ← parseTupleRest st'
          let st' ← expect .rparen st'
          .ok (.tuple (e :: rest), st')
        else do
          let st' ← expect .rparen st'
          .ok (e, st')
    | t => .error s!"unexpected token: {t}"

  -- Parse `, e2, e3, ...` after the first element of a tuple
  parseTupleRest : Parser (List Expr) := fun st =>
    match peek st with
    | .comma => do
      let (e, st) ← parseExpr (advance st)
      if peek st == .comma then do
        let (rest, st) ← parseTupleRest st
        .ok (e :: rest, st)
      else
        .ok ([e], st)
    | _ => .ok ([], st)

  -- Parse postfix `.n` projection
  parsePostfix (e : Expr) : Parser Expr := fun st =>
    match peek st with
    | .dot =>
      match peek (advance st) with
      | .intLit n =>
        if n ≥ 0 then
          parsePostfix (.unop (.proj n.toNat) e) (advance (advance st))
        else
          .error s!"projection index must be non-negative, got {n}"
      | _ => .ok (e, st)  -- dot not followed by int, leave it
    | _ => .ok (e, st)

/-- Parse a top-level declaration. -/
partial def parseDecl : Parser (Decl Expr) := fun st => do
  -- Optional `[@spec e]` prefix attribute
  let (preSpec, st) ← parsePreSpec st
  let st ← expect .kw_let st
  let isRec := peek st == .kw_rec
  let st := if isRec then advance st else st
  let (b, st) ← parseBinder st
  let (args, st) ← parseLetArgs st
  let (retTy, st) ← parseOptRetTy st
  let st ← expect .eq st
  let (body, st) ← parseExpr st
  let self := match b with
    | .named name => if isRec then Binder.named name else Binder.none
    | .none => Binder.none
  if args.isEmpty && isRec then
    .error "let rec without arguments is not supported"
  else
  let body := wrapFix self args retTy body
  -- Optional `[@@spec e]` postfix attribute (takes priority over prefix)
  let (postSpec, st) ← parsePostSpec st
  let spec := postSpec.orElse (fun _ => preSpec)
  .ok ({ name := b, body := body, spec := spec }, st)
where
  parseLetArgs (st : ParserState) : Except String (List (Binder × Option Type_) × ParserState) :=
    match peek st with
    | .ident _ | .underscore => do
      let (b, st) ← parseBinder st
      let (bs, st) ← parseLetArgs st
      .ok ((b, none) :: bs, st)
    | .lparen => do
      let st' := advance st
      match peek st' with
      | .ident _ | .underscore => do
        let (b, st') ← parseBinder st'
        match peek st' with
        | .colon => do
          let (ty, st') ← parseType (advance st')
          let st' ← expect .rparen st'
          let (bs, st') ← parseLetArgs st'
          .ok ((b, some ty) :: bs, st')
        | .rparen => do
          let (bs, st') ← parseLetArgs (advance st')
          .ok ((b, none) :: bs, st')
        | t => .error s!"expected ':' or ')' in annotated binder, got {t}"
      | _ => .ok ([], st)
    | _ => .ok ([], st)

  parseOptRetTy (st : ParserState) : Except String (Option Type_ × ParserState) :=
    match peek st with
    | .colon => do
      let (ty, st) ← parseType (advance st)
      .ok (some ty, st)
    | _ => .ok (none, st)

  wrapFix (self : Binder) (args : List (Binder × Option Type_)) (retTy : Option Type_)
      (body : Expr) : Expr :=
    match args with
    | [] => body
    | _ => .fix self args retTy body

  -- `[@spec e]` before the `let`
  parsePreSpec (st : ParserState) : Except String (Option Expr × ParserState) := do
    if peek st == .lbracket && peek (advance st) == .at then
      let st ← expect .lbracket st
      let st ← expect .at st
      let st ← expect .kw_spec st
      let (e, st) ← parseExpr st
      let st ← expect .rbracket st
      .ok (.some e, st)
    else
      .ok (.none, st)

  -- `[@@spec e]` after the body
  parsePostSpec (st : ParserState) : Except String (Option Expr × ParserState) := do
    if peek st == .lbracket && peek (advance st) == .atat then
      let st ← expect .lbracket st
      let st ← expect .atat st
      let st ← expect .kw_spec st
      let (e, st) ← parseExpr st
      let st ← expect .rbracket st
      .ok (.some e, st)
    else
      .ok (.none, st)

/-- Parse `type foo = A | B of int | C of int * int`.
    Returns the updated parser state with constructors registered. -/
partial def parseTypeDecl (st : ParserState) : Except String ParserState := do
  let st ← expect .kw_type st
  let (typeName, st) ← expectIdent st
  let st ← expect .eq st
  -- Parse constructors: `A | B of int | C of int * int`
  let (ctorDefs, st) ← parseCtors st
  -- Assign tags 0..n-1, arity = total number of constructors
  let arity := ctorDefs.length
  let ctors := ctorDefs.foldl (fun (acc, i) (name, _) => ((name, i, arity) :: acc, i + 1))
    (st.ctors, 0) |>.1
  -- Register the type alias using parsed payload types
  let sumTy := Type_.sum (ctorDefs.map (fun (_, ty) => ty.getD .unit))
  .ok { st with ctors := ctors, typeAliases := (typeName, sumTy) :: st.typeAliases }
where
  parseCtors (st : ParserState) : Except String (List (String × Option Type_) × ParserState) := do
    -- Optional leading pipe
    let st := if peek st == .pipe then advance st else st
    let (name, st) ← expectIdent st
    let (payloadTy, st) ← parseOfType st
    match peek st with
    | .pipe => do
      let (rest, st) ← parseCtors (advance st)
      .ok ((name, payloadTy) :: rest, st)
    | _ => .ok ([(name, payloadTy)], st)
  parseOfType (st : ParserState) : Except String (Option Type_ × ParserState) := do
    if peek st == .kw_of then
      let st' := advance st  -- skip `of`
      let (ty, st'') ← parseType st'
      .ok (.some ty, st'')
    else
      .ok (.none, st)

/-- Parse a program: a sequence of declarations separated by `;;`. -/
partial def parseProgram : Parser Program := fun st => do
  match peek st with
  | .kw_type => do
    let st ← parseTypeDecl st
    match peek st with
    | .semisemi => parseProgram (advance st)
    | _ => parseProgram st
  | _ =>
    let startsDecl := peek st == .kw_let ||
      (peek st == .lbracket && peek (advance st) == .at)
    match startsDecl with
    | true => do
      let (decl, st) ← parseDecl st
      match peek st with
      | .semisemi =>
        let (rest, st) ← parseProgram (advance st)
        .ok (decl :: rest, st)
      | _ => .ok ([decl], st)
    | false => .ok ([], st)

def parse (input : String) : Except String Expr := do
  let tokens ← tokenize input
  let st : ParserState := { tokens := tokens.toArray, pos := 0 }
  let (expr, st) ← parseExpr st
  if peek st != .eof then
    .error s!"unexpected token after expression: {peek st}"
  else
    .ok expr

def parseFile (input : String) : Except String Program := do
  let tokens ← tokenize input
  let st : ParserState := { tokens := tokens.toArray, pos := 0 }
  let (prog, st) ← parseProgram st
  if peek st != .eof then
    .error s!"unexpected token after program: {peek st}"
  else
    .ok prog

end TinyML
