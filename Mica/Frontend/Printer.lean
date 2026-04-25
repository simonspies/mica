-- SUMMARY: Pretty-printing of frontend syntax back into OCaml-like concrete syntax.
import Mica.Frontend.AST

namespace Frontend

-- ---------------------------------------------------------------------------
-- Helpers

private def joinWith (sep : String) (parts : List String) : String :=
  sep.intercalate parts

private def parens (s : String) : String := "(" ++ s ++ ")"

private def parenIf (cond : Bool) (s : String) : String :=
  if cond then parens s else s

-- ---------------------------------------------------------------------------
-- Const printing

partial def Const.print : Const → String
  | .int n   => toString n
  | .bool b  => if b then "true" else "false"
  | .unit    => "()"
  | .char c  =>
    let s := match c with
      | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
      | '\'' => "\\'" | '\\' => "\\\\"
      | c    => c.toString
    s!"'{s}'"

-- ---------------------------------------------------------------------------
-- Operators

partial def UnOp.print : UnOp → String
  | .neg    => "-"
  | .deref  => "!"
  | .assert => "assert"
  | .proj n     => s!".{n}"
  | .field name => s!".{name}"

-- Does this prefix unop need a space before its argument?
private def UnOp.needsSpace : UnOp → Bool
  | .neg | .deref => false
  | _ => true

partial def BinOp.print : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "mod"
  | .eq => "=" | .neq => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"
  | .semi => ";" | .pipeRight => "|>" | .atAt => "@@" | .assign => ":="

partial def BinOp.prec : BinOp → Nat
  | .semi => 1 | .assign => 2 | .or => 3 | .and => 4
  | .pipeRight => 5 | .atAt => 6
  | .eq | .neq | .lt | .le | .gt | .ge => 7
  | .add | .sub => 8 | .mul | .div | .mod => 9

partial def BinOp.rightAssoc : BinOp → Bool
  | .semi | .assign | .or | .and | .atAt => true
  | _ => false

-- ---------------------------------------------------------------------------
-- Type printing

partial def Typ.print (t : Typ) : String :=
  match t.kind with
  | .var name => s!"'{name}"
  | .con name [] => name
  | .con name [arg] => s!"{printAppArg arg} {name}"
  | .con name args => s!"({joinWith ", " (args.map Typ.print)}) {name}"
  | .arrow dom cod =>
    let domStr := match dom.kind with
      | .arrow _ _ => parens (Typ.print dom)
      | _ => Typ.print dom
    s!"{domStr} -> {Typ.print cod}"
  | .tuple components => joinWith " * " (components.map Typ.print)
where
  -- Type constructor arguments that are themselves applications need parens
  printAppArg (t : Typ) : String :=
    match t.kind with
    | .arrow _ _ => parens (Typ.print t)
    | .tuple (_ :: _ :: _) => parens (Typ.print t)
    | _ => Typ.print t

-- ---------------------------------------------------------------------------
-- Pattern printing

partial def Pattern.isAtom (p : Pattern) : Bool :=
  match p.kind with
  | .ctor _ (some _) => false
  | _ => true

partial def Pattern.print (p : Pattern) : String :=
  match p.kind with
  | .wildcard => "_"
  | .binder (some name) none => name
  | .binder (some name) (some ty) => s!"({name} : {Typ.print ty})"
  | .binder none none => "_"
  | .binder none (some ty) => s!"(_ : {Typ.print ty})"
  | .const c => Const.print c
  | .ctor name none => name
  | .ctor name (some pat) => s!"{name} {parenIf (!Pattern.isAtom pat) (Pattern.print pat)}"
  | .tuple pats => parens (joinWith ", " (pats.map Pattern.print))

-- ---------------------------------------------------------------------------
-- Expression printing

partial def Expr.isAtom (e : Expr) : Bool :=
  match e.kind with
  | .const _ | .var _ | .ctor _ | .tuple _ | .record _ | .annot _ _ => true
  | _ => false

partial def Expr.isKeywordExpr (e : Expr) : Bool :=
  match e.kind with
  | .letIn _ _ _ _ | .fun_ _ _ _ | .ite _ _ _ | .match_ _ _ => true
  | _ => false

partial def Expr.printPrec (e : Expr) (outerPrec : Nat) : String :=
  match e.kind with
  | .const c => Const.print c
  | .var name => name
  | .ctor name => name
  | .annot inner ty => s!"({Expr.printPrec inner 0} : {Typ.print ty})"
  | .tuple es => parens (joinWith ", " (es.map fun x => Expr.printPrec x 0))
  | .record fields => "{ " ++ fmtFields fields ++ " }"
  | .recordUpdate base fields =>
    "{ " ++ Expr.printPrec base 0 ++ " with " ++ fmtFields fields ++ " }"
  | .unop op inner => printUnop op inner
  | .binop op lhs rhs => printBinop op lhs rhs outerPrec
  | .app fn args =>
    joinWith " " (fmtArg fn :: args.map fmtArg)
  | .ite cond thn els =>
    "if " ++ Expr.printPrec cond 0 ++ " then " ++ Expr.printPrec thn 0 ++
    " else " ++ Expr.printPrec els 0
  | .letIn isRec binders bound body =>
    let recStr := if isRec then "rec " else ""
    "let " ++ recStr ++ joinWith " " (binders.map Pattern.print) ++
    " = " ++ Expr.printPrec bound 0 ++ " in\n" ++ Expr.printPrec body 0
  | .fun_ args retTy body =>
    let retStr := match retTy with | none => "" | some ty => " : " ++ Typ.print ty
    "fun " ++ joinWith " " (args.map Pattern.print) ++ retStr ++
    " -> " ++ Expr.printPrec body 0
  | .match_ scrutinee arms =>
    let armsStr := arms.map fun arm =>
      "| " ++ Pattern.print arm.pat ++ " -> " ++ Expr.printPrec arm.body 0
    "match " ++ Expr.printPrec scrutinee 0 ++ " with\n" ++ joinWith "\n" armsStr
where
  fmtArg (e : Expr) : String :=
    parenIf (!Expr.isAtom e) (Expr.printPrec e 0)
  fmtBase (e : Expr) : String :=
    parenIf (!Expr.isAtom e) (Expr.printPrec e 0)
  fmtFields (fields : List (FieldName × Expr)) : String :=
    joinWith "; " (fields.map fun (f, v) => f ++ " = " ++ Expr.printPrec v 0)
  printUnop (op : UnOp) (inner : Expr) : String :=
    match op with
    | .proj n => fmtBase inner ++ s!".{n}"
    | .field name => fmtBase inner ++ "." ++ name
    | _ =>
      let space := if UnOp.needsSpace op then " " else ""
      UnOp.print op ++ space ++ fmtArg inner

  printBinop (op : BinOp) (lhs rhs : Expr) (outerPrec : Nat) : String :=
    let p := BinOp.prec op
    -- Special case: semicolons print with newline
    if op == .semi then
      let result := Expr.printPrec lhs (p + 1) ++ ";\n" ++ Expr.printPrec rhs 0
      parenIf (outerPrec > p) result
    else
      let lhsNeedsParens : Bool := match lhs.kind with
        | .binop lop _ _ => BinOp.prec lop < p
        | _ => Expr.isKeywordExpr lhs
      let rhsNeedsParens : Bool := match rhs.kind with
        | .binop rop _ _ =>
          if BinOp.rightAssoc op then BinOp.prec rop < p
          else BinOp.prec rop <= p
        -- For @@, don't parenthesize keyword exprs on the RHS
        | _ => if op == .atAt then false else Expr.isKeywordExpr rhs
      let lhsStr := parenIf lhsNeedsParens (Expr.printPrec lhs p)
      let rhsStr := parenIf rhsNeedsParens (Expr.printPrec rhs p)
      parenIf (outerPrec > p) (lhsStr ++ " " ++ BinOp.print op ++ " " ++ rhsStr)

partial def Expr.print (e : Expr) : String := Expr.printPrec e 0

-- ---------------------------------------------------------------------------
-- Declaration printing

partial def Decl.print (d : Decl) : String :=
  let attrsStr := d.attrs.map fun attr =>
    "\n[@@" ++ attr.name ++ " " ++ Expr.print attr.payload ++ "]"
  let attrsSuffix := joinWith "" attrsStr
  match d.kind with
  | .type_ td => printTypeDecl td ++ attrsSuffix
  | .val_ isRec binders retTy body =>
    let recStr := if isRec then "rec " else ""
    let retStr := match retTy with | none => "" | some ty => " : " ++ Typ.print ty
    "let " ++ recStr ++ joinWith " " (binders.map Pattern.print) ++
    retStr ++ " = " ++ Expr.print body ++ attrsSuffix
where
  printTypeDecl (td : TypeDecl) : String :=
    let paramsStr := match td.params with
      | [] => ""
      | [p] => s!"'{p} "
      | ps => parens (joinWith ", " (ps.map fun p => s!"'{p}")) ++ " "
    let bodyStr := match td.body with
      | .variant ctors =>
        joinWith "\n" (ctors.map fun (name, payload) =>
          match payload with
          | none => "| " ++ name
          | some ty => "| " ++ name ++ " of " ++ Typ.print ty)
      | .record fields =>
        "{ " ++ joinWith "; " (fields.map fun (name, ty) => name ++ " : " ++ Typ.print ty) ++ " }"
    "type " ++ paramsStr ++ td.name ++ " = " ++ bodyStr

-- ---------------------------------------------------------------------------
-- Program printing

partial def Program.print (prog : Program) : String :=
  joinWith "\n;;\n" (prog.map Decl.print)

end Frontend
