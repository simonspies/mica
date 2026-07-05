-- SUMMARY: Pretty-printing of frontend syntax back into OCaml-like concrete syntax.
import Mica.Frontend.AST

/-!
This file renders frontend AST nodes back to OCaml-like concrete syntax with
precedence-aware formatting for expressions, types, and declarations. It is
used for user-facing output and debugging of frontend transformations.
-/

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

private def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

private def byteEsc (b : UInt8) : String :=
  let n := b.toNat
  if n == 10 then "\\n"
  else if n == 9 then "\\t"
  else if n == 13 then "\\r"
  else if n == 34 then "\\\""
  else if n == 92 then "\\\\"
  else if 32 ≤ n && n < 127 then String.singleton (Char.ofNat n)
  else "\\x" ++ String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

partial def Const.print : Const → String
  | .int n   => toString n
  | .float f => toString f
  | .bool b  => if b then "true" else "false"
  | .string s => "\"" ++ joinWith "" (s.map byteEsc) ++ "\""
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
  | .fadd => "+." | .fsub => "-." | .fmul => "*." | .fdiv => "/."
  | .eq => "=" | .neq => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"
  | .semi => ";" | .pipeRight => "|>" | .atAt => "@@" | .assign => ":="
  | .concat => "^"

private partial def BinOp.prec : BinOp → Nat
  | .semi => 1 | .assign => 2 | .or => 3 | .and => 4
  | .pipeRight => 5 | .atAt => 6
  | .eq | .neq | .lt | .le | .gt | .ge => 7
  | .concat => 8 | .add | .sub | .fadd | .fsub => 9
  | .mul | .div | .mod | .fmul | .fdiv => 10

private partial def BinOp.rightAssoc : BinOp → Bool
  | .semi | .assign | .or | .and | .atAt | .concat => true
  | _ => false

-- ---------------------------------------------------------------------------
-- Type printing

partial def Typ.print (t : Typ) : String :=
  let base := match t.kind with
    | .var name => s!"'{name}"
    | .con path [] => path.toString
    | .con path [arg] => s!"{printAppArg arg} {path.toString}"
    | .con path args => s!"({joinWith ", " (args.map Typ.print)}) {path.toString}"
    | .arrow dom cod =>
      let domStr := match dom.kind with
        | .arrow _ _ => parens (Typ.print dom)
        | _ => Typ.print dom
      s!"{domStr} -> {Typ.print cod}"
    | .tuple components => joinWith " * " (components.map Typ.print)
  base ++ joinWith "" (t.attrs.map (fun a => s!" [@{a}]"))
where
  -- Type constructor arguments that are themselves applications need parens
  printAppArg (t : Typ) : String :=
    match t.kind with
    | .arrow _ _ => parens (Typ.print t)
    | .tuple (_ :: _ :: _) => parens (Typ.print t)
    | _ => Typ.print t

-- ---------------------------------------------------------------------------
-- Pattern printing

private partial def Pattern.isAtom (p : Pattern) : Bool :=
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
  | .ctor path none => path.toString
  | .ctor path (some pat) => s!"{path.toString} {parenIf (!Pattern.isAtom pat) (Pattern.print pat)}"
  | .tuple pats => parens (joinWith ", " (pats.map Pattern.print))

-- ---------------------------------------------------------------------------
-- Expression printing

private partial def Expr.isAtom (e : Expr) : Bool :=
  match e.kind with
  | .const _ | .var _ | .ctor _ | .tuple _ | .record _ | .annot _ _ | .arrayGet _ _ => true
  | _ => false

private partial def Expr.isKeywordExpr (e : Expr) : Bool :=
  match e.kind with
  | .letIn _ _ _ _ | .fun_ _ _ _ | .ite _ _ _ | .match_ _ _ => true
  | _ => false

private partial def Expr.printPrec (e : Expr) (outerPrec : Nat) : String :=
  if !e.attrs.isEmpty then
    -- Expression attributes `e [@name payload]` attach at application precedence,
    -- so parenthesize any compound base to round-trip with the parser.
    let bare := Expr.printPrec { e with attrs := [] } 0
    let baseStr := parenIf (!Expr.isAtom e) bare
    baseStr ++ joinWith "" (e.attrs.map printAttr)
  else match e.kind with
  | .const c => Const.print c
  | .var path => path.toString
  | .ctor path => path.toString
  | .annot inner ty => s!"({Expr.printPrec inner 0} : {Typ.print ty})"
  | .tuple es => parens (joinWith ", " (es.map fun x => Expr.printPrec x 0))
  | .record fields => "{ " ++ fmtFields fields ++ " }"
  | .recordUpdate base fields =>
    "{ " ++ Expr.printPrec base 0 ++ " with " ++ fmtFields fields ++ " }"
  | .unop op inner => printUnop op inner
  | .arrayGet arr idx => printArrayGet arr idx outerPrec
  | .arraySet arr idx val => printArraySet arr idx val outerPrec
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
  -- Expression attribute `[@name]` or `[@name payload]` (single `@`).
  printAttr (attr : Attribute) : String :=
    match attr.payload with
    | none         => s!" [@{attr.name}]"
    | some payload => s!" [@{attr.name} {Expr.printPrec payload 0}]"
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
  printArrayGet (arr idx : Expr) (outerPrec : Nat) : String :=
    let p := 11
    let arrNeedsParens : Bool := match arr.kind with
      | .binop op _ _ => BinOp.prec op < p
      | _ => Expr.isKeywordExpr arr
    let arrStr := parenIf arrNeedsParens (Expr.printPrec arr p)
    parenIf (outerPrec > p) (arrStr ++ ".(" ++ Expr.printPrec idx 0 ++ ")")
  printArraySet (arr idx val : Expr) (outerPrec : Nat) : String :=
    let p := 2
    let lhs := printArrayGet arr idx p
    let rhsNeedsParens : Bool := match val.kind with
      | .binop op _ _ => BinOp.prec op < p
      | _ => Expr.isKeywordExpr val
    let rhs := parenIf rhsNeedsParens (Expr.printPrec val p)
    parenIf (outerPrec > p) (lhs ++ " <- " ++ rhs)

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
    match attr.payload with
    | none => "\n[@@" ++ attr.name ++ "]"
    | some payload => "\n[@@" ++ attr.name ++ " " ++ Expr.print payload ++ "]"
  let attrsSuffix := joinWith "" attrsStr
  match d.kind with
  | .open_ path => "open " ++ path.toString
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
