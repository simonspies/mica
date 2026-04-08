import Mica.TinyML.Typed
import Mica.TinyML.Untyped

open TinyML

namespace Untyped

def BinOp.toString : TinyML.BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "mod"
  | .eq => "=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"

def UnOp.toString : TinyML.UnOp → String
  | .neg => "-" | .not => "not"
  | .proj n => s!".{n}"

def Binder.print : Untyped.Binder → String
  | .none => "_"
  | .named name _ => name

private def argsStr (args : List Untyped.Binder) : String :=
  " ".intercalate (args.map Binder.print)

private partial def collectFixArgs (f : String) (args : List Untyped.Binder) (body : Untyped.Expr)
    : List Untyped.Binder × Untyped.Expr :=
  match body with
  | .fix (.named f' _) args' _ inner =>
    if f == f' then
      let (moreArgs, finalBody) := collectFixArgs f args' inner
      (args ++ moreArgs, finalBody)
    else (args, body)
  | _ => (args, body)

private partial def collectAnonArgs (args : List Untyped.Binder) (body : Untyped.Expr)
    : List Untyped.Binder × Untyped.Expr :=
  match body with
  | .fix .none args' _ inner =>
    let (moreArgs, finalBody) := collectAnonArgs args' inner
    (args ++ moreArgs, finalBody)
  | _ => (args, body)

mutual

partial def printExpr : Untyped.Expr → String
  | .letIn .none bound body => s!"{printOr bound};\n{printExpr body}"
  | .letIn name bound body => printLetIn name bound body
  | .ifThenElse cond thn els =>
    s!"if {printExpr cond} then {printExpr thn} else {printExpr els}"
  | .match_ scrut branches =>
    let arms := (List.range branches.length).zip branches |>.map fun ⟨i, (binder, body)⟩ =>
      s!"| {i} {binder.print} -> {printExpr body}"
    s!"match {printExpr scrut} with {" ".intercalate arms}"
  | .store l r => s!"{printOr l} := {printOr r}"
  | e => printOr e

partial def printLetIn (name : Untyped.Binder) (bound body : Untyped.Expr) : String :=
  match bound with
  | .fix (.named f _) args _ inner =>
    let (allArgs, innerBody) := collectFixArgs f args inner
    let nameMatchesF := match name with | .named n _ => n == f | .none => false
    if nameMatchesF then
      s!"let rec {f} {argsStr allArgs} = {printExpr innerBody} in\n{printExpr body}"
    else
      s!"let {name.print} = (let rec {f} {argsStr allArgs} = {printExpr innerBody} in {f}) in\n{printExpr body}"
  | .fix .none args _ inner =>
    let (allArgs, innerBody) := collectAnonArgs args inner
    s!"let {name.print} {argsStr allArgs} = {printExpr innerBody} in\n{printExpr body}"
  | _ =>
    s!"let {name.print} = {printExpr bound} in\n{printExpr body}"

partial def printOr : Untyped.Expr → String
  | .binop .or lhs rhs => s!"{printAnd lhs} || {printOr rhs}"
  | e => printAnd e

partial def printAnd : Untyped.Expr → String
  | .binop .and lhs rhs => s!"{printCmp lhs} && {printAnd rhs}"
  | e => printCmp e

partial def printCmp : Untyped.Expr → String
  | .binop .eq lhs rhs => s!"{printAdd lhs} = {printAdd rhs}"
  | .binop .lt lhs rhs => s!"{printAdd lhs} < {printAdd rhs}"
  | .binop .le lhs rhs => s!"{printAdd lhs} <= {printAdd rhs}"
  | .binop .gt lhs rhs => s!"{printAdd lhs} > {printAdd rhs}"
  | .binop .ge lhs rhs => s!"{printAdd lhs} >= {printAdd rhs}"
  | e => printAdd e

partial def printAdd : Untyped.Expr → String
  | .binop .add lhs rhs => s!"{printAdd lhs} + {printMul rhs}"
  | .binop .sub lhs rhs => s!"{printAdd lhs} - {printMul rhs}"
  | e => printMul e

partial def printMul : Untyped.Expr → String
  | .binop .mul lhs rhs => s!"{printMul lhs} * {printApp rhs}"
  | .binop .div lhs rhs => s!"{printMul lhs} / {printApp rhs}"
  | .binop .mod lhs rhs => s!"{printMul lhs} mod {printApp rhs}"
  | e => printApp e

partial def printApp : Untyped.Expr → String
  | .app fn args => s!"{printApp fn} {" ".intercalate (args.map printUnary)}"
  | .unop .not e => s!"not {printAtom e}"
  | .ref e => s!"ref {printAtom e}"
  | .inj tag arity e => s!"(inj {tag}/{arity} {printAtom e})"
  | .assert e => s!"assert {printAtom e}"
  | e => printUnary e

partial def printUnary : Untyped.Expr → String
  | .unop .neg e => s!"-{printAtom e}"
  | .deref e => s!"!{printAtom e}"
  | .unop (.proj n) e => s!"{printAtom e}.{n}"
  | e => printAtom e

partial def printAtom : Untyped.Expr → String
  | .const c => printConst c
  | .var name => name
  | .fix self args _ body => printFix self args body
  | .tuple es => s!"({", ".intercalate (es.map printOr)})"
  | e => s!"({printExpr e})"

partial def printConst : TinyML.Const → String
  | .int n => if n < 0 then s!"({n})" else s!"{n}"
  | .bool b => if b then "true" else "false"
  | .unit => "()"

partial def printFix (self : Untyped.Binder) (args : List Untyped.Binder) (body : Untyped.Expr) : String :=
  match self with
  | .none =>
    let (allArgs, inner) := collectAnonArgs args body
    s!"fun {argsStr allArgs} -> {printExpr inner}"
  | .named f _ =>
    let (allArgs, inner) := collectFixArgs f args body
    s!"(let rec {f} {argsStr allArgs} = {printExpr inner} in {f})"

end

def Expr.print (e : Untyped.Expr) : String := printExpr e

def Decl.print (d : Untyped.Decl Untyped.Expr) : String :=
  let decl := match d.body with
    | .fix (.named f _) args _ inner =>
      let (allArgs, innerBody) := collectFixArgs f args inner
      let nameMatchesF := match d.name with | .named n _ => n == f | .none => false
      if nameMatchesF then
        s!"let rec {f} {argsStr allArgs} = {printExpr innerBody}"
      else
        s!"let {d.name.print} = (let rec {f} {argsStr allArgs} = {printExpr innerBody} in {f})"
    | .fix .none args _ inner =>
      let (allArgs, innerBody) := collectAnonArgs args inner
      s!"let {d.name.print} {argsStr allArgs} = {printExpr innerBody}"
    | body => s!"let {d.name.print} = {printExpr body}"
  match d.spec with
  | .none => decl
  | .some e => s!"{decl} [@@spec {printExpr e}]"

def Program.print (p : Untyped.Program Untyped.Expr) : String :=
  "\n;;\n".intercalate (p.map Decl.print)

end Untyped
