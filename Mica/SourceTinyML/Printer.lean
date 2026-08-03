-- SUMMARY: Pretty-printing for the untyped TinyML IR and declarations.
import Mica.TinyML.Common
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.Untyped
import Mica.SourceTinyML.Typed

open TinyML

namespace TinyML

/-- Does the type print without parentheses in argument position? -/
private def Typ.atomic : Typ.WithTypeVars V → Bool
  | .prim _ | .empty | .value | .tvar _ | .named _ [] => true
  | _ => false

/-- Print a type, rendering its variables with `pvar`. -/
def Typ.printWith (pvar : V → String) : Typ.WithTypeVars V → String
  | .prim p => p.print
  | .sum ts => s!"sum ({", ".intercalate (ts.map (Typ.printWith pvar))})"
  | .arrow args ret spec =>
      -- A specification has no surface syntax to print back into, but two
      -- arrows can differ in nothing else, so at least record that it is there.
      " -> ".intercalate ((args.map fun arg => wrapArg arg (Typ.printWith pvar arg))
        ++ [Typ.printWith pvar ret]) ++ (if spec.isSome then " [@@spec]" else "")
  | .ref t => s!"ref {wrapArg t (Typ.printWith pvar t)}"
  | .array t => s!"array {wrapArg t (Typ.printWith pvar t)}"
  | .ownedArray t => s!"owned-array {wrapArg t (Typ.printWith pvar t)}"
  | .vec t => s!"vec {wrapArg t (Typ.printWith pvar t)}"
  | .owned t => s!"owned {wrapArg t (Typ.printWith pvar t)}"
  | .empty => "empty"
  | .value => "value"
  | .tuple ts => s!"({", ".intercalate (ts.map (Typ.printWith pvar))})"
  | .tvar v => pvar v
  | .named T [] => T.print
  | .named T args =>
      s!"{T.print} ({", ".intercalate (args.map (Typ.printWith pvar))})"
where
  wrapArg (t : Typ.WithTypeVars V) (s : String) : String :=
    if Typ.atomic t then s else s!"({s})"

/-- Print a closed type. -/
def Typ.print : Typ → String := Typ.printWith Empty.elim

/-- Print a schema type, showing its variables in source syntax. -/
def SchemaTyp.print : SchemaTyp → String := Typ.printWith (fun v => s!"'{v}")

end TinyML

namespace Untyped

/-- Print a type of the untyped IR. Like `TinyML.Typ.print`, a specification an
arrow carries is dropped: there is no surface syntax to print it back into. -/
def Typ.print : Untyped.Typ → String
  | .core t => t.print
  | .tvar v => s!"'{v}"
  | .sum ts => s!"sum ({", ".intercalate (ts.map Typ.print)})"
  | .arrow args ret _ =>
      " -> ".intercalate ((args.map fun arg => wrapArg arg (Typ.print arg)) ++ [Typ.print ret])
  | .ref t => s!"ref {wrapArg t (Typ.print t)}"
  | .array t => s!"array {wrapArg t (Typ.print t)}"
  | .ownedArray t => s!"owned-array {wrapArg t (Typ.print t)}"
  | .vec t => s!"vec {wrapArg t (Typ.print t)}"
  | .owned t => s!"owned {wrapArg t (Typ.print t)}"
  | .tuple ts => s!"({", ".intercalate (ts.map Typ.print)})"
  | .named T [] => T.print
  | .named T args => s!"{T.print} ({", ".intercalate (args.map Typ.print)})"
where
  wrapArg (t : Untyped.Typ) (s : String) : String :=
    match t with
    | .core c => if TinyML.Typ.atomic c then s else s!"({s})"
    | .tvar _ => s
    | .named _ [] => s
    | _ => s!"({s})"

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
  | .letProd names bound body => s!"let ({", ".intercalate (names.map Binder.print)}) = {printExpr bound} in\n{printExpr body}"
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

private partial def printOr : Untyped.Expr → String
  | .binop .or lhs rhs => s!"{printAnd lhs} || {printOr rhs}"
  | e => printAnd e

private partial def printAnd : Untyped.Expr → String
  | .binop .and lhs rhs => s!"{printCmp lhs} && {printAnd rhs}"
  | e => printCmp e

private partial def printCmp : Untyped.Expr → String
  | .binop .eq lhs rhs => s!"{printAdd lhs} = {printAdd rhs}"
  | .binop .lt lhs rhs => s!"{printAdd lhs} < {printAdd rhs}"
  | .binop .le lhs rhs => s!"{printAdd lhs} <= {printAdd rhs}"
  | .binop .gt lhs rhs => s!"{printAdd lhs} > {printAdd rhs}"
  | .binop .ge lhs rhs => s!"{printAdd lhs} >= {printAdd rhs}"
  | e => printAdd e

private partial def printAdd : Untyped.Expr → String
  | .binop .add lhs rhs => s!"{printAdd lhs} + {printMul rhs}"
  | .binop .sub lhs rhs => s!"{printAdd lhs} - {printMul rhs}"
  | e => printMul e

private partial def printMul : Untyped.Expr → String
  | .binop .mul lhs rhs => s!"{printMul lhs} * {printApp rhs}"
  | .binop .div lhs rhs => s!"{printMul lhs} / {printApp rhs}"
  | .binop .mod lhs rhs => s!"{printMul lhs} mod {printApp rhs}"
  | e => printApp e

private partial def printApp : Untyped.Expr → String
  | .app fn args => s!"{printApp fn} {" ".intercalate (args.map printUnary)}"
  | .unop .not e => s!"not {printAtom e}"
  | .ref .owned e => s!"ref {printAtom e} [@owned]"
  | .ref .shared e => s!"ref {printAtom e}"
  | .inj tag arity e ty => s!"(inj {tag}/{arity} : {ty} {printAtom e})"
  | .assert e => s!"assert {printAtom e}"
  | e => printUnary e

private partial def printUnary : Untyped.Expr → String
  | .unop .neg e => s!"-{printAtom e}"
  | .deref e => s!"!{printAtom e}"
  | .unop (.proj n) e => s!"{printAtom e}.{n}"
  | e => printAtom e

private partial def printAtom : Untyped.Expr → String
  | .const c => printConst c
  | .var name => name
  | .prim name => name
  | .fix self args _ body => printFix self args body
  | .tuple es => s!"({", ".intercalate (es.map printOr)})"
  | e => s!"({printExpr e})"

partial def printConst : TinyML.Const → String
  | .int n => if n < 0 then s!"({n})" else s!"{n}"
  | .bool b => if b then "true" else "false"
  | .char c => s!"'{Char.ofNat c.toNat}'"
  | .string _ => "\"...\""
  | .float b => toString (Float.ofBits b)
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

namespace Spec

def Pred.print : Spec.Pred → String
  | .isinj tag arity scrut => s!"isinj {tag} {arity} {scrut}"
  | .own loc => s!"own {loc}"
  | .arr loc => s!"arr {loc}"

def Assert.print (inner : α → String) : Spec.Assert Untyped.Expr Untyped.Typ α → String
  | .ret a => s!"ret {inner a}"
  | .assert cond rest => s!"assert {printExpr cond}; {Assert.print inner rest}"
  | .let_ x e rest => s!"let {x} = {printExpr e} in {Assert.print inner rest}"
  | .bind pred x ty rest =>
      s!"bind ({Pred.print pred}) (fun ({x} : {ty.print}) -> {Assert.print inner rest})"
  | .ite cond thn els =>
      s!"if {printExpr cond} then {Assert.print inner thn} else {Assert.print inner els}"

def Post.print (post : Spec.Post Untyped.Expr Untyped.Typ) : String :=
  s!"fun {post.name} -> {Assert.print (fun () => "()") post.body}"

def Pre.print : Spec.Pre Untyped.Expr Untyped.Typ → String :=
  Assert.print Post.print

def Body.print (body : Untyped.SpecBody) : String :=
  s!"fun {" ".intercalate body.args} -> {Pre.print body.pre}"

end Spec

class SpecPayloadPrinter (S : Type) where
  print : S → String

instance : SpecPayloadPrinter Untyped.Expr where
  print := Expr.print

instance : SpecPayloadPrinter Untyped.SpecBody where
  print := Spec.Body.print

def ValDecl.print {S : Type} [SpecPayloadPrinter S] (d : Untyped.ValDecl S) : String :=
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
  let withSpec := match d.spec with
    | .none => decl
    | .some e => s!"{decl} [@@spec {SpecPayloadPrinter.print e}]"
  match d.relation with
  | .none => withSpec
  | .some _ => s!"{withSpec} [@@fn]"

def TypeDecl.print (d : Untyped.TypeDecl) : String :=
  let payloads := (List.range d.body.payloads.length).zip d.body.payloads |>.map
    (fun (i, ty) => s!"C{i} of {ty.print}")
  s!"type {d.name} = {" | ".intercalate payloads}"

def Decl.print {S : Type} [SpecPayloadPrinter S] : Untyped.Decl S → String
  | .val_ d => d.print
  | .type_ d => d.print

def Program.print {S : Type} [SpecPayloadPrinter S] (p : Untyped.Program S) : String :=
  "\n;;\n".intercalate (p.map Decl.print)

end Untyped
