-- SUMMARY: Structural translation from elaborated frontend terms into the specification language.
import Mica.Frontend.Spec
import Mica.TinyML.Untyped

/-!
# Spec Parser

Translates `Untyped.Expr` (from elaborated `[@@spec ...]` attributes) into the
untyped `Spec` AST. This is purely structural recognition — no sort checking.
-/

namespace Spec

private abbrev M := Except String

private def parseBinOp : TinyML.BinOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .eq => .eq | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge
  | .and => .and | .or => .or

private def parseTerm : Untyped.Expr → M Term
  | .var x => .ok (.var x)
  | .const (.int n) => .ok (.int n)
  | .const (.bool b) => .ok (.bool b)
  | .const .unit => .ok .unit
  | .binop op l r => do
    .ok (.binop (parseBinOp op) (← parseTerm l) (← parseTerm r))
  | .unop .neg e => do .ok (.unop .neg (← parseTerm e))
  | .unop .not e => do .ok (.unop .not (← parseTerm e))
  | .unop (.proj n) e => do .ok (.unop (.proj n) (← parseTerm e))
  | .tuple es => do .ok (.tuple (← es.mapM parseTerm))
  | .inj tag arity payload => do .ok (.unop (.inj tag arity) (← parseTerm payload))
  | .app (.var "inj") [.const (.int tag), .const (.int arity), payload] => do
    .ok (.unop (.inj tag.toNat arity.toNat) (← parseTerm payload))
  | .app (.var "tagof") [e] => do .ok (.unop .tagof (← parseTerm e))
  | .app (.var "arityof") [e] => do .ok (.unop .arityof (← parseTerm e))
  | .app (.var "payloadof") [e] => do .ok (.unop .payloadof (← parseTerm e))
  | .ifThenElse c t e => do
    .ok (.ite (← parseTerm c) (← parseTerm t) (← parseTerm e))
  | e => .error s!"unexpected term in spec: {repr e}"

private def parsePred : Untyped.Expr → M Pred
  | .app (.var "isint") [e] => do .ok (.isint (← parseTerm e))
  | .app (.var "isbool") [e] => do .ok (.isbool (← parseTerm e))
  | .app (.var "isinj") [.const (.int tag), .const (.int arity), e] => do
    .ok (.isinj tag.toNat arity.toNat (← parseTerm e))
  | .app (.var "own") [e] => do .ok (.own (← parseTerm e))
  | e => .error s!"expected type predicate (isint, isbool, isinj, own), got {repr e}"

private def parseAssert (inner : Untyped.Expr → M α)
    (bareAssert : Untyped.Expr → M (Assert α)) : Untyped.Expr → M (Assert α)
  | .app (.var "ret") [e] => do .ok (.ret (← inner e))
  | .app (.app (.var "bind") [e1]) [.fix .none [Untyped.Binder.named x _] _ e2] => do
    let pred ← parsePred e1
    let rest ← parseAssert inner bareAssert e2
    .ok (.bind pred x rest)
  | .letIn (Untyped.Binder.named x _) bound body => do
    let t ← parseTerm bound
    let rest ← parseAssert inner bareAssert body
    .ok (.let_ x t rest)
  | .letIn .none (.assert cond) body => do
    let c ← parseTerm cond
    let rest ← parseAssert inner bareAssert body
    .ok (.assert c rest)
  | .assert cond => bareAssert cond
  | .ifThenElse cond thn els => do
    let c ← parseTerm cond
    .ok (.ite c (← parseAssert inner bareAssert thn) (← parseAssert inner bareAssert els))
  | e => .error s!"expected assertion, got {repr e}"

private def parsePost : Untyped.Expr → M Post :=
  parseAssert
    (fun | .const .unit => .ok ()
         | e => .error s!"expected (), got {repr e}")
    (fun cond => do .ok (.assert (← parseTerm cond) (.ret ())))

private def parsePre : Untyped.Expr → M Pre :=
  parseAssert
    (fun | .fix .none [Untyped.Binder.named x _] _ body => do
           let post ← parsePost body
           .ok (x, post)
         | e => .error s!"expected fun v -> ..., got {repr e}")
    (fun _ => .error "bare assert is only allowed in postconditions")

private def peelBinders : Untyped.Expr → M Body
  | Untyped.Expr.fix .none args _ body => do
    let names ← getNames args
    if names.isEmpty then .error "spec must bind at least one argument"
    else do
      let pre ← parsePre body
      .ok (names, pre)
  | e => .error s!"expected fun x -> ..., got {repr e}"
where
  getNames : List Untyped.Binder → M (List String)
    | [] => .ok []
    | Untyped.Binder.named x _ :: rest => do let xs ← getNames rest; .ok (x :: xs)
    | Untyped.Binder.none :: _ => .error "unnamed binder in spec is not allowed"

def parse (e : Untyped.Expr) : M Body :=
  peelBinders e

end Spec
