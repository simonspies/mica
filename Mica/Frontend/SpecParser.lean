-- SUMMARY: Structural translation from elaborated TinyML terms into the specification language.
import Mica.TinyML.Spec
import Mica.TinyML.Untyped

/-!
# Spec Parser

Translates `Untyped.Expr` (from elaborated `[@@spec ...]` attributes) into the
`Spec` AST. This recognises only the control structure (`ret`, predicate
`bind`, `let`, `assert`, `ite`); embedded leaf expressions are preserved
verbatim as `Untyped.Expr` and typechecked later during elaboration.
-/

namespace Spec

private abbrev M := Except String

private def parsePred : Untyped.Expr → M Pred
  | .app (.var "isinj") [.const (.int tag), .const (.int arity), .var scrut] =>
    .ok (.isinj tag.toNat arity.toNat scrut)
  | .app (.var "own") [.var loc] => .ok (.own loc)
  | e => .error s!"expected predicate (isinj, own) over a variable, got {repr e}"

private def parseAssert (inner : Untyped.Expr → M α)
    (bareAssert : Untyped.Expr → M (Assert Untyped.Expr α)) :
    Untyped.Expr → M (Assert Untyped.Expr α)
  | .app (.var "ret") [e] => do .ok (.ret (← inner e))
  | .app (.app (.var "bind") [e1]) [.fix .none [Untyped.Binder.named x (some ty)] _ e2] => do
    let pred ← parsePred e1
    let rest ← parseAssert inner bareAssert e2
    .ok (.bind pred x ty rest)
  | .app (.app (.var "bind") [_]) [.fix .none [Untyped.Binder.named _ none] _ _] =>
    .error "bind continuation binder must be type-annotated"
  | .letIn (Untyped.Binder.named x _) bound body => do
    let rest ← parseAssert inner bareAssert body
    .ok (.let_ x bound rest)
  | .letIn .none (.assert cond) body => do
    let rest ← parseAssert inner bareAssert body
    .ok (.assert cond rest)
  | .assert cond => bareAssert cond
  | .ifThenElse cond thn els => do
    .ok (.ite cond (← parseAssert inner bareAssert thn) (← parseAssert inner bareAssert els))
  | e => .error s!"expected assertion, got {repr e}"

private def parsePost : Untyped.Expr → M (Post Untyped.Expr) :=
  parseAssert
    (fun | .const .unit => .ok ()
         | e => .error s!"expected (), got {repr e}")
    (fun cond => .ok (.assert cond (.ret ())))

private def parsePre : Untyped.Expr → M (Pre Untyped.Expr) :=
  parseAssert
    (fun | .fix .none [Untyped.Binder.named x _] _ body => do
           let post ← parsePost body
           .ok (x, post)
         | e => .error s!"expected fun v -> ..., got {repr e}")
    (fun _ => .error "bare assert is only allowed in postconditions")

private def peelBinders : Untyped.Expr → M (Body Untyped.Expr)
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

def parse (e : Untyped.Expr) : M (Body Untyped.Expr) :=
  peelBinders e

end Spec
