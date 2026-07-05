-- SUMMARY: Surface syntax trees and source locations for the OCaml frontend.

/-!
This file defines the frontend surface AST and source-location types used across
lexing, parsing, pretty-printing, and elaboration. The structures here preserve
source-level shape and metadata before lowering to TinyML core syntax.
-/

namespace Frontend

-- Name types

abbrev Var             := String
abbrev Constructor     := String
abbrev TypeConstructor := String
abbrev TypeVariable    := String
abbrev FieldName       := String

/-- A nonempty list of identifier segments in a (possibly) qualified path:
`Int.min` is `⟨"Int", ["min"]⟩`; an unqualified `foo` is `⟨"foo", []⟩`. -/
structure Path where
  head : String
  tail : List String := []
  deriving Repr, Inhabited, BEq, DecidableEq

namespace Path

def single (s : String) : Path := ⟨s, []⟩

def segments (p : Path) : List String := p.head :: p.tail

def isQualified (p : Path) : Bool := !p.tail.isEmpty

/-- Final segment of the path (the value/type/constructor name). -/
def last (p : Path) : String :=
  (p.head :: p.tail).getLast (by simp)

def toString (p : Path) : String :=
  String.intercalate "." p.segments

instance : ToString Path := ⟨Path.toString⟩

end Path

-- Locations

structure Position where
  file : String
  line : Nat
  col  : Nat
  deriving Repr, Inhabited

structure Location where
  start : Position
  stop  : Position
  deriving Repr, Inhabited

-- Constants and operators

inductive Const where
  | int (n : Int)
  | float (value : Float)
  | bool (b : Bool)
  | string (s : List UInt8)
  | char (c : Char)
  | unit
  deriving Repr

inductive UnOp where
  | neg | deref | assert
  | proj (n : Nat)
  | field (name : FieldName)
  deriving Repr

inductive BinOp where
  | add | sub | mul | div | mod
  | fadd | fsub | fmul | fdiv
  | eq | neq | lt | le | gt | ge
  | and | or
  | semi | pipeRight | atAt | assign | concat
  deriving Repr, BEq

-- Types

mutual
  inductive TypKind where
    | var (name : TypeVariable)
    | con (path : Path) (args : List Typ)
    | arrow (dom cod : Typ)
    | tuple (components : List Typ)

  structure Typ where
    loc   : Location
    kind  : TypKind
    attrs : List String := []   -- type attributes `T [@name]` (name-only, e.g. `[@owned]`)
end

-- Patterns, expressions, match arms

mutual
  inductive PatternKind where
    | wildcard
    | binder (name : Option Var) (ty : Option Typ)
    | const (c : Const)
    | ctor (path : Path) (payload : Option Pattern)
    | tuple (pats : List Pattern)

  structure Pattern where
    loc  : Location
    kind : PatternKind

  inductive ExprKind where
    | const (c : Const)
    | var (path : Path)
    | ctor (path : Path)
    | app (fn : Expr) (args : List Expr)
    | binop (op : BinOp) (lhs rhs : Expr)
    | arrayGet (arr idx : Expr)
    | arraySet (arr idx val : Expr)
    | unop (op : UnOp) (e : Expr)
    | ite (cond thn els : Expr)
    | letIn (rec : Bool) (binders : List Pattern) (bound body : Expr)
    | fun_ (args : List Pattern) (retTy : Option Typ) (body : Expr)
    | match_ (scrutinee : Expr) (arms : List MatchArm)
    | tuple (es : List Expr)
    | record (fields : List (FieldName × Expr))
    | recordUpdate (e : Expr) (fields : List (FieldName × Expr))
    | annot (e : Expr) (ty : Typ)

  structure Expr where
    loc   : Location
    kind  : ExprKind
    attrs : List Attribute := []   -- expression attributes `e [@name payload]`

  structure MatchArm where
    pat  : Pattern
    body : Expr

  /-- An OCaml attribute `[@name payload]` (expression-level, single `@`) or
  `[@@name payload]` (declaration-level, double `@`). The payload, when present,
  is a surface expression. -/
  structure Attribute where
    name    : String
    payload : Option Expr
end

-- Declarations and programs

inductive TypeDeclBody where
  | variant (ctors : List (Constructor × Option Typ))
  | record (fields : List (FieldName × Typ))

structure TypeDecl where
  params : List TypeVariable
  name   : TypeConstructor
  body   : TypeDeclBody

inductive DeclKind where
  | open_ (path : Path)
  | type_ (decl : TypeDecl)
  | val_ (rec : Bool) (binders : List Pattern) (retTy : Option Typ) (body : Expr)

structure Decl where
  loc   : Location
  kind  : DeclKind
  attrs : List Attribute

abbrev Program := List Decl

end Frontend
