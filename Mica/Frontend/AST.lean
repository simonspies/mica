-- SUMMARY: Surface syntax trees and source locations for the OCaml frontend.
namespace Frontend

-- Name types

abbrev Var             := String
abbrev Constructor     := String
abbrev TypeConstructor := String
abbrev TypeVariable    := String
abbrev FieldName       := String

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
  | bool (b : Bool)
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
  | eq | neq | lt | le | gt | ge
  | and | or
  | semi | pipeRight | atAt | assign
  deriving Repr, BEq

-- Types

mutual
  inductive TypKind where
    | var (name : TypeVariable)
    | con (name : TypeConstructor) (args : List Typ)
    | arrow (dom cod : Typ)
    | tuple (components : List Typ)

  structure Typ where
    loc  : Location
    kind : TypKind
end

-- Patterns, expressions, match arms

mutual
  inductive PatternKind where
    | wildcard
    | binder (name : Option Var) (ty : Option Typ)
    | const (c : Const)
    | ctor (name : Constructor) (payload : Option Pattern)
    | tuple (pats : List Pattern)

  structure Pattern where
    loc  : Location
    kind : PatternKind

  inductive ExprKind where
    | const (c : Const)
    | var (name : Var)
    | ctor (name : Constructor)
    | app (fn : Expr) (args : List Expr)
    | binop (op : BinOp) (lhs rhs : Expr)
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
    loc  : Location
    kind : ExprKind

  structure MatchArm where
    pat  : Pattern
    body : Expr
end

-- Declarations and programs

inductive TypeDeclBody where
  | variant (ctors : List (Constructor × Option Typ))
  | record (fields : List (FieldName × Typ))

structure TypeDecl where
  params : List TypeVariable
  name   : TypeConstructor
  body   : TypeDeclBody

structure Attribute where
  name    : String
  payload : Expr

inductive DeclKind where
  | type_ (decl : TypeDecl)
  | val_ (rec : Bool) (binders : List Pattern) (retTy : Option Typ) (body : Expr)

structure Decl where
  loc   : Location
  kind  : DeclKind
  attrs : List Attribute

abbrev Program := List Decl

end Frontend
