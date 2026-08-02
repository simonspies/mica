(* TEST: --print-ocaml --no-check no-compile roundtrip *)
open Mica

(* The three unary levels a single `parseUnary` used to collapse into one.
   Prefix `!` is the tightest form of all, above postfix access and above
   application. The differential corpus checks these against ocamlc; this pins
   them in readable form. *)
type point = { x : int; y : int }

let deref_binds_tighter_than_field (r : point ref) = (!r).x

let deref_binds_tighter_than_index (a : int array ref) i = (!a).(i)

let deref_is_an_argument (f : int -> int) (r : int ref) = f !r

let deref_nests (r : int ref ref) = !(!r)

(* Prefix `-` sits below application and above every binary operator. *)
let neg_takes_an_application (f : int -> int) a = - (f a)

let neg_binds_tighter_than_mul a b = (- a) * b

(* `assert` sits at the application level but takes a single operand, so
   `assert f a` is a syntax error rather than an assertion of `f a`. *)
let assert_takes_one_operand (f : int -> bool) a = assert (f a)
