(* TEST: --print-ocaml --no-check roundtrip *)

open Mica

(* Unary and multi-argument function expressions elaborate to n-ary core arrows. *)
let unary (x : int) : int = x

let multi (x : int) (y : int) : int = x + y

let apply_two (f : int -> int -> int) (x : int) (y : int) : int = f x y

let result : int = apply_two multi (unary 1) 2
