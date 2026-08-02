(* TEST: --print-ocaml --parse-only no-compile roundtrip *)
open Mica

(* The leading `|` is optional, as in OCaml. The printer always writes it. *)
let first_bar_optional x = match x with
  A y -> y
| B -> 0

(* A `let`'s return annotation is delimited by the `=` that follows, so it may
   be an arrow. A `fun`'s is delimited by `->`, so an arrow needs parentheses
   there — and the printer has to put them back. *)
let arrow_return_type g x : int -> int = g x

let fun_arrow_return_type g = (fun y : (int -> int) -> y) g
