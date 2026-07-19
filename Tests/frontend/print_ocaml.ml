(* TEST: --print-ocaml --no-check no-compile roundtrip *)
open Mica

(* Pins parentheses that preserve the parsed expression tree. *)
let nested : int list list = (1 :: []) :: []
let sequenced (r : int ref) : int list = [(r := 1; 2); 3]
