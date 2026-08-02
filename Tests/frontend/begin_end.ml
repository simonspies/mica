(* TEST: --print-ocaml --parse-only no-compile roundtrip *)
open Mica

(* `begin e end` is `(e)`: the grouping is read and then forgotten, so the
   printer writes parentheses where they are needed and nothing where they are
   not. Before `begin` and `end` were keywords, this file parsed as
   applications of two variables by those names. *)
let grouping a b c = begin a + b end * c

let as_an_argument f a = f begin a end

let sequence a b = begin a; b end

let access r = begin r end.u
