(* TEST: --print-ocaml --parse-only no-compile roundtrip *)
open Mica

type point = { u : int; v : int }

(* `{ u }` is `{ u = u }`, in expressions, in record updates, and in patterns.
   The printer always writes the field out. `--parse-only`: record updates parse
   but do not elaborate, which is a separate question. *)
let punned u v = { u; v }

let mixed u = { u; v = 0 }

let update r v = { r with v }

let pattern_punning p = match p with
| { u; v } -> u + v
