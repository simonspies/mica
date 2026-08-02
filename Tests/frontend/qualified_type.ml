(* TEST: --print-ocaml --parse-only no-compile roundtrip *)
open Mica

(* A type application's head may be a module path: `int Queue.t`. The parser
   used to accept only a lowercase head, so the `Queue` was left behind and
   reported at the token after the type. `--parse-only`: the resolver knows no
   such module, which is a separate question. *)
let qualified (q : int Queue.t) = q

let qualified_argument (q : int list Queue.t) = q

let applied_to_qualified (q : int Queue.t list) = q

let qualified_nullary (q : Queue.t) = q

let multi_parameter (h : (int, int) Hashtbl.t) = h

let qualified_argument_and_head (q : Foo.t Bar.t) = q
