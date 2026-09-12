(* TEST: no-compile *)

open Mica

(* `ghost` is the only payload [@@fn] takes. *)
let f (n : int) : int = n + 1
[@@fn lemma]
