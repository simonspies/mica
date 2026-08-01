(* TEST: no-compile *)

open Mica

(* A declaration that takes arguments annotates its return type after them, so
   there is nothing for an annotation on its name to mean. It is rejected
   rather than silently dropped. OCaml rejects the syntax outright. *)
let (f : bool) (n : int) : int = n
