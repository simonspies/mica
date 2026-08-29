(* TEST: no-compile *)

open Mica

(* A [@@fn] declaration is its own definition, so it has nothing left to
   state. Use [@@impl] to also verify the body as run-time code. *)
let f (n : int) : int = n
[@@fn]
[@@spec fun n -> ret (fun r -> assert (r = n))]
