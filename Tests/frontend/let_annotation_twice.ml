(* TEST: no-compile *)

open Mica

(* A `let` with no arguments has two places to write its type — on the binder
   pattern and after it — and they mean the same thing, so writing both is
   rejected rather than one of them being dropped. *)
let f (n : int) : int =
  let (b : int) : bool = n in
  0
[@@spec fun n -> ret (fun r -> assert (r = 0))]
