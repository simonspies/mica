(* TEST: no-compile *)

open Mica

(* A declaration is specified once. A second [@@spec] is rejected rather than
   ignored in favour of the first. *)
let f (n : int) : int = n
[@@spec fun n -> ret (fun r -> assert (r = n))]
[@@spec fun n -> ret (fun r -> assert (r = n + 1))]
