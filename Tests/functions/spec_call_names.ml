open Mica

let zero (n : int) : int = 0 [@@fn];;

(* Nested calls must preserve both argument and result names in scope. *)
let keep (r : int) : int = r
[@@spec fun r -> ret (fun r1 -> assert (zero (zero r) + r = r1))];;
