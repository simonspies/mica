open Mica

(* The call result must not capture the postcondition's result variable. *)
let zero (n : int) : int = 0 [@@fn];;

let bad (n : int) : int = 42
[@@spec fun n -> ret (fun r -> assert (zero n = r))];;
