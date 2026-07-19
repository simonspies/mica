open Mica

(* A spec referring to a variable that is not in scope must be rejected. *)
let double (x: int) : int = x + x
[@@spec fun x -> ret (fun v -> assert (v = y))];;
