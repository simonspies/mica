open Mica

(* An unprovable spec: double returns 2 * x, not x. Verification must fail. *)
let double (x: int) : int = x + x
[@@spec fun x -> ret (fun v -> assert (v = x))];;
