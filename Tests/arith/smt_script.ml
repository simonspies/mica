(* TEST: --smt-commands-only *)
open Mica

(* Pins the SMT script generated for a minimal verified function. *)
let id_ (x: int) : int = x
[@@spec fun x -> ret (fun v -> assert (v = x))];;
