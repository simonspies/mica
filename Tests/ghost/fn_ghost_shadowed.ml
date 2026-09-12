(* TEST: no-compile *)
open Mica

(* A run-time binder hides the spec-level function of its name. In its scope
   the name is a value, and ghost code cannot call a value. *)
let plus2 (x : int) : int = x + 2
[@@fn ghost]
;;

let other (x : int) : int = x + 3
[@@spec fun x -> ret (fun v -> assert (v = x + 3))]
;;

let use (n : int) : int =
  let plus2 = other in
  let%ghost _ = plus2 n in
  plus2 n
[@@spec fun n -> ret (fun v -> assert (v = n + 3))]
