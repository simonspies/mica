(* TEST: roundtrip *)
open Mica

(* The body of a [@@fn ghost] declaration is checked as ghost code, so a
   primitive it calls is compiled as a ghost call. *)
let pos (x : int) : int = Int.max x 0
[@@fn ghost]
;;

let use (x : int) : int =
  let%ghost p = pos x in
  let%ghost _ = assert (0 <= p) in
  x
[@@spec fun x -> ret (fun v -> assert (v = x))]
