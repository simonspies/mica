(* TEST: no-compile *)
open Mica

let countdown_unfold (u : unit) : unit = ()
;;

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@opaque] [@@decreases n]
;;
