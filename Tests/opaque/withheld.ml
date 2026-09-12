open Mica

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@opaque] [@@decreases n]
;;

(* Without a call to countdown_unfold the equation is out of reach, and
   totality alone says nothing about the result. *)
let zero (u : unit) : int = 0
[@@spec fun u -> ret (fun r -> assert (r = countdown 0))]
;;
