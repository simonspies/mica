open Mica

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@opaque] [@@decreases n]
;;

(* A call gives the equation at its own argument only. Here it states the
   result at 1 in terms of countdown 0, which stays folded. *)
let zero (u : unit) : int =
  let%ghost _ = countdown_unfold 1 in
  0
[@@spec fun u -> ret (fun r -> assert (r = countdown 1))]
;;
