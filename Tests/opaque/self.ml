open Mica

(* The implementation and the ghost body are proofs about this declaration, so
   they run with the equation it withholds from everyone else. *)
let rec sum (n : int) : int =
  if n <= 0 then 0 else n + sum (n - 1)
[@@fn ghost] [@@opaque] [@@impl] [@@decreases n]
;;

let one (u : unit) : int =
  let%ghost _ = sum_unfold 1 in
  let%ghost _ = sum_unfold 0 in
  sum 1
[@@spec fun u -> ret (fun r -> assert (r = 1))]
;;
