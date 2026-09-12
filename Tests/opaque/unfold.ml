(* TEST: roundtrip *)
open Mica

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@opaque] [@@decreases n]
;;

(* The call brings countdown's defining equation at 0 into this proof. *)
let zero (u : unit) : int =
  let%ghost _ = countdown_unfold 0 in
  0
[@@spec fun u -> ret (fun r -> assert (r = countdown 0))]
;;

(* Unfolding at each argument of a chain reaches the base case. *)
let zero_of_two (u : unit) : int =
  let%ghost _ = countdown_unfold 2 in
  let%ghost _ = countdown_unfold 1 in
  let%ghost _ = countdown_unfold 0 in
  0
[@@spec fun u -> ret (fun r -> assert (r = countdown 2))]
;;
