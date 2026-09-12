open Mica

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@opaque] [@@decreases n]
;;

let zero (u : unit) : int =
  let%ghost _ = countdown_unfold 0 in
  0
[@@spec fun u -> ret (fun r -> assert (r = countdown 0))]
;;

(* The call above brings the equation into that proof alone. It is never added
   to the solver context, so this proof cannot see it. *)
let zero_again (u : unit) : int = 0
[@@spec fun u -> ret (fun r -> assert (r = countdown 0))]
;;
