(* TEST: roundtrip *)
open Mica

(* [@@opaque] withholds the defining equation from the solver context. The
   unfolding function the declaration publishes is the only way to obtain it. *)
let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@opaque] [@@decreases n]
;;

(* Opacity composes with every other [@@fn] attribute. *)
let rec sum (n : int) : int =
  if n <= 0 then 0 else n + sum (n - 1)
[@@fn ghost] [@@opaque] [@@impl] [@@decreases n]
;;
