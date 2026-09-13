open Mica

(* Names with a prime are not simple SMT-LIB symbols. *)

let incr' (x : int) : int = x + 1
[@@fn];;

let f (x : int) : int =
  let x' = x + 1 in x'
[@@spec fun x -> ret (fun r -> assert (r = incr' x))];;

let g (x : int) : unit = ()
[@@spec fun x -> ret (fun r -> let x' = x + 1 in assert (x' > x))];;
