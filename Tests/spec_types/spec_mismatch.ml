open Mica

(* A specified arrow is invariant: a function passed by name has to have the
   parameter's arrow, specification included. A weaker one is rejected. *)
let apply (g : (int -> int) [@spec fun x -> ret (fun r -> assert (r > x))]) (n : int) : int =
  g n
[@@spec fun g n -> ret (fun r -> assert (r > n))]

let same (x : int) : int = x
[@@spec fun x -> ret (fun r -> assert (r = x))]

let use (m : int) : int = apply same m
[@@spec fun m -> ret (fun r -> assert (r > m))]
