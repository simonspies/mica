open Mica

(* An unspecified function is not a value of a specified arrow type. *)
let apply (g : (int -> int) [@spec fun x -> ret (fun r -> assert (r > x))]) (n : int) : int =
  g n
[@@spec fun g n -> ret (fun r -> assert (r > n))]

let plain (x : int) : int = x + 1

let use (m : int) : int = apply plain m
[@@spec fun m -> ret (fun r -> assert (r > m))]
