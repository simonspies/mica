(* TEST: no-compile *)
open Mica

let leak (x : int) : int = x + hi
[@@spec fun x ->
  ret (fun v -> assert (v <= hi))]
[@@ghost (hi : int)]
