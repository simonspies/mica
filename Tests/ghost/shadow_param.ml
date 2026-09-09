(* TEST: no-compile *)
open Mica

let bump (x : int) : int = x + 1
[@@spec fun x ->
  assert (x < hi);
  ret (fun v -> assert (v <= hi))]
[@@ghost (x : int) (hi : int)]
