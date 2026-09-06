(* TEST: no-compile *)
open Mica

let bump (x : int) : int = x + 1
[@@spec fun x ->
  assert (x < hi);
  ret (fun v -> assert (v <= hi))]
[@@ghost (hi : int)]
;;

let use (n : int) : int = (bump n [@ghost 100 200])
[@@spec fun n -> ret (fun v -> assert (v <= 100))]
