(* TEST: no-compile *)
open Mica

let bump (x : int) : int = x + 1
[@@spec fun x ->
  assert (x < hi);
  ret (fun v -> assert (v <= hi))]
[@@ghost (hi : int)]
;;

(* `Range.all` is a specification-level primitive, not a ghost function, so a
   bounded quantifier in a ghost argument is rejected. *)
let use (n : int) : int =
  (bump n [@ghost (if Range.all 0 3 (fun i -> i >= 0) then n + 1 else n + 1 : int)])
[@@spec fun n -> ret (fun v -> assert (v <= n + 1))]
