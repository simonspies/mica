(* TEST: no-compile *)
open Mica

(* A ghost argument is ghost code, and ghost code may only call a ghost
   function. Without the `ghost` payload the verifier never checks a [@@fn]
   body as a proof, so a ghost call has nothing to apply. *)
let bump (x : int) : int = x + 1
[@@spec fun x ->
  assert (x < hi);
  ret (fun v -> assert (v <= hi))]
[@@ghost (hi : int)]
;;

let plus2 (x : int) : int = x + 2
[@@fn]
;;

let use_fn (n : int) : int = (bump n [@ghost (plus2 n : int)])
[@@spec fun n ->
  ret (fun v ->
    assert (v <= n + 2))]
