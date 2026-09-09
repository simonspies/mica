open Mica

(* A ghost declaration is a lemma: its body is a proof, not code. Every
   construct in it is a step of that proof, so a ghost body may name an
   intermediate value, split on a condition, and call another lemma. *)

let step (lo : int) (hi : int) : unit = ()
[@@ghost]
[@@spec fun lo hi ->
  assert (lo <= hi);
  ret (fun u -> assert (lo <= hi + 1))]
;;

let widen (a : int) (b : int) : unit =
  let%ghost m = b + 1 in
  if a <= b then step a m else step b m
[@@ghost]
[@@spec fun a b ->
  assert (0 <= a);
  assert (0 <= b);
  ret (fun u -> assert (a <= b + 2 || b <= b + 2))]
;;

let use (x : int) : int =
  let%ghost _ = widen x (x + 1) in
  x
[@@spec fun x ->
  assert (0 <= x);
  ret (fun v -> assert (v = x))]
