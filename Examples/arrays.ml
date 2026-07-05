open Mica

(* Shared (unowned) arrays.

   An [int array] is a heap-allocated block exposing only its length at the
   spec level (via the uninterpreted [array_length]); element contents are not
   value-tracked.  Every [a.(i)] read/write and [Array.make] must discharge its
   in-bounds / nonnegative-length side conditions as SMT proof obligations. *)

(* Constant size and indices, with bounds [0 <= 3 < 10]. *)
let build_and_read (n : int) : int =
  let a = Array.make 10 0 in
  a.(3) <- 7;
  let x = a.(3) in
  x + Array.length a
[@@spec fun n -> ret (fun v -> assert (v = v))];;

(* [Array.length] in spec to ensure the precondition for the read [a.(i)] *)
let get_checked (a : int array) (i : int) : int =
  a.(i)
[@@spec fun a i ->
  assert (0 <= i);
  assert (i < Array.length a);
  ret (fun v -> assert (v = v))];;

(* A freshly allocated array has exactly the requested length. *)
let alloc (n : int) : int array =
  Array.make n 0
[@@spec fun n ->
  assert (n >= 0);
  ret (fun a -> assert (Array.length a = n))];;


(* Bounds constraints are also gathered from dynamic checks. *)
let dynamic_access (a : int array) (i : int) : int =
  if 0 <= i && i < Array.length a then a.(i) else 0
[@@spec fun a i -> ret (fun v -> assert (true))];;