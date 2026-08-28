open Mica

(* Selection sort over a shared [int array]: repeatedly find a minimal element
   of the unsorted suffix and swap it to the front.

   Shared arrays expose only their length in specifications, so the verified
   property is that every read, write, and swap index stays in bounds.  Each
   helper states the index bounds it needs as preconditions, and nothing
   else. *)

(* Swap [a.(i)] and [a.(j)]. *)
let swap_safe (a : int array) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  assert (0 <= i && i < Array.length a);
  assert (0 <= j && j < Array.length a);
  ret (fun r -> assert (true))];;

(* Index of a minimal element of [a.(m .. n-1)]; [m] is the best index so far,
   [j] the scan cursor. *)
let rec find_min_safe (a : int array) (m : int) (j : int) (n : int) : int =
  if j < n then
    (if a.(j) < a.(m) then find_min_safe a j (j + 1) n
     else find_min_safe a m (j + 1) n)
  else m
[@@spec fun a m j n ->
  assert (0 <= m && m < Array.length a);
  assert (m < j && n <= Array.length a);
  ret (fun r -> assert (0 <= r && r < Array.length a))];;

(* Sort [a.(k .. n-1)], assuming the prefix [a.(0 .. k-1)] is already in
   place. *)
let rec sel_sort_safe (a : int array) (k : int) (n : int) : unit =
  if k < n then
    (let m = find_min_safe a k (k + 1) n in
     swap_safe a k m;
     sel_sort_safe a (k + 1) n)
  else ()
[@@spec fun a k n ->
  assert (0 <= k);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

let selectionsort_safe (a : int array) : unit =
  sel_sort_safe a 0 (Array.length a)
[@@spec fun a -> ret (fun r -> assert (true))];;
