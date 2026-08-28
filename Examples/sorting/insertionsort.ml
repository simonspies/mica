open Mica

(* Insertion sort over a shared [int array]: grow a sorted prefix by shifting
   each next element left into place with adjacent swaps.

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

(* Shift [a.(j)] left into the sorted prefix by adjacent swaps. *)
let rec shift_down_safe (a : int array) (j : int) : unit =
  if j > 0 then
    (if a.(j - 1) > a.(j) then
       (swap_safe a (j - 1) j;
        shift_down_safe a (j - 1))
     else ())
  else ()
[@@spec fun a j ->
  assert (0 <= j);
  assert (j < Array.length a);
  ret (fun r -> assert (true))];;

(* Insert [a.(i)] for increasing [i], growing the sorted prefix [a.(0 .. i-1)]. *)
let rec insert_from_safe (a : int array) (i : int) (n : int) : unit =
  if i < n then
    (shift_down_safe a i;
     insert_from_safe a (i + 1) n)
  else ()
[@@spec fun a i n ->
  assert (0 <= i);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

let insertionsort_safe (a : int array) : unit =
  insert_from_safe a 1 (Array.length a)
[@@spec fun a -> ret (fun r -> assert (true))];;
