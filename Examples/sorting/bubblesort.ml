open Mica

(* Bubble sort over a shared [int array]: repeated passes bubble the largest
   element of the unsorted prefix to its end.

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

(* One left-to-right pass bubbling the largest element of [a.(0 .. n-1)] to
   position [n-1]. *)
let rec bubble_pass_safe (a : int array) (i : int) (n : int) : unit =
  if i + 1 < n then
    ((if a.(i) > a.(i + 1) then swap_safe a i (i + 1) else ());
     bubble_pass_safe a (i + 1) n)
  else ()
[@@spec fun a i n ->
  assert (0 <= i);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

(* [k] passes, each shrinking the unsorted prefix by one. *)
let rec bubble_safe (a : int array) (k : int) : unit =
  if k > 0 then
    (bubble_pass_safe a 0 k;
     bubble_safe a (k - 1))
  else ()
[@@spec fun a k ->
  assert (k <= Array.length a);
  ret (fun r -> assert (true))];;

let bubblesort_safe (a : int array) : unit =
  bubble_safe a (Array.length a)
[@@spec fun a -> ret (fun r -> assert (true))];;
