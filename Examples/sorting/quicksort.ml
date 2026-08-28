open Mica

(* In-place quicksort (Lomuto partition scheme) over a shared [int array].

   Shared arrays expose only their length in specifications, so the verified
   property is that every read, write, and swap index stays in bounds — in
   particular that the partition boundary and the returned pivot index stay
   within the window, which the recursive calls rely on. *)

(* Swap [a.(i)] and [a.(j)]. *)
let swap_safe (a : int array) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  assert (0 <= i && i < Array.length a);
  assert (0 <= j && j < Array.length a);
  ret (fun r -> assert (true))];;

(* Lomuto partition of the window [lo, hi] around [pivot]: [i] marks the
   boundary of the "<= pivot" region, [j] is the scan cursor; returns the
   pivot's final index. *)
let rec partition_safe
    (a : int array) (hi : int) (pivot : int) (i : int) (j : int) : int =
  if j < hi then
    (if a.(j) <= pivot then
       (swap_safe a i j;
        partition_safe a hi pivot (i + 1) (j + 1))
     else
       partition_safe a hi pivot i (j + 1))
  else
    (swap_safe a i hi;
     i)
[@@spec fun a hi pivot i j ->
  assert (0 <= i);
  assert (i <= j);
  assert (j <= hi);
  assert (hi < Array.length a);
  ret (fun result ->
    assert (0 <= result);
    assert (result <= hi))];;

let rec qsort_safe (a : int array) (lo : int) (hi : int) : unit =
  if lo < hi then
    (let pivot = a.(hi) in
     let p = partition_safe a hi pivot lo lo in
     qsort_safe a lo (p - 1);
     qsort_safe a (p + 1) hi)
  else ()
[@@spec fun a lo hi ->
  assert (0 <= lo);
  assert (hi < Array.length a);
  ret (fun r -> assert (true))];;

let quicksort_safe (a : int array) : unit =
  qsort_safe a 0 (Array.length a - 1)
[@@spec fun a -> ret (fun r -> assert (true))];;
