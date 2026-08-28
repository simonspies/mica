open Mica

(* Binary min-heap embedded in the prefix [a.(0 .. n-1)] of an [int array]:
   the safety variant.  Shared arrays expose only their length in
   specifications, so the verified property is that every access is in
   bounds — in particular the child index computations [2*i + 1]/[2*i + 2]
   and the parent index [(i - 1) / 2].  There is no functional-correctness
   variant yet. *)

(* Swap [a.(i)] and [a.(j)]. *)
let swap_safe (a : int array) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  assert (0 <= i && i < Array.length a);
  assert (0 <= j && j < Array.length a);
  ret (fun r -> assert (true))];;

(* Move [a.(i)] up toward the root while it is below its parent. *)
let rec sift_up_safe (a : int array) (i : int) : unit =
  if i > 0 then
    (let p = (i - 1) / 2 in
     if a.(i) < a.(p) then
       (swap_safe a i p;
        sift_up_safe a p)
     else ())
  else ()
[@@spec fun a i ->
  assert (0 <= i && i < Array.length a);
  ret (fun r -> assert (true))];;

(* Move [a.(i)] down into the heap prefix [a.(0 .. n-1)] while a child is
   smaller. *)
let rec sift_down_safe (a : int array) (i : int) (n : int) : unit =
  let l = 2 * i + 1 in
  let r = 2 * i + 2 in
  let m = if l < n then (if a.(l) < a.(i) then l else i) else i in
  let m = if r < n then (if a.(r) < a.(m) then r else m) else m in
  if m > i then
    (swap_safe a i m;
     sift_down_safe a m n)
  else ()
[@@spec fun a i n ->
  assert (0 <= i && i < n);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

(* Insert [x] into the heap prefix [a.(0 .. n-1)], growing it by one. *)
let insert_safe (a : int array) (n : int) (x : int) : unit =
  a.(n) <- x;
  sift_up_safe a n
[@@spec fun a n x ->
  assert (0 <= n && n < Array.length a);
  ret (fun r -> assert (true))];;

(* Remove and return the root of the heap prefix [a.(0 .. n-1)], shrinking
   it by one. *)
let extract_min_safe (a : int array) (n : int) : int =
  let x = a.(0) in
  a.(0) <- a.(n - 1);
  (if n > 1 then sift_down_safe a 0 (n - 1) else ());
  x
[@@spec fun a n ->
  assert (0 < n && n <= Array.length a);
  ret (fun r -> assert (true))];;

(* Establish the heap property on [a.(0 .. n-1)] bottom-up (Floyd), sifting
   down each internal node from the last to the root. *)
let rec heapify_from_safe (a : int array) (i : int) (n : int) : unit =
  if i >= 0 then
    (sift_down_safe a i n;
     heapify_from_safe a (i - 1) n)
  else ()
[@@spec fun a i n ->
  assert (i < n);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

let heapify_safe (a : int array) (n : int) : unit =
  heapify_from_safe a (n / 2 - 1) n
[@@spec fun a n ->
  assert (0 <= n && n <= Array.length a);
  ret (fun r -> assert (true))];;

(* Heapsort: repeatedly swap the root to the end of the shrinking heap
   prefix [a.(0 .. s-1)] and sift the new root down. *)
let rec sort_down_safe (a : int array) (s : int) : unit =
  if s > 1 then
    (swap_safe a 0 (s - 1);
     sift_down_safe a 0 (s - 1);
     sort_down_safe a (s - 1))
  else ()
[@@spec fun a s ->
  assert (s <= Array.length a);
  ret (fun r -> assert (true))];;

let heapsort_safe (a : int array) : unit =
  heapify_safe a (Array.length a);
  sort_down_safe a (Array.length a)
[@@spec fun a -> ret (fun r -> assert (true))];;
