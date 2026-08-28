open Mica

(* Merge sort over a shared [int array], with an explicit temporary buffer:
   recursive splitting, merging the sorted runs into [tmp], and copying back.

   Shared arrays expose only their length in specifications, so the verified
   property is that every read and write index stays in bounds — including the
   merge cursors, which the spec ties together with the linear relation
   [k = i + j - mid]. *)

(* Merge the sorted runs [a.(lo .. mid-1)] and [a.(mid .. hi-1)] into
   [tmp.(lo .. hi-1)], with read cursors [i], [j] and write cursor [k].  The
   "run exhausted" cases are split into explicit [if] guards, rather than a
   [&&]/[||] condition, so that no [a.(i)]/[a.(j)] read is evaluated once its
   cursor has run off the end of its run. *)
let rec merge_safe
    (a : int array) (tmp : int array)
    (lo : int) (mid : int) (hi : int) (i : int) (j : int) (k : int) : unit =
  if k < hi then
    (if i >= mid then
       (* left run exhausted: take from the right *)
       (tmp.(k) <- a.(j);
        merge_safe a tmp lo mid hi i (j + 1) (k + 1))
     else if j >= hi then
       (* right run exhausted: take from the left *)
       (tmp.(k) <- a.(i);
        merge_safe a tmp lo mid hi (i + 1) j (k + 1))
     else if a.(i) <= a.(j) then
       (tmp.(k) <- a.(i);
        merge_safe a tmp lo mid hi (i + 1) j (k + 1))
     else
       (tmp.(k) <- a.(j);
        merge_safe a tmp lo mid hi i (j + 1) (k + 1)))
  else ()
[@@spec fun a tmp lo mid hi i j k ->
  assert (0 <= lo && lo <= i && i <= mid && mid <= j && j <= hi && hi <= Array.length a);
  assert (k = i + j - mid);
  assert (lo <= k && k <= hi);
  assert (hi <= Array.length tmp);
  ret (fun r -> assert (true))];;

(* Copy [tmp.(lo .. hi-1)] back over [a.(lo .. hi-1)]. *)
let rec copy_back_safe
    (a : int array) (tmp : int array) (k : int) (hi : int) : unit =
  if k < hi then
    (a.(k) <- tmp.(k);
     copy_back_safe a tmp (k + 1) hi)
  else ()
[@@spec fun a tmp k hi ->
  assert (0 <= k);
  assert (hi <= Array.length a);
  assert (hi <= Array.length tmp);
  ret (fun r -> assert (true))];;

let rec msort_safe
    (a : int array) (tmp : int array) (lo : int) (hi : int) : unit =
  if hi - lo > 1 then
    (let mid = lo + (hi - lo) / 2 in
     msort_safe a tmp lo mid;
     msort_safe a tmp mid hi;
     merge_safe a tmp lo mid hi lo mid lo;
     copy_back_safe a tmp lo hi)
  else ()
[@@spec fun a tmp lo hi ->
  assert (0 <= lo && lo <= hi && hi <= Array.length a);
  assert (hi <= Array.length tmp);
  ret (fun r -> assert (true))];;

let mergesort_safe (a : int array) : unit =
  let n = Array.length a in
  let tmp = Array.make n 0 in
  msort_safe a tmp 0 n
[@@spec fun a -> ret (fun r -> assert (true))];;
