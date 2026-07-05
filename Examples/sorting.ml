open Mica

(* In-place sorting and binary search over shared (unowned) [int array]s.

   Arrays expose only their length at the spec level; element contents are not
   value-tracked in shared arrays.  So the *functional* specs below are trivial
   ([assert true]). What the verifier still has to discharge — for every single
   [a.(i)] read and [a.(i) <- v] write, and every [Array.make] — is the
   in-bounds / nonnegative-length side condition. *)


(* Shared swap.  Both indices must be in bounds; the spec records that as a
   precondition the callers below are obliged to establish. *)
let swap (a : int array) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  assert (0 <= i && i < Array.length a);
  assert (0 <= j && j < Array.length a);
  ret (fun r -> assert (true))];;


(* ---------------------------------------------------------------------- *)
(* Bubble sort                                                            *)
(* ---------------------------------------------------------------------- *)

(* One left-to-right pass bubbling the largest element of [a.(0 .. n-1)] to
   position [n-1].  Reads [a.(i)] and [a.(i+1)]; the guard [i + 1 < n] together
   with [n <= length a] keeps both in bounds. *)
let rec bubble_pass (a : int array) (i : int) (n : int) : unit =
  if i + 1 < n then
    ((if a.(i) > a.(i + 1) then swap a i (i + 1) else ());
     bubble_pass a (i + 1) n)
  else ()
[@@spec fun a i n ->
  assert (0 <= i);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

(* [k] passes, each shrinking the unsorted prefix by one. *)
let rec bubble (a : int array) (k : int) : unit =
  if k > 0 then
    (bubble_pass a 0 k;
     bubble a (k - 1))
  else ()
[@@spec fun a k ->
  assert (k <= Array.length a);
  ret (fun r -> assert (true))];;

let bubblesort (a : int array) : unit =
  bubble a (Array.length a)
[@@spec fun a -> ret (fun r -> assert (true))];;


(* ---------------------------------------------------------------------- *)
(* Insertion sort                                                         *)
(* ---------------------------------------------------------------------- *)

(* Shift [a.(j)] left into the sorted prefix by adjacent swaps. *)
let rec shift_down (a : int array) (j : int) : unit =
  if j > 0 then
    (if a.(j - 1) > a.(j) then
       (swap a (j - 1) j;
        shift_down a (j - 1))
     else ())
  else ()
[@@spec fun a j ->
  assert (0 <= j);
  assert (j < Array.length a);
  ret (fun r -> assert (true))];;

(* Insert [a.(i)] for increasing [i], growing the sorted prefix [a.(0 .. i-1)]. *)
let rec insert_from (a : int array) (i : int) (n : int) : unit =
  if i < n then
    (shift_down a i;
     insert_from a (i + 1) n)
  else ()
[@@spec fun a i n ->
  assert (0 <= i);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

let insertionsort (a : int array) : unit =
  insert_from a 1 (Array.length a)
[@@spec fun a -> ret (fun r -> assert (true))];;


(* ---------------------------------------------------------------------- *)
(* Quicksort (in-place)                                                   *)
(* ---------------------------------------------------------------------- *)

(* Quicksort with pivot [a.(hi)].  [i] marks the boundary of the "<= pivot"
   region, [j] is the scan cursor.  Invariant [i <= j <= hi] with [0 <= i] keeps
   every access in range.  The returned index is bounded by [0 <= result <= hi],
   which the recursive quicksort calls rely on. *)
let rec partition_lo
    (a : int array) (hi : int) (pivot : int) (i : int) (j : int) : int =
  if j < hi then
    (if a.(j) <= pivot then
       (swap a i j;
        partition_lo a hi pivot (i + 1) (j + 1))
     else
       partition_lo a hi pivot i (j + 1))
  else
    (swap a i hi;
     i)
[@@spec fun a hi pivot i j ->
  assert (0 <= i);
  assert (i <= j);
  assert (j <= hi);
  assert (hi < Array.length a);
  ret (fun result ->
    assert (0 <= result);
    assert (result <= hi))];;

let rec qsort (a : int array) (lo : int) (hi : int) : unit =
  if lo < hi then
    (let pivot = a.(hi) in
     let p = partition_lo a hi pivot lo lo in
     qsort a lo (p - 1);
     qsort a (p + 1) hi)
  else ()
[@@spec fun a lo hi ->
  assert (0 <= lo);
  assert (hi < Array.length a);
  ret (fun r -> assert (true))];;

let quicksort (a : int array) : unit =
  qsort a 0 (Array.length a - 1)
[@@spec fun a -> ret (fun r -> assert (true))];;


(* ---------------------------------------------------------------------- *)
(* Merge sort                                                             *)
(* ---------------------------------------------------------------------- *)

(* Merge the sorted runs [a.(lo .. mid-1)] and [a.(mid .. hi-1)] into
   [tmp.(lo .. hi-1)].  Cursors [i], [j], [k] satisfy the linear invariant
   [k = i + j - mid], which is what lets the verifier prove the write target
   [tmp.(k)] and both reads stay in bounds even when one run is exhausted.
   The "exhausted" cases are split into explicit [if] guards (rather than a
   [&&]/[||] condition) so that no [a.(i)]/[a.(j)] read is evaluated once its
   cursor has run off the end of its run. *)
let rec merge
    (a : int array) (tmp : int array)
    (lo : int) (mid : int) (hi : int) (i : int) (j : int) (k : int) : unit =
  if k < hi then
    (if i >= mid then
       (* left run exhausted: take from the right *)
       (tmp.(k) <- a.(j);
        merge a tmp lo mid hi i (j + 1) (k + 1))
     else if j >= hi then
       (* right run exhausted: take from the left *)
       (tmp.(k) <- a.(i);
        merge a tmp lo mid hi (i + 1) j (k + 1))
     else if a.(i) <= a.(j) then
       (tmp.(k) <- a.(i);
        merge a tmp lo mid hi (i + 1) j (k + 1))
     else
       (tmp.(k) <- a.(j);
        merge a tmp lo mid hi i (j + 1) (k + 1)))
  else ()
[@@spec fun a tmp lo mid hi i j k ->
  assert (0 <= lo && lo <= i && i <= mid && mid <= j && j <= hi && hi <= Array.length a);
  assert (k = i + j - mid);
  assert (lo <= k && k <= hi);
  assert (hi <= Array.length tmp);
  ret (fun r -> assert (true))];;

(* Copy [tmp.(lo .. hi-1)] back over [a.(lo .. hi-1)]. *)
let rec copy_back
    (a : int array) (tmp : int array) (k : int) (hi : int) : unit =
  if k < hi then
    (a.(k) <- tmp.(k);
     copy_back a tmp (k + 1) hi)
  else ()
[@@spec fun a tmp k hi ->
  assert (0 <= k);
  assert (hi <= Array.length a);
  assert (hi <= Array.length tmp);
  ret (fun r -> assert (true))];;

let rec msort
    (a : int array) (tmp : int array) (lo : int) (hi : int) : unit =
  if hi - lo > 1 then
    (let mid = lo + (hi - lo) / 2 in
     msort a tmp lo mid;
     msort a tmp mid hi;
     merge a tmp lo mid hi lo mid lo;
     copy_back a tmp lo hi)
  else ()
[@@spec fun a tmp lo hi ->
  assert (0 <= lo && lo <= hi && hi <= Array.length a);
  assert (hi <= Array.length tmp);
  ret (fun r -> assert (true))];;

let mergesort (a : int array) : unit =
  let n = Array.length a in
  let tmp = Array.make n 0 in
  msort a tmp 0 n
[@@spec fun a -> ret (fun r -> assert (true))];;


(* ---------------------------------------------------------------------- *)
(* Binary search                                                          *)
(* ---------------------------------------------------------------------- *)

(* Search [a.(lo .. hi)] (inclusive bounds) for [x], returning a matching index
   or [-1].  The midpoint [lo + (hi - lo) / 2] must be shown in range: under the
   guard [lo <= hi] it lies in [lo, hi], and the precondition [hi < length a]
   then discharges the read at [a.(mid)].  Each recursive call shrinks the
   window to one side of [mid] while preserving [0 <= lo] and [hi < length a]. *)
let rec bsearch (a : int array) (x : int) (lo : int) (hi : int) : int =
  if lo > hi then -1
  else
    let mid = lo + (hi - lo) / 2 in
    let v = a.(mid) in
    if v = x then mid
    else if v < x then bsearch a x (mid + 1) hi
    else bsearch a x lo (mid - 1)
[@@spec fun a x lo hi ->
  assert (0 <= lo);
  assert (hi < Array.length a);
  ret (fun r -> assert (true))];;

let binary_search (a : int array) (x : int) : int =
  bsearch a x 0 (Array.length a - 1)
[@@spec fun a x -> ret (fun r -> assert (true))];;


(* ---------------------------------------------------------------------- *)
(* In-place reverse                                                       *)
(* ---------------------------------------------------------------------- *)

(* Reverse [a.(i .. j)] by swapping the ends and walking the cursors inward.
   The symmetric invariant [0 <= i] and [j < length a] makes both swap indices
   in range; each step preserves it for [(i+1, j-1)]. *)
let rec rev (a : int array) (i : int) (j : int) : unit =
  if i < j then
    (swap a i j;
     rev a (i + 1) (j - 1))
  else ()
[@@spec fun a i j ->
  assert (0 <= i);
  assert (j < Array.length a);
  ret (fun r -> assert (true))];;

let reverse (a : int array) : unit =
  rev a 0 (Array.length a - 1)
[@@spec fun a -> ret (fun r -> assert (true))];;
