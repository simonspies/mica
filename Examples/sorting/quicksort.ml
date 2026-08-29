open Mica

(* In-place quicksort (Lomuto partition scheme), in a functional-correctness
   variant and a safety variant, for comparison.  Both partition the window
   around the pivot [a.(hi)] and recurse on both halves, with the same body.

   Functional correctness ([quicksort], owned array): the specification binds
   the array contents as an [int vec], and the postcondition states that the
   final contents are sorted, as a bounded quantifier over index pairs.  The
   parameters [blo] and [bhi] are ghost: they carry the bounds that
   partitioning establishes into the recursive calls.  Without them the two
   sorted halves do not combine into a sorted whole.

   Safety ([quicksort_safe], shared array): shared arrays expose only their
   length in specifications, so the verified property is that every read,
   write, and swap index stays in bounds. *)


(* -------------------------------------------------------------------- *)
(* Functional correctness                                               *)
(* -------------------------------------------------------------------- *)

(* Swap [a.(i)] and [a.(j)]; the postcondition gives the two new elements and
   the frame (all other positions unchanged). *)
let swap (a : int array [@owned]) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= i && i < Vec.length v);
  assert (0 <= j && j < Vec.length v);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Vec.get w i = Vec.get v j);
    assert (Vec.get w j = Vec.get v i);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
      if not (q = i) && not (q = j) then Vec.get w q = Vec.get v q else true)))];;

(* Lomuto partition of the window [lo, hi] around the pivot [a.(hi)]: [i] marks
   the boundary of the "<= pivot" region, [j] is the scan cursor.  Returns the
   pivot's final index, elements no greater than it to its left, and greater
   elements to its right. *)
let rec partition (a : int array [@owned]) (lo : int) (hi : int) (i : int) (j : int)
    (blo : int option) (bhi : int option) : int =
  if j < hi then
    (if a.(j) <= a.(hi) then
       (swap a i j;
        partition a lo hi (i + 1) (j + 1) blo bhi)
     else
       partition a lo hi i (j + 1) blo bhi)
  else
    (swap a i hi;
     i)
[@@spec fun a lo hi i j blo bhi ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= lo && lo <= i && i <= j && j <= hi && hi < Vec.length v);
  assert (Range.all lo i (fun (q : int) : bool -> Vec.get v q <= Vec.get v hi));
  assert (Range.all i j (fun (q : int) : bool -> Vec.get v hi < Vec.get v q));
  assert (match blo with
          | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> b <= Vec.get v q)
          | None -> true);
  assert (match bhi with
          | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> Vec.get v q <= b)
          | None -> true);
  ret (fun p ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (lo <= p && p <= hi);
    assert (Range.all lo (hi + 1) (fun (q : int) : bool ->
              if q < p then Vec.get w q <= Vec.get w p
              else Vec.get w p <= Vec.get w q));
    assert (match blo with
            | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> b <= Vec.get w q)
            | None -> true);
    assert (match bhi with
            | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> Vec.get w q <= b)
            | None -> true);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              if q < lo || hi < q then Vec.get w q = Vec.get v q else true)))];;

(* Sort the window [lo, hi].  [blo] ([bhi]), when present, bounds the window's
   contents from below (above), before and after. *)
let rec qsort (a : int array [@owned]) (lo : int) (hi : int)
    (blo : int option) (bhi : int option) : unit =
  if lo < hi then
    (let p = partition a lo hi lo lo blo bhi in
     let y = a.(p) in
     qsort a lo (p - 1) blo (Some y);
     qsort a (p + 1) hi (Some y) bhi)
  else ()
[@@spec fun a lo hi blo bhi ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= lo && hi < Vec.length v);
  assert (match blo with
          | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> b <= Vec.get v q)
          | None -> true);
  assert (match bhi with
          | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> Vec.get v q <= b)
          | None -> true);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all lo (hi + 1) (fun (p : int) : bool ->
              Range.all lo (hi + 1) (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true)));
    assert (match blo with
            | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> b <= Vec.get w q)
            | None -> true);
    assert (match bhi with
            | Some b -> Range.all lo (hi + 1) (fun (q : int) : bool -> Vec.get w q <= b)
            | None -> true);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              if q < lo || hi < q then Vec.get w q = Vec.get v q else true)))];;

let quicksort (a : int array [@owned]) : unit =
  qsort a 0 (Array.length a - 1) None None
[@@spec fun a ->
  bind (arr a) @@ fun (v : int vec) ->
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 (Vec.length w) (fun (p : int) : bool ->
              Range.all 0 (Vec.length w) (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true))))];;


(* -------------------------------------------------------------------- *)
(* Safety variant                                                       *)
(* -------------------------------------------------------------------- *)

(* Swap [a.(i)] and [a.(j)]. *)
let swap_safe (a : int array) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  assert (0 <= i && i < Array.length a);
  assert (0 <= j && j < Array.length a);
  ret (fun r -> assert (true))];;

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
