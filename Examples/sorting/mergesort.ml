open Mica

(* Merge sort.  The array variants merge the sorted halves into a buffer [tmp]
   and copy back.  The list variant splits into alternate elements. *)


(* -------------------------------------------------------------------- *)
(* Functional correctness                                               *)
(* -------------------------------------------------------------------- *)

(* Merge the sorted runs [a.(lo .. mid-1)] and [a.(mid .. hi-1)] into
   [tmp.(lo .. hi-1)], with read cursors [i], [j] and write cursor [k].  The
   output written so far is sorted and at most the head of each run.  The
   exhausted-run cases are separate [if]s because [&&] and [||] evaluate both
   operands, which would read past the end of a run. *)
let rec merge
    (a : int array [@owned]) (tmp : int array [@owned])
    (mid : int) (hi : int) (i : int) (j : int) (k : int) : unit =
  if k < hi then
    (if i >= mid then
       (tmp.(k) <- a.(j);
        (merge a tmp mid hi i (j + 1) (k + 1) [@ghost lo]))
     else if j >= hi then
       (tmp.(k) <- a.(i);
        (merge a tmp mid hi (i + 1) j (k + 1) [@ghost lo]))
     else if a.(i) <= a.(j) then
       (tmp.(k) <- a.(i);
        (merge a tmp mid hi (i + 1) j (k + 1) [@ghost lo]))
     else
       (tmp.(k) <- a.(j);
        (merge a tmp mid hi i (j + 1) (k + 1) [@ghost lo])))
  else ()
[@@spec fun a tmp mid hi i j k ->
  bind (arr a) @@ fun (v : int vec) ->
  bind (arr tmp) @@ fun (t : int vec) ->
  assert (0 <= lo && lo <= i && i <= mid && mid <= j && j <= hi && hi <= Vec.length v);
  assert (k = i + j - mid);
  assert (hi <= Vec.length t);
  assert (Range.all lo mid (fun (p : int) : bool ->
            Range.all lo mid (fun (q : int) : bool ->
              if p <= q then Vec.get v p <= Vec.get v q else true)));
  assert (Range.all mid hi (fun (p : int) : bool ->
            Range.all mid hi (fun (q : int) : bool ->
              if p <= q then Vec.get v p <= Vec.get v q else true)));
  assert (Range.all lo k (fun (p : int) : bool ->
            Range.all lo k (fun (q : int) : bool ->
              if p <= q then Vec.get t p <= Vec.get t q else true)));
  assert (Range.all lo k (fun (q : int) : bool ->
            (if i < mid then Vec.get t q <= Vec.get v i else true) &&
            (if j < hi then Vec.get t q <= Vec.get v j else true)));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    bind (arr tmp) @@ fun (u : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Vec.length u = Vec.length t);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              Vec.get w q = Vec.get v q));
    assert (Range.all lo hi (fun (p : int) : bool ->
              Range.all lo hi (fun (q : int) : bool ->
                if p <= q then Vec.get u p <= Vec.get u q else true))))]
[@@ghost (lo : int)];;

(* Copy [tmp.(k .. hi-1)] back over [a.(k .. hi-1)]. *)
let rec copy_back
    (a : int array [@owned]) (tmp : int array [@owned]) (k : int) (hi : int) : unit =
  if k < hi then
    (a.(k) <- tmp.(k);
     copy_back a tmp (k + 1) hi)
  else ()
[@@spec fun a tmp k hi ->
  bind (arr a) @@ fun (v : int vec) ->
  bind (arr tmp) @@ fun (t : int vec) ->
  assert (0 <= k && hi <= Vec.length v && hi <= Vec.length t);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    bind (arr tmp) @@ fun (u : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Vec.length u = Vec.length t);
    assert (Range.all 0 (Vec.length t) (fun (q : int) : bool ->
              Vec.get u q = Vec.get t q));
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              if k <= q && q < hi then Vec.get w q = Vec.get t q
              else Vec.get w q = Vec.get v q)))];;

(* Sort [a.(lo .. hi-1)], using [tmp.(lo .. hi-1)] as scratch space. *)
let rec msort
    (a : int array [@owned]) (tmp : int array [@owned]) (lo : int) (hi : int) : unit =
  if hi - lo > 1 then
    (let mid = lo + (hi - lo) / 2 in
     msort a tmp lo mid;
     msort a tmp mid hi;
     (merge a tmp mid hi lo mid lo [@ghost lo]);
     copy_back a tmp lo hi)
  else ()
[@@spec fun a tmp lo hi ->
  bind (arr a) @@ fun (v : int vec) ->
  bind (arr tmp) @@ fun (t : int vec) ->
  assert (0 <= lo && lo <= hi && hi <= Vec.length v);
  assert (hi <= Vec.length t);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    bind (arr tmp) @@ fun (u : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Vec.length u = Vec.length t);
    assert (Range.all lo hi (fun (p : int) : bool ->
              Range.all lo hi (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true)));
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              if lo <= q && q < hi then true else Vec.get w q = Vec.get v q)))];;

let mergesort (a : int array [@owned]) : unit =
  let n = Array.length a in
  let tmp = Array.make n 0 [@owned] in
  msort a tmp 0 n
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

(* Merge [a.(lo .. mid-1)] and [a.(mid .. hi-1)] into [tmp.(lo .. hi-1)]. *)
let rec merge_safe
    (a : int array) (tmp : int array)
    (mid : int) (hi : int) (i : int) (j : int) (k : int) : unit =
  if k < hi then
    (if i >= mid then
       (tmp.(k) <- a.(j);
        merge_safe a tmp mid hi i (j + 1) (k + 1))
     else if j >= hi then
       (tmp.(k) <- a.(i);
        merge_safe a tmp mid hi (i + 1) j (k + 1))
     else if a.(i) <= a.(j) then
       (tmp.(k) <- a.(i);
        merge_safe a tmp mid hi (i + 1) j (k + 1))
     else
       (tmp.(k) <- a.(j);
        merge_safe a tmp mid hi i (j + 1) (k + 1)))
  else ()
[@@spec fun a tmp mid hi i j k ->
  assert (0 <= i && i <= mid && mid <= j && j <= hi && hi <= Array.length a);
  assert (k = i + j - mid);
  assert (hi <= Array.length tmp);
  ret (fun r -> assert (true))];;

(* Copy [tmp.(k .. hi-1)] back over [a.(k .. hi-1)]. *)
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
     merge_safe a tmp mid hi lo mid lo;
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


(* -------------------------------------------------------------------- *)
(* List variant                                                         *)
(* -------------------------------------------------------------------- *)

(* Adjacent elements are in order. *)
let rec sorted (l : int list) : bool =
  match l with
  | [] -> true
  | x :: rest ->
    (match rest with
     | [] -> true
     | y :: _ -> x <= y) && sorted rest
[@@fn];;

(* The elements at even and at odd positions. *)
let rec split_list (l : int list) : int list * int list =
  match l with
  | [] -> ([], [])
  | x :: rest ->
    (match rest with
     | [] -> ([x], [])
     | y :: rest2 ->
       let (xs, ys) = split_list rest2 in
       (x :: xs, y :: ys))
[@@spec fun l -> ret (fun r -> assert (true))];;

(* The ghost [b] is a lower bound on both inputs, which carries over to the
   result.  The recursive calls pass the element they put in front. *)
let rec merge_list (l1 : int list) (l2 : int list) : int list =
  match l1 with
  | [] -> l2
  | x :: rest1 ->
    (match l2 with
     | [] -> l1
     | y :: rest2 ->
       if x <= y then x :: (merge_list rest1 l2 [@ghost x])
       else y :: (merge_list l1 rest2 [@ghost y]))
[@@spec fun l1 l2 ->
  assert (sorted l1);
  assert (sorted l2);
  ret (fun r ->
    assert (sorted r);
    assert (if sorted (b :: l1) && sorted (b :: l2) then sorted (b :: r) else true))]
[@@ghost (b : int)];;

let rec mergesort_list (l : int list) : int list =
  match l with
  | [] -> []
  | _ :: rest ->
    (match rest with
     | [] -> l
     | _ :: _ ->
       let (xs, ys) = split_list l in
       (* This caller does not use the bound, so any [b] will do. *)
       (merge_list (mergesort_list xs) (mergesort_list ys) [@ghost 0]))
[@@spec fun l -> ret (fun r -> assert (sorted r))];;
