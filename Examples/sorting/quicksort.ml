open Mica

(* Quicksort.  The array variants use the Lomuto scheme with the pivot
   [a.(hi)].  The list variant partitions around the head and sorts onto an
   accumulator, which avoids list append. *)


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
let rec partition (a : int array [@owned]) (hi : int) (i : int) (j : int) : int =
  if j < hi then
    (if a.(j) <= a.(hi) then
       (swap a i j;
        (partition a hi (i + 1) (j + 1) [@ghost lo blo bhi]))
     else
       (partition a hi i (j + 1) [@ghost lo blo bhi]))
  else
    (swap a i hi;
     i)
[@@spec fun a hi i j ->
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
              if q < lo || hi < q then Vec.get w q = Vec.get v q else true)))]
[@@ghost (lo : int) (blo : int option) (bhi : int option)];;

(* Sort the window [lo, hi].  The ghost [blo] ([bhi]), when present, bounds
   the window from below (above), before and after.  Without these bounds the
   two sorted halves do not combine into a sorted whole.  The pivot value comes
   from a ghost read. *)
let rec qsort (a : int array [@owned]) (lo : int) (hi : int) : unit =
  if lo < hi then
    (let p = (partition a hi lo lo [@ghost lo blo bhi]) in
     let%ghost y = a.(p) in
     (qsort a lo (p - 1) [@ghost blo (Some y)]);
     (qsort a (p + 1) hi [@ghost (Some y) bhi]))
  else ()
[@@spec fun a lo hi ->
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
              if q < lo || hi < q then Vec.get w q = Vec.get v q else true)))]
[@@ghost (blo : int option) (bhi : int option)];;

let quicksort (a : int array [@owned]) : unit =
  (qsort a 0 (Array.length a - 1) [@ghost None None])
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

let rec partition_safe (a : int array) (hi : int) (i : int) (j : int) : int =
  if j < hi then
    (if a.(j) <= a.(hi) then
       (swap_safe a i j;
        partition_safe a hi (i + 1) (j + 1))
     else
       partition_safe a hi i (j + 1))
  else
    (swap_safe a i hi;
     i)
[@@spec fun a hi i j ->
  assert (0 <= i);
  assert (i <= j);
  assert (j <= hi);
  assert (hi < Array.length a);
  ret (fun result ->
    assert (0 <= result);
    assert (result <= hi))];;

let rec qsort_safe (a : int array) (lo : int) (hi : int) : unit =
  if lo < hi then
    (let p = partition_safe a hi lo lo in
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

(* Every element of [l] is at least [b]. *)
let rec all_ge ((l : int list), (b : int)) : bool =
  match l with
  | [] -> true
  | x :: rest -> b <= x && all_ge (rest, b)
[@@fn];;

(* Every element of [l] is at most [c]. *)
let rec all_le ((l : int list), (c : int)) : bool =
  match l with
  | [] -> true
  | x :: rest -> x <= c && all_le (rest, c)
[@@fn];;

(* Every element of [l] is at most every element of the sorted list [acc]. *)
let bounded ((l : int list), (acc : int list)) : bool =
  match acc with
  | [] -> true
  | y :: _ -> all_le (l, y)
[@@fn];;

(* The ghosts [b] and [acc] are a lower and an upper bound, which carry over
   to both parts. *)
let rec partition_list (p : int) (l : int list) : int list * int list =
  match l with
  | [] -> ([], [])
  | x :: rest ->
    let (lo, hi) = (partition_list p rest [@ghost b acc]) in
    if x <= p then (x :: lo, hi) else (lo, x :: hi)
[@@spec fun p l ->
  ret (fun ((lo : int list), (hi : int list)) ->
    assert (all_le (lo, p));
    assert (all_ge (hi, p));
    assert (if all_ge (l, b) then all_ge (lo, b) && all_ge (hi, b) else true);
    assert (if bounded (l, acc) then bounded (lo, acc) && bounded (hi, acc) else true))]
[@@ghost (b : int) (acc : int list)];;

(* Sort [l] onto the front of [acc]. *)
let rec qsort_list (l : int list) (acc : int list) : int list =
  match l with
  | [] -> acc
  | x :: rest ->
    let (lo, hi) = (partition_list x rest [@ghost b acc]) in
    (qsort_list lo (x :: (qsort_list hi acc [@ghost x])) [@ghost b])
[@@spec fun l acc ->
  assert (sorted acc);
  assert (bounded (l, acc));
  ret (fun r ->
    assert (sorted r);
    assert (if all_ge (l, b) && sorted (b :: acc) then sorted (b :: r) else true))]
[@@ghost (b : int)];;

(* This caller does not use the bound, so any [b] will do. *)
let quicksort_list (l : int list) : int list = (qsort_list l [] [@ghost 0])
[@@spec fun l -> ret (fun r -> assert (sorted r))];;
