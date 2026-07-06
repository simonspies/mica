open Mica

(* In-place partition over a recursive list.

   The input list is pure, but the two output accumulators are owned heap cells.
   Each element is pushed onto exactly one accumulator depending on its sign.
   The spec proves exact final accumulator lengths against [partition_counts],
   a pure recursive relation over `(input, negative_count, nonnegative_count)`.
   It also proves the sign invariant for both output lists. *)


type ilist = Nil | Cons of int * ilist

let rec length (xs : ilist) : int =
  match xs with
  | Nil -> 0
  | Cons (x, rest) -> 1 + length rest
[@@fn];;

let rec all_neg (xs : ilist) : bool =
  match xs with
  | Nil -> true
  | Cons (x, rest) -> x < 0 && all_neg rest
[@@fn];;

let rec all_nonneg (xs : ilist) : bool =
  match xs with
  | Nil -> true
  | Cons (x, rest) -> x >= 0 && all_nonneg rest
[@@fn];;

let empty (unused : int) : ilist =
  Nil
[@@spec fun unused ->
  ret (fun result ->
    assert (all_neg result);
    assert (all_nonneg result);
    assert (length result = 0))];;

let rec partition_counts ((xs : ilist), (neg_len : int), (nonneg_len : int)) : int * int =
  match xs with
  | Nil -> (neg_len, nonneg_len)
  | Cons (x, rest) ->
    if x < 0 then
      partition_counts (rest, neg_len + 1, nonneg_len)
    else
      partition_counts (rest, neg_len, nonneg_len + 1)
[@@fn];;

let rec partition_into
    (xs : ilist) (neg : ilist ref [@owned]) (nonneg : ilist ref [@owned]) : unit =
  match xs with
  | Nil -> ()
  | Cons (x, rest) ->
    if x < 0 then
      neg := Cons (x, !neg)
    else
      nonneg := Cons (x, !nonneg);
    partition_into rest neg nonneg
[@@spec fun xs neg nonneg ->
  bind (own neg) @@ fun (start_neg : ilist) ->
  bind (own nonneg) @@ fun (start_nonneg : ilist) ->
  let start_neg_len = length start_neg in
  let start_nonneg_len = length start_nonneg in
  assert (all_neg start_neg);
  assert (all_nonneg start_nonneg);
  ret (fun result ->
    bind (own neg) @@ fun (final_neg : ilist) ->
    bind (own nonneg) @@ fun (final_nonneg : ilist) ->
	    let expected =
	      partition_counts (xs, start_neg_len, start_nonneg_len) in
	    let ((expected_neg : int), (expected_nonneg : int)) = expected in
	    assert (all_neg final_neg);
	    assert (all_nonneg final_nonneg);
	    assert (length final_neg = expected_neg);
	    assert (length final_nonneg = expected_nonneg))];;

let partition (xs : ilist) : ilist * ilist =
  let neg = ref (empty 0) [@owned] in
  let nonneg = ref (empty 0) [@owned] in
  partition_into xs neg nonneg;
  (!neg, !nonneg)
[@@spec fun xs ->
	  ret (fun ((neg : ilist), (nonneg : ilist)) ->
	    let expected = partition_counts (xs, 0, 0) in
	    let ((expected_neg : int), (expected_nonneg : int)) = expected in
	    assert (all_neg neg);
	    assert (all_nonneg nonneg);
	    assert (length neg = expected_neg);
	    assert (length nonneg = expected_nonneg))];;
