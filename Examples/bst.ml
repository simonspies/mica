open Mica

(* Binary search trees with a sortedness invariant.

   Representation: a raw recursive tree, [Leaf | Node (value, left, right)],
   packaged in a public handle

     Bst (lo, tree, hi)

   whose inclusive interval [lo, hi] encloses every value in the tree.  The
   invariant is the recursive specification function [sorted (tree, lo, hi)]
   — every value lies in [lo, hi], with the interval tightening at each node
   — and [valid] states it for handles.

   Main functions:
   - [singleton x] — the one-element tree.
   - [insert x h] — insert [x], widening the stored interval as needed;
     preserves [valid].
   - [min h], [max h] — the stored bounds, enclosing every value.

   [widen_tree] is a lemma function: it computes nothing, and its
   postcondition establishes that sortedness survives widening the
   interval. *)

type tree = Leaf | Node of int * tree * tree

type t = Bst of int * tree * int

let min_int (x: int) (y: int) : int =
  if x < y then x else y
[@@spec fun x y ->
  ret (fun result ->
    assert (result <= x);
    assert (result <= y))];;

let max_int (x: int) (y: int) : int =
  if x < y then y else x
[@@spec fun x y ->
  ret (fun result ->
    assert (x <= result);
    assert (y <= result))];;

let rec sorted ((tr : tree), (lo : int), (hi : int)) : bool =
  match tr with
  | Leaf -> true
  | Node (v, l, r) ->
    let right_sorted = sorted (r, v, hi) in
    let left_sorted = sorted (l, lo, v) in
    right_sorted && left_sorted && lo <= v && v <= hi
[@@fn];;

let valid (h: t) : bool =
  match h with
  | Bst (lo, tr, hi) ->
    let ok = sorted (tr, lo, hi) in
    lo <= hi && ok
[@@fn];;

let make_node (v: int) (lo: int) (hi: int) (l: tree) (r: tree) : tree =
  Node (v, l, r)
[@@spec fun v lo hi l r ->
  assert (lo <= v);
  assert (v <= hi);
  let sr = sorted (r, v, hi) in
  assert (sr);
  let sl = sorted (l, lo, v) in
  assert (sl);
  ret (fun result ->
    let st = sorted (result, lo, hi) in
    assert (st))];;

let rec widen_tree (lo: int) (hi: int) (new_lo: int) (new_hi: int) (tr: tree) : unit =
  match tr with
  | Leaf -> ()
  | Node (v, l, r) ->
    assert (new_lo <= v);
    assert (v <= new_hi);
    widen_tree lo v new_lo v l;
    widen_tree v hi v new_hi r
[@@spec fun lo hi new_lo new_hi tr ->
  assert (new_lo <= lo);
  assert (hi <= new_hi);
  let st = sorted (tr, lo, hi) in
  assert (st);
  ret (fun result ->
    let sr = sorted (tr, new_lo, new_hi) in
    assert (sr))];;

let rec insert_raw (x: int) (lo: int) (hi: int) (tr: tree) : tree =
  match tr with
  | Leaf -> Node (x, Leaf, Leaf)
  | Node (v, l, r) ->
    if x < v then make_node v lo hi (insert_raw x lo v l) r
    else if v < x then make_node v lo hi l (insert_raw x v hi r)
    else tr
[@@spec fun x lo hi tr ->
  assert (lo <= x);
  assert (x <= hi);
  let st = sorted (tr, lo, hi) in
  assert (st);
  ret (fun result ->
    let sr = sorted (result, lo, hi) in
    assert (sr))];;

let singleton (x: int) : t =
  Bst (x, Node (x, Leaf, Leaf), x)
[@@spec fun x ->
  ret (fun result ->
    let vr = valid result in
    assert (vr))];;

let insert (x: int) (h: t) : t =
  match h with
  | Bst (lo, tr, hi) ->
    let new_lo = min_int x lo in
    let new_hi = max_int x hi in
    widen_tree lo hi new_lo new_hi tr;
    Bst (new_lo, insert_raw x new_lo new_hi tr, new_hi)
[@@spec fun x h ->
  let vh = valid h in
  assert (vh);
  ret (fun result ->
    let vr = valid result in
    assert (vr))];;

let min (h: t) : int =
  match h with
  | Bst (lo, tr, hi) -> lo
[@@spec fun h ->
  let vh = valid h in
  assert (vh);
  bind (isinj 0 1 h) @@ fun ((lo : int), (tr : tree), (hi : int)) ->
  ret (fun result ->
    assert (result = lo))];;

let max (h: t) : int =
  match h with
  | Bst (lo, tr, hi) -> hi
[@@spec fun h ->
  let vh = valid h in
  assert (vh);
  bind (isinj 0 1 h) @@ fun ((lo : int), (tr : tree), (hi : int)) ->
  ret (fun result ->
    assert (result = hi))];;
