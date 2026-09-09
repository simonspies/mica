open Mica

(* AVL trees: self-balancing binary search trees with cached heights.

   Representation: each internal node stores its value and cached height,

     Node (value, height, left, right)

   packaged in a public handle [Avl (lo, tree, hi)] whose inclusive interval
   encloses every value.  The invariant [avl_tree_inv (tree, lo, hi)] states,
   recursively: values lie in the interval, cached heights are exact and
   nonnegative, and each node's children differ in height by at most one.
   [avl_tree] states it for handles.

   Main functions:
   - [singleton x] — the one-element tree.
   - [insert x h] — standard AVL insertion: insert into the selected child,
     rebuild with a fresh height, rotate ([balance]) when one child grows two
     levels taller than the other.  Preserves [avl_tree]; the specs also
     bound how far each rebuild can move the height.
   - [min h], [max h] — the stored bounds, enclosing every value.

   The interval parameters [lo]/[hi] of the helpers are ghost: they are erased
   before the program is compiled and exist only for the specifications.
   [widen_tree] is a ghost declaration, a lemma proved by induction on the
   height of the tree, establishing that the invariant survives widening the
   interval. *)

type tree = Leaf | Node of int * int * tree * tree

type t = Avl of int * tree * int

let min_int (x: int) (y: int) : int =
  if x < y then x else y
[@@spec fun x y ->
  ret (fun result -> if x < y then assert (result = x) else assert (result = y))];;

let max_int (x: int) (y: int) : int =
  if x < y then y else x
[@@spec fun x y ->
  ret (fun result -> if x < y then assert (result = y) else assert (result = x))];;

let height (tr: tree) : int =
  match tr with
  | Leaf -> 0
  | Node (v, h, l, r) -> h
[@@fn] [@@impl];;

let rec avl_tree_inv ((tr : tree), (lo : int), (hi : int)) : bool =
  match tr with
  | Leaf -> true
  | Node (v, h, l, r) ->
    let right_ok = avl_tree_inv (r, v, hi) in
    let left_ok = avl_tree_inv (l, lo, v) in
    let rh = height r in
    let lh = height l in
    let mh = if lh < rh then rh else lh in
    right_ok && left_ok && lo <= v && v <= hi &&
    h = mh + 1 && lh <= rh + 1 && rh <= lh + 1 &&
    0 <= lh && 0 <= rh
[@@fn];;

let avl_tree (h: t) : bool =
  match h with
  | Avl (lo, tr, hi) ->
    let ok = avl_tree_inv (tr, lo, hi) in
    lo <= hi && ok
[@@fn];;


let make_node (v: int) (l: tree) (r: tree) : tree =
  let lh = height l in
  let rh = height r in
  let h = max_int lh rh + 1 in
  Node (v, h, l, r)
[@@ghost (lo : int) (hi : int)]
[@@spec fun v l r ->
  assert (lo <= v && v <= hi);
  assert (avl_tree_inv (l, lo, v));
  assert (avl_tree_inv (r, v, hi));
  let lh = height l in
  let rh = height r in
  assert (lh <= rh + 1 && rh <= lh + 1 && 0 <= lh && 0 <= rh);
  ret (fun result ->
    assert (avl_tree_inv (result, lo, hi));
    let hres = height result in
    let mh = if lh < rh then rh else lh in
    assert (hres = mh + 1))];;

let balance (v: int) (l: tree) (r: tree) : tree =
  let lh = height l in
  let rh = height r in
  if lh > rh + 1 then
    match l with
    | Leaf -> failwith "unreachable"
    | Node (lv, lh, ll, lr) ->
      if height ll >= height lr then
        (make_node lv ll (make_node v lr r [@ghost lv hi]) [@ghost lo hi])
      else
        match lr with
        | Leaf -> failwith "unreachable"
        | Node (lrv, lrh, lrl, lrr) ->
          (make_node lrv
             (make_node lv ll lrl [@ghost lo lrv])
             (make_node v lrr r [@ghost lrv hi]) [@ghost lo hi])
  else if rh > lh + 1 then
    match r with
    | Leaf -> failwith "unreachable"
    | Node (rv, rh, rl, rr) ->
      if height rr >= height rl then
        (make_node rv (make_node v l rl [@ghost lo rv]) rr [@ghost lo hi])
      else
        match rl with
        | Leaf -> failwith "unreachable"
        | Node (rlv, rlh, rll, rlr) ->
          (make_node rlv
             (make_node v l rll [@ghost lo rlv])
             (make_node rv rlr rr [@ghost rlv hi]) [@ghost lo hi])
  else (make_node v l r [@ghost lo hi])
[@@ghost (lo : int) (hi : int)]
[@@spec fun v l r ->
  assert (lo <= v && v <= hi);
  assert (avl_tree_inv (l, lo, v));
  assert (avl_tree_inv (r, v, hi));
  let lh = height l in
  let rh = height r in
  assert (lh <= rh + 2 && rh <= lh + 2 && 0 <= lh && 0 <= rh);
  ret (fun result ->
    assert (avl_tree_inv (result, lo, hi));
    let hres = height result in
    let mh = if lh < rh then rh else lh in
    assert (mh <= hres && hres <= mh + 1);
    if lh <= rh + 1 then
      (if rh <= lh + 1 then assert (hres = mh + 1) else assert (mh <= hres))
    else assert (mh <= hres))];;

let rec widen_tree (lo: int) (hi: int) (new_lo: int) (new_hi: int) (tr: tree) : unit =
  match tr with
  | Leaf -> ()
  | Node (v, h, l, r) ->
    assert (new_lo <= v);
    assert (v <= new_hi);
    widen_tree lo v new_lo v l;
    widen_tree v hi v new_hi r
[@@ghost]
[@@spec fun lo hi new_lo new_hi tr ->
  assert (new_lo <= lo && hi <= new_hi);
  assert (avl_tree_inv (tr, lo, hi));
  ret (fun result ->
    assert (avl_tree_inv (tr, new_lo, new_hi)))]
[@@decreases height tr];;

let rec insert_raw (x: int) (tr: tree) : tree =
  match tr with
  | Leaf -> Node (x, 1, Leaf, Leaf)
  | Node (v, h, l, r) ->
    if x < v then (balance v (insert_raw x l [@ghost lo v]) r [@ghost lo hi])
    else if v < x then (balance v l (insert_raw x r [@ghost v hi]) [@ghost lo hi])
    else tr
[@@ghost (lo : int) (hi : int)]
[@@spec fun x tr ->
  assert (lo <= x && x <= hi);
  assert (avl_tree_inv (tr, lo, hi));
  ret (fun result ->
    assert (avl_tree_inv (result, lo, hi));
    let htr = height tr in
    let hres = height result in
    assert (htr <= hres && hres <= htr + 1 && 0 <= hres))];;

let singleton (x: int) : t =
  Avl (x, Node (x, 1, Leaf, Leaf), x)
[@@spec fun x ->
  ret (fun result -> assert (avl_tree result))];;

let insert (x: int) (h: t) : t =
  match h with
  | Avl (lo, tr, hi) ->
    let new_lo = min_int x lo in
    let new_hi = max_int x hi in
    let%ghost _ = widen_tree lo hi new_lo new_hi tr in
    Avl (new_lo, (insert_raw x tr [@ghost new_lo new_hi]), new_hi)
[@@spec fun x h ->
  assert (avl_tree h);
  ret (fun result -> assert (avl_tree result))];;

let min (h: t) : int =
  match h with
  | Avl (lo, tr, hi) -> lo
[@@spec fun h ->
  assert (avl_tree h);
  bind (isinj 0 1 h) @@ fun ((lo : int), (tr : tree), (hi : int)) ->
  ret (fun result ->
    assert (result = lo))];;

let max (h: t) : int =
  match h with
  | Avl (lo, tr, hi) -> hi
[@@spec fun h ->
  assert (avl_tree h);
  bind (isinj 0 1 h) @@ fun ((lo : int), (tr : tree), (hi : int)) ->
  ret (fun result ->
    assert (result = hi))];;
