open Mica

(* AVL trees with the same public-bound wrapper style as [bst.ml].

   Each internal node stores its cached height:

     Node (value, height, left, right)

   The public handle hides the inclusive lower and upper bounds used by
   the recursive invariant:

     Avl (min, tree, max)

   Insertion is the usual AVL insertion: recursively insert into the
   selected child, rebuild the node with a fresh height, and rotate when
   one child is more than one level taller than the other.

   The bound-carrying helpers ([make_node], [balance], [insert_raw]) take
   the inclusive interval [lo, hi] as extra arguments.  These are ghost
   bounds: they are unused at runtime and only thread through the [@@spec]
   obligations so the recursive [avl_tree_inv] invariant can be re-established
   after each rebuild.  [widen_tree] is a lemma-only function showing the
   invariant survives widening the interval, exactly as in [bst.ml]. *)

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
  | Node n -> n.2
[@@fn];;

let height_impl (tr: tree) : int =
  match tr with
  | Leaf -> 0
  | Node n -> n.2
[@@spec fun tr ->
  ret (fun result -> assert (result = height tr))];;

(* [avl_tree_inv (tree, lo, hi)] means:
   - values are in the inclusive BST interval [lo, hi],
   - cached heights are exact and non-negative,
   - every node satisfies the AVL balance bound. *)
let rec avl_tree_inv (args: tree * int * int) : bool =
  let tr = args.1 in
  let lo = args.2 in
  let hi = args.3 in
  match tr with
  | Leaf -> true
  | Node n ->
    let v = n.1 in
    let h = n.2 in
    let l = n.3 in
    let r = n.4 in
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
  | Avl p ->
    let lo = p.1 in
    let tr = p.2 in
    let hi = p.3 in
    let ok = avl_tree_inv (tr, lo, hi) in
    lo <= hi && ok
[@@fn];;


let make_node (v: int) (lo: int) (hi: int) (l: tree) (r: tree) : tree =
  let lh = height_impl l in
  let rh = height_impl r in
  let h = max_int lh rh + 1 in
  Node (v, h, l, r)
[@@spec fun v lo hi l r ->
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

let balance (v: int) (lo: int) (hi: int) (l: tree) (r: tree) : tree =
  let lh = height_impl l in
  let rh = height_impl r in
  if lh > rh + 1 then
    match l with
    | Leaf -> (* unreachable *) make_node v lo hi l r
    | Node ln ->
      let lv = ln.1 in
      let ll = ln.3 in
      let lr = ln.4 in
      if height_impl ll >= height_impl lr then
        make_node lv lo hi ll (make_node v lv hi lr r)
      else
        match lr with
        | Leaf -> (* unreachable *) make_node v lo hi l r
        | Node lrn ->
          let lrv = lrn.1 in
          let lrl = lrn.3 in
          let lrr = lrn.4 in
          make_node lrv lo hi (make_node lv lo lrv ll lrl) (make_node v lrv hi lrr r)
  else if rh > lh + 1 then
    match r with
    | Leaf -> (* unreachable *) make_node v lo hi l r
    | Node rn ->
      let rv = rn.1 in
      let rl = rn.3 in
      let rr = rn.4 in
      if height_impl rr >= height_impl rl then
        make_node rv lo hi (make_node v lo rv l rl) rr
      else
        match rl with
        | Leaf -> (* unreachable *) make_node v lo hi l r
        | Node rln ->
          let rlv = rln.1 in
          let rll = rln.3 in
          let rlr = rln.4 in
          make_node rlv lo hi (make_node v lo rlv l rll) (make_node rv rlv hi rlr rr)
  else make_node v lo hi l r
[@@spec fun v lo hi l r ->
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

(* Lemma-like function: widening the inclusive interval preserves
   [avl_tree_inv].  Only the value-in-bounds part of the invariant depends on
   the bounds; the cached heights and balance conditions are unaffected. *)
let rec widen_tree (lo: int) (hi: int) (new_lo: int) (new_hi: int) (tr: tree) : unit =
  match tr with
  | Leaf -> ()
  | Node n ->
    let v = n.1 in
    let l = n.3 in
    let r = n.4 in
    assert (new_lo <= v);
    assert (v <= new_hi);
    widen_tree lo v new_lo v l;
    widen_tree v hi v new_hi r
[@@spec fun lo hi new_lo new_hi tr ->
  assert (new_lo <= lo && hi <= new_hi);
  assert (avl_tree_inv (tr, lo, hi));
  ret (fun result ->
    assert (avl_tree_inv (tr, new_lo, new_hi)))];;

let rec insert_raw (x: int) (lo: int) (hi: int) (tr: tree) : tree =
  match tr with
  | Leaf -> Node (x, 1, Leaf, Leaf)
  | Node n ->
    let v = n.1 in
    let l = n.3 in
    let r = n.4 in
    if x < v then balance v lo hi (insert_raw x lo v l) r
    else if v < x then balance v lo hi l (insert_raw x v hi r)
    else tr
[@@spec fun x lo hi tr ->
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
  | Avl p ->
    let lo = p.1 in
    let tr = p.2 in
    let hi = p.3 in
    let new_lo = min_int x lo in
    let new_hi = max_int x hi in
    widen_tree lo hi new_lo new_hi tr;
    Avl (new_lo, insert_raw x new_lo new_hi tr, new_hi)
[@@spec fun x h ->
  assert (avl_tree h);
  ret (fun result -> assert (avl_tree result))];;

let min (h: t) : int =
  match h with
  | Avl p -> p.1
[@@spec fun h ->
  assert (avl_tree h);
  bind (isinj 0 1 h) @@ fun (p : int * tree * int) ->
  ret (fun result ->
    assert (result = p.1))];;

let max (h: t) : int =
  match h with
  | Avl p -> p.3
[@@spec fun h ->
  assert (avl_tree h);
  bind (isinj 0 1 h) @@ fun (p : int * tree * int) ->
  ret (fun result ->
    assert (result = p.3))];;
