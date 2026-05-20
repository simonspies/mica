(* Binary search trees with a global sortedness invariant hidden behind
   a small public handle.

   Clients work with values of type [t].  Internally, a [t] packages
   the current inclusive lower bound, the raw recursive tree, and the
   current inclusive upper bound:

     Bst (min, tree, max)

   Inserting a value updates those stored bounds with [min_int] and
   [max_int], so callers do not have to thread ghost bounds by hand.
   The raw tree predicate still carries bounds down the tree; that is
   what rules out violations by deeper descendants. *)

type tree = Leaf | Node of int * tree * tree

type t = Bst of int * tree * int

let min_int (x: int) (y: int) : int =
  if x < y then x else y
[@@spec fun x y ->
  bind (isint x) @@ fun xv ->
  bind (isint y) @@ fun yv ->
  ret (fun result ->
    bind (isint result) @@ fun rv ->
    assert (rv <= xv);
    assert (rv <= yv))];;

let max_int (x: int) (y: int) : int =
  if x < y then y else x
[@@spec fun x y ->
  bind (isint x) @@ fun xv ->
  bind (isint y) @@ fun yv ->
  ret (fun result ->
    bind (isint result) @@ fun rv ->
    assert (xv <= rv);
    assert (yv <= rv))];;

(* [sorted (tree, lo, hi)] means every value in [tree] lies in the
   inclusive interval [lo, hi].  Each recursive call tightens the
   interval with the parent value, so descendants are checked against
   every ancestor bound. *)
let rec sorted_spec (args: tree * int * int) : bool =
  let tr = args.0 in
  let lo = args.1 in
  let hi = args.2 in
  match tr with
  | Leaf -> true
  | Node n ->
    let v = n.0 in
    let l = n.1 in
    let r = n.2 in
    let right_sorted = sorted_spec (r, v, hi) in
    let left_sorted = sorted_spec (l, lo, v) in
    right_sorted && left_sorted && lo <= v && v <= hi
[@@fn sorted];;

(* The public invariant for handles. *)
let valid_spec (h: t) : bool =
  match h with
  | Bst p ->
    let lo = p.0 in
    let tr = p.1 in
    let hi = p.2 in
    let ok = sorted_spec (tr, lo, hi) in
    lo <= hi && ok
[@@fn valid];;

let make_node (v: int) (lo: int) (hi: int) (l: tree) (r: tree) : tree =
  Node (v, l, r)
[@@spec fun v lo hi l r ->
  bind (isint v) @@ fun vv ->
  bind (isint lo) @@ fun lov ->
  bind (isint hi) @@ fun hiv ->
  assert (lov <= vv);
  assert (vv <= hiv);
  bind (call sorted (r, v, hi)) @@ fun sr ->
  bind (isbool sr) @@ fun srb ->
  assert (srb = true);
  bind (call sorted (l, lo, v)) @@ fun sl ->
  bind (isbool sl) @@ fun slb ->
  assert (slb = true);
  ret (fun result ->
    bind (call sorted (result, lo, hi)) @@ fun st ->
    bind (isbool st) @@ fun stb ->
    assert (stb = true))];;

(* Lemma-like function: prove that [tr] is still sorted when its
   inclusive interval is widened.  It returns only [unit]; the useful
   payload is the postcondition fact about the original tree. *)
let rec widen_tree (lo: int) (hi: int) (new_lo: int) (new_hi: int) (tr: tree) : unit =
  match tr with
  | Leaf -> ()
  | Node n ->
    let v = n.0 in
    let l = n.1 in
    let r = n.2 in
    widen_tree lo v new_lo v l;
    widen_tree v hi v new_hi r
[@@spec fun lo hi new_lo new_hi tr ->
  bind (isint lo) @@ fun lov ->
  bind (isint hi) @@ fun hiv ->
  bind (isint new_lo) @@ fun nlov ->
  bind (isint new_hi) @@ fun nhiv ->
  assert (nlov <= lov);
  assert (hiv <= nhiv);
  bind (call sorted (tr, lo, hi)) @@ fun st ->
  bind (isbool st) @@ fun stb ->
  assert (stb = true);
  ret (fun result ->
    assert (result = ());
    bind (call sorted (tr, new_lo, new_hi)) @@ fun sr ->
    bind (isbool sr) @@ fun srb ->
    assert (srb = true))];;

let rec insert_raw (x: int) (lo: int) (hi: int) (tr: tree) : tree =
  match tr with
  | Leaf -> Node (x, Leaf, Leaf)
  | Node n ->
    let v = n.0 in
    let l = n.1 in
    let r = n.2 in
    if x < v then make_node v lo hi (insert_raw x lo v l) r
    else if v < x then make_node v lo hi l (insert_raw x v hi r)
    else tr
[@@spec fun x lo hi tr ->
  bind (isint x) @@ fun xv ->
  bind (isint lo) @@ fun lov ->
  bind (isint hi) @@ fun hiv ->
  assert (lov <= xv);
  assert (xv <= hiv);
  bind (call sorted (tr, lo, hi)) @@ fun st ->
  bind (isbool st) @@ fun stb ->
  assert (stb = true);
  ret (fun result ->
    bind (call sorted (result, lo, hi)) @@ fun sr ->
    bind (isbool sr) @@ fun srb ->
    assert (srb = true))];;

let singleton (x: int) : t =
  Bst (x, Node (x, Leaf, Leaf), x)
[@@spec fun x ->
  bind (isint x) @@ fun xv ->
  ret (fun result ->
    bind (call valid result) @@ fun vr ->
    bind (isbool vr) @@ fun vb ->
    assert (vb = true))];;

let insert (x: int) (h: t) : t =
  match h with
  | Bst p ->
    let lo = p.0 in
    let tr = p.1 in
    let hi = p.2 in
    let new_lo = min_int x lo in
    let new_hi = max_int x hi in
    widen_tree lo hi new_lo new_hi tr;
    Bst (new_lo, insert_raw x new_lo new_hi tr, new_hi)
[@@spec fun x h ->
  bind (isint x) @@ fun xv ->
  bind (call valid h) @@ fun vh ->
  bind (isbool vh) @@ fun vhb ->
  assert (vhb = true);
  ret (fun result ->
    bind (call valid result) @@ fun vr ->
    bind (isbool vr) @@ fun vrb ->
    assert (vrb = true))];;

let min (h: t) : int =
  match h with
  | Bst p -> p.0
[@@spec fun h ->
  bind (call valid h) @@ fun vh ->
  bind (isbool vh) @@ fun vhb ->
  assert (vhb = true);
  bind (isinj 0 1 h) @@ fun p ->
  bind (isint p.0) @@ fun lo ->
  ret (fun result ->
    bind (isint result) @@ fun r ->
    assert (r = lo))];;

let max (h: t) : int =
  match h with
  | Bst p -> p.2
[@@spec fun h ->
  bind (call valid h) @@ fun vh ->
  bind (isbool vh) @@ fun vhb ->
  assert (vhb = true);
  bind (isinj 0 1 h) @@ fun p ->
  bind (isint p.2) @@ fun hi ->
  ret (fun result ->
    bind (isint result) @@ fun r ->
    assert (r = hi))];;
