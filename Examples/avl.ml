(* AVL trees with the same public-bound wrapper style as [bst.ml].

   Each internal node stores its cached height:

     Node (value, height, left, right)

   The public handle hides the inclusive lower and upper bounds used by
   the recursive invariant:

     Avl (min, tree, max)

   Insertion is the usual AVL insertion: recursively insert into the
   selected child, rebuild the node with a fresh height, and rotate when
   one child is more than one level taller than the other. *)

type tree = Leaf | Node of int * int * tree * tree

type t = Avl of int * tree * int

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

let rec height (tr: tree) : int =
  match tr with
  | Leaf -> 0
  | Node n -> n.2
[@@fn];;

(* [valid_raw (tree, lo, hi)] means:
   - values are in the inclusive BST interval [lo, hi],
   - cached heights are exact and non-negative,
   - every node satisfies the AVL balance bound. *)
let rec valid_raw (args: tree * int * int) : bool =
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
    let right_ok = valid_raw (r, v, hi) in
    let left_ok = valid_raw (l, lo, v) in
    let rh = height r in
    let lh = height l in
    let mh = if lh < rh then rh else lh in
    right_ok && left_ok && lo <= v && v <= hi &&
    h = mh + 1 && lh <= rh + 1 && rh <= lh + 1
[@@fn];;

let valid (h: t) : bool =
  match h with
  | Avl p ->
    let lo = p.1 in
    let tr = p.2 in
    let hi = p.3 in
    let ok = valid_raw (tr, lo, hi) in
    lo <= hi && ok
[@@fn];;

let height_impl (tr: tree) : int =
  match tr with
  | Leaf -> 0
  | Node n -> n.2;;

let make_node (v: int) (l: tree) (r: tree) : tree =
  let lh = height_impl l in
  let rh = height_impl r in
  let h = max_int lh rh + 1 in
  Node (v, h, l, r)
;;

let balance (v: int) (l: tree) (r: tree) : tree =
  let lh = height_impl l in
  let rh = height_impl r in
  if lh > rh + 1 then
    match l with
    | Leaf -> make_node v l r
    | Node ln ->
      let lv = ln.1 in
      let ll = ln.3 in
      let lr = ln.4 in
      if height_impl ll >= height_impl lr then
        make_node lv ll (make_node v lr r)
      else
        match lr with
        | Leaf -> make_node v l r
        | Node lrn ->
          let lrv = lrn.1 in
          let lrl = lrn.3 in
          let lrr = lrn.4 in
          make_node lrv (make_node lv ll lrl) (make_node v lrr r)
  else if rh > lh + 1 then
    match r with
    | Leaf -> make_node v l r
    | Node rn ->
      let rv = rn.1 in
      let rl = rn.3 in
      let rr = rn.4 in
      if height_impl rr >= height_impl rl then
        make_node rv (make_node v l rl) rr
      else
        match rl with
        | Leaf -> make_node v l r
        | Node rln ->
          let rlv = rln.1 in
          let rll = rln.3 in
          let rlr = rln.4 in
          make_node rlv (make_node v l rll) (make_node rv rlr rr)
  else make_node v l r
;;

let rec insert_raw (x: int) (tr: tree) : tree =
  match tr with
  | Leaf -> Node (x, 1, Leaf, Leaf)
  | Node n ->
    let v = n.1 in
    let l = n.3 in
    let r = n.4 in
    if x < v then balance v (insert_raw x l) r
    else if v < x then balance v l (insert_raw x r)
    else tr
;;

let singleton (x: int) : t =
  Avl (x, Node (x, 1, Leaf, Leaf), x);;

let insert (x: int) (h: t) : t =
  match h with
  | Avl p ->
    let lo = p.1 in
    let tr = p.2 in
    let hi = p.3 in
    let new_lo = min_int x lo in
    let new_hi = max_int x hi in
    Avl (new_lo, insert_raw x tr, new_hi)
;;

let min (h: t) : int =
  match h with
  | Avl p -> p.1;;

let max (h: t) : int =
  match h with
  | Avl p -> p.3;;
