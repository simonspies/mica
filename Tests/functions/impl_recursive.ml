open Mica

(* A recursive [@@impl] declaration proves its own specification by induction:
   the recursive call carries the same specification, so one unfolding of the
   defining axiom closes each branch. *)

type tree = Leaf | Node of int * tree * tree

let rec insert ((tr : tree), (x : int)) : tree =
  match tr with
  | Leaf -> Node (x, Leaf, Leaf)
  | Node (v, l, r) ->
    if x < v then Node (v, insert (l, x), r) else Node (v, l, insert (r, x))
[@@fn] [@@impl];;

(* A tree is not a scalar, so the equality the specification states is
   [Logic.eq]. *)
let insert_three (tr : tree) : tree = insert (tr, 3)
[@@spec fun tr -> ret (fun r -> assert (Logic.eq r (insert (tr, 3))))];;
