open Mica

(* Logic.size counts constructor nodes, so a specification function may recurse
   into a constructor payload. *)
type tree = Leaf | Node of tree * int * tree

let rec total (l : int list) : int =
  match l with
  | [] -> 0
  | h :: t -> h + total t
[@@fn] [@@decreases Logic.size l];;

let rec count (t : tree) : int =
  match t with
  | Leaf -> 0
  | Node (l, _, r) -> count l + 1 + count r
[@@fn] [@@decreases Logic.size t];;
