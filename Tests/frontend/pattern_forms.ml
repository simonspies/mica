(* TEST: --print-ocaml --parse-only no-compile roundtrip *)
open Mica

type 'a tree = Leaf | Node of 'a tree * 'a tree

(* A parenthesized pattern is a full pattern: an uppercase head keeps its
   payload, and `::` is allowed inside. *)
let payload_in_parens x = match x with
| Node (Node (l, r), _) -> l
| t -> t

let cons_in_parens x = match x with
| (y :: _, w) -> y
| (_, w) -> w

(* `::` is right-associative, so a `::` on the left keeps its parentheses. *)
let cons_nests_left x = match x with
| (a :: _) :: _ -> a
| _ -> []

(* A constructor payload is an atom, and `[]` is one of them. *)
let empty_list_payload x = match x with
| Node ([], _) -> 0
| _ -> 1

(* An annotation attaches to a binder inside parentheses. *)
let annotated_binder (x : int) (_ : bool) = x
