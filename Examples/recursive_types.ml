open Mica

(* Examples using recursive types.
   `ilist` is an integer list: `Nil` (tag 0) or `Cons of int * ilist` (tag 1). *)

type ilist = Nil | Cons of int * ilist

(* Return the head of the list, or 0 if empty. *)
let head_or_zero (l: ilist) : int =
  match l with
  | Nil -> 0
  | Cons (x, rest) -> x
[@@spec fun l ->
  bind (isinj 1 2 l) @@ fun ((x : int), (rest : ilist)) ->
  ret (fun v ->
    assert (v = x))];;

(* Length is non-negative. *)
let rec list_length (l: ilist) : int =
  match l with
  | Nil -> 0
  | Cons (x, rest) -> 1 + list_length rest
[@@spec fun l ->
  ret (fun v ->
    assert (v >= 0))];;


let result = list_length (Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil))))));;

(* Requires matching on x.2, which has type Typ.named "ilist" []. *)
let second_or_zero (l: ilist) : int =
  match l with
  | Nil -> 0
  | Cons (x, rest) ->
    match rest with
    | Nil -> 0
    | Cons (y, rest2) -> if y <= 0 then 0 else y
[@@spec fun l ->
  ret (fun v ->
    assert (v >= 0))];;
