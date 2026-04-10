(* Examples using recursive types.
   `ilist` is an integer list: `Nil` (tag 0) or `Cons of int * ilist` (tag 1). *)

type ilist = Nil | Cons of int * ilist

(* Return the head of the list, or 0 if empty. *)
let head_or_zero (l: ilist) : int =
  match l with
  | Nil -> 0
  | Cons x -> x.0
[@@spec fun l ->
  bind (isinj 1 2 l) @@ fun payload ->
  bind (isint payload.0) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n))];;

(* Length is non-negative. *)
let rec list_length (l: ilist) : int =
  match l with
  | Nil -> 0
  | Cons x -> 1 + list_length x.1
[@@spec fun l ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= 0))];;


let result = list_length (Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil))))));;

(* Requires matching on x.1, which has type Typ.named "ilist" []. *)
(* let second_or_zero (l: ilist) : int =
  match l with
  | Nil -> 0
  | Cons x ->
    match x.1 with
    | Nil -> 0
    | Cons y -> y.0
[@@spec fun l ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= 0))];; *)
