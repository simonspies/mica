open Mica

(* A product argument becomes one binder plus a destructuring `let`, so the
   measure may rank a component of it. *)
let rec total ((l : int list), (k : int)) : int =
  match l with
  | [] -> k
  | h :: t -> h + total (t, k)
[@@fn] [@@decreases Logic.size l];;

(* The same recursion ranked by the product itself. *)
let rec drop ((l : int list), (k : int)) : int =
  match l with
  | [] -> k
  | h :: t -> h + drop (t, k)
[@@fn] [@@decreases Logic.size ((l, k))];;

(* A sum of components, each read out of the argument the call receives. *)
let rec zip ((a : int list), (b : int list)) : int =
  match a with
  | [] -> 0
  | x :: xs ->
    match b with
    | [] -> 0
    | y :: ys -> x + y + zip (xs, ys)
[@@fn] [@@decreases Logic.size a + Logic.size b];;

(* One component descends per call, and which one it is alternates. *)
let rec inter ((a : int list), (b : int list)) : int =
  match a with
  | [] -> 0
  | x :: xs ->
    match b with
    | [] -> 0
    | y :: ys -> if x < y then inter (xs, b) else inter (a, ys)
[@@fn] [@@decreases Logic.size a + Logic.size b];;
