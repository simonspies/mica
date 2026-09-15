open Mica

(* Insertion sort.  The array variants grow a sorted prefix by adjacent swaps.
   The list variant inserts each element into the sorted rest. *)


(* -------------------------------------------------------------------- *)
(* Functional correctness                                               *)
(* -------------------------------------------------------------------- *)

(* Swap [a.(i)] and [a.(j)]; the postcondition gives the two new elements and
   the frame (all other positions unchanged). *)
let swap (a : int array [@owned]) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= i && i < Vec.length v);
  assert (0 <= j && j < Vec.length v);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Vec.get w i = Vec.get v j);
    assert (Vec.get w j = Vec.get v i);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
      if not (q = i) && not (q = j) then Vec.get w q = Vec.get v q else true)))];;

(* Move [a.(j)] down through [a.(0 .. n-1)] to its place.  The ghost [n] is
   fixed through the recursion.  The precondition is the loop invariant: the
   region is sorted apart from [j], and [a.(j)] is at most everything above it.
   The last conjunct, that [a.(j-1)] bounds the region below it, follows from
   the first.  It is stated because the solver has no trigger to instantiate
   the sortedness quantifier at [j-1], and the stop case times out without it. *)
let rec shift_down (a : int array [@owned]) (j : int) : unit =
  if j > 0 then
    (if a.(j - 1) > a.(j) then
       (swap a (j - 1) j;
        (shift_down a (j - 1) [@ghost n]))
     else ())
  else ()
[@@spec fun a j ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= j && j < n && n <= Vec.length v);
  assert (Range.all 0 n (fun (p : int) : bool ->
            Range.all 0 n (fun (q : int) : bool ->
              if p <= q && not (p = j) && not (q = j)
              then Vec.get v p <= Vec.get v q else true)));
  assert (Range.all 0 n (fun (q : int) : bool ->
            if j < q then Vec.get v j <= Vec.get v q else true));
  assert (Range.all 0 n (fun (p : int) : bool ->
            if p < j then Vec.get v p <= Vec.get v (j - 1) else true));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 n (fun (p : int) : bool ->
              Range.all 0 n (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true))))]
[@@ghost (n : int)];;

(* Grow the sorted prefix [a.(0 .. i-1)] until it covers [a.(0 .. n-1)]. *)
let rec insert_from (a : int array [@owned]) (i : int) (n : int) : unit =
  if i < n then
    ((shift_down a i [@ghost i + 1]);
     insert_from a (i + 1) n)
  else ()
[@@spec fun a i n ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= i && i <= n && n <= Vec.length v);
  assert (Range.all 0 i (fun (p : int) : bool ->
            Range.all 0 i (fun (q : int) : bool ->
              if p <= q then Vec.get v p <= Vec.get v q else true)));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 n (fun (p : int) : bool ->
              Range.all 0 n (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true))))];;

let insertionsort (a : int array [@owned]) : unit =
  insert_from a 0 (Array.length a)
[@@spec fun a ->
  bind (arr a) @@ fun (v : int vec) ->
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 (Vec.length w) (fun (p : int) : bool ->
              Range.all 0 (Vec.length w) (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true))))];;


(* -------------------------------------------------------------------- *)
(* Safety variant                                                       *)
(* -------------------------------------------------------------------- *)

(* Swap [a.(i)] and [a.(j)]. *)
let swap_safe (a : int array) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  assert (0 <= i && i < Array.length a);
  assert (0 <= j && j < Array.length a);
  ret (fun r -> assert (true))];;

(* Move [a.(j)] down into the sorted prefix [a.(0 .. j-1)]. *)
let rec shift_down_safe (a : int array) (j : int) : unit =
  if j > 0 then
    (if a.(j - 1) > a.(j) then
       (swap_safe a (j - 1) j;
        shift_down_safe a (j - 1))
     else ())
  else ()
[@@spec fun a j ->
  assert (0 <= j);
  assert (j < Array.length a);
  ret (fun r -> assert (true))];;

(* Grow the sorted prefix [a.(0 .. i-1)] until it covers [a.(0 .. n-1)]. *)
let rec insert_from_safe (a : int array) (i : int) (n : int) : unit =
  if i < n then
    (shift_down_safe a i;
     insert_from_safe a (i + 1) n)
  else ()
[@@spec fun a i n ->
  assert (0 <= i);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

let insertionsort_safe (a : int array) : unit =
  insert_from_safe a 0 (Array.length a)
[@@spec fun a -> ret (fun r -> assert (true))];;


(* -------------------------------------------------------------------- *)
(* List variant                                                         *)
(* -------------------------------------------------------------------- *)

(* Adjacent elements are in order. *)
let rec sorted (l : int list) : bool =
  match l with
  | [] -> true
  | x :: rest ->
    (match rest with
     | [] -> true
     | y :: _ -> x <= y) && sorted rest
[@@fn];;

(* Insert [x] into [l].  The ghost [b] is a lower bound: if [b :: l] is sorted
   and [b <= x], then [b :: r] is sorted. *)
let rec insert_list (x : int) (l : int list) : int list =
  match l with
  | [] -> [x]
  | y :: rest -> if x <= y then x :: l else y :: (insert_list x rest [@ghost y])
[@@spec fun x l ->
  assert (sorted l);
  ret (fun r ->
    assert (sorted r);
    assert (if sorted (b :: l) && b <= x then sorted (b :: r) else true))]
[@@ghost (b : int)];;

let rec insertionsort_list (l : int list) : int list =
  match l with
  | [] -> []
  | x :: rest ->
    (* This caller does not use the bound, so any [b] will do. *)
    (insert_list x (insertionsort_list rest) [@ghost 0])
[@@spec fun l ->
  ret (fun r -> assert (sorted r))];;
