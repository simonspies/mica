open Mica

(* Selection sort.  The array variants swap a minimal element of the unsorted
   suffix to its front.  The list variant takes out a least element and sorts
   the rest. *)


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

(* Index of a minimal element of [a.(k .. n-1)]. *)
let rec find_min (a : int array [@owned]) (k : int) (n : int) : int =
  if k + 1 >= n then k
  else
    let m = find_min a (k + 1) n in
    if a.(k) <= a.(m) then k else m
[@@spec fun a k n ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= k && k < n && n <= Vec.length v);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 (Vec.length v) (fun (i : int) : bool ->
              Vec.get w i = Vec.get v i));
    assert (k <= r && r < n);
    assert (Range.all k n (fun (q : int) : bool -> Vec.get w r <= Vec.get w q)))];;

(* Sort [a.(k .. n-1)], assuming the prefix [a.(0 .. k-1)] is sorted and
   everything in it is at most everything in the suffix. *)
let rec sel_sort (a : int array [@owned]) (k : int) (n : int) : unit =
  if k < n then
    (let m = find_min a k n in
     swap a k m;
     sel_sort a (k + 1) n)
  else ()
[@@spec fun a k n ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= k && k <= n && n <= Vec.length v);
  assert (Range.all 0 k (fun (p : int) : bool ->
            Range.all 0 k (fun (q : int) : bool ->
              if p <= q then Vec.get v p <= Vec.get v q else true)));
  assert (Range.all 0 k (fun (p : int) : bool ->
            Range.all k n (fun (q : int) : bool ->
              Vec.get v p <= Vec.get v q)));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 n (fun (p : int) : bool ->
              Range.all 0 n (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true))))];;

let selectionsort (a : int array [@owned]) : unit =
  sel_sort a 0 (Array.length a)
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

(* Index of a minimal element of [a.(k .. n-1)]. *)
let rec find_min_safe (a : int array) (k : int) (n : int) : int =
  if k + 1 >= n then k
  else
    let m = find_min_safe a (k + 1) n in
    if a.(k) <= a.(m) then k else m
[@@spec fun a k n ->
  assert (0 <= k && k < n);
  assert (n <= Array.length a);
  ret (fun r -> assert (0 <= r && r < Array.length a))];;

(* Sort [a.(k .. n-1)], the prefix [a.(0 .. k-1)] being already in place. *)
let rec sel_sort_safe (a : int array) (k : int) (n : int) : unit =
  if k < n then
    (let m = find_min_safe a k n in
     swap_safe a k m;
     sel_sort_safe a (k + 1) n)
  else ()
[@@spec fun a k n ->
  assert (0 <= k);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

let selectionsort_safe (a : int array) : unit =
  sel_sort_safe a 0 (Array.length a)
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

(* Every element of [l] is at least [b]. *)
let rec all_ge ((l : int list), (b : int)) : bool =
  match l with
  | [] -> true
  | x :: rest -> b <= x && all_ge (rest, b)
[@@fn];;

(* The least element of [m :: l], and the other elements.  The ghost [b] is a
   lower bound, which carries over to the other elements. *)
let rec select_list (m : int) (l : int list) : int * int list =
  match l with
  | [] -> (m, [])
  | x :: rest ->
    if x < m then
      (let (k, r) = (select_list x rest [@ghost b]) in (k, m :: r))
    else
      (let (k, r) = (select_list m rest [@ghost b]) in (k, x :: r))
[@@spec fun m l ->
  ret (fun ((k : int), (r : int list)) ->
    assert (k <= m);
    assert (all_ge (r, k));
    assert (if all_ge (m :: l, b) then b <= k && all_ge (r, b) else true))]
[@@ghost (b : int)];;

(* The ghost [b] is a lower bound on [l], which carries over to the head of
   the result. *)
let rec selectionsort_list (l : int list) : int list =
  match l with
  | [] -> []
  | x :: rest ->
    let (m, r) = (select_list x rest [@ghost b]) in
    m :: (selectionsort_list r [@ghost m])
[@@spec fun l ->
  ret (fun r ->
    assert (sorted r);
    assert (if all_ge (l, b) then sorted (b :: r) else true))]
[@@ghost (b : int)];;
