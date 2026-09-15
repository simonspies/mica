open Mica

(* Bubble sort: each pass moves the largest element of the unsorted prefix to
   its end.  The list variant stops after a pass without a swap.  Nothing
   shows that it terminates. *)


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

(* One left-to-right pass over [a.(0 .. n-1)], from [i] on.  [a.(i)] is the
   largest element of [a.(0 .. i)]; the pass moves the largest element of the
   region to position [n-1].  Everything in the region stays at most
   everything above it, and the positions above it do not change. *)
let rec bubble_pass (a : int array [@owned]) (i : int) (n : int) : unit =
  if i + 1 < n then
    ((if a.(i) > a.(i + 1) then swap a i (i + 1) else ());
     bubble_pass a (i + 1) n)
  else ()
[@@spec fun a i n ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= i && i < n && n <= Vec.length v);
  assert (Range.all 0 i (fun (q : int) : bool -> Vec.get v q <= Vec.get v i));
  assert (Range.all n (Vec.length v) (fun (p : int) : bool ->
            Range.all 0 n (fun (q : int) : bool -> Vec.get v q <= Vec.get v p)));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 n (fun (q : int) : bool -> Vec.get w q <= Vec.get w (n - 1)));
    assert (Range.all n (Vec.length v) (fun (p : int) : bool ->
              Range.all 0 n (fun (q : int) : bool -> Vec.get w q <= Vec.get w p)));
    assert (Range.all n (Vec.length v) (fun (q : int) : bool ->
              Vec.get w q = Vec.get v q)))];;

(* [k] passes.  The suffix [a.(k ..)] is sorted and bounds the prefix
   [a.(0 .. k-1)] from above; each pass grows the suffix by one. *)
let rec bubble (a : int array [@owned]) (k : int) : unit =
  if k > 0 then
    (bubble_pass a 0 k;
     bubble a (k - 1))
  else ()
[@@spec fun a k ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= k && k <= Vec.length v);
  assert (Range.all k (Vec.length v) (fun (p : int) : bool ->
            Range.all k (Vec.length v) (fun (q : int) : bool ->
              if p <= q then Vec.get v p <= Vec.get v q else true)));
  assert (Range.all k (Vec.length v) (fun (p : int) : bool ->
            Range.all 0 k (fun (q : int) : bool -> Vec.get v q <= Vec.get v p)));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = Vec.length v);
    assert (Range.all 0 (Vec.length w) (fun (p : int) : bool ->
              Range.all 0 (Vec.length w) (fun (q : int) : bool ->
                if p <= q then Vec.get w p <= Vec.get w q else true))))];;

let bubblesort (a : int array [@owned]) : unit =
  bubble a (Array.length a)
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

(* One left-to-right pass bubbling the largest element of [a.(0 .. n-1)] to
   position [n-1]. *)
let rec bubble_pass_safe (a : int array) (i : int) (n : int) : unit =
  if i + 1 < n then
    ((if a.(i) > a.(i + 1) then swap_safe a i (i + 1) else ());
     bubble_pass_safe a (i + 1) n)
  else ()
[@@spec fun a i n ->
  assert (0 <= i);
  assert (n <= Array.length a);
  ret (fun r -> assert (true))];;

(* [k] passes, each shrinking the unsorted prefix by one. *)
let rec bubble_safe (a : int array) (k : int) : unit =
  if k > 0 then
    (bubble_pass_safe a 0 k;
     bubble_safe a (k - 1))
  else ()
[@@spec fun a k ->
  assert (k <= Array.length a);
  ret (fun r -> assert (true))];;

let bubblesort_safe (a : int array) : unit =
  bubble_safe a (Array.length a)
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

(* One pass over [x :: l].  The flag is whether the pass swapped.  A pass
   without a swap shows that [x :: l] is already sorted, so the sort returns
   its input unchanged. *)
let rec pass_list (x : int) (l : int list) : int list * bool =
  match l with
  | [] -> ([x], false)
  | y :: rest ->
    if x > y then
      (let (r, _) = pass_list x rest in (y :: r, true))
    else
      (let (r, c) = pass_list y rest in (x :: r, c))
[@@spec fun x l ->
  ret (fun ((r : int list), (c : bool)) ->
    assert (if c then true else sorted (x :: l)))];;

let rec bubblesort_list (l : int list) : int list =
  match l with
  | [] -> []
  | x :: rest ->
    let (r, c) = pass_list x rest in
    if c then bubblesort_list r else l
[@@spec fun l -> ret (fun r -> assert (sorted r))];;
