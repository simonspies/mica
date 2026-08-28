open Mica

(* Binary search over a sorted [int array], in a functional-correctness
   variant and a safety variant, for comparison.  Both search the half-open
   window [lo, hi) with the same body; [find] recurses, [search] closes it
   over the whole array.

   Functional correctness ([find]/[search], owned array): the specification
   binds the array contents as an [int vec], states sortedness of the contents
   as a bounded quantifier over index pairs, and the postcondition is exact in
   both directions — a returned index lies in the searched window and stores
   the key, while [-1] means the key occurs nowhere in the window.

   Safety ([find_safe]/[search_safe], shared array): shared arrays expose only
   their length in specifications, so the verified property is that every
   access — in particular the midpoint read — stays in bounds.  The annotation
   cost is two bound preconditions.

   This example lives apart from the smaller bounded-range examples so their
   unrelated quantified axioms do not compete for the solver's fixed time
   budget. *)


(* -------------------------------------------------------------------- *)
(* Functional correctness                                               *)
(* -------------------------------------------------------------------- *)

(* Search the window [lo, hi) of the sorted array [a] for [key], returning its
   index or [-1] if it does not occur there. *)
let rec find (a : int array [@owned]) (key : int) (lo : int) (hi : int) : int =
  if lo >= hi then -1
  else
    let mid = lo + (hi - lo) / 2 in
    let m = a.(mid) in
    if m = key then mid
    else if m < key then find a key (mid + 1) hi
    else find a key lo mid
[@@spec fun a key lo hi ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 <= lo && lo <= hi && hi <= Vec.length v);
  assert (Range.all 0 (Vec.length v) (fun (i : int) : bool ->
            Range.all 0 (Vec.length v) (fun (j : int) : bool ->
              if i <= j then Vec.get v i <= Vec.get v j else true)));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    if r >= 0 then
      assert (lo <= r && r < hi && Vec.get v r = key)
    else
      assert (Range.all lo hi (fun (i : int) : bool -> not (Vec.get v i = key))))];;

let search (a : int array [@owned]) (key : int) : int =
  find a key 0 (Array.length a)
[@@spec fun a key ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (Range.all 0 (Vec.length v) (fun (i : int) : bool ->
            Range.all 0 (Vec.length v) (fun (j : int) : bool ->
              if i <= j then Vec.get v i <= Vec.get v j else true)));
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    if r >= 0 then
      assert (0 <= r && r < Vec.length v && Vec.get v r = key)
    else
      assert (Range.all 0 (Vec.length v) (fun (i : int) : bool ->
                not (Vec.get v i = key))))];;


(* -------------------------------------------------------------------- *)
(* Safety variant                                                       *)
(* -------------------------------------------------------------------- *)

(* The midpoint [lo + (hi - lo) / 2] must be shown in range: under the guard
   [lo < hi] it lies in [lo, hi), and the precondition [hi <= length a] then
   discharges the read at [a.(mid)]. *)
let rec find_safe (a : int array) (key : int) (lo : int) (hi : int) : int =
  if lo >= hi then -1
  else
    let mid = lo + (hi - lo) / 2 in
    let m = a.(mid) in
    if m = key then mid
    else if m < key then find_safe a key (mid + 1) hi
    else find_safe a key lo mid
[@@spec fun a key lo hi ->
  assert (0 <= lo);
  assert (hi <= Array.length a);
  ret (fun r -> assert (true))];;

let search_safe (a : int array) (key : int) : int =
  find_safe a key 0 (Array.length a)
[@@spec fun a key -> ret (fun r -> assert (true))];;
