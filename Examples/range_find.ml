open Mica

(* Binary search over a sorted array, returning the index of the key in the
   window [lo, hi) or [-1] if it does not occur there.  The postcondition is
   exact in both directions: a returned index is in the window and stores the
   key, while [-1] means that the key is absent from the whole window.

   This example lives separately from the smaller bounded-range examples so
   their unrelated quantified axioms do not compete for the solver's fixed
   time budget. *)
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
