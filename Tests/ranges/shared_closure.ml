open Mica

(* Lifted bounded quantifiers are named by a digest of the closure they lift, so
   the same closure occurring more than once lifts to a single symbol that is
   declared and axiomatized once. The occurrences below differ only in their
   bounds, which are arguments to the lifted symbol rather than part of it, so
   all three share one symbol. *)

let all_nonneg (a : int array [@owned]) (i : int) : int =
  a.(i)
[@@spec fun a i ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (Range.all 0 (Vec.length v) (fun (k : int) : bool -> Vec.get v k >= 0));
  assert (Range.all 0 1 (fun (k : int) : bool -> Vec.get v k >= 0));
  assert (0 <= i);
  assert (i < Vec.length v);
  ret (fun r ->
    assert (r >= 0))];;

(* The identical closure again, in a second declaration: still one symbol. *)
let also_nonneg (a : int array [@owned]) (i : int) : int =
  a.(i)
[@@spec fun a i ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (Range.all 0 (Vec.length v) (fun (k : int) : bool -> Vec.get v k >= 0));
  assert (0 <= i);
  assert (i < Vec.length v);
  ret (fun r ->
    assert (r >= 0))];;
