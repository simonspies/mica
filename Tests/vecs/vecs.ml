open Mica

(* Immutable vectors.

   Unlike a shared [int array], whose contents live in the heap and are not
   value-tracked, an [int vec] carries its contents in the value itself.  Specs
   can therefore relate elements, not just lengths.

   [Vec.get] and [Vec.set] must discharge in-bounds obligations, and [Vec.make]
   a nonnegative-length obligation. *)

(* A freshly made vector has exactly the requested length. *)
let make_length (n : int) (x : int) : int =
  Vec.length (Vec.make n x)
[@@spec fun n x ->
  assert (n >= 0);
  ret (fun v -> assert (v = n))];;

(* Every element of a freshly made vector is the fill value. *)
let make_get (n : int) (x : int) (i : int) : int =
  Vec.get (Vec.make n x) i
[@@spec fun n x i ->
  assert (0 <= i);
  assert (i < n);
  ret (fun v -> assert (v = x))];;

(* Reading back the slot just written. *)
let set_get (v : int vec) (i : int) (x : int) : int =
  Vec.get (Vec.set v i x) i
[@@spec fun v i x ->
  assert (0 <= i);
  assert (i < Vec.length v);
  ret (fun r -> assert (r = x))];;

(* A functional update preserves the length. *)
let set_length (v : int vec) (i : int) (x : int) : int =
  Vec.length (Vec.set v i x)
[@@spec fun v i x ->
  assert (0 <= i);
  assert (i < Vec.length v);
  ret (fun r -> assert (r = Vec.length v))];;

(* Writing one slot leaves the others alone. *)
let set_get_other (v : int vec) (i : int) (j : int) (x : int) : int =
  Vec.get (Vec.set v i x) j
[@@spec fun v i j x ->
  assert (0 <= i);
  assert (i < Vec.length v);
  assert (0 <= j);
  assert (j < Vec.length v);
  assert (j <> i);
  ret (fun r -> assert (r = Vec.get v j))];;
