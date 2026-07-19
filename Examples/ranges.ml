open Mica

(* Bounded quantifiers in specifications.

   [Range.all a b (fun i -> p i)] means [forall i, a <= i < b -> p i], and is
   vacuously true when [b <= a]; [Range.exists] is the dual.  They may appear
   only in specifications: the verifier lambda-lifts each occurrence into an
   uninterpreted function with defining axioms. The registry operations have a
   false precondition, so any occurrence that survives into ordinary
   verification fails like any other unprovable call.

   Both directions are usable: a universally quantified range is proved by
   instantiating the hypotheses' axioms at the goal's (skolemized) index, and an
   existentially quantified one by supplying a witness. *)

(* Empty ranges: [all] holds, [exists] does not, whatever the body says. *)
let vacuous (n : int) : int =
  n
[@@spec fun n ->
  ret (fun v ->
    assert (Range.all 0 0 (fun (i : int) : bool -> i < 0));
    assert (not (Range.exists 0 0 (fun (i : int) : bool -> i >= 0))))];;

(* Nested ranges with a captured vector: pairwise sortedness, instantiated at
   the two indices of interest. *)
let get_sorted (a : int array [@owned]) (i : int) (j : int) : int =
  a.(i)
[@@spec fun a i j ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (Range.all 0 (Vec.length v) (fun (x : int) : bool ->
            Range.all x (Vec.length v) (fun (y : int) : bool -> Vec.get v x <= Vec.get v y)));
  assert (0 <= i);
  assert (i <= j);
  assert (j < Vec.length v);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.get w i <= Vec.get w j))];;

(* A [Range.exists] postcondition: after the write, the key occurs in the
   array. *)
let plant (a : int array [@owned]) (x : int) : unit =
  a.(0) <- x
[@@spec fun a x ->
  assert (Array.length a > 0);
  bind (arr a) @@ fun (before : int vec) ->
  ret (fun r ->
    bind (arr a) @@ fun (v : int vec) ->
    assert (Range.exists 0 (Vec.length v) (fun (i : int) : bool -> Vec.get v i = x)))];;
