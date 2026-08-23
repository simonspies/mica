open Mica

(* Logic.eq is a structural equality of values, for specifications only.
   See Mica/Stdlib/LogicStd.lean. It lets a specification state an equality
   on a cell that holds a list. The surface operator = refuses such a cell. *)

(* The equality is reflexive on an argument that holds a list. *)
let refl (m : (int * int) list) : unit = ()
[@@spec fun m -> ret (fun r -> assert (Logic.eq m m))];;

(* The equality is symmetric. Assume it in one direction. The verifier then
   proves it in the other direction. *)
let symm (m1 : (int * int) list) (m2 : (int * int) list) : unit = ()
[@@spec fun m1 m2 ->
  assert (Logic.eq m1 m2);
  ret (fun r -> assert (Logic.eq m2 m1))];;

(* This is the case that the equality is made for. The specification states a
   Range.all frame over array cells that hold lists, and the verifier proves
   it. The surface operator = refuses this form. *)
let frame (a : (int * int) list array [@owned]) (cap : int) : unit = ()
[@@spec fun a cap ->
  bind (arr a) @@ fun (v : (int * int) list vec) ->
  assert (cap >= 1 && Vec.length v = cap);
  ret (fun r ->
    bind (arr a) @@ fun (w : (int * int) list vec) ->
    assert (Range.all 0 cap (fun (q : int) : bool ->
              Logic.eq (Vec.get w q) (Vec.get v q))))];;
