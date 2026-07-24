open Mica

(* Logic.eq is spec-only structural value equality (see Mica/Stdlib/LogicStd.lean).
   It lets specs state equality on list-valued cells, which the surface `=`
   rejects. *)

(* Reflexivity holds on a list-valued argument. *)
let refl (m : (int * int) list) : unit = ()
[@@spec fun m -> ret (fun r -> assert (Logic.eq m m))];;

(* It behaves as an equality: assumed one way, derivable the other. *)
let symm (m1 : (int * int) list) (m2 : (int * int) list) : unit = ()
[@@spec fun m1 m2 ->
  assert (Logic.eq m1 m2);
  ret (fun r -> assert (Logic.eq m2 m1))];;

(* The payoff: a Range.all frame over list-valued array cells is expressible
   and reflexive (this shape is rejected by the surface `=`). *)
let frame (a : (int * int) list array [@owned]) (cap : int) : unit = ()
[@@spec fun a cap ->
  bind (arr a) @@ fun (v : (int * int) list vec) ->
  assert (cap >= 1 && Vec.length v = cap);
  ret (fun r ->
    bind (arr a) @@ fun (w : (int * int) list vec) ->
    assert (Range.all 0 cap (fun (q : int) : bool ->
              Logic.eq (Vec.get w q) (Vec.get v q))))];;
