open Mica

(* A ghost read of an owned array or an owned reference is the value its
   points-to assertion records. It takes no step, so the heap is unchanged. *)
let first (a : int array [@owned]) : int =
  let%ghost x = a.(0) in
  let y = a.(0) in
  let%ghost _ = assert (x = y) in
  y
[@@spec fun a ->
  bind (arr a) @@ fun (v : int vec) ->
  assert (0 < Vec.length v);
  ret (fun r ->
    bind (arr a) @@ fun (w : int vec) ->
    assert (r = Vec.get v 0);
    assert (Vec.length w = Vec.length v))]
;;

let incr (r : int ref [@owned]) : unit =
  let%ghost old = !r in
  r := !r + 1;
  let%ghost _ = assert (!r = old + 1) in
  ()
[@@spec fun r ->
  bind (own r) @@ fun (n : int) ->
  ret (fun u ->
    bind (own r) @@ fun (m : int) ->
    assert (m = n + 1))]
