open Mica

(* Post-side [own] and [arr] binders over spec-level let aliases.

   The location a binder resolves flows through a spec-level [let] — for a
   returned owned ref or mutable array directly and for owned locations stored
   in returned record fields.  Regression test: the spec-level [let] asserts
   the bound expression's type constraints ([isLoc] for owned locations), so
   allocation must assume them; without that, a post-side ownership binder over
   an alias of a freshly allocated location fails. *)

type box = { data : int array [@owned]; size : int ref [@owned] }

let alloc (x : int) : int ref [@owned] =
  ref x [@owned]
[@@spec fun x ->
  ret (fun r ->
    let s = r in
    bind (own s) @@ fun (v : int) ->
    assert (v = x))];;

let alloc_array (n : int) : int array [@owned] =
  Array.make n 0 [@owned]
[@@spec fun n ->
  assert (0 <= n);
  ret (fun r ->
    let a = r in
    bind (arr a) @@ fun (w : int vec) ->
    assert (Vec.length w = n))];;

let make (n : int) : box =
  { data = (Array.make n 0 [@owned]); size = (ref 7 [@owned]) }
[@@spec fun n ->
  assert (0 <= n);
  ret (fun d ->
    let a = d.data in
    bind (arr a) @@ fun (w : int vec) ->
    let s = d.size in
    bind (own s) @@ fun (m : int) ->
    assert (Vec.length w = n);
    assert (m = 7))];;

(* Mutate through the projected field; the caller observes it across the
   call boundary. *)
let bump (d : box) : unit =
  let s = d.size in
  let n = !s in
  s := n + 1
[@@spec fun d ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  ret (fun r ->
    let s2 = d.size in
    bind (own s2) @@ fun (m : int) ->
    assert (m = n + 1))];;

let drive (unused : int) : int =
  let d = make 3 in
  bump d;
  let s = d.size in
  !s
[@@spec fun unused ->
  ret (fun r -> assert (r = 8))];;
