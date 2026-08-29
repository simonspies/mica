open Mica

(* Dynamic array: a growable [int array] behind a fully mutable handle.

   The handle holds two owned cells.  [data] is a ref, so [grow] can replace
   the backing array without replacing the handle.  [size] is the logical
   size, under the invariant [0 <= !size <= Array.length !data].

   A specification reaches a field by projecting it and binding it: [own] on
   the ref gives the backing array, [arr] on that array gives its contents as
   an [int vec]. *)

type dyn = { data : (int array [@owned]) ref [@owned]; size : int ref [@owned] }

(* An empty dynarray: capacity 0, size 0. *)
let create (u : unit) : dyn =
  { data = (ref (Array.make 0 0 [@owned]) [@owned]); size = (ref 0 [@owned]) }
[@@spec fun u ->
  ret (fun d ->
    let dr = d.data in
    bind (own dr) @@ fun (a : int array [@owned]) ->
    bind (arr a) @@ fun (v : int vec) ->
    let s = d.size in
    bind (own s) @@ fun (n : int) ->
    assert (Vec.length v = 0);
    assert (n = 0))];;

(* Read the element at index [i]. *)
let get (d : dyn) (i : int) : int =
  let dr = d.data in
  let a = !dr in
  a.(i)
[@@spec fun d i ->
  let dr = d.data in
  bind (own dr) @@ fun (a : int array [@owned]) ->
  bind (arr a) @@ fun (v : int vec) ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  assert (0 <= i && i < n && n <= Vec.length v);
  ret (fun r ->
    let dr2 = d.data in
    bind (own dr2) @@ fun (a2 : int array [@owned]) ->
    bind (arr a2) @@ fun (v2 : int vec) ->
    let s2 = d.size in
    bind (own s2) @@ fun (n2 : int) ->
    assert (n2 = n);
    assert (Vec.length v2 = Vec.length v);
    assert (r = Vec.get v i);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              Vec.get v2 q = Vec.get v q)))];;

(* Write [x] at index [i]. *)
let set (d : dyn) (i : int) (x : int) : unit =
  let dr = d.data in
  let a = !dr in
  a.(i) <- x
[@@spec fun d i x ->
  let dr = d.data in
  bind (own dr) @@ fun (a : int array [@owned]) ->
  bind (arr a) @@ fun (v : int vec) ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  assert (0 <= i && i < n && n <= Vec.length v);
  ret (fun r ->
    let dr2 = d.data in
    bind (own dr2) @@ fun (a2 : int array [@owned]) ->
    bind (arr a2) @@ fun (v2 : int vec) ->
    let s2 = d.size in
    bind (own s2) @@ fun (n2 : int) ->
    assert (n2 = n);
    assert (Vec.length v2 = Vec.length v);
    assert (Vec.get v2 i = x);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              if not (q = i) then Vec.get v2 q = Vec.get v q else true)))];;

(* The last element of the live prefix. *)
let last (d : dyn) : int =
  let dr = d.data in
  let s = d.size in
  let a = !dr in
  let n = !s in
  a.(n - 1)
[@@spec fun d ->
  let dr = d.data in
  bind (own dr) @@ fun (a : int array [@owned]) ->
  bind (arr a) @@ fun (v : int vec) ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  assert (0 < n && n <= Vec.length v);
  ret (fun r ->
    let dr2 = d.data in
    bind (own dr2) @@ fun (a2 : int array [@owned]) ->
    bind (arr a2) @@ fun (v2 : int vec) ->
    let s2 = d.size in
    bind (own s2) @@ fun (n2 : int) ->
    assert (n2 = n);
    assert (Vec.length v2 = Vec.length v);
    assert (r = Vec.get v (n - 1));
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              Vec.get v2 q = Vec.get v q)))];;

(* Remove and return the last element, shrinking the size in place. *)
let pop (d : dyn) : int =
  let dr = d.data in
  let s = d.size in
  let a = !dr in
  let n = !s in
  s := n - 1;
  a.(n - 1)
[@@spec fun d ->
  let dr = d.data in
  bind (own dr) @@ fun (a : int array [@owned]) ->
  bind (arr a) @@ fun (v : int vec) ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  assert (0 < n && n <= Vec.length v);
  ret (fun r ->
    let dr2 = d.data in
    bind (own dr2) @@ fun (a2 : int array [@owned]) ->
    bind (arr a2) @@ fun (v2 : int vec) ->
    let s2 = d.size in
    bind (own s2) @@ fun (n2 : int) ->
    assert (n2 = n - 1);
    assert (Vec.length v2 = Vec.length v);
    assert (r = Vec.get v (n - 1));
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              Vec.get v2 q = Vec.get v q)))];;

(* Copy [src.(k .. n-1)] into [dst.(k .. n-1)].  Hand-rolled until Mica's
   modeled standard library supports [Array.blit]. *)
let rec copy_into (src : int array [@owned]) (dst : int array [@owned])
    (k : int) (n : int) : unit =
  if k < n then
    (dst.(k) <- src.(k);
     copy_into src dst (k + 1) n)
  else ()
[@@spec fun src dst k n ->
  bind (arr src) @@ fun (v : int vec) ->
  bind (arr dst) @@ fun (u : int vec) ->
  assert (0 <= k && n <= Vec.length v && n <= Vec.length u);
  ret (fun r ->
    bind (arr src) @@ fun (v2 : int vec) ->
    bind (arr dst) @@ fun (u2 : int vec) ->
    assert (Vec.length v2 = Vec.length v);
    assert (Vec.length u2 = Vec.length u);
    assert (Range.all 0 (Vec.length v) (fun (q : int) : bool ->
              Vec.get v2 q = Vec.get v q));
    assert (Range.all k n (fun (q : int) : bool ->
              Vec.get u2 q = Vec.get v q));
    assert (Range.all 0 (Vec.length u) (fun (q : int) : bool ->
              if q < k || n <= q then Vec.get u2 q = Vec.get u q else true)))];;

(* Replace the backing array with one of capacity [2c+1], keeping the live
   prefix.  The old array is consumed. *)
let grow (d : dyn) : unit =
  let dr = d.data in
  let s = d.size in
  let a = !dr in
  let n = !s in
  let a2 = Array.make (2 * Array.length a + 1) 0 [@owned] in
  copy_into a a2 0 n;
  dr := a2
[@@spec fun d ->
  let dr = d.data in
  bind (own dr) @@ fun (a : int array [@owned]) ->
  bind (arr a) @@ fun (v : int vec) ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  assert (0 <= n && n <= Vec.length v);
  ret (fun r ->
    let dr2 = d.data in
    bind (own dr2) @@ fun (a2 : int array [@owned]) ->
    bind (arr a2) @@ fun (v2 : int vec) ->
    let s2 = d.size in
    bind (own s2) @@ fun (n2 : int) ->
    assert (n2 = n);
    assert (Vec.length v2 = 2 * Vec.length v + 1);
    assert (Range.all 0 n (fun (q : int) : bool ->
              Vec.get v2 q = Vec.get v q)))];;

(* Append [x], reallocating when full. *)
let push (d : dyn) (x : int) : unit =
  let dr = d.data in
  let s = d.size in
  let a = !dr in
  let n = !s in
  (if n < Array.length a then () else grow d);
  let a2 = !dr in
  a2.(n) <- x;
  s := n + 1
[@@spec fun d x ->
  let dr = d.data in
  bind (own dr) @@ fun (a : int array [@owned]) ->
  bind (arr a) @@ fun (v : int vec) ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  assert (0 <= n && n <= Vec.length v);
  ret (fun r ->
    let dr2 = d.data in
    bind (own dr2) @@ fun (a2 : int array [@owned]) ->
    bind (arr a2) @@ fun (v2 : int vec) ->
    let s2 = d.size in
    bind (own s2) @@ fun (n2 : int) ->
    assert (n2 = n + 1);
    assert (n2 <= Vec.length v2);
    assert (Vec.get v2 n = x);
    assert (Range.all 0 n (fun (q : int) : bool ->
              Vec.get v2 q = Vec.get v q)))];;

(* Push [!size], .., [k-1] onto a dynarray already holding [0, .., !size-1]. *)
let rec fill_from (d : dyn) (k : int) : unit =
  let s = d.size in
  let n = !s in
  if n < k then
    (push d n;
     fill_from d k)
  else ()
[@@spec fun d k ->
  let dr = d.data in
  bind (own dr) @@ fun (a : int array [@owned]) ->
  bind (arr a) @@ fun (v : int vec) ->
  let s = d.size in
  bind (own s) @@ fun (n : int) ->
  assert (0 <= n && n <= k && n <= Vec.length v);
  assert (Range.all 0 n (fun (q : int) : bool -> Vec.get v q = q));
  ret (fun r ->
    let dr2 = d.data in
    bind (own dr2) @@ fun (a2 : int array [@owned]) ->
    bind (arr a2) @@ fun (v2 : int vec) ->
    let s2 = d.size in
    bind (own s2) @@ fun (n2 : int) ->
    assert (n2 = k);
    assert (n2 <= Vec.length v2);
    assert (Range.all 0 k (fun (q : int) : bool -> Vec.get v2 q = q)))];;

(* From [create], a dynarray holding [0, 1, .., k-1].  The pushes cross
   several resizes. *)
let fill (k : int) : dyn =
  let d = create () in
  fill_from d k;
  d
[@@spec fun k ->
  assert (0 <= k);
  ret (fun e ->
    let dr = e.data in
    bind (own dr) @@ fun (a : int array [@owned]) ->
    bind (arr a) @@ fun (v : int vec) ->
    let s = e.size in
    bind (own s) @@ fun (n : int) ->
    assert (n = k);
    assert (n <= Vec.length v);
    assert (Range.all 0 k (fun (q : int) : bool -> Vec.get v q = q)))];;
