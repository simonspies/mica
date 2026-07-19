open Mica

(* Owned references across calls (Phase 6).

   The spec-level binder `bind (own r)` introduces the bundled typed points-to
   `pointsTo r v A`, the *same* context entry that an expression-level
   allocation `ref e [@owned]` produces.  A callee can therefore take ownership
   of a cell through its `[@@spec]` precondition, and the verifier transfers an
   allocated owned cell across the call.  Because the points-to bundles the
   value's type `A`, `deref` (`!`) performs a *strong* read returning the exact
   stored term, and the result is usable at the (possibly non-flat) type `A`. *)

type ilist = Nil | Cons of int * ilist

(* A spec-introduced owned cell holding a *flat* `int`.  The body derefs the
   same cell twice; the strong read returns the exact stored value each time, so
   the result is provably `v + v` (the shared discipline could only conclude
   `result : int`). *)
let read_twice (r : int ref [@owned]) : int =
  let a = !r in
  let b = !r in
  a + b
[@@spec fun r ->
  bind (own r) @@ fun (v : int) ->
  ret (fun result ->
    assert (result = v + v))];;

(* Caller side: allocate an owned `int` cell with `ref e [@owned]`, then transfer
   it across the call to `read_twice`.  The allocated `pointsTo l 5 int` matches
   the callee's spec-introduced `own r` entry exactly. *)
let drive_read_twice (unused : int) : int =
  let r = ref 5 [@owned] in
  read_twice r
[@@spec fun unused ->
  ret (fun result ->
    assert (result = 10))];;

(* A spec-introduced owned cell holding a *non-flat* recursive `ilist`.  The
   `own r` binder types the stored value as `ilist`, so the body's `!r` returns
   a value usable at type `ilist` — this is exactly what fails under the old
   `typeConstraints`-only path, which carries no usable type for named types. *)
let take_list (r : ilist ref [@owned]) : ilist =
  !r
[@@spec fun r ->
  bind (own r) @@ fun (xs : ilist) ->
  ret (fun result ->
    ret ())];;

let singleton (x : int) : ilist =
  Cons (x, Nil)
[@@spec fun x ->
  ret (fun r ->
    ret ())];;

(* Caller side: allocate an owned `ilist` cell and transfer it to `take_list`. *)
let build_and_take (a : int) : ilist =
  let r = ref (singleton a) [@owned] in
  take_list r
[@@spec fun a ->
  ret (fun result ->
    ret ())];;
