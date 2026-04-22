(* References combined with recursive datatypes, matching, recursion, integers,
   and booleans.

   References are currently managed by the logical relation, so the specs below
   deliberately avoid describing the values stored in cells.  The example 
   implements a small mutable stack and a bounded worklist transfer over a 
   recursive integer-list datatype. *)

type ilist = Nil | Cons of int * ilist

(* A pure helper can still get a meaningful non-reference spec. *)
let rec length (xs : ilist) : int =
  match xs with
  | Nil -> 0
  | Cons p -> 1 + length p.1
[@@spec fun xs ->
  ret (fun v ->
    bind (isint v) @@ fun n ->
    assert (n >= 0);
    if tagof xs = 0 then
      assert (n = 0)
    else
      assert (n >= 1))];;

let push (stack : ilist ref) (x : int) : unit =
  stack := Cons (x, !stack)
[@@spec fun stack x ->
  ret (fun r ->
    assert (r = ()))];;

let singleton (x : int) : ilist =
  Cons (x, Nil)
[@@spec fun x ->
  bind (isint x) @@ fun m ->
  ret (fun r ->
    bind (isinj 1 2 r) @@ fun payload ->
    bind (isint payload.0) @@ fun n ->
    bind (isinj 0 2 payload.1) @@ fun tail_payload ->
    assert (n = m);
    assert (tail_payload = ()))];;

let pop_or_zero (stack : ilist ref) : int =
  match !stack with
  | Nil -> 0
  | Cons p ->
    stack := p.1;
    p.0
[@@spec fun stack ->
  ret (fun r ->
    bind (isint r) @@ fun n ->
    assert (n = n))];;

let top_is_positive (stack : ilist ref) : bool =
  match !stack with
  | Nil -> false
  | Cons p -> p.0 > 0
[@@spec fun stack ->
  ret (fun r ->
    bind (isbool r) @@ fun b ->
    assert (b = b))];;

let rec transfer (fuel : int) (src : ilist ref) (dst : ilist ref) : unit =
  if fuel <= 0 then
    ()
  else
    match !src with
    | Nil -> ()
    | Cons p ->
      src := p.1;
      dst := Cons (p.0, !dst);
      transfer (fuel - 1) src dst
[@@spec fun fuel src dst ->
  ret (fun r ->
    assert (r = ()))];;

let choose_and_push (prefer_left : bool) (left : ilist ref) (right : ilist ref)
    (x : int) : unit =
  if prefer_left then
    push left x
  else
    push right x
[@@spec fun prefer_left left right x ->
  ret (fun r ->
    assert (r = ()))];;

let worklist_demo (a : int) (b : int) (c : int) (prefer_left : bool) : unit =
  let todo = ref (singleton a) in
  let done_ = ref (singleton b) in
  push todo a;
  push todo b;
  choose_and_push prefer_left todo done_ c;
  if top_is_positive todo then
    transfer 3 todo done_
  else
    transfer 1 done_ todo;
  let dropped_todo = pop_or_zero todo in
  let dropped_done = pop_or_zero done_ in
  ()
[@@spec fun a b c prefer_left ->
  ret (fun r ->
    assert (r = ()))];;

let build_and_measure (a : int) (b : int) (c : int) : int =
  length (Cons (a, Cons (b, Cons (c, Nil))))
[@@spec fun a b c ->
  ret (fun v ->
    bind (isint v) @@ fun n ->
    assert (n >= 1))];;
