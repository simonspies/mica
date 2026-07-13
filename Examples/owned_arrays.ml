open Mica

(* Owned arrays carry an immutable vector snapshot in specifications. Reads
   preserve that snapshot, writes replace it with [Vec.set], and ownership is
   threaded linearly through the postcondition. *)

let swap (a : int array [@owned]) (i : int) (j : int) : unit =
  let x = a.(i) in
  let y = a.(j) in
  a.(i) <- y;
  a.(j) <- x
[@@spec fun a i j ->
  assert (0 <= i);
  assert (i < Array.length a);
  assert (0 <= j);
  assert (j < Array.length a);
  bind (arr a) @@ fun (before : int vec) ->
  ret (fun result ->
    bind (arr a) @@ fun (after : int vec) ->
    assert (Vec.length after = Vec.length before);
    assert (Vec.get after i = Vec.get before j);
    assert (Vec.get after j = Vec.get before i))];;

(* Length plus all four element equations is an exact extensional reverse
   postcondition; no vector equality or bounded quantifier is needed. *)
let reverse4 (a : int array [@owned]) : unit =
  let x0 = a.(0) in
  let x3 = a.(3) in
  a.(0) <- x3;
  a.(3) <- x0;
  let x1 = a.(1) in
  let x2 = a.(2) in
  a.(1) <- x2;
  a.(2) <- x1
[@@spec fun a ->
  assert (Array.length a = 4);
  bind (arr a) @@ fun (before : int vec) ->
  ret (fun result ->
    bind (arr a) @@ fun (after : int vec) ->
    assert (Vec.length after = 4);
    assert (Vec.get after 0 = Vec.get before 3);
    assert (Vec.get after 1 = Vec.get before 2);
    assert (Vec.get after 2 = Vec.get before 1);
    assert (Vec.get after 3 = Vec.get before 0))];;

let allocate_owned (x : int) : unit =
  let _a = Array.make 4 x [@owned] in
  ()
[@@spec fun x -> ret (fun result -> assert (true))];;
