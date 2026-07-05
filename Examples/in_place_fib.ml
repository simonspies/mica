open Mica

(* In-place Fibonacci

   The runtime loop owns two heap cells.  Each step performs the simultaneous
   transition `(a, b) := (b, a + b)` using ordinary reads and writes.  The spec
   proves that after [fuel] steps the two cells contain exactly the tuple
   computed by the pure recurrence [fib_state]. *)

let rec fib_state (s : int * int * int) : int * int =
  let a = s.1 in
  let b = s.2 in
  let fuel = s.3 in
  if fuel <= 0 then (a, b)
  else fib_state (b, a + b, fuel - 1)
[@@fn];;

let rec advance (fuel : int) (a : int ref [@owned]) (b : int ref [@owned]) : unit =
  if fuel <= 0 then
    ()
  else
    let old_a = !a in
    let old_b = !b in
    a := old_b;
    b := old_a + old_b;
    advance (fuel - 1) a b
[@@spec fun fuel a b ->
  assert (fuel >= 0);
  bind (own a) @@ fun (start_a : int) ->
  bind (own b) @@ fun (start_b : int) ->
  ret (fun result ->
    bind (own a) @@ fun (final_a : int) ->
    bind (own b) @@ fun (final_b : int) ->
    let expected = fib_state (start_a, start_b, fuel) in
    assert (final_a = expected.1);
    assert (final_b = expected.2))];;

let fib (n : int) : int =
  let a = ref 0 [@owned] in
  let b = ref 1 [@owned] in
  advance n a b;
  !a
[@@spec fun n ->
  assert (n >= 0);
  ret (fun result ->
    let expected = fib_state (0, 1, n) in
    assert (result = expected.1))];;

