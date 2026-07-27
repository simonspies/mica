(* TEST: roundtrip *)

open Mica

(* A specification means the same thing wherever it is written: it is recorded
   on the arrow it annotates. [@@spec] on a declaration and [@spec] in a type
   position are one mechanism. *)

(* The declaration form, unchanged: arguments in the binder list, [@@spec] on
   the declaration. *)
let rec sum_to (n : int) : int =
  if n <= 0 then 0 else n + sum_to (n - 1)
[@@spec fun n ->
  assert (n >= 0);
  ret (fun r -> assert (r >= 0))]

(* A parameter's own type may carry a specification. The body may call the
   parameter, assuming the specification it was annotated with. *)
let apply (g : (int -> int) [@spec fun x ->
                 assert (x >= 0);
                 ret (fun r -> assert (r > x))])
          (n : int) : int =
  g n
[@@spec fun g n ->
  assert (n >= 0);
  ret (fun r -> assert (r > n))]

(* A function literal is checked against the specification of the parameter it
   is passed at. *)
let use_literal (m : int) : int =
  if m >= 0 then apply (fun y -> y + 1) m else 0
[@@spec fun m -> ret (fun r -> assert (r >= 0))]

(* A declaration whose arrow is exactly the parameter's arrow passes by name. *)
let incr (x : int) : int = x + 1
[@@spec fun x ->
  assert (x >= 0);
  ret (fun r -> assert (r > x))]

let use_named (m : int) : int =
  if m >= 0 then apply incr m else 0
[@@spec fun m -> ret (fun r -> assert (r >= 0))]

(* A declaration with no arguments is specified through its own type. *)
let double : (int -> int) [@spec fun x -> ret (fun r -> assert (r = x * 2))] =
  fun x -> x * 2

(* Recursion goes through the annotated type: the self-reference is typed at
   the specified arrow. *)
let rec fact : (int -> int) [@spec fun n ->
                  assert (n >= 0);
                  ret (fun r -> assert (r >= 1))] =
  fun n -> if n <= 0 then 1 else n * fact (n - 1)

(* A specification nests: the argument of a specified arrow may itself be a
   specified arrow. *)
let higher (h : ((((int -> int) [@spec fun x -> ret (fun r -> assert (r > x))]) -> int)
                   [@spec fun k -> ret (fun r -> assert (r >= 0))])) : int =
  h (fun y -> y + 1)
[@@spec fun h -> ret (fun r -> assert (r >= 0))]

(* A specification may sit under a type constructor. *)
let ignore_fns (fs : (((int -> int) [@spec fun x -> ret (fun r -> assert (r >= x))]) list)) : int = 0
[@@spec fun fs -> ret (fun r -> assert (r = 0))]

(* Bounded quantifiers are lifted in a type-position specification, exactly as
   in a declaration's. *)
let call_bq (g : (int -> int) [@spec fun n ->
                    assert (Range.all 0 n (fun (i : int) : bool -> i >= 0));
                    ret (fun r -> assert (r >= 0))])
            (m : int) : int =
  g m
[@@spec fun g m ->
  assert (m >= 0);
  ret (fun r -> assert (r >= 0))]
