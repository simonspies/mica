(* TEST: roundtrip *)

open Mica

(* An annotation written on the binder pattern is the annotation written after
   the binder: both give the bound value's own type. *)

let on_local (n : int) : int =
  let (b : int) = n + 1 in
  b
[@@spec fun n -> ret (fun r -> assert (r = n + 1))]

(* So a pattern annotation carries a [@spec] exactly as the keyword form does:
   the specification lands on the arrow it annotates. *)

let (double : (int -> int) [@spec fun x -> ret (fun r -> assert (r = x * 2))]) =
  fun x -> x * 2

let use_double (n : int) : int = double n
[@@spec fun n -> ret (fun r -> assert (r = n * 2))]

let on_local_spec (n : int) : int =
  let (triple : (int -> int) [@spec fun x -> ret (fun r -> assert (r = x * 3))]) =
    fun x -> x * 3 in
  triple n
[@@spec fun n -> ret (fun r -> assert (r = n * 3))]

(* A constructor payload is annotated in the match arm itself. *)

type option_int = Absent | Present of int

let payload_or_zero (opt : option_int) : int =
  match opt with
  | Absent -> 0
  | Present (x : int) -> x
[@@spec fun opt ->
  bind (isinj 1 2 opt) @@ fun (payload : int) ->
  ret (fun v -> assert (v = payload))]
