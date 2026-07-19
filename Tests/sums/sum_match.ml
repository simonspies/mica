(* TEST: roundtrip *)
open Mica

(* User-defined option-like sum with match expressions (the ctor names must
   not clash with the prelude option). *)
type option_int = Absent | Present of int

(* Unwrap with default *)
let unwrap_or (default : int) (opt : option_int) : int =
  match opt with
  | Absent -> default
  | Present x -> x
[@@spec fun default opt ->
  ret (fun v ->
    ret ())];;

(* Double the Present payload, or return 0.
   The spec uses isinj to extract the payload of the Present constructor. *)
let double_or_zero (opt : option_int) : int =
  match opt with
  | Absent -> 0
  | Present x -> x + x
[@@spec fun opt ->
  bind (isinj 1 2 opt) @@ fun (payload : int) ->
  ret (fun v ->
    assert (v = payload + payload))];;

(* Negate the payload if Present, return 0 if Absent *)
let negate_or_zero (opt : option_int) : int =
  match opt with
  | Absent -> 0
  | Present x -> 0 - x
[@@spec fun opt ->
  bind (isinj 1 2 opt) @@ fun (payload : int) ->
  ret (fun v ->
    assert (v = 0 - payload))];;