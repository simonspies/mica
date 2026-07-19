(* TEST: roundtrip *)
open Mica

(* Option type with match expressions *)
type option_int = None | Some of int

(* Unwrap with default *)
let unwrap_or (default : int) (opt : option_int) : int =
  match opt with
  | None -> default
  | Some x -> x
[@@spec fun default opt ->
  ret (fun v ->
    ret ())];;

(* Double the Some payload, or return 0.
   The spec uses isinj to extract the payload of the Some constructor. *)
let double_or_zero (opt : option_int) : int =
  match opt with
  | None -> 0
  | Some x -> x + x
[@@spec fun opt ->
  bind (isinj 1 2 opt) @@ fun (payload : int) ->
  ret (fun v ->
    assert (v = payload + payload))];;

(* Negate the payload if Some, return 0 if None *)
let negate_or_zero (opt : option_int) : int =
  match opt with
  | None -> 0
  | Some x -> 0 - x
[@@spec fun opt ->
  bind (isinj 1 2 opt) @@ fun (payload : int) ->
  ret (fun v ->
    assert (v = 0 - payload))];;