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
   Spec uses tagof to distinguish cases and isinj to extract the payload. *)
let double_or_zero (opt : option_int) : int =
  match opt with
  | None -> 0
  | Some x -> x + x
[@@spec fun opt ->
  bind (isinj 1 2 opt) @@ fun payload ->
  bind (isint payload) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n + n); ret ())];;

(* Negate the payload if Some, return 0 if None *)
let negate_or_zero (opt : option_int) : int =
  match opt with
  | None -> 0
  | Some x -> 0 - x
[@@spec fun opt ->
  bind (isinj 1 2 opt) @@ fun payload ->
  bind (isint payload) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = 0 - n); ret ())];;
