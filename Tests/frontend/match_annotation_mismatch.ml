(* TEST: no-compile *)

open Mica

(* A constructor payload's annotation is checked against the payload type the
   constructor was declared with. *)
type option_int = Absent | Present of int

let f (opt : option_int) : int =
  match opt with
  | Absent -> 0
  | Present (x : bool) -> 0
[@@spec fun opt -> ret (fun r -> assert (r = 0))]
