(* TEST: no-compile *)
open Mica

let%ghost widen (lo : int) (hi : int) : unit = ()
