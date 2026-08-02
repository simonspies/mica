(* TEST: no-compile *)
open Mica

(* Every declaration kind parses the same trailing `[@@...]`, so a type
   declaration carrying one is reported as unsupported rather than as a stray
   '[' at the next declaration. *)
type t = A of int [@@deriving show]
