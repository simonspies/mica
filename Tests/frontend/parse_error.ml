(* TEST: no-compile *)
open Mica

(* A declaration with a missing body must be rejected by the parser. *)
let broken = ;;
