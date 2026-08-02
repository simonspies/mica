(* TEST: no-compile *)
open Mica

(* A `let` or `fun` binder is parsed as a pattern atom and then checked, so a
   pattern that can fail to match is reported where it stands. *)
let f 0 = 0
