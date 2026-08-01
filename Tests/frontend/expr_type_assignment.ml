(* TEST: no-compile *)

open Mica

(* KNOWN GAP (#155): a type assignment `(e : t)` is dropped during elaboration,
   so the type it names is never checked and a [@spec] written in it is lost.
   This file pins that behaviour: `(n : bool)` on an `int` is accepted, where
   the same annotation on the binder is rejected (pattern_annotation_mismatch). *)
let f (n : int) : int =
  (n : bool)
[@@spec fun n -> ret (fun r -> assert (r = n))]
