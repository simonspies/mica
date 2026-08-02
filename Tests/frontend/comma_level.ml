(* TEST: --print-ocaml --parse-only no-compile roundtrip *)
open Mica

(* The comma sits between `:=` and `||`, so a tuple needs no parentheses of its
   own. The printer writes them anyway, which is what makes this a fixpoint. *)
let tuple_without_parens a b = a, b

let tuple_is_flat a b c = a, b, c

let comma_binds_looser_than_cons a b = a :: b, a

let comma_binds_tighter_than_assign r a b = r := a, b

(* A list element is above the comma, so `[a, b]` is a one-element list. *)
let list_of_one_tuple a b = [a, b]

let arm_pattern x = match x with
| y :: z, w -> w
| y, z -> y
| _ -> x
