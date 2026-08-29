open Mica

(* [@@impl] on a [@@fn] declaration also verifies the body as run-time code,
   against the specification that its result is the spec-level function's
   value. The body is written once and used at both levels. *)

let double (n : int) : int = n + n
[@@fn] [@@impl];;

(* The generated specification is what a caller sees. *)
let quadruple (n : int) : int = double (double n)
[@@spec fun n -> ret (fun r -> assert (r = 4 * n))];;
