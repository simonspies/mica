open Mica

(* A type attribute binds to the type immediately to its left, exactly as
   [@owned] does: this specification lands on the result type [int], not on the
   arrow. A specified arrow has to be parenthesized. *)
let f (g : int -> int [@spec fun x -> ret (fun r -> assert (r > x))]) (n : int) : int = g n
