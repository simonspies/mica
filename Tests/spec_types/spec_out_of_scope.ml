open Mica

(* A specification in a type position sees the program's globals and the arrow's
   own arguments — never the binders around it. The type describes a function
   that cannot mention [n]. *)
let f (n : int) (g : (int -> int) [@spec fun x -> assert (x >= n); ret (fun r -> assert (r > x))]) : int =
  g n
