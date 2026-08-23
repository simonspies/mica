open Mica

(* A polymorphic declaration over a polymorphic data type: the payload's
   variable is the declaration's own, and the use site instantiates both. A
   polymorphic spec-level function reads the payload's number back out, so the
   fact survives the substitution into the data declaration. *)

type 'a box = Box of 'a * int

let tag (b : 'a box) : int = match b with Box (_, n) -> n
[@@fn];;

let wrap (x : 'a) (n : int) : 'a box = Box (x, n + 1)
[@@spec fun x n -> ret (fun v -> assert (tag v = n + 1))];;

let wrap_int (n : int) : int box = wrap n 3
[@@spec fun n -> ret (fun v -> assert (tag v = 4))];;

let wrap_list (l : bool list) : bool list box = wrap l 3
[@@spec fun l -> ret (fun v -> assert (tag v = 4))];;
