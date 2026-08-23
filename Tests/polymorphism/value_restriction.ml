(* TEST: no-compile *)
open Mica

type 'a mylist = Nil | Cons of 'a * 'a mylist

(* An allocation is not a signature: what its type is settled by is what runs.
   Were ['a] bound here, the one cell would be reachable at [int mylist] from
   the declaration below it and at [bool mylist] from the one below that. *)
let r : 'a mylist ref = ref Nil

let set_int (n : int) : unit = r := Cons (n, Nil)

let get_bool (u : unit) : bool mylist = !r
