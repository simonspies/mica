open Mica

type 'a mylist = Nil | Cons of 'a * 'a mylist

(* Only a function literal is generalized. OCaml accepts this one — a
   constructor application allocates nothing, so its value restriction lets it
   through and no weak variable is spent — but mica has no weak variables at
   all, so it draws the line at the function literal. *)
let empty : 'a mylist = Nil
