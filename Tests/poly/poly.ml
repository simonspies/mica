open Mica
(* Polymorphic intrinsics: identity instantiated at different types. *)

(* [Fun.id : 'a -> 'a] at int. *)
let id_int (x : int) : int = Fun.id x
[@@spec fun x -> ret (fun v -> assert (v = x))];;

(* The same [Fun.id] at string: one symbol, a different instantiation. *)
let id_str (s : string) : string = Fun.id s
[@@spec fun s -> ret (fun v -> assert (String.equal v s))];;
