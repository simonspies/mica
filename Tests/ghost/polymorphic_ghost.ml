(* TEST: no-compile *)
open Mica

(* A ghost declaration is called at the arrow it was checked at, so a call at a
   non-trivial instantiation of a type variable is rejected. *)

let id_lemma (x : 'a) : unit = ()
[@@ghost]
[@@spec fun v -> ret (fun u -> assert true)]
;;

let use (n : int) : int =
  let%ghost _ = id_lemma n in
  n
[@@spec fun n -> ret (fun v -> assert (v = n))]
