open Mica

(* Recursion on the same list does not lower Logic.size. *)
let rec loop (l : int list) : int =
  match l with
  | [] -> 0
  | _ :: _ -> loop l
[@@fn] [@@decreases Logic.size l];;
