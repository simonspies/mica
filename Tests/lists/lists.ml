(* TEST: roundtrip *)
open Mica

(* Predefined list and option types: constructors, literals, match patterns,
   and standard operations all share one canonical representation. *)

let head_or (l : int list) (d : int) : int =
  match l with
  | [] -> d
  | x :: _ -> x
[@@spec fun l d ->
  bind (isinj 1 2 l) @@ fun ((x : int), (rest : int list)) ->
  ret (fun v -> assert (v = x))];;

let rec length (l : int list) : int =
  match l with
  | [] -> 0
  | _ :: rest -> 1 + length rest
[@@spec fun l ->
  ret (fun v -> assert (v >= 0))];;

let value_or (o : int option) (d : int) : int =
  match o with
  | None -> d
  | Some x -> x
[@@spec fun o d ->
  bind (isinj 1 2 o) @@ fun (x : int) ->
  ret (fun v -> assert (v = x))];;

let _ = assert (head_or [7; 8; 9] 0 = 7)

(* Only the spec (v >= 0) is known at call sites, so bind, don't assert. *)
let result = length (1 :: 2 :: [])

let _ = assert (length [] >= 0)

let _ = assert (value_or (Some 5) 0 = 5)

let builtin_length : int = List.length [4; 5; 6]
let appended : int list = [1; 2] @ [3]
let reversed : int list = List.rev [1; 2; 3]
let _ = assert (Option.is_some (Some 4))
let _ = assert (Option.is_none None)
let _ = assert (Option.value (Some 9) = 9)
