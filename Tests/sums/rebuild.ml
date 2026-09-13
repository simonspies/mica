(* TEST: roundtrip *)
open Mica

(* A match that rebuilds its argument returns an equal value. *)

type shape = Dot | Line of int | Box of int * int * int

let rebuild (s : shape) : shape =
  match s with
  | Dot -> Dot
  | Line a -> Line a
  | Box (a, b, c) -> Box (a, b, c)
[@@spec fun s -> ret (fun r -> assert (Logic.eq r s))];;

(* A match with unit branches proves a statement about every constructor. *)

let widen (s : shape) : shape =
  match s with
  | Dot -> Dot
  | Line a -> Line (a + 1)
  | Box (a, b, c) -> Box (a + 1, b, c)
[@@fn];;

let narrow (s : shape) : shape =
  match s with
  | Dot -> Dot
  | Line a -> Line (a - 1)
  | Box (a, b, c) -> Box (a - 1, b, c)
[@@fn];;

let narrow_widen (s : shape) : unit =
  match s with
  | Dot -> ()
  | Line a -> ()
  | Box (a, b, c) -> ()
[@@spec fun s -> ret (fun r -> assert (Logic.eq (narrow (widen s)) s))];;
