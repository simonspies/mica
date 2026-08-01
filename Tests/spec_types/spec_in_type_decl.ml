(* TEST: roundtrip *)

open Mica

(* A data declaration's payloads are types like any other, so a record field or
   a constructor payload may describe a specified function, and calling one
   assumes the specification it was declared with. *)

type box = { run : (int -> int) [@spec fun x ->
                      assert (x >= 0);
                      ret (fun r -> assert (r > x))] }

let use_field (b : box) (n : int) : int =
  if n >= 0 then b.run n else 0
[@@spec fun b n -> ret (fun r -> assert (r >= 0))]

(* A record literal is checked against the field's specified arrow, so the
   function literal it carries is elaborated at that arrow. *)
let build_box (n : int) : int = use_field { run = (fun x -> x + 1) } n
[@@spec fun n -> ret (fun r -> assert (r >= 0))]

type wrapped =
  | Plain of int
  | Fn of ((int -> int) [@spec fun x ->
               assert (x >= 0);
               ret (fun r -> assert (r > x))])

let use_payload (w : wrapped) (n : int) : int =
  if n >= 0 then
    match w with
    | Plain _ -> 0
    | Fn f -> f n
  else 0
[@@spec fun w n -> ret (fun r -> assert (r >= 0))]

let incr (x : int) : int = x + 1
[@@spec fun x ->
  assert (x >= 0);
  ret (fun r -> assert (r > x))]

(* Both constructors are built and passed on: the payload of [Fn] is a
   declaration whose own type is the specified arrow the payload declares. *)
let build_plain (n : int) : int = use_payload (Plain 7) n
[@@spec fun n -> ret (fun r -> assert (r >= 0))]

let build_fn (n : int) : int = use_payload (Fn incr) n
[@@spec fun n -> ret (fun r -> assert (r >= 0))]
