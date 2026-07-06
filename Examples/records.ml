open Mica

(* Record syntax elaborates to tuple-shaped products in the frontend. *)

type point = { x : int; y : int }

type wrapped_point = Empty | Wrap of point

let sum_record_binding (p : point) : int =
  let { y = yy; x = xx } = p in
  xx + yy
[@@spec fun p ->
  ret (fun v ->
    assert (v = p.x + p.y))];;

let sum_record_argument { y = yy; x = xx } : int =
  xx + yy
[@@spec fun p ->
  ret (fun v ->
    assert (v = p.x + p.y))];;

let sum_record_literal (n : int) : int =
  let { y = yy; x = xx } = { y = 2; x = 1 } in
  xx + yy + n - n
[@@spec fun n ->
  ret (fun v ->
    assert (v = 3))];;

let sum_wrapped (w : wrapped_point) : int =
  match w with
  | Empty -> 0
  | Wrap { y = yy; x = xx } -> xx + yy
[@@spec fun w ->
  ret (fun v ->
    ret ())];;

let result =
  sum_record_binding { y = 4; x = 3 }
  + sum_record_argument { y = 6; x = 5 }
  + sum_record_literal 0
  + sum_wrapped (Wrap { y = 8; x = 7 });;
