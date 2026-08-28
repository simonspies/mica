open Mica

(* In-place reversal of a shared array: swap the ends, walk the cursors
   inward; every access is verified in bounds. *)

let swap (a : int array) (i : int) (j : int) : unit =
  let t = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- t
[@@spec fun a i j ->
  assert (0 <= i && i < Array.length a);
  assert (0 <= j && j < Array.length a);
  ret (fun r -> assert (true))];;

let rec rev (a : int array) (i : int) (j : int) : unit =
  if i < j then
    (swap a i j;
     rev a (i + 1) (j - 1))
  else ()
[@@spec fun a i j ->
  assert (0 <= i);
  assert (j < Array.length a);
  ret (fun r -> assert (true))];;

let reverse (a : int array) : unit =
  rev a 0 (Array.length a - 1)
[@@spec fun a -> ret (fun r -> assert (true))];;
