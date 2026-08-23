open Mica

(* Ownership at a variable type: the specification's [own] atom carries ['a],
   so instantiating the declaration substitutes inside the specification too.
   The cell's number is read back out and the cell is left as it was. *)

let get (r : ('a * int) ref [@owned]) : 'a * int =
  !r
[@@spec fun r ->
  bind (own r) @@ fun ((x : 'a), (n : int)) ->
  ret (fun v ->
    bind (own r) @@ fun ((y : 'a), (m : int)) ->
    let (_, k) = v in assert (k = n); assert (m = n))]

let get_int (n : int) : int =
  let r = ref (n, 7) [@owned] in
  let (_, k) = get r in k
[@@spec fun n -> ret (fun v -> assert (v = 7))]
