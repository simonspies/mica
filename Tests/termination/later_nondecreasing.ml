open Mica

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@decreases n];;

let rec loop (n : int) : int =
  let k = countdown n in
  loop n + k
[@@fn] [@@decreases n];;
