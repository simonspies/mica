open Mica

let rec loop (n : int) : int = loop n
[@@fn];;

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@decreases loop n];;
