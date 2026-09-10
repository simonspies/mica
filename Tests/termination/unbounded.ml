open Mica

let rec loop (n : int) : int = loop (n - 1)
[@@fn] [@@decreases n];;
