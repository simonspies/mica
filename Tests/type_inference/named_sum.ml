open Mica

type box = Empty | Full of int

let _ =
  let x : box = Full 4 in
  match x with
  | Empty -> ()
  | Full _ -> ()
