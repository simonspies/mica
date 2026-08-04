open Mica

let _ =
  let inferred_list : int list =
    let xs = [] in
    4 :: xs
  in
  let _ = List.length inferred_list in
  ()
