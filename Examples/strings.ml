open Mica

(* String lane acceptance tests. *)

let wrap (s : string) : string =
  let x = ref ("[." ^ s ^ ".]") [@owned] in 
  ! x
[@@spec fun s ->
  ret (fun v ->
    assert (String.starts_with "[" v);
    assert (String.length v = String.length s + 4);
    assert (String.ends_with "]" v))];;

let greet (name : string) : string =
  "hello " ^ name
[@@spec fun name ->
  ret (fun v ->
    assert (String.starts_with "hello " v);
    assert (not (String.starts_with "hi" v));
    assert (String.ends_with name v))];;
