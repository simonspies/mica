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

let first_byte (s : string) : char =
  String.get s 0
[@@spec fun s ->
  assert (String.length s > 0);
  ret (fun v -> assert (Char.equal v (String.get s 0)))];;

let first_two (s : string) : string =
  String.sub s 0 2
[@@spec fun s ->
  assert (String.length s >= 2);
  ret (fun v ->
    assert (String.equal v (String.sub s 0 2));
    assert (String.length v = 2))];;

let halves_rejoin (s : string) (k : int) : string =
  String.cat (String.sub s 0 k) (String.sub s k (String.length s - k))
[@@spec fun s k ->
  assert (0 <= k && k <= String.length s);
  ret (fun v ->
    assert (String.equal v s))];;
