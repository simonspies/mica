(* TEST: --print-ocaml --no-check no-compile roundtrip *)
open Mica

(* Levels that a hand-written chain of parser functions got wrong: `|>` sits at
   the comparison level and `@@` with `@` and `^`, because OCaml places an
   operator by its leading character. The differential corpus checks the whole
   table against ocamlc; this pins the two cells that used to be invented. *)
let pipe_binds_looser_than_compare x g y = x |> g = y

let at_at_binds_tighter_than_compare f x y = f @@ x = y

let at_at_stops_at_semi f a b = f @@ a; b

let at_at_is_right_associative f g x = f @@ g @@ x

let pipe_is_left_associative x f g = x |> f |> g

(* `let`, `fun`, `if` and `match` are operands at every level, and their
   trailing branch runs as far right as it can. *)
let keyword_operand a b c d = a + (if b then c else d)

let keyword_operand_absorbs b c d a = if b then c else d + a

let fun_after_at_at f = f @@ fun x -> x

let match_operand a b c = a || (match b with
| [] -> c
| x :: _ -> x)

let let_operand a b = a + (let x = b in
x)

(* `if` branches stop at `;`, which is looser; the condition does not, being
   delimited by `then`. *)
let semi_sequences_the_whole_if a b c =
  (if a then b else c);
  b

let condition_takes_a_sequence a b c =
  if
    a;
    b
  then c
  else b
