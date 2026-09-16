open Mica

(* A verified compiler from arithmetic expressions to RV32I instructions.

   [graph] compiles an expression to labelled blocks. [lower_blocks] assigns
   physical registers and spill slots. [layout] resolves forward PC-relative
   transfers after spilling. A conditional follows exactly one successor.

   [assemble] tests [need e] and [cost e] against the limits of the target.
   Under them, [assemble_valid] proves that the code exists and meets the
   RV32I field ranges, and [assemble_correct] proves that it runs without
   failure from zero registers and zero spill memory, and returns
   [eval (e, [])] in x1.

   The target machines are models in this file. They use the field widths and
   displacement ranges of RV32I, but there is no encoder and no fetch.
   [COMPILER.md] explains the passes and the scope.

   Opaque definitions are unfolded at explicit arguments. [@@opaque]
   requires [let rec]; non-recursive definitions use measure [0]. *)

(* ------------------------------------------------------------------ *)
(* The source language                                                 *)
(* ------------------------------------------------------------------ *)

type expr =
  | Cst of int32
  | Var of int
  | Plus of expr * expr
  | Bind of expr * expr
  | If of expr * expr * expr

(* A variable out of scope evaluates to zero. The compiled code reads such a
   variable from [x0], which is also zero. So the theorems hold for open
   expressions too. *)

let rec nth ((env : int32 list), (i : int)) : int32 =
  match env with
  | [] -> 0l
  | x :: rest -> if i <= 0 then x else nth (rest, i - 1)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size env];;

let rec eval ((e : expr), (env : int32 list)) : int32 =
  match e with
  | Cst c -> c
  | Var i -> nth (env, i)
  | Plus (a, b) -> Int32.add (eval (a, env)) (eval (b, env))
  | Bind (a, b) -> eval (b, eval (a, env) :: env)
  | If (c, t, e) ->
    if Int32.equal (eval (c, env)) 0l then eval (e, env) else eval (t, env)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size e];;

(* ------------------------------------------------------------------ *)
(* The target                                                          *)
(* ------------------------------------------------------------------ *)

type instr =
  | Addi of int * int * int32
  | Add of int * int * int
  | Lui of int * int32
  | Sub of int * int * int
  | Xor of int * int * int
  | And of int * int * int
  | Sltu of int * int * int

(* [x0] reads as zero and ignores writes. So does an index out of range.
   [@@impl] gives no precondition, so [get] and [set] must be total. *)

let get ((v : int32 vec), (i : int)) : int32 =
  if i <= 0 || Vec.length v <= i then 0l else Vec.get v i
[@@fn ghost] [@@impl];;

let set ((v : int32 vec), (i : int), (x : int32)) : int32 vec =
  if i <= 0 || Vec.length v <= i then v else Vec.set v i x
[@@fn ghost] [@@impl];;

let step ((i : instr), (v : int32 vec)) : int32 vec =
  match i with
  | Addi (rd, rs1, imm) ->
    set (v, rd, Int32.add (get (v, rs1)) imm)
  | Add (rd, rs1, rs2) ->
    set (v, rd, Int32.add (get (v, rs1)) (get (v, rs2)))
  | Lui (rd, imm) -> set (v, rd, imm)
  | Sub (rd, rs1, rs2) ->
    set (v, rd, Int32.sub (get (v, rs1)) (get (v, rs2)))
  | Xor (rd, rs1, rs2) ->
    set (v, rd, Int32.logxor (get (v, rs1)) (get (v, rs2)))
  | And (rd, rs1, rs2) ->
    set (v, rd, Int32.logand (get (v, rs1)) (get (v, rs2)))
  | Sltu (rd, rs1, rs2) ->
    set (v, rd,
         if Int32.unsigned_compare (get (v, rs1)) (get (v, rs2)) < 0 then 1l
         else 0l)
[@@fn ghost] [@@impl];;

let rec exec ((c : instr list), (v : int32 vec)) : int32 vec =
  match c with
  | [] -> v
  | i :: rest -> exec (rest, step (i, v))
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

(* Labels belong to one function. The straight-line executor above runs a
   block body; only its terminator selects the next block. *)

type terminator =
  | Jump of int
  | Branch of int * int * int
  | Return of int

type block = { body : instr list; terminator : terminator }

type func = { entry : int; blocks : (int * block) list }

let rec lookup ((blocks : (int * block) list), (label : int)) : block option =
  match blocks with
  | [] -> None
  | pair :: rest ->
    let (k, b) = pair in
    if k = label then Some b else lookup (rest, label)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size blocks];;

type transfer =
  | Next of int
  | Done of int32

let transfer ((t : terminator), (v : int32 vec)) : transfer =
  match t with
  | Jump k -> Next k
  | Branch (r, yes, no) ->
    Next (if Int32.equal (get (v, r)) 0l then no else yes)
  | Return r -> Done (get (v, r))
[@@fn ghost] [@@impl];;

type execution =
  | Returned of int32 * int32 vec
  | Failed of string
  | Exhausted

(* Fuel counts blocks, including the block that returns. Exhaustion is not
   a successful return. Lookup uses the first definition of a label. *)

let rec run ((f : func), (label : int), (v : int32 vec), (fuel : int))
    : execution =
  if fuel <= 0 then Exhausted
  else match lookup (f.blocks, label) with
  | None -> Failed "CFG label is undefined"
  | Some b ->
    let w = exec (b.body, v) in
    match transfer (b.terminator, w) with
    | Next k -> run (f, k, w, fuel - 1)
    | Done x -> Returned (x, w)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases fuel];;

(* The field ranges of the RV32I encoder. *)

let register (r : int) : bool = 0 <= r && r < 32
[@@fn ghost] [@@impl];;

let immediate (x : int32) : bool =
  Int32.equal (Int32.shift_right (Int32.shift_left x 20) 20) x
[@@fn ghost] [@@impl];;

let upper (x : int32) : bool =
  Int32.equal (Int32.logand x 0xfffl) 0l
[@@fn ghost] [@@impl];;

let wf (i : instr) : bool =
  match i with
  | Addi (rd, rs1, imm) -> register rd && register rs1 && immediate imm
  | Add (rd, rs1, rs2) -> register rd && register rs1 && register rs2
  | Lui (rd, imm) -> register rd && upper imm
  | Sub (rd, rs1, rs2) -> register rd && register rs1 && register rs2
  | Xor (rd, rs1, rs2) -> register rd && register rs1 && register rs2
  | And (rd, rs1, rs2) -> register rd && register rs1 && register rs2
  | Sltu (rd, rs1, rs2) -> register rd && register rs1 && register rs2
[@@fn ghost] [@@impl];;

(* ------------------------------------------------------------------ *)
(* The compiler                                                        *)
(* ------------------------------------------------------------------ *)

(* [List.append] has no equation that the solver can use. Thus [app] is a
   separate function. *)

let rec app ((c : instr list), (k : instr list)) : instr list =
  match c with
  | [] -> k
  | i :: rest -> i :: app (rest, k)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let rec reg ((rs : int list), (i : int)) : int =
  match rs with
  | [] -> 0
  | r :: rest -> if i <= 0 then r else reg (rest, i - 1)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size rs];;

(* [build] and [need] use the same immediate-addition decision. *)

let literal (e : expr) : int32 option =
  match e with
  | Cst c -> if immediate c then Some c else None
  | Var i -> None
  | Plus (a, b) -> None
  | Bind (a, b) -> None
  | If (c, t, e) -> None
[@@fn ghost] [@@impl];;

(* [hi x + lo x = x]. [lo x] fits a 12-bit signed immediate, and [hi x] fits
   a U-type immediate. *)

let lo (x : int32) : int32 =
  Int32.shift_right (Int32.shift_left x 20) 20
[@@fn ghost] [@@impl];;

let hi (x : int32) : int32 = Int32.sub x (lo x)
[@@fn ghost] [@@impl];;

(* ------------------------------------------------------------------ *)
(* Environments in registers                                          *)
(* ------------------------------------------------------------------ *)

(* [agree (rs, env, v)]: each variable of [env] is in its register in [v], and
   [rs] and [env] have the same length. *)

let rec agree ((rs : int list), (env : int32 list), (v : int32 vec)) : bool =
  match rs with
  | [] -> (match env with [] -> true | y :: ys -> false)
  | r :: rest ->
    (match env with
     | [] -> false
     | y :: ys -> Int32.equal (get (v, r)) y && agree (rest, ys, v))
[@@fn] [@@opaque] [@@decreases Logic.size rs];;

(* All registers of the environment are in [1] to [d - 1], below the scratch
   registers. *)

let rec below ((rs : int list), (d : int)) : bool =
  match rs with
  | [] -> true
  | r :: rest -> 1 <= r && r < d && below (rest, d)
[@@fn] [@@opaque] [@@decreases Logic.size rs];;

(* ------------------------------------------------------------------ *)
(* Lemmas                                                              *)
(* ------------------------------------------------------------------ *)

let set_length (v : int32 vec) (i : int) (x : int32) : unit = ()
[@@ghost]
[@@spec fun v i x ->
  ret (fun r ->
    assert (Vec.length (set (v, i, x)) = Vec.length v))];;

let step_length (i : instr) (v : int32 vec) : unit =
  match i with
  | Addi (d, a, x) -> set_length v d (Int32.add (get (v, a)) x)
  | Add (d, a, b) -> set_length v d (Int32.add (get (v, a)) (get (v, b)))
  | Lui (d, x) -> set_length v d x
  | Sub (d, a, b) -> set_length v d (Int32.sub (get (v, a)) (get (v, b)))
  | Xor (d, a, b) -> set_length v d (Int32.logxor (get (v, a)) (get (v, b)))
  | And (d, a, b) -> set_length v d (Int32.logand (get (v, a)) (get (v, b)))
  | Sltu (d, a, b) -> set_length v d
      (if Int32.unsigned_compare (get (v, a)) (get (v, b)) < 0 then 1l else 0l)
[@@ghost]
[@@spec fun i v -> ret (fun u -> assert (Vec.length (step (i, v)) = Vec.length v))];;

let rec exec_length (c : instr list) (v : int32 vec) : unit =
  exec_unfold (c, v);
  match c with
  | [] -> ()
  | i :: rest -> step_length i v; exec_length rest (step (i, v))
[@@ghost]
[@@spec fun c v ->
  ret (fun r -> assert (Vec.length (exec (c, v)) = Vec.length v))]
[@@decreases Logic.size c];;

let rec run_length (f : func) (label : int) (v : int32 vec) (fuel : int)
    : unit =
  run_unfold (f, label, v, fuel);
  if fuel <= 0 then ()
  else match lookup (f.blocks, label) with
  | None -> ()
  | Some b ->
    exec_length b.body v;
    let w = exec (b.body, v) in
    match transfer (b.terminator, w) with
    | Next k -> run_length f k w (fuel - 1)
    | Done x -> ()
[@@ghost]
[@@spec fun f label v fuel ->
  ret (fun u -> assert (
    match run (f, label, v, fuel) with
    | Returned (x, w) -> Vec.length w = Vec.length v
    | Failed reason -> true
    | Exhausted -> true))]
[@@decreases fuel];;

(* Extra fuel does not change a completed execution. *)

let rec run_more (f : func) (label : int) (v : int32 vec)
                 (fuel : int) (extra : int) : unit =
  run_unfold (f, label, v, fuel);
  run_unfold (f, label, v, fuel + extra);
  if fuel <= 0 then ()
  else match lookup (f.blocks, label) with
  | None -> ()
  | Some b ->
    let w = exec (b.body, v) in
    match transfer (b.terminator, w) with
    | Next k -> run_more f k w (fuel - 1) extra
    | Done x -> ()
[@@ghost]
[@@spec fun f label v fuel extra ->
  assert (0 <= extra);
  ret (fun u -> assert (
    match run (f, label, v, fuel) with
    | Exhausted -> true
    | Failed reason -> Logic.eq (run (f, label, v, fuel + extra))
                               (run (f, label, v, fuel))
    | Returned (x, w) -> Logic.eq (run (f, label, v, fuel + extra))
                                 (run (f, label, v, fuel))))]
[@@decreases fuel];;

let rec exec_app (c : instr list) (k : instr list) (v : int32 vec) : unit =
  app_unfold (c, k);
  exec_unfold (c, v);
  exec_unfold (app (c, k), v);
  match c with
  | [] -> ()
  | i :: rest -> exec_app rest k (step (i, v))
[@@ghost]
[@@spec fun c k v ->
  ret (fun r ->
    assert (Logic.eq (exec (app (c, k), v)) (exec (k, exec (c, v)))))]
[@@decreases Logic.size c];;

let exec_one (i : instr) (w : int32 vec) : unit =
  let s = step (i, w) in
  exec_unfold ([i], w);
  exec_unfold ([], s);
  ()
[@@ghost]
[@@spec fun i w ->
  ret (fun r -> assert (Logic.eq (exec ([i], w)) (step (i, w))))];;

let index (i : int) : unit = ()
[@@ghost]
[@@spec fun i ->
  assert (0 <= i);
  assert (i < 32);
  ret (fun r -> assert (register i))];;

let fields (x : int32) : unit = ()
[@@ghost]
[@@spec fun x ->
  ret (fun r ->
    assert (immediate (lo x));
    assert (upper (hi x));
    assert (Int32.equal (Int32.add (hi x) (lo x)) x))];;

let get_set_at (v : int32 vec) (j : int) (x : int32) : unit = ()
[@@ghost]
[@@spec fun v j x ->
  assert (1 <= j);
  assert (j < Vec.length v);
  ret (fun r -> assert (Int32.equal (get (set (v, j, x), j)) x))];;

let get_set_off (v : int32 vec) (j : int) (x : int32) (i : int) : unit = ()
[@@ghost]
[@@spec fun v j x i ->
  assert (i <> j);
  ret (fun r ->
    assert (Int32.equal (get (set (v, j, x), i)) (get (v, i))))];;

let exec_cons (i : instr) (c : instr list) (v : int32 vec) : unit =
  exec_unfold (i :: c, v);
  ()
[@@ghost]
[@@spec fun i c v ->
  ret (fun r ->
    assert (Logic.eq (exec (i :: c, v)) (exec (c, step (i, v)))))];;

let leaf_code (rd : int) (rs1 : int) (imm : int32)
              (v : int32 vec) : unit =
  exec_one (Addi (rd, rs1, imm)) v
[@@ghost]
[@@spec fun rd rs1 imm v ->
  ret (fun r ->
    assert (Logic.eq (exec ([Addi (rd, rs1, imm)], v))
                     (set (v, rd, Int32.add (get (v, rs1)) imm))))];;

let const_code (d : int) (c : int32) (v : int32 vec) : unit =
  let upper = Lui (d, hi c) in
  let lower = Addi (d, d, lo c) in
  let v1 = step (upper, v) in
  fields c;
  get_set_at v d (hi c);
  set_length v d (hi c);
  get_set_at v1 d c;
  exec_cons upper [lower] v;
  exec_one lower v1
[@@ghost]
[@@spec fun d c v ->
  assert (1 <= d);
  assert (d < Vec.length v);
  ret (fun r ->
    assert (Int32.equal
      (get (exec ([Lui (d, hi c); Addi (d, d, lo c)], v), d)) c))];;

(* [same (w, v, d)]: [w] and [v] agree on the registers below [d]. [same] does
   not use [Range.all], because its axioms would go to every goal in the file. *)

let rec same ((w : int32 vec), (v : int32 vec), (d : int)) : bool =
  if d <= 0 then true
  else Int32.equal (get (w, d - 1)) (get (v, d - 1)) && same (w, v, d - 1)
[@@fn] [@@opaque] [@@decreases d];;

let rec same_at (w : int32 vec) (v : int32 vec) (d : int) (i : int) : unit =
  same_unfold (w, v, d);
  if d <= 0 then ()
  else if i = d - 1 then ()
  else same_at w v (d - 1) i
[@@ghost]
[@@spec fun w v d i ->
  assert (same (w, v, d));
  assert (0 <= i);
  assert (i < d);
  ret (fun r -> assert (Int32.equal (get (w, i)) (get (v, i))))]
[@@decreases d];;

let rec same_trans (u : int32 vec) (w : int32 vec) (v : int32 vec)
                   (d : int) : unit =
  same_unfold (u, w, d);
  same_unfold (w, v, d);
  same_unfold (u, v, d);
  if d <= 0 then () else same_trans u w v (d - 1)
[@@ghost]
[@@spec fun u w v d ->
  assert (same (u, w, d));
  assert (same (w, v, d));
  ret (fun r -> assert (same (u, v, d)))]
[@@decreases d];;

let rec same_narrow (w : int32 vec) (v : int32 vec) (d : int)
                    (d2 : int) : unit =
  same_unfold (w, v, d);
  if d <= d2 then () else same_narrow w v (d - 1) d2
[@@ghost]
[@@spec fun w v d d2 ->
  assert (same (w, v, d));
  assert (0 <= d2);
  assert (d2 <= d);
  ret (fun r -> assert (same (w, v, d2)))]
[@@decreases d];;

let rec same_set (w : int32 vec) (d : int) (x : int32) (k : int) : unit =
  same_unfold (set (w, d, x), w, k);
  if k <= 0 then ()
  else begin
    get_set_off w d x (k - 1);
    same_set w d x (k - 1)
  end
[@@ghost]
[@@spec fun w d x k ->
  assert (0 <= k);
  assert (k <= d);
  ret (fun r -> assert (same (set (w, d, x), w, k)))]
[@@decreases k];;

let agree_cons (r : int) (rs : int list) (y : int32) (env : int32 list)
               (v : int32 vec) : unit =
  agree_unfold (r :: rs, y :: env, v);
  ()
[@@ghost]
[@@spec fun r rs y env v ->
  assert (Int32.equal (get (v, r)) y);
  assert (agree (rs, env, v));
  ret (fun u -> assert (agree (r :: rs, y :: env, v)))];;

let rec agree_frame (rs : int list) (env : int32 list) (v : int32 vec)
                    (w : int32 vec) (d : int) : unit =
  below_unfold (rs, d);
  agree_unfold (rs, env, v);
  agree_unfold (rs, env, w);
  match rs with
  | [] -> ()
  | r :: rest ->
    (match env with
     | [] -> ()
     | y :: ys -> same_at w v d r; agree_frame rest ys v w d)
[@@ghost]
[@@spec fun rs env v w d ->
  assert (below (rs, d));
  assert (agree (rs, env, v));
  assert (same (w, v, d));
  ret (fun r -> assert (agree (rs, env, w)))]
[@@decreases Logic.size rs];;

(* ------------------------------------------------------------------ *)
(* Compiler correctness                                                *)
(* ------------------------------------------------------------------ *)

let rec below_mono (rs : int list) (d : int) (d2 : int) : unit =
  below_unfold (rs, d);
  below_unfold (rs, d2);
  match rs with
  | [] -> ()
  | r :: rest -> below_mono rest d d2
[@@ghost]
[@@spec fun rs d d2 ->
  assert (below (rs, d));
  assert (d <= d2);
  ret (fun r -> assert (below (rs, d2)))]
[@@decreases Logic.size rs];;

let below_cons (r : int) (rs : int list) (d : int) : unit =
  below_unfold (r :: rs, d);
  ()
[@@ghost]
[@@spec fun r rs d ->
  assert (1 <= r);
  assert (r < d);
  assert (below (rs, d));
  ret (fun u -> assert (below (r :: rs, d)))];;

let rec reg_bound (rs : int list) (d : int) (i : int) : unit =
  below_unfold (rs, d);
  reg_unfold (rs, i);
  match rs with
  | [] -> ()
  | r :: rest -> if i <= 0 then () else reg_bound rest d (i - 1)
[@@ghost]
[@@spec fun rs d i ->
  assert (1 <= d);
  assert (below (rs, d));
  ret (fun r ->
    assert (0 <= reg (rs, i));
    assert (reg (rs, i) < d))]
[@@decreases Logic.size rs];;

let literal_wf (e : expr) (c : int32) : unit =
  match e with
  | Cst c0 -> ()
  | Var i -> ()
  | Plus (a, b) -> ()
  | Bind (a, b) -> ()
  | If (c0, t, f) -> ()
[@@ghost]
[@@spec fun e c ->
  assert (Logic.eq (literal e) (Some c));
  ret (fun r -> assert (immediate c))];;

let literal_eval (e : expr) (env : int32 list) (c : int32) : unit =
  eval_unfold (e, env);
  match e with
  | Cst c0 -> ()
  | Var i -> ()
  | Plus (a, b) -> ()
  | Bind (a, b) -> ()
  | If (c0, t, f) -> ()
[@@ghost]
[@@spec fun e env c ->
  assert (Logic.eq (literal e) (Some c));
  ret (fun r -> assert (Int32.equal (eval (e, env)) c))];;

let rec agree_nth (rs : int list) (env : int32 list) (v : int32 vec)
                  (i : int) : unit =
  agree_unfold (rs, env, v);
  reg_unfold (rs, i);
  nth_unfold (env, i);
  match rs with
  | [] -> ()
  | r :: rest ->
    (match env with
     | [] -> ()
     | y :: ys -> if i <= 0 then () else agree_nth rest ys v (i - 1))
[@@ghost]
[@@spec fun rs env v i ->
  assert (agree (rs, env, v));
  ret (fun r -> assert (Int32.equal (get (v, reg (rs, i))) (nth (env, i))))]
[@@decreases Logic.size rs];;

(* ------------------------------------------------------------------ *)
(* Spill allocation                                                    *)
(* ------------------------------------------------------------------ *)

(* A virtual register below 29 stays a register. Each other virtual register
   gets a memory slot. [lower] uses [x29] to [x31] as temporaries. *)

type location =
  | Reg of int
  | Slot of int

let locate (i : int) : location =
  if i < 29 then Reg i else Slot (i - 29)
[@@fn ghost] [@@impl];;

let slots (limit : int) : int =
  if limit <= 29 then 0 else limit - 29
[@@fn ghost] [@@impl];;

let location_wf ((l : location), (n : int)) : bool =
  match l with
  | Reg r -> 0 <= r && r < 29
  | Slot s -> 0 <= s && s < n
[@@fn];;

let allocated (limit : int) (i : int) : unit =
  if i < 29 then () else ()
[@@ghost]
[@@spec fun limit i ->
  assert (0 <= i);
  assert (i < limit);
  ret (fun r -> assert (location_wf (locate i, slots limit)))];;

(* Like [wf], but a register must have a location instead of 5 bits. *)

let allocatable ((i : instr), (n : int)) : bool =
  match i with
  | Addi (rd, rs1, imm) ->
    location_wf (locate rd, n) && location_wf (locate rs1, n)
    && immediate imm
  | Add (rd, rs1, rs2) ->
    location_wf (locate rd, n) && location_wf (locate rs1, n)
    && location_wf (locate rs2, n)
  | Lui (rd, imm) -> location_wf (locate rd, n) && upper imm
  | Sub (rd, rs1, rs2) ->
    location_wf (locate rd, n) && location_wf (locate rs1, n)
    && location_wf (locate rs2, n)
  | Xor (rd, rs1, rs2) ->
    location_wf (locate rd, n) && location_wf (locate rs1, n)
    && location_wf (locate rs2, n)
  | And (rd, rs1, rs2) ->
    location_wf (locate rd, n) && location_wf (locate rs1, n)
    && location_wf (locate rs2, n)
  | Sltu (rd, rs1, rs2) ->
    location_wf (locate rd, n) && location_wf (locate rs1, n)
    && location_wf (locate rs2, n)
[@@fn];;

let rec allocation ((c : instr list), (n : int)) : bool =
  match c with
  | [] -> true
  | i :: rest -> allocatable (i, n) && allocation (rest, n)
[@@fn] [@@opaque] [@@decreases Logic.size c];;

let allocation_nil (n : int) : unit =
  allocation_unfold ([], n);
  ()
[@@ghost]
[@@spec fun n -> ret (fun u -> assert (allocation ([], n)))];;

let allocation_cons (i : instr) (c : instr list) (n : int) : unit =
  allocation_unfold (i :: c, n);
  ()
[@@ghost]
[@@spec fun i c n ->
  assert (allocatable (i, n));
  assert (allocation (c, n));
  ret (fun u -> assert (allocation (i :: c, n)))];;

let rec app_allocation (c : instr list) (k : instr list) (n : int) : unit =
  app_unfold (c, k);
  allocation_unfold (c, n);
  allocation_unfold (app (c, k), n);
  match c with
  | [] -> ()
  | i :: rest -> app_allocation rest k n
[@@ghost]
[@@spec fun c k n ->
  assert (allocation (c, n));
  assert (allocation (k, n));
  ret (fun r -> assert (allocation (app (c, k), n)))]
[@@decreases Logic.size c];;

(* ------------------------------------------------------------------ *)
(* Physical spill memory                                               *)
(* ------------------------------------------------------------------ *)

(* Little-endian word access on a vector of bytes, as in RV32I. Spill
   code uses [x0] as its base, so the slots are at addresses [0] to [2047]. *)

let rec load32 ((mem : int32 vec), (i : int)) : int32 option =
  if 0 <= i && i + 3 < Vec.length mem then
    Some
      (Int32.logor (Vec.get mem i)
         (Int32.logor (Int32.shift_left (Vec.get mem (i + 1)) 8)
            (Int32.logor (Int32.shift_left (Vec.get mem (i + 2)) 16)
               (Int32.shift_left (Vec.get mem (i + 3)) 24))))
  else None
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec store32 ((mem : int32 vec), (i : int), (x : int32))
    : int32 vec option =
  if 0 <= i && i + 3 < Vec.length mem then
    Some (Vec.set
      (Vec.set
        (Vec.set
          (Vec.set mem i (Int32.logand x 0xffl))
          (i + 1) (Int32.logand (Int32.shift_right_logical x 8) 0xffl))
        (i + 2) (Int32.logand (Int32.shift_right_logical x 16) 0xffl))
      (i + 3) (Int32.logand (Int32.shift_right_logical x 24) 0xffl))
  else None
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

(* The word in slot [s], or zero if [s] is out of range. Only the simulation
   uses [word]. Execution uses [load32], which traps. *)

let word ((mem : int32 vec), (s : int)) : int32 =
  match load32 (mem, 4 * s) with
  | None -> 0l
  | Some x -> x
[@@fn ghost] [@@impl];;

let word_load (mem : int32 vec) (s : int) : unit =
  load32_unfold (mem, 4 * s)
[@@ghost]
[@@spec fun mem s ->
  assert (0 <= s); assert (s < 512);
  assert (4 * (s + 1) <= Vec.length mem);
  ret (fun u -> assert (Logic.eq (load32 (mem, 4 * s)) (Some (word (mem, s)))))];;

let word_store (mem : int32 vec) (s : int) (x : int32) : unit =
  store32_unfold (mem, 4 * s, x);
  match store32 (mem, 4 * s, x) with
  | None -> assert false
  | Some mem_written -> load32_unfold (mem_written, 4 * s)
[@@ghost]
[@@spec fun mem s x ->
  assert (0 <= s); assert (s < 512);
  assert (4 * (s + 1) <= Vec.length mem);
  ret (fun u -> assert (
    match store32 (mem, 4 * s, x) with
    | None -> false
    | Some mem_written -> Vec.length mem_written = Vec.length mem
      && Int32.equal (word (mem_written, s)) x))];;

let word_store_off (mem : int32 vec) (s : int) (x : int32) (t : int) : unit =
  store32_unfold (mem, 4 * s, x);
  load32_unfold (mem, 4 * t);
  match store32 (mem, 4 * s, x) with
  | None -> assert false
  | Some mem_written -> load32_unfold (mem_written, 4 * t)
[@@ghost]
[@@spec fun mem s x t ->
  assert (0 <= s); assert (s < 512);
  assert (0 <= t); assert (t < 512); assert (s <> t);
  assert (4 * (s + 1) <= Vec.length mem);
  assert (4 * (t + 1) <= Vec.length mem);
  ret (fun u -> assert (
    match store32 (mem, 4 * s, x) with
    | None -> false
    | Some mem_written -> Int32.equal (word (mem_written, t)) (word (mem, t))))];;

(* ------------------------------------------------------------------ *)
(* Physical execution and lowering                                     *)
(* ------------------------------------------------------------------ *)

(* [Alu] holds an instruction of the virtual machine. [Lw] and [Sw] have the
   operand order of RV32I. *)

type physical =
  | Alu of instr
  | Lw of int * int * int
  | Sw of int * int * int

(* [base + imm] modulo 2^32, as a signed integer. *)

let address ((base : int32), (imm : int)) : int =
  let a = (Int32.to_int base + imm) mod 4294967296 in
  (a + 6442450944) mod 4294967296 - 2147483648
[@@fn ghost] [@@impl];;

type machine = { regs : int32 vec; mem : int32 vec; ok : bool }

let physical_step ((i : physical), (p : machine)) : machine =
  if not p.ok then p else
  match i with
  | Alu i -> { regs = step (i, p.regs); mem = p.mem; ok = true }
  | Lw (rd, rs1, imm) ->
    (match load32 (p.mem, address (get (p.regs, rs1), imm)) with
     | None -> { regs = p.regs; mem = p.mem; ok = false }
     | Some x -> { regs = set (p.regs, rd, x); mem = p.mem; ok = true })
  | Sw (rs1, rs2, imm) ->
    (match store32 (p.mem, address (get (p.regs, rs1), imm),
                    get (p.regs, rs2)) with
     | None -> { regs = p.regs; mem = p.mem; ok = false }
     | Some mem -> { regs = p.regs; mem = mem; ok = true })
[@@fn ghost] [@@impl];;

let rec physical_exec ((c : physical list), (p : machine)) : machine =
  match c with
  | [] -> p
  | i :: rest -> physical_exec (rest, physical_step (i, p))
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let physical_wf (i : physical) : bool =
  match i with
  | Alu i -> wf i
  | Lw (rd, rs1, imm) -> register rd && register rs1 && -2048 <= imm && imm < 2048
  | Sw (rs1, rs2, imm) -> register rs1 && register rs2 && -2048 <= imm && imm < 2048
[@@fn ghost] [@@impl];;

let rec physical_valid (c : physical list) : bool =
  match c with
  | [] -> true
  | i :: rest -> physical_wf i && physical_valid rest
[@@fn] [@@opaque] [@@decreases Logic.size c];;

(* The destination and the two sources. An unused source is [x0]. *)

let operands (i : instr) : int * int * int =
  match i with
  | Addi (d, a, x) -> (d, a, 0)
  | Add (d, a, b) -> (d, a, b)
  | Lui (d, x) -> (d, 0, 0)
  | Sub (d, a, b) -> (d, a, b)
  | Xor (d, a, b) -> (d, a, b)
  | And (d, a, b) -> (d, a, b)
  | Sltu (d, a, b) -> (d, a, b)
[@@fn ghost] [@@impl];;

let rename ((i : instr), (d : int), (a : int), (b : int)) : instr =
  match i with
  | Addi (rd, rs1, imm) -> Addi (d, a, imm)
  | Add (rd, rs1, rs2) -> Add (d, a, b)
  | Lui (rd, imm) -> Lui (d, imm)
  | Sub (rd, rs1, rs2) -> Sub (d, a, b)
  | Xor (rd, rs1, rs2) -> Xor (d, a, b)
  | And (rd, rs1, rs2) -> And (d, a, b)
  | Sltu (rd, rs1, rs2) -> Sltu (d, a, b)
[@@fn ghost] [@@impl];;

let result ((i : instr), (x : int32), (y : int32)) : int32 =
  match i with
  | Addi (rd, rs1, imm) -> Int32.add x imm
  | Add (rd, rs1, rs2) -> Int32.add x y
  | Lui (rd, imm) -> imm
  | Sub (rd, rs1, rs2) -> Int32.sub x y
  | Xor (rd, rs1, rs2) -> Int32.logxor x y
  | And (rd, rs1, rs2) -> Int32.logand x y
  | Sltu (rd, rs1, rs2) -> if Int32.unsigned_compare x y < 0 then 1l else 0l
[@@fn ghost] [@@impl];;

let temporary ((i : int), (t : int)) : int =
  match locate i with Reg r -> r | Slot s -> t
[@@fn ghost] [@@impl];;

let fetch ((i : int), (t : int), (k : physical list)) : physical list =
  match locate i with
  | Reg r -> k
  | Slot s -> Lw (t, 0, 4 * s) :: k
[@@fn ghost] [@@impl];;

let save ((d : int), (k : physical list)) : physical list =
  match locate d with
  | Reg r -> k
  | Slot s -> Sw (0, 31, 4 * s) :: k
[@@fn ghost] [@@impl];;

(* [x29] and [x30] hold sources from slots, and [x31] holds a result for a
   slot. [lower_one] adds to [k], so [lower] does not copy lists. The proofs
   require at most 512 slots, because a larger offset does not fit a 12-bit
   immediate. *)

let lower_one ((i : instr), (k : physical list)) : physical list =
  let (d, a, b) = operands i in
  fetch (a, 29, fetch (b, 30,
    Alu (rename (i, temporary (d, 31), temporary (a, 29), temporary (b, 30)))
      :: save (d, k)))
[@@fn ghost] [@@impl];;

let rec lower (c : instr list) : physical list =
  match c with
  | [] -> []
  | i :: rest -> lower_one (i, lower rest)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let operands_valid (i : instr) (n : int) : unit =
  match i with
  | Addi (d, a, x) -> ()
  | Add (d, a, b) -> ()
  | Lui (d, x) -> ()
  | Sub (d, a, b) -> ()
  | Xor (d, a, b) -> ()
  | And (d, a, b) -> ()
  | Sltu (d, a, b) -> ()
[@@ghost]
[@@spec fun i n ->
  assert (allocatable (i, n));
  ret (fun u -> assert (
    let (d, a, b) = operands i in
    location_wf (locate d, n) && location_wf (locate a, n)
      && location_wf (locate b, n)))];;

let rename_valid (i : instr) (n : int) (d : int) (a : int) (b : int) : unit =
  match i with
  | Addi (rd, rs1, imm) -> ()
  | Add (rd, rs1, rs2) -> ()
  | Lui (rd, imm) -> ()
  | Sub (rd, rs1, rs2) -> ()
  | Xor (rd, rs1, rs2) -> ()
  | And (rd, rs1, rs2) -> ()
  | Sltu (rd, rs1, rs2) -> ()
[@@ghost]
[@@spec fun i n d a b ->
  assert (allocatable (i, n));
  assert (register d); assert (register a); assert (register b);
  ret (fun u -> assert (wf (rename (i, d, a, b))))];;

let temporary_valid (i : int) (t : int) (n : int) : unit = ()
[@@ghost]
[@@spec fun i t n ->
  assert (location_wf (locate i, n)); assert (register t);
  ret (fun u -> assert (register (temporary (i, t))))];;

let fetch_valid (i : int) (t : int) (n : int) (k : physical list) : unit =
  match locate i with
  | Reg r -> ()
  | Slot s ->
    physical_valid_unfold (Lw (t, 0, 4 * s) :: k)
[@@ghost]
[@@spec fun i t n k ->
  assert (location_wf (locate i, n)); assert (n <= 512);
  assert (register t); assert (physical_valid k);
  ret (fun u -> assert (physical_valid (fetch (i, t, k))))];;

let save_valid (d : int) (n : int) (k : physical list) : unit =
  match locate d with
  | Reg r -> ()
  | Slot s ->
    physical_valid_unfold (Sw (0, 31, 4 * s) :: k)
[@@ghost]
[@@spec fun d n k ->
  assert (location_wf (locate d, n)); assert (n <= 512);
  assert (physical_valid k);
  ret (fun u -> assert (physical_valid (save (d, k))))];;

let lower_one_valid (i : instr) (n : int) (k : physical list) : unit =
  let (d, a, b) = operands i in
  operands_valid i n;
  temporary_valid d 31 n;
  temporary_valid a 29 n;
  temporary_valid b 30 n;
  rename_valid i n (temporary (d, 31)) (temporary (a, 29)) (temporary (b, 30));
  let op = Alu (rename (i, temporary (d, 31), temporary (a, 29), temporary (b, 30))) in
  let tail = save (d, k) in
  save_valid d n k;
  physical_valid_unfold (op :: tail);
  fetch_valid b 30 n (op :: tail);
  fetch_valid a 29 n (fetch (b, 30, op :: tail))
[@@ghost]
[@@spec fun i n k ->
  assert (allocatable (i, n)); assert (n <= 512);
  assert (physical_valid k);
  ret (fun u -> assert (physical_valid (lower_one (i, k))))];;

let rec lower_valid (c : instr list) (n : int) : unit =
  lower_unfold c;
  allocation_unfold (c, n);
  match c with
  | [] -> physical_valid_unfold []
  | i :: rest ->
    lower_valid rest n;
    lower_one_valid i n (lower rest)
[@@ghost]
[@@spec fun c n ->
  assert (allocation (c, n)); assert (n <= 512);
  ret (fun u -> assert (physical_valid (lower c)))]
[@@decreases Logic.size c];;

(* ------------------------------------------------------------------ *)
(* Virtual/physical simulation                                         *)
(* ------------------------------------------------------------------ *)

let observe ((p : machine), (i : int)) : int32 =
  match locate i with
  | Reg r -> get (p.regs, r)
  | Slot s -> word (p.mem, s)
[@@fn ghost] [@@impl];;

let rec represented ((v : int32 vec), (p : machine), (k : int)) : bool =
  if k <= 0 then true
  else Int32.equal (get (v, k - 1)) (observe (p, k - 1))
    && represented (v, p, k - 1)
[@@fn] [@@opaque] [@@decreases k];;

let room ((p : machine), (n : int)) : bool =
  p.ok && Vec.length p.regs = 32 && 29 <= n && n <= 541
    && 4 * slots n <= Vec.length p.mem
[@@fn];;

let simulation ((v : int32 vec), (p : machine)) : bool =
  room (p, Vec.length v) && represented (v, p, Vec.length v)
[@@fn];;

let rec represented_at (v : int32 vec) (p : machine) (k : int) (i : int) : unit =
  represented_unfold (v, p, k);
  if i = k - 1 then () else represented_at v p (k - 1) i
[@@ghost]
[@@spec fun v p k i ->
  assert (represented (v, p, k)); assert (0 <= i); assert (i < k);
  ret (fun u -> assert (Int32.equal (get (v, i)) (observe (p, i))))]
[@@decreases k];;

let scratch ((p : machine), (t : int), (x : int32)) : machine =
  { regs = set (p.regs, t, x); mem = p.mem; ok = p.ok }
[@@fn ghost] [@@impl];;

let rec represented_scratch (v : int32 vec) (p : machine) (k : int)
                            (t : int) (x : int32) : unit =
  represented_unfold (v, p, k);
  represented_unfold (v, scratch (p, t, x), k);
  if k <= 0 then () else begin
    if k - 1 < 29 then get_set_off p.regs t x (k - 1) else ();
    represented_scratch v p (k - 1) t x
  end
[@@ghost]
[@@spec fun v p k t x ->
  assert (represented (v, p, k)); assert (29 <= t);
  ret (fun u -> assert (represented (v, scratch (p, t, x), k)))]
[@@decreases k];;

let simulation_scratch (v : int32 vec) (p : machine) (t : int) (x : int32) : unit =
  represented_scratch v p (Vec.length v) t x;
  set_length p.regs t x
[@@ghost]
[@@spec fun v p t x ->
  assert (simulation (v, p)); assert (29 <= t);
  ret (fun u -> assert (simulation (v, scratch (p, t, x))))];;

(* The state after the load that [fetch] adds, if any. *)

let fetched ((p : machine), (i : int), (t : int)) : machine =
  match locate i with
  | Reg r -> p
  | Slot s -> physical_step (Lw (t, 0, 4 * s), p)
[@@fn ghost] [@@impl];;

let fetch_exec (i : int) (t : int) (k : physical list) (p : machine) : unit =
  match locate i with
  | Reg r -> ()
  | Slot s -> physical_exec_unfold (Lw (t, 0, 4 * s) :: k, p)
[@@ghost]
[@@spec fun i t k p ->
  ret (fun u -> assert (Logic.eq (physical_exec (fetch (i, t, k), p))
    (physical_exec (k, fetched (p, i, t)))))];;

let fetch_correct (v : int32 vec) (p : machine) (i : int) (t : int) : unit =
  represented_at v p (Vec.length v) i;
  match locate i with
  | Reg r -> ()
  | Slot s ->
    word_load p.mem s;
    simulation_scratch v p t (word (p.mem, s));
    get_set_at p.regs t (word (p.mem, s))
[@@ghost]
[@@spec fun v p i t ->
  assert (simulation (v, p)); assert (0 <= i); assert (i < Vec.length v);
  assert (29 <= t); assert (t < 32);
  ret (fun u ->
    assert (simulation (v, fetched (p, i, t)));
    assert (Int32.equal
      (get ((fetched (p, i, t)).regs, temporary (i, t))) (get (v, i))))];;

let committed ((p : machine), (d : int), (x : int32)) : machine =
  let q = scratch (p, temporary (d, 31), x) in
  match locate d with
  | Reg r -> q
  | Slot s -> physical_step (Sw (0, 31, 4 * s), q)
[@@fn ghost] [@@impl];;

let commit_room (p : machine) (n : int) (d : int) (x : int32) : unit =
  match locate d with
  | Reg r -> set_length p.regs r x
  | Slot s ->
    set_length p.regs 31 x;
    get_set_at p.regs 31 x;
    word_store p.mem s x
[@@ghost]
[@@spec fun p n d x ->
  assert (room (p, n)); assert (0 <= d); assert (d < n);
  ret (fun u ->
    assert (room (committed (p, d, x), n));
    assert (Vec.length (committed (p, d, x)).mem = Vec.length p.mem))];;

let commit_at (p : machine) (n : int) (d : int) (x : int32) (i : int) : unit =
  match locate d with
  | Reg r ->
    if i < 29 then
      (if i = d then (if d = 0 then () else get_set_at p.regs d x)
       else get_set_off p.regs d x i)
    else ()
  | Slot s ->
    get_set_at p.regs 31 x;
    if i < 29 then begin
      word_store p.mem s x;
      get_set_off p.regs 31 x i
    end else if i = d then word_store p.mem s x
    else word_store_off p.mem s x (i - 29)
[@@ghost]
[@@spec fun p n d x i ->
  assert (room (p, n)); assert (0 <= d); assert (d < n);
  assert (0 <= i); assert (i < n);
  ret (fun u -> assert (Int32.equal (observe (committed (p, d, x), i))
    (if i = d && d <> 0 then x else observe (p, i))))];;

let rec represented_commit (v : int32 vec) (p : machine) (k : int)
                           (d : int) (x : int32) : unit =
  represented_unfold (v, p, k);
  represented_unfold (set (v, d, x), committed (p, d, x), k);
  if k <= 0 then () else begin
    commit_at p (Vec.length v) d x (k - 1);
    if k - 1 = d then (if d = 0 then () else get_set_at v d x)
    else get_set_off v d x (k - 1);
    represented_commit v p (k - 1) d x
  end
[@@ghost]
[@@spec fun v p k d x ->
  assert (room (p, Vec.length v)); assert (represented (v, p, k));
  assert (k <= Vec.length v); assert (0 <= d); assert (d < Vec.length v);
  ret (fun u -> assert (represented (set (v, d, x), committed (p, d, x), k)))]
[@@decreases k];;

let commit_correct (v : int32 vec) (p : machine) (d : int) (x : int32) : unit =
  commit_room p (Vec.length v) d x;
  represented_commit v p (Vec.length v) d x;
  set_length v d x
[@@ghost]
[@@spec fun v p d x ->
  assert (simulation (v, p)); assert (0 <= d); assert (d < Vec.length v);
  ret (fun u -> assert (simulation (set (v, d, x), committed (p, d, x))))];;

let location_bound (i : int) (n : int) : unit = ()
[@@ghost]
[@@spec fun i n ->
  assert (29 <= n); assert (location_wf (locate i, slots n));
  ret (fun u -> assert (0 <= i); assert (i < n))];;

let step_result (i : instr) (v : int32 vec) : unit =
  match i with
  | Addi (d, a, x) -> ()
  | Add (d, a, b) -> ()
  | Lui (d, x) -> ()
  | Sub (d, a, b) -> ()
  | Xor (d, a, b) -> ()
  | And (d, a, b) -> ()
  | Sltu (d, a, b) -> ()
[@@ghost]
[@@spec fun i v ->
  ret (fun u -> assert (
    let (d, a, b) = operands i in
    Logic.eq (step (i, v)) (set (v, d, result (i, get (v, a), get (v, b))))))];;

let rename_step (i : instr) (d : int) (a : int) (b : int) (v : int32 vec) : unit =
  match i with
  | Addi (rd, rs1, imm) -> ()
  | Add (rd, rs1, rs2) -> ()
  | Lui (rd, imm) -> ()
  | Sub (rd, rs1, rs2) -> ()
  | Xor (rd, rs1, rs2) -> ()
  | And (rd, rs1, rs2) -> ()
  | Sltu (rd, rs1, rs2) -> ()
[@@ghost]
[@@spec fun i d a b v ->
  ret (fun u -> assert (Logic.eq (step (rename (i, d, a, b), v))
    (set (v, d, result (i, get (v, a), get (v, b))))))];;

let fetch_off (p : machine) (n : int) (i : int) (t : int) (j : int) : unit =
  match locate i with
  | Reg r -> ()
  | Slot s ->
    word_load p.mem s;
    get_set_off p.regs t (word (p.mem, s)) j
[@@ghost]
[@@spec fun p n i t j ->
  assert (room (p, n)); assert (0 <= i); assert (i < n); assert (j <> t);
  ret (fun u -> assert (Int32.equal (get ((fetched (p, i, t)).regs, j))
    (get (p.regs, j))))];;

let lowered ((i : instr), (p : machine)) : machine =
  let (d, a, b) = operands i in
  let p1 = fetched (p, a, 29) in
  let p2 = fetched (p1, b, 30) in
  committed (p2, d, result (i,
    get (p2.regs, temporary (a, 29)), get (p2.regs, temporary (b, 30))))
[@@fn ghost] [@@impl];;

let lower_step_correct (i : instr) (v : int32 vec) (p : machine) : unit =
  let (d, a, b) = operands i in
  operands_valid i (slots (Vec.length v));
  location_bound d (Vec.length v);
  location_bound a (Vec.length v);
  location_bound b (Vec.length v);
  let p1 = fetched (p, a, 29) in
  let p2 = fetched (p1, b, 30) in
  fetch_correct v p a 29;
  fetch_correct v p1 b 30;
  fetch_off p1 (Vec.length v) b 30 (temporary (a, 29));
  step_result i v;
  commit_correct v p2 d (result (i, get (v, a), get (v, b)))
[@@ghost]
[@@spec fun i v p ->
  assert (simulation (v, p)); assert (allocatable (i, slots (Vec.length v)));
  ret (fun u -> assert (simulation (step (i, v), lowered (i, p))))];;

let save_exec (d : int) (x : int32) (p : machine) (k : physical list) : unit =
  match locate d with
  | Reg r -> ()
  | Slot s -> physical_exec_unfold
    (Sw (0, 31, 4 * s) :: k, scratch (p, temporary (d, 31), x))
[@@ghost]
[@@spec fun d x p k ->
  ret (fun u -> assert (Logic.eq
    (physical_exec (save (d, k), scratch (p, temporary (d, 31), x)))
    (physical_exec (k, committed (p, d, x)))))];;

let lower_one_exec (i : instr) (v : int32 vec) (p : machine)
                   (k : physical list) : unit =
  let (d, a, b) = operands i in
  operands_valid i (slots (Vec.length v));
  location_bound a (Vec.length v);
  location_bound b (Vec.length v);
  let p1 = fetched (p, a, 29) in
  let p2 = fetched (p1, b, 30) in
  fetch_correct v p a 29;
  fetch_correct v p1 b 30;
  let op = Alu (rename (i, temporary (d, 31), temporary (a, 29), temporary (b, 30))) in
  let tail = save (d, k) in
  fetch_exec a 29 (fetch (b, 30, op :: tail)) p;
  fetch_exec b 30 (op :: tail) p1;
  physical_exec_unfold (op :: tail, p2);
  rename_step i (temporary (d, 31)) (temporary (a, 29)) (temporary (b, 30)) p2.regs;
  save_exec d (result (i, get (p2.regs, temporary (a, 29)),
    get (p2.regs, temporary (b, 30)))) p2 k
[@@ghost]
[@@spec fun i v p k ->
  assert (simulation (v, p)); assert (allocatable (i, slots (Vec.length v)));
  ret (fun u -> assert (Logic.eq (physical_exec (lower_one (i, k), p))
    (physical_exec (k, lowered (i, p)))))];;

let rec lower_correct (c : instr list) (v : int32 vec) (p : machine) : unit =
  lower_unfold c;
  exec_unfold (c, v);
  allocation_unfold (c, slots (Vec.length v));
  match c with
  | [] -> physical_exec_unfold ([], p)
  | i :: rest ->
    lower_step_correct i v p;
    lower_one_exec i v p (lower rest);
    step_result i v;
    let (d, a, b) = operands i in
    set_length v d (result (i, get (v, a), get (v, b)));
    lower_correct rest (step (i, v)) (lowered (i, p))
[@@ghost]
[@@spec fun c v p ->
  assert (simulation (v, p)); assert (allocation (c, slots (Vec.length v)));
  ret (fun u -> assert (simulation (exec (c, v), physical_exec (lower c, p))))]
[@@decreases Logic.size c];;

let initial (n : int) : machine =
  { regs = Vec.make 32 0l; mem = Vec.make (4 * slots n) 0l; ok = true }
[@@fn ghost] [@@impl];;

let rec represented_initial (n : int) (k : int) : unit =
  let v = Vec.make n 0l in
  let p = initial n in
  represented_unfold (v, p, k);
  if k <= 0 then () else begin
    if 29 <= k - 1 then load32_unfold (p.mem, 4 * (k - 30)) else ();
    represented_initial n (k - 1)
  end
[@@ghost]
[@@spec fun n k ->
  assert (29 <= n); assert (n <= 541); assert (k <= n);
  ret (fun u -> assert (represented (Vec.make n 0l, initial n, k)))]
[@@decreases k];;

let initial_simulation (n : int) : unit =
  represented_initial n n
[@@ghost]
[@@spec fun n ->
  assert (29 <= n); assert (n <= 541);
  ret (fun u -> assert (simulation (Vec.make n 0l, initial n)))];;

(* ------------------------------------------------------------------ *)
(* CFG construction                                                    *)
(* ------------------------------------------------------------------ *)

(* [head] is an open block. [formed] requires labels in [blocks_new] to be
   below [fresh], and every successor to have an older label. *)

type fragment = { head : block; blocks_new : (int * block) list; fresh : int }

let rec prepend ((body : instr list), (f : fragment)) : fragment =
  { head = { body = app (body, f.head.body); terminator = f.head.terminator };
    blocks_new = f.blocks_new; fresh = f.fresh }
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

(* Close the open block and leave a jump to it as the continuation. *)

let rec close (f : fragment) : fragment =
  { head = { body = []; terminator = Jump f.fresh };
    blocks_new = (f.fresh, f.head) :: f.blocks_new; fresh = f.fresh + 1 }
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let lookup_close (f : fragment) : unit =
  close_unfold f;
  lookup_unfold ((close f).blocks_new, f.fresh)
[@@ghost]
[@@spec fun f ->
  ret (fun u -> assert (Logic.eq (lookup ((close f).blocks_new, f.fresh))
                               (Some f.head)))];;

let lookup_close_off (f : fragment) (label : int) : unit =
  close_unfold f;
  lookup_unfold ((close f).blocks_new, label)
[@@ghost]
[@@spec fun f label ->
  assert (label <> f.fresh);
  ret (fun u -> assert (Logic.eq (lookup ((close f).blocks_new, label))
                               (lookup (f.blocks_new, label))))];;

let prepend_exec (body : instr list) (f : fragment) (v : int32 vec) : unit =
  prepend_unfold (body, f);
  exec_app body f.head.body v
[@@ghost]
[@@spec fun body f v ->
  ret (fun u -> assert (Logic.eq (exec ((prepend (body, f)).head.body, v))
                               (exec (f.head.body, exec (body, v)))) )];;

let rec resume ((head : block), (f : fragment)) : fragment =
  { head = head; blocks_new = f.blocks_new; fresh = f.fresh }
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec build ((e : expr), (rs : int list), (d : int), (f : fragment))
    : fragment =
  match e with
  | Cst c -> prepend ([Lui (d, hi c); Addi (d, d, lo c)], f)
  | Var i -> prepend ([Addi (d, reg (rs, i), 0l)], f)
  | Plus (a, b) ->
    (match literal b with
     | Some c -> build (a, rs, d, prepend ([Addi (d, d, c)], f))
     | None ->
       let tail = prepend ([Add (d, d, d + 1)], f) in
       let right = build (b, rs, d + 1, tail) in
       build (a, rs, d, right))
  | Bind (a, b) ->
    let tail = prepend ([Addi (d, d + 1, 0l)], f) in
    let body = build (b, d :: rs, d + 1, tail) in
    build (a, rs, d, body)
  | If (c, t, e) ->
    let join = close f in
    let yes = build (t, rs, d, join) in
    let no = build (e, rs, d, resume (join.head, close yes)) in
    let test = { body = []; terminator = Branch (d, yes.fresh, no.fresh) } in
    build (c, rs, d, resume (test, close no))
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size e];;

let rec graph (e : expr) : func =
  let f = { head = { body = []; terminator = Return 1 };
            blocks_new = []; fresh = 0 } in
  let g = build (e, [], 1, f) in
  { entry = g.fresh; blocks = (g.fresh, g.head) :: g.blocks_new }
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec targets ((t : terminator), (limit : int)) : bool =
  match t with
  | Jump k -> 0 <= k && k < limit
  | Branch (r, yes, no) -> 0 <= yes && yes < limit && 0 <= no && no < limit
  | Return r -> true
[@@fn] [@@opaque] [@@decreases 0];;

let targets_mono (t : terminator) (limit : int) (limit2 : int) : unit =
  targets_unfold (t, limit);
  targets_unfold (t, limit2);
  match t with
  | Jump k -> ()
  | Branch (r, yes, no) -> ()
  | Return r -> ()
[@@ghost]
[@@spec fun t limit limit2 ->
  assert (targets (t, limit)); assert (limit <= limit2);
  ret (fun u -> assert (targets (t, limit2)))];;

(* Labels are consecutive in reverse order. Every edge points to an older
   block, so lookup succeeds and execution cannot follow a cycle. *)

let rec linked ((blocks : (int * block) list), (limit : int)) : bool =
  match blocks with
  | [] -> limit = 0
  | pair :: rest ->
    let (label, b) = pair in
    label = limit - 1 && 0 <= label && targets (b.terminator, label)
      && linked (rest, label)
[@@fn] [@@opaque] [@@decreases Logic.size blocks];;

let rec formed (f : fragment) : bool =
  0 <= f.fresh && linked (f.blocks_new, f.fresh)
    && targets (f.head.terminator, f.fresh)
[@@fn] [@@opaque] [@@decreases 0];;

let prepend_formed (body : instr list) (f : fragment) : unit =
  formed_unfold f;
  prepend_unfold (body, f);
  formed_unfold (prepend (body, f))
[@@ghost]
[@@spec fun body f ->
  assert (formed f);
  ret (fun u -> assert (formed (prepend (body, f)));
                assert ((prepend (body, f)).fresh = f.fresh))];;

let close_formed (f : fragment) : unit =
  formed_unfold f;
  close_unfold f;
  formed_unfold (close f);
  linked_unfold ((close f).blocks_new, (close f).fresh);
  targets_unfold ((close f).head.terminator, (close f).fresh)
[@@ghost]
[@@spec fun f ->
  assert (formed f);
  ret (fun u -> assert (formed (close f));
                assert ((close f).fresh = f.fresh + 1))];;

let resume_formed (head : block) (f : fragment) : unit =
  formed_unfold f;
  resume_unfold (head, f);
  formed_unfold (resume (head, f))
[@@ghost]
[@@spec fun head f ->
  assert (formed f); assert (targets (head.terminator, f.fresh));
  ret (fun u -> assert (formed (resume (head, f)));
                assert ((resume (head, f)).fresh = f.fresh))];;

let rec build_formed (e : expr) (rs : int list) (d : int) (f : fragment)
    : unit =
  build_unfold (e, rs, d, f);
  match e with
  | Cst c -> prepend_formed [Lui (d, hi c); Addi (d, d, lo c)] f
  | Var i -> prepend_formed [Addi (d, reg (rs, i), 0l)] f
  | Plus (a, b) ->
    (match literal b with
     | Some c ->
       prepend_formed [Addi (d, d, c)] f;
       build_formed a rs d (prepend ([Addi (d, d, c)], f))
     | None ->
       let tail = prepend ([Add (d, d, d + 1)], f) in
       prepend_formed [Add (d, d, d + 1)] f;
       build_formed b rs (d + 1) tail;
       build_formed a rs d (build (b, rs, d + 1, tail)))
  | Bind (a, b) ->
    let tail = prepend ([Addi (d, d + 1, 0l)], f) in
    prepend_formed [Addi (d, d + 1, 0l)] f;
    build_formed b (d :: rs) (d + 1) tail;
    build_formed a rs d (build (b, d :: rs, d + 1, tail))
  | If (c, t, e) ->
    let join = close f in
    close_formed f;
    build_formed t rs d join;
    let yes = build (t, rs, d, join) in
    close_formed yes;
    formed_unfold join;
    targets_mono join.head.terminator join.fresh (close yes).fresh;
    resume_formed join.head (close yes);
    let other = resume (join.head, close yes) in
    build_formed e rs d other;
    let no = build (e, rs, d, other) in
    close_formed no;
    let test = { body = []; terminator = Branch (d, yes.fresh, no.fresh) } in
    formed_unfold yes;
    targets_unfold (test.terminator, (close no).fresh);
    resume_formed test (close no);
    build_formed c rs d (resume (test, close no))
[@@ghost]
[@@spec fun e rs d f ->
  assert (formed f);
  ret (fun u -> assert (formed (build (e, rs, d, f)));
                assert (f.fresh <= (build (e, rs, d, f)).fresh))]
[@@decreases Logic.size e];;

let rec linked_lookup (blocks : (int * block) list) (limit : int) (label : int)
    : unit =
  linked_unfold (blocks, limit);
  lookup_unfold (blocks, label);
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (k, b) = pair in
    if k = label then () else linked_lookup rest k label
[@@ghost]
[@@spec fun blocks limit label ->
  assert (linked (blocks, limit)); assert (0 <= label); assert (label < limit);
  ret (fun u -> assert (
    match lookup (blocks, label) with
    | None -> false
    | Some b -> targets (b.terminator, label)))]
[@@decreases Logic.size blocks];;

let transfer_target (t : terminator) (v : int32 vec) (limit : int) : unit =
  targets_unfold (t, limit);
  match t with
  | Jump k -> ()
  | Branch (r, yes, no) -> ()
  | Return r -> ()
[@@ghost]
[@@spec fun t v limit ->
  assert (targets (t, limit));
  ret (fun u -> assert (
    match transfer (t, v) with
    | Next k -> 0 <= k && k < limit
    | Done x -> true))];;

let graph_linked (e : expr) : unit =
  graph_unfold e;
  let f = { head = { body = []; terminator = Return 1 };
            blocks_new = []; fresh = 0 } in
  formed_unfold f;
  linked_unfold ([], 0);
  targets_unfold (Return 1, 0);
  build_formed e [] 1 f;
  let g = build (e, [], 1, f) in
  formed_unfold g;
  linked_unfold ((graph e).blocks, (graph e).entry + 1)
[@@ghost]
[@@spec fun e ->
  ret (fun u -> assert (0 <= (graph e).entry);
    assert (linked ((graph e).blocks, (graph e).entry + 1)))];;

(* The condition is dead before either alternative starts. All three parts
   therefore use the same destination and scratch registers. *)

let rec need (e : expr) : int =
  match e with
  | Cst c -> 1
  | Var i -> 1
  | Plus (a, b) ->
    (match literal b with
     | Some c -> need a
     | None ->
       let ha = need a in
       let hb = 1 + need b in
       if ha > hb then ha else hb)
  | Bind (a, b) ->
    let ha = need a in
    let hb = 1 + need b in
    if ha > hb then ha else hb
  | If (c, t, e) ->
    let hc = need c in
    let ht = need t in
    let he = need e in
    let h = if hc > ht then hc else ht in
    if h > he then h else he
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size e];;

let rec need_positive (e : expr) : unit =
  need_unfold e;
  match e with
  | Cst c -> ()
  | Var i -> ()
  | Plus (a, b) ->
    need_positive a;
    (match literal b with Some c -> () | None -> need_positive b)
  | Bind (a, b) -> need_positive a; need_positive b
  | If (c, t, e) -> need_positive c; need_positive t; need_positive e
[@@ghost]
[@@spec fun e -> ret (fun u -> assert (1 <= need e))]
[@@decreases Logic.size e];;

(* Register-state semantics of expression evaluation. This supplies the
   intermediate states for the CFG continuation proof. *)

let rec compute ((e : expr), (rs : int list), (d : int), (v : int32 vec))
    : int32 vec =
  match e with
  | Cst c -> exec ([Lui (d, hi c); Addi (d, d, lo c)], v)
  | Var i -> exec ([Addi (d, reg (rs, i), 0l)], v)
  | Plus (a, b) ->
    let v1 = compute (a, rs, d, v) in
    (match literal b with
     | Some c -> exec ([Addi (d, d, c)], v1)
     | None ->
       let v2 = compute (b, rs, d + 1, v1) in
       exec ([Add (d, d, d + 1)], v2))
  | Bind (a, b) ->
    let v1 = compute (a, rs, d, v) in
    let v2 = compute (b, d :: rs, d + 1, v1) in
    exec ([Addi (d, d + 1, 0l)], v2)
  | If (c, t, e) ->
    let v1 = compute (c, rs, d, v) in
    if Int32.equal (get (v1, d)) 0l then compute (e, rs, d, v1)
    else compute (t, rs, d, v1)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size e];;

let add_value (d : int) (a : int) (b : int) (v : int32 vec) : unit =
  exec_one (Add (d, a, b)) v;
  get_set_at v d (Int32.add (get (v, a)) (get (v, b)))
[@@ghost]
[@@spec fun d a b v ->
  assert (1 <= d); assert (d < Vec.length v);
  ret (fun u -> assert (Int32.equal
    (get (exec ([Add (d, a, b)], v), d))
    (Int32.add (get (v, a)) (get (v, b)))))];;

let rec compute_correct (whole : expr) (rs : int list) (env : int32 list)
                        (d : int) (v : int32 vec) : unit =
  compute_unfold (whole, rs, d, v);
  need_unfold whole;
  need_positive whole;
  eval_unfold (whole, env);
  match whole with
  | Cst c ->
    let upper = Lui (d, hi c) in
    let lower = Addi (d, d, lo c) in
    let v1 = step (upper, v) in
    let v2 = step (lower, v1) in
    const_code d c v;
    exec_length [upper; lower] v;
    exec_cons upper [lower] v;
    exec_one lower v1;
    same_set v d (hi c) d;
    same_set v1 d (Int32.add (get (v1, d)) (lo c)) d;
    same_trans v2 v1 v d
  | Var i ->
    agree_nth rs env v i;
    leaf_code d (reg (rs, i)) 0l v;
    exec_length [Addi (d, reg (rs, i), 0l)] v;
    same_set v d (Int32.add (get (v, reg (rs, i))) 0l) d
  | Plus (a, b) ->
    compute_correct a rs env d v;
    let v1 = compute (a, rs, d, v) in
    (match literal b with
     | Some c ->
       literal_eval b env c;
       exec_one (Addi (d, d, c)) v1;
       let x = Int32.add (get (v1, d)) c in
       get_set_at v1 d x;
       same_set v1 d x d;
       same_trans (set (v1, d, x)) v1 v d
     | None ->
       agree_frame rs env v v1 d;
       below_mono rs d (d + 1);
       compute_correct b rs env (d + 1) v1;
       let v2 = compute (b, rs, d + 1, v1) in
       exec_one (Add (d, d, d + 1)) v2;
       add_value d d (d + 1) v2;
       let x = Int32.add (get (v2, d)) (get (v2, d + 1)) in
       same_at v2 v1 (d + 1) d;
       get_set_at v2 d x;
       same_set v2 d x d;
       same_narrow v2 v1 (d + 1) d;
       same_trans (set (v2, d, x)) v2 v1 d;
       same_trans (set (v2, d, x)) v1 v d)
  | Bind (a, b) ->
    compute_correct a rs env d v;
    let v1 = compute (a, rs, d, v) in
    agree_frame rs env v v1 d;
    agree_cons d rs (eval (a, env)) env v1;
    below_mono rs d (d + 1);
    below_cons d rs (d + 1);
    compute_correct b (d :: rs) (eval (a, env) :: env) (d + 1) v1;
    let v2 = compute (b, d :: rs, d + 1, v1) in
    exec_one (Addi (d, d + 1, 0l)) v2;
    let x = get (v2, d + 1) in
    get_set_at v2 d x;
    same_set v2 d x d;
    same_narrow v2 v1 (d + 1) d;
    same_trans (set (v2, d, x)) v2 v1 d;
    same_trans (set (v2, d, x)) v1 v d
  | If (c, t, e) ->
    compute_correct c rs env d v;
    let v1 = compute (c, rs, d, v) in
    agree_frame rs env v v1 d;
    if Int32.equal (get (v1, d)) 0l then begin
      compute_correct e rs env d v1;
      same_trans (compute (e, rs, d, v1)) v1 v d
    end else begin
      compute_correct t rs env d v1;
      same_trans (compute (t, rs, d, v1)) v1 v d
    end
[@@ghost]
[@@spec fun whole rs env d v ->
  assert (1 <= d); assert (d + need whole <= Vec.length v);
  assert (below (rs, d)); assert (agree (rs, env, v));
  ret (fun u ->
    assert (Vec.length (compute (whole, rs, d, v)) = Vec.length v);
    assert (Int32.equal (get (compute (whole, rs, d, v), d)) (eval (whole, env)));
    assert (same (compute (whole, rs, d, v), v, d)))]
[@@decreases Logic.size whole];;

(* Continuation semantics for a reverse-ordered block table. Every transfer
   consumes its block; [linked] ensures that all successors are in the tail. *)

let rec follow ((blocks : (int * block) list), (label : int), (v : int32 vec))
    : execution =
  match blocks with
  | [] -> Failed "CFG label is undefined"
  | pair :: rest ->
    let (k, b) = pair in
    if label <> k then follow (rest, label, v)
    else
      let w = exec (b.body, v) in
      match transfer (b.terminator, w) with
      | Next next -> follow (rest, next, w)
      | Done x -> Returned (x, w)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size blocks];;

let rec finish ((f : fragment), (v : int32 vec)) : execution =
  let w = exec (f.head.body, v) in
  match transfer (f.head.terminator, w) with
  | Next k -> follow (f.blocks_new, k, w)
  | Done x -> Returned (x, w)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let prepend_finish (body : instr list) (f : fragment) (v : int32 vec) : unit =
  prepend_unfold (body, f);
  finish_unfold (prepend (body, f), v);
  finish_unfold (f, exec (body, v));
  prepend_exec body f v
[@@ghost]
[@@spec fun body f v ->
  ret (fun u -> assert (Logic.eq (finish (prepend (body, f), v))
                               (finish (f, exec (body, v)))))];;

let close_finish (f : fragment) (v : int32 vec) : unit =
  close_unfold f;
  finish_unfold (close f, v);
  finish_unfold (f, v);
  exec_unfold ([], v);
  follow_unfold ((close f).blocks_new, f.fresh, v)
[@@ghost]
[@@spec fun f v ->
  ret (fun u -> assert (Logic.eq (finish (close f, v)) (finish (f, v))))];;

let close_follow (f : fragment) (label : int) (v : int32 vec) : unit =
  close_unfold f;
  follow_unfold ((close f).blocks_new, label, v)
[@@ghost]
[@@spec fun f label v ->
  assert (label < f.fresh);
  ret (fun u -> assert (Logic.eq (follow ((close f).blocks_new, label, v))
                               (follow (f.blocks_new, label, v))))];;

let rec build_follow (e : expr) (rs : int list) (d : int) (f : fragment)
                     (label : int) (v : int32 vec) : unit =
  build_unfold (e, rs, d, f);
  match e with
  | Cst c -> prepend_unfold ([Lui (d, hi c); Addi (d, d, lo c)], f)
  | Var i -> prepend_unfold ([Addi (d, reg (rs, i), 0l)], f)
  | Plus (a, b) ->
    (match literal b with
     | Some c ->
       let tail = prepend ([Addi (d, d, c)], f) in
       prepend_unfold ([Addi (d, d, c)], f);
       prepend_formed [Addi (d, d, c)] f;
       build_follow a rs d tail label v
     | None ->
       let tail = prepend ([Add (d, d, d + 1)], f) in
       prepend_unfold ([Add (d, d, d + 1)], f);
       prepend_formed [Add (d, d, d + 1)] f;
       build_formed b rs (d + 1) tail;
       build_follow b rs (d + 1) tail label v;
       build_follow a rs d (build (b, rs, d + 1, tail)) label v)
  | Bind (a, b) ->
    let tail = prepend ([Addi (d, d + 1, 0l)], f) in
    prepend_unfold ([Addi (d, d + 1, 0l)], f);
    prepend_formed [Addi (d, d + 1, 0l)] f;
    build_formed b (d :: rs) (d + 1) tail;
    build_follow b (d :: rs) (d + 1) tail label v;
    build_follow a rs d (build (b, d :: rs, d + 1, tail)) label v
  | If (c, t, e) ->
    let join = close f in
    close_formed f;
    close_follow f label v;
    build_formed t rs d join;
    build_follow t rs d join label v;
    let yes = build (t, rs, d, join) in
    close_formed yes;
    close_follow yes label v;
    formed_unfold join;
    targets_mono join.head.terminator join.fresh (close yes).fresh;
    resume_formed join.head (close yes);
    resume_unfold (join.head, close yes);
    let other = resume (join.head, close yes) in
    build_formed e rs d other;
    build_follow e rs d other label v;
    let no = build (e, rs, d, other) in
    close_formed no;
    close_follow no label v;
    let test = { body = []; terminator = Branch (d, yes.fresh, no.fresh) } in
    formed_unfold yes;
    targets_unfold (test.terminator, (close no).fresh);
    resume_formed test (close no);
    resume_unfold (test, close no);
    build_follow c rs d (resume (test, close no)) label v
[@@ghost]
[@@spec fun e rs d f label v ->
  assert (formed f); assert (label < f.fresh);
  ret (fun u -> assert (Logic.eq
    (follow ((build (e, rs, d, f)).blocks_new, label, v))
    (follow (f.blocks_new, label, v))))]
[@@decreases Logic.size e];;

let close_context (head : block) (f : fragment) (v : int32 vec) : unit =
  resume_unfold (head, close f);
  resume_unfold (head, f);
  finish_unfold (resume (head, close f), v);
  finish_unfold (resume (head, f), v);
  let w = exec (head.body, v) in
  transfer_target head.terminator w f.fresh;
  match transfer (head.terminator, w) with
  | Next k -> close_follow f k w
  | Done x -> ()
[@@ghost]
[@@spec fun head f v ->
  assert (targets (head.terminator, f.fresh));
  ret (fun u -> assert (Logic.eq (finish (resume (head, close f), v))
                               (finish (resume (head, f), v))))];;

let build_context (e : expr) (rs : int list) (d : int) (f : fragment)
                  (head : block) (v : int32 vec) : unit =
  resume_unfold (head, build (e, rs, d, f));
  resume_unfold (head, f);
  finish_unfold (resume (head, build (e, rs, d, f)), v);
  finish_unfold (resume (head, f), v);
  let w = exec (head.body, v) in
  transfer_target head.terminator w f.fresh;
  match transfer (head.terminator, w) with
  | Next k -> build_follow e rs d f k w
  | Done x -> ()
[@@ghost]
[@@spec fun e rs d f head v ->
  assert (formed f); assert (targets (head.terminator, f.fresh));
  ret (fun u -> assert (Logic.eq
    (finish (resume (head, build (e, rs, d, f)), v))
    (finish (resume (head, f), v))))];;

let follow_entry (f : fragment) (v : int32 vec) : unit =
  close_unfold f;
  follow_unfold ((close f).blocks_new, f.fresh, v);
  finish_unfold (f, v)
[@@ghost]
[@@spec fun f v ->
  ret (fun u -> assert (Logic.eq (follow ((close f).blocks_new, f.fresh, v))
                               (finish (f, v))))];;

let rec build_correct (whole : expr) (rs : int list) (d : int)
                      (f : fragment) (v : int32 vec) : unit =
  build_unfold (whole, rs, d, f);
  compute_unfold (whole, rs, d, v);
  match whole with
  | Cst c -> prepend_finish [Lui (d, hi c); Addi (d, d, lo c)] f v
  | Var i -> prepend_finish [Addi (d, reg (rs, i), 0l)] f v
  | Plus (a, b) ->
    let v1 = compute (a, rs, d, v) in
    (match literal b with
     | Some c ->
       let tail = prepend ([Addi (d, d, c)], f) in
       prepend_formed [Addi (d, d, c)] f;
       build_correct a rs d tail v;
       prepend_finish [Addi (d, d, c)] f v1
     | None ->
       let tail = prepend ([Add (d, d, d + 1)], f) in
       prepend_formed [Add (d, d, d + 1)] f;
       build_formed b rs (d + 1) tail;
       build_correct a rs d (build (b, rs, d + 1, tail)) v;
       build_correct b rs (d + 1) tail v1;
       prepend_finish [Add (d, d, d + 1)] f (compute (b, rs, d + 1, v1)))
  | Bind (a, b) ->
    let tail = prepend ([Addi (d, d + 1, 0l)], f) in
    prepend_formed [Addi (d, d + 1, 0l)] f;
    build_formed b (d :: rs) (d + 1) tail;
    build_correct a rs d (build (b, d :: rs, d + 1, tail)) v;
    let v1 = compute (a, rs, d, v) in
    build_correct b (d :: rs) (d + 1) tail v1;
    prepend_finish [Addi (d, d + 1, 0l)] f (compute (b, d :: rs, d + 1, v1))
  | If (c, t, e) ->
    let join = close f in
    close_formed f;
    build_formed t rs d join;
    let yes = build (t, rs, d, join) in
    close_formed yes;
    formed_unfold join;
    targets_mono join.head.terminator join.fresh (close yes).fresh;
    resume_formed join.head (close yes);
    let other = resume (join.head, close yes) in
    build_formed e rs d other;
    let no = build (e, rs, d, other) in
    close_formed no;
    let test = { body = []; terminator = Branch (d, yes.fresh, no.fresh) } in
    formed_unfold yes;
    targets_unfold (test.terminator, (close no).fresh);
    resume_formed test (close no);
    let branch = resume (test, close no) in
    build_correct c rs d branch v;
    let v1 = compute (c, rs, d, v) in
    resume_unfold (test, close no);
    finish_unfold (branch, v1);
    exec_unfold ([], v1);
    if Int32.equal (get (v1, d)) 0l then begin
      follow_entry no v1;
      build_correct e rs d other v1;
      let w = compute (e, rs, d, v1) in
      targets_mono join.head.terminator join.fresh yes.fresh;
      close_context join.head yes w;
      build_context t rs d join join.head w;
      resume_unfold (join.head, join);
      close_finish f w
    end else begin
      close_follow no yes.fresh v1;
      build_follow e rs d other yes.fresh v1;
      resume_unfold (join.head, close yes);
      follow_entry yes v1;
      build_correct t rs d join v1;
      close_finish f (compute (t, rs, d, v1))
    end
[@@ghost]
[@@spec fun whole rs d f v ->
  assert (formed f);
  ret (fun u -> assert (Logic.eq (finish (build (whole, rs, d, f), v))
                               (finish (f, compute (whole, rs, d, v))))) ]
[@@decreases Logic.size whole];;

(* A newer block is unreachable from the older, closed subgraph. *)

let rec run_drop (blocks : (int * block) list) (limit : int) (head : block)
                 (label : int) (v : int32 vec) (fuel : int) : unit =
  let f = { entry = 0; blocks = (limit, head) :: blocks } in
  let g = { entry = 0; blocks = blocks } in
  run_unfold (f, label, v, fuel);
  run_unfold (g, label, v, fuel);
  if fuel <= 0 then () else begin
    lookup_unfold (f.blocks, label);
    linked_lookup blocks limit label;
    match lookup (blocks, label) with
    | None -> ()
    | Some b ->
      let w = exec (b.body, v) in
      transfer_target b.terminator w label;
      match transfer (b.terminator, w) with
      | Next k -> run_drop blocks limit head k w (fuel - 1)
      | Done x -> ()
  end
[@@ghost]
[@@spec fun blocks limit head label v fuel ->
  assert (linked (blocks, limit)); assert (0 <= label); assert (label < limit);
  ret (fun u -> assert (Logic.eq
    (run ({ entry = 0; blocks = (limit, head) :: blocks }, label, v, fuel))
    (run ({ entry = 0; blocks = blocks }, label, v, fuel))))]
[@@decreases fuel];;

let rec run_entry (f : func) (entry : int) (label : int) (v : int32 vec)
                  (fuel : int) : unit =
  let g = { entry = entry; blocks = f.blocks } in
  run_unfold (f, label, v, fuel);
  run_unfold (g, label, v, fuel);
  if fuel <= 0 then ()
  else match lookup (f.blocks, label) with
  | None -> ()
  | Some b ->
    let w = exec (b.body, v) in
    match transfer (b.terminator, w) with
    | Next k -> run_entry f entry k w (fuel - 1)
    | Done x -> ()
[@@ghost]
[@@spec fun f entry label v fuel ->
  ret (fun u -> assert (Logic.eq (run (f, label, v, fuel))
    (run ({ entry = entry; blocks = f.blocks }, label, v, fuel))))]
[@@decreases fuel];;

let rec follow_run (blocks : (int * block) list) (limit : int) (label : int)
                   (v : int32 vec) (fuel : int) : unit =
  linked_unfold (blocks, limit);
  follow_unfold (blocks, label, v);
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (k, b) = pair in
    if label <> k then begin
      run_drop rest k b label v fuel;
      follow_run rest k label v fuel
    end else begin
      let f = { entry = 0; blocks = blocks } in
      run_unfold (f, label, v, fuel);
      lookup_unfold (blocks, label);
      let w = exec (b.body, v) in
      transfer_target b.terminator w k;
      match transfer (b.terminator, w) with
      | Next next ->
        run_drop rest k b next w (fuel - 1);
        follow_run rest k next w (fuel - 1)
      | Done x -> ()
    end
[@@ghost]
[@@spec fun blocks limit label v fuel ->
  assert (linked (blocks, limit)); assert (0 <= label); assert (label < limit);
  assert (label < fuel);
  ret (fun u -> assert (Logic.eq (follow (blocks, label, v))
    (run ({ entry = 0; blocks = blocks }, label, v, fuel))))]
[@@decreases Logic.size blocks];;

let graph_correct (e : expr) (v : int32 vec) : unit =
  graph_unfold e;
  let f = { head = { body = []; terminator = Return 1 };
            blocks_new = []; fresh = 0 } in
  formed_unfold f;
  linked_unfold ([], 0);
  targets_unfold (Return 1, 0);
  build_correct e [] 1 f v;
  let g = build (e, [], 1, f) in
  follow_entry g v;
  close_unfold g;
  graph_linked e;
  follow_run (graph e).blocks ((graph e).entry + 1) (graph e).entry v
             ((graph e).entry + 1);
  run_entry (graph e) 0 (graph e).entry v ((graph e).entry + 1);
  below_unfold ([], 1);
  agree_unfold ([], [], v);
  compute_correct e [] [] 1 v;
  finish_unfold (f, compute (e, [], 1, v));
  exec_unfold ([], compute (e, [], 1, v))
[@@ghost]
[@@spec fun e v ->
  assert (1 + need e <= Vec.length v);
  ret (fun u -> assert (
    match run (graph e, (graph e).entry, v, (graph e).entry + 1) with
    | Returned (x, w) -> Int32.equal x (eval (e, []))
      && Int32.equal (get (w, 1)) x && same (w, v, 1)
    | Failed reason -> false
    | Exhausted -> false))];;

let conditional_case (c : int32) : unit =
  let e = If (Cst c, Cst 7l, Cst 9l) in
  need_unfold e;
  need_unfold (Cst c);
  need_unfold (Cst 7l);
  need_unfold (Cst 9l);
  eval_unfold (e, []);
  eval_unfold (Cst c, []);
  eval_unfold (Cst 7l, []);
  eval_unfold (Cst 9l, []);
  graph_correct e (Vec.make 2 0l)
[@@ghost]
[@@spec fun c ->
  ret (fun u -> assert (
    let e = If (Cst c, Cst 7l, Cst 9l) in
    need e = 1 &&
    match run (graph e, (graph e).entry, Vec.make 2 0l, (graph e).entry + 1) with
    | Returned (x, w) -> Int32.equal x (if Int32.equal c 0l then 9l else 7l)
    | Failed reason -> false
    | Exhausted -> false))];;

let rec terminator_allocation ((t : terminator), (n : int)) : bool =
  match t with
  | Jump k -> true
  | Branch (r, yes, no) -> location_wf (locate r, n)
  | Return r -> location_wf (locate r, n)
[@@fn] [@@opaque] [@@decreases 0];;

let rec block_allocation ((b : block), (n : int)) : bool =
  allocation (b.body, n) && terminator_allocation (b.terminator, n)
[@@fn] [@@opaque] [@@decreases 0];;

let rec blocks_allocation ((blocks : (int * block) list), (n : int)) : bool =
  match blocks with
  | [] -> true
  | pair :: rest ->
    let (label, b) = pair in
    block_allocation (b, n) && blocks_allocation (rest, n)
[@@fn] [@@opaque] [@@decreases Logic.size blocks];;

let rec fragment_allocation ((f : fragment), (n : int)) : bool =
  block_allocation (f.head, n) && blocks_allocation (f.blocks_new, n)
[@@fn] [@@opaque] [@@decreases 0];;

let prepend_allocation (body : instr list) (f : fragment) (n : int) : unit =
  prepend_unfold (body, f);
  fragment_allocation_unfold (f, n);
  block_allocation_unfold (f.head, n);
  app_allocation body f.head.body n;
  block_allocation_unfold ((prepend (body, f)).head, n);
  fragment_allocation_unfold (prepend (body, f), n)
[@@ghost]
[@@spec fun body f n ->
  assert (allocation (body, n)); assert (fragment_allocation (f, n));
  ret (fun u -> assert (fragment_allocation (prepend (body, f), n)))];;

let close_allocation (f : fragment) (n : int) : unit =
  close_unfold f;
  fragment_allocation_unfold (f, n);
  fragment_allocation_unfold (close f, n);
  block_allocation_unfold ((close f).head, n);
  allocation_nil n;
  terminator_allocation_unfold (Jump f.fresh, n);
  blocks_allocation_unfold ((close f).blocks_new, n)
[@@ghost]
[@@spec fun f n ->
  assert (fragment_allocation (f, n));
  ret (fun u -> assert (fragment_allocation (close f, n)))];;

let resume_allocation (head : block) (f : fragment) (n : int) : unit =
  resume_unfold (head, f);
  fragment_allocation_unfold (f, n);
  fragment_allocation_unfold (resume (head, f), n)
[@@ghost]
[@@spec fun head f n ->
  assert (block_allocation (head, n)); assert (fragment_allocation (f, n));
  ret (fun u -> assert (fragment_allocation (resume (head, f), n)))];;

let rec build_allocation (whole : expr) (rs : int list) (d : int)
                         (f : fragment) (limit : int) : unit =
  build_unfold (whole, rs, d, f);
  need_unfold whole;
  need_positive whole;
  let n = slots limit in
  allocated limit d;
  allocation_nil n;
  match whole with
  | Cst c ->
    fields c;
    allocation_cons (Addi (d, d, lo c)) [] n;
    allocation_cons (Lui (d, hi c)) [Addi (d, d, lo c)] n;
    prepend_allocation [Lui (d, hi c); Addi (d, d, lo c)] f n
  | Var i ->
    reg_bound rs d i;
    allocated limit (reg (rs, i));
    allocation_cons (Addi (d, reg (rs, i), 0l)) [] n;
    prepend_allocation [Addi (d, reg (rs, i), 0l)] f n
  | Plus (a, b) ->
    (match literal b with
     | Some c ->
       literal_wf b c;
       allocation_cons (Addi (d, d, c)) [] n;
       prepend_allocation [Addi (d, d, c)] f n;
       build_allocation a rs d (prepend ([Addi (d, d, c)], f)) limit
     | None ->
       need_positive b;
       allocated limit (d + 1);
       allocation_cons (Add (d, d, d + 1)) [] n;
       prepend_allocation [Add (d, d, d + 1)] f n;
       let tail = prepend ([Add (d, d, d + 1)], f) in
       below_mono rs d (d + 1);
       build_allocation b rs (d + 1) tail limit;
       build_allocation a rs d (build (b, rs, d + 1, tail)) limit)
  | Bind (a, b) ->
    need_positive b;
    allocated limit (d + 1);
    allocation_cons (Addi (d, d + 1, 0l)) [] n;
    prepend_allocation [Addi (d, d + 1, 0l)] f n;
    let tail = prepend ([Addi (d, d + 1, 0l)], f) in
    below_mono rs d (d + 1);
    below_cons d rs (d + 1);
    build_allocation b (d :: rs) (d + 1) tail limit;
    build_allocation a rs d (build (b, d :: rs, d + 1, tail)) limit
  | If (c, t, e) ->
    close_allocation f n;
    let join = close f in
    build_allocation t rs d join limit;
    let yes = build (t, rs, d, join) in
    close_allocation yes n;
    fragment_allocation_unfold (join, n);
    resume_allocation join.head (close yes) n;
    let other = resume (join.head, close yes) in
    build_allocation e rs d other limit;
    let no = build (e, rs, d, other) in
    close_allocation no n;
    let test = { body = []; terminator = Branch (d, yes.fresh, no.fresh) } in
    block_allocation_unfold (test, n);
    terminator_allocation_unfold (test.terminator, n);
    resume_allocation test (close no) n;
    build_allocation c rs d (resume (test, close no)) limit
[@@ghost]
[@@spec fun whole rs d f limit ->
  assert (1 <= d); assert (d + need whole <= limit); assert (below (rs, d));
  assert (fragment_allocation (f, slots limit));
  ret (fun u -> assert (fragment_allocation (build (whole, rs, d, f), slots limit)))]
[@@decreases Logic.size whole];;

let graph_allocation (e : expr) (limit : int) : unit =
  graph_unfold e;
  need_positive e;
  allocated limit 1;
  let f = { head = { body = []; terminator = Return 1 };
            blocks_new = []; fresh = 0 } in
  fragment_allocation_unfold (f, slots limit);
  block_allocation_unfold (f.head, slots limit);
  blocks_allocation_unfold ([], slots limit);
  terminator_allocation_unfold (Return 1, slots limit);
  allocation_nil (slots limit);
  below_unfold ([], 1);
  build_allocation e [] 1 f limit;
  let g = build (e, [], 1, f) in
  fragment_allocation_unfold (g, slots limit);
  blocks_allocation_unfold ((graph e).blocks, slots limit)
[@@ghost]
[@@spec fun e limit ->
  assert (1 + need e <= limit);
  ret (fun u -> assert (blocks_allocation ((graph e).blocks, slots limit)))];;

let nested_case (c : int32) : unit =
  let yes = Bind (Cst 40l, Plus (Var 0, Cst 2l)) in
  let no = If (Cst 1l, Cst 7l, Cst 9l) in
  let e = If (Cst c, yes, no) in
  need_unfold e;
  need_unfold (Cst c);
  need_unfold yes;
  need_unfold (Cst 40l);
  need_unfold (Plus (Var 0, Cst 2l));
  need_unfold (Var 0);
  need_unfold no;
  need_unfold (Cst 1l);
  need_unfold (Cst 7l);
  need_unfold (Cst 9l);
  eval_unfold (e, []);
  eval_unfold (Cst c, []);
  eval_unfold (yes, []);
  eval_unfold (Cst 40l, []);
  eval_unfold (Plus (Var 0, Cst 2l), [40l]);
  eval_unfold (Var 0, [40l]);
  nth_unfold ([40l], 0);
  eval_unfold (Cst 2l, [40l]);
  eval_unfold (no, []);
  eval_unfold (Cst 1l, []);
  eval_unfold (Cst 7l, []);
  graph_correct e (Vec.make 3 0l)
[@@ghost]
[@@spec fun c ->
  ret (fun u -> assert (
    let e = If (Cst c, Bind (Cst 40l, Plus (Var 0, Cst 2l)),
                If (Cst 1l, Cst 7l, Cst 9l)) in
    need e = 2 &&
    match run (graph e, (graph e).entry, Vec.make 3 0l, (graph e).entry + 1) with
    | Returned (x, w) -> Int32.equal x (if Int32.equal c 0l then 7l else 42l)
    | Failed reason -> false
    | Exhausted -> false))];;

(* ------------------------------------------------------------------ *)
(* Physical CFG                                                        *)
(* ------------------------------------------------------------------ *)

type block_physical = { body_physical : physical list; terminator_physical : terminator }

let rec physical_app ((c : physical list), (k : physical list)) : physical list =
  match c with
  | [] -> k
  | i :: rest -> i :: physical_app (rest, k)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let rec physical_app_exec (c : physical list) (k : physical list) (p : machine)
    : unit =
  physical_app_unfold (c, k);
  physical_exec_unfold (physical_app (c, k), p);
  physical_exec_unfold (c, p);
  match c with
  | [] -> ()
  | i :: rest -> physical_app_exec rest k (physical_step (i, p))
[@@ghost]
[@@spec fun c k p ->
  ret (fun u -> assert (Logic.eq (physical_exec (physical_app (c, k), p))
                               (physical_exec (k, physical_exec (c, p))))) ]
[@@decreases Logic.size c];;

(* A spilled terminator operand is loaded after the block body. *)

let rec ending (t : terminator) : block_physical =
  match t with
  | Jump k -> { body_physical = []; terminator_physical = Jump k }
  | Branch (r, yes, no) ->
    { body_physical = fetch (r, 29, []);
      terminator_physical = Branch (temporary (r, 29), yes, no) }
  | Return r ->
    { body_physical = fetch (r, 29, []);
      terminator_physical = Return (temporary (r, 29)) }
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec lower_block (b : block) : block_physical =
  let tail = ending b.terminator in
  { body_physical = physical_app (lower b.body, tail.body_physical);
    terminator_physical = tail.terminator_physical }
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec lower_blocks (blocks : (int * block) list) : (int * block_physical) list =
  match blocks with
  | [] -> []
  | pair :: rest ->
    let (label, b) = pair in
    (label, lower_block b) :: lower_blocks rest
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size blocks];;

let rec transfer_simulation ((v : transfer), (p : transfer)) : bool =
  match v with
  | Next k -> (match p with Next next -> k = next | Done x -> false)
  | Done x -> (match p with Next next -> false | Done y -> Int32.equal x y)
[@@fn ghost] [@@opaque] [@@decreases 0];;

let ending_correct (t : terminator) (v : int32 vec) (p : machine) : unit =
  ending_unfold t;
  transfer_simulation_unfold (transfer (t, v),
    transfer ((ending t).terminator_physical,
              (physical_exec ((ending t).body_physical, p)).regs));
  terminator_allocation_unfold (t, slots (Vec.length v));
  match t with
  | Jump k -> physical_exec_unfold ([], p)
  | Branch (r, yes, no) ->
    location_bound r (Vec.length v);
    fetch_correct v p r 29;
    fetch_exec r 29 [] p;
    physical_exec_unfold ([], fetched (p, r, 29))
  | Return r ->
    location_bound r (Vec.length v);
    fetch_correct v p r 29;
    fetch_exec r 29 [] p;
    physical_exec_unfold ([], fetched (p, r, 29))
[@@ghost]
[@@spec fun t v p ->
  assert (simulation (v, p));
  assert (terminator_allocation (t, slots (Vec.length v)));
  ret (fun u ->
    assert (simulation (v, physical_exec ((ending t).body_physical, p)));
    assert (transfer_simulation (transfer (t, v),
      transfer ((ending t).terminator_physical,
                 (physical_exec ((ending t).body_physical, p)).regs))))];;

let lower_block_correct (b : block) (v : int32 vec) (p : machine) : unit =
  lower_block_unfold b;
  block_allocation_unfold (b, slots (Vec.length v));
  lower_correct b.body v p;
  exec_length b.body v;
  ending_correct b.terminator (exec (b.body, v)) (physical_exec (lower b.body, p));
  physical_app_exec (lower b.body) (ending b.terminator).body_physical p
[@@ghost]
[@@spec fun b v p ->
  assert (simulation (v, p)); assert (block_allocation (b, slots (Vec.length v)));
  ret (fun u ->
    assert (simulation (exec (b.body, v),
                        physical_exec ((lower_block b).body_physical, p)));
    assert (transfer_simulation (transfer (b.terminator, exec (b.body, v)),
      transfer ((lower_block b).terminator_physical,
                 (physical_exec ((lower_block b).body_physical, p)).regs))))];;

type execution_physical =
  | Returned_physical of int32 * machine
  | Failed_physical of string

let rec follow_physical ((blocks : (int * block_physical) list), (label : int),
                         (p : machine)) : execution_physical =
  match blocks with
  | [] -> Failed_physical "CFG label is undefined"
  | pair :: rest ->
    let (k, b) = pair in
    if label <> k then follow_physical (rest, label, p)
    else
      let q = physical_exec (b.body_physical, p) in
      if not q.ok then Failed_physical "CFG memory access failed"
      else match transfer (b.terminator_physical, q.regs) with
      | Next next -> follow_physical (rest, next, q)
      | Done x -> Returned_physical (x, q)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size blocks];;

let rec execution_simulation ((v : execution), (p : execution_physical)) : bool =
  match v with
  | Returned (x, w) ->
    (match p with
     | Returned_physical (y, q) -> Int32.equal x y && simulation (w, q)
     | Failed_physical reason -> false)
  | Failed reason ->
    (match p with
     | Returned_physical (y, q) -> false
     | Failed_physical reason -> true)
  | Exhausted -> false
[@@fn] [@@opaque] [@@decreases 0];;

let rec lower_blocks_correct (blocks : (int * block) list) (label : int)
                             (v : int32 vec) (p : machine) : unit =
  lower_blocks_unfold blocks;
  follow_unfold (blocks, label, v);
  follow_physical_unfold (lower_blocks blocks, label, p);
  blocks_allocation_unfold (blocks, slots (Vec.length v));
  match blocks with
  | [] -> execution_simulation_unfold (follow (blocks, label, v),
                                      follow_physical (lower_blocks blocks, label, p))
  | pair :: rest ->
    let (k, b) = pair in
    if label <> k then lower_blocks_correct rest label v p
    else begin
      lower_block_correct b v p;
      exec_length b.body v;
      let w = exec (b.body, v) in
      let q = physical_exec ((lower_block b).body_physical, p) in
      transfer_simulation_unfold (transfer (b.terminator, w),
                                  transfer ((lower_block b).terminator_physical, q.regs));
      match transfer (b.terminator, w) with
      | Next next -> lower_blocks_correct rest next w q
      | Done x ->
        (match transfer ((lower_block b).terminator_physical, q.regs) with
         | Next next -> ()
         | Done y -> execution_simulation_unfold (Returned (x, w), Returned_physical (y, q)))
    end
[@@ghost]
[@@spec fun blocks label v p ->
  assert (simulation (v, p));
  assert (blocks_allocation (blocks, slots (Vec.length v)));
  ret (fun u -> assert (execution_simulation (follow (blocks, label, v),
    follow_physical (lower_blocks blocks, label, p))))]
[@@decreases Logic.size blocks];;

let graph_physical_correct (e : expr) (v : int32 vec) (p : machine) : unit =
  need_positive e;
  graph_correct e v;
  graph_linked e;
  graph_allocation e (Vec.length v);
  follow_run (graph e).blocks ((graph e).entry + 1) (graph e).entry v
             ((graph e).entry + 1);
  run_entry (graph e) 0 (graph e).entry v ((graph e).entry + 1);
  lower_blocks_correct (graph e).blocks (graph e).entry v p;
  execution_simulation_unfold (follow ((graph e).blocks, (graph e).entry, v),
    follow_physical (lower_blocks (graph e).blocks, (graph e).entry, p));
  match follow ((graph e).blocks, (graph e).entry, v) with
  | Returned (x, w) ->
    (match follow_physical (lower_blocks (graph e).blocks, (graph e).entry, p) with
     | Returned_physical (y, q) ->
       run_length (graph e) (graph e).entry v ((graph e).entry + 1);
       represented_at w q (Vec.length w) 1
     | Failed_physical reason -> ())
  | Failed reason -> ()
  | Exhausted -> ()
[@@ghost]
[@@spec fun e v p ->
  assert (simulation (v, p)); assert (1 + need e <= Vec.length v);
  ret (fun u -> assert (
    match follow_physical (lower_blocks (graph e).blocks, (graph e).entry, p) with
    | Returned_physical (x, q) -> q.ok && Int32.equal x (eval (e, []))
      && Int32.equal (get (q.regs, 1)) x
    | Failed_physical reason -> false))];;

let rec terminator_valid (t : terminator) : bool =
  match t with
  | Jump k -> true
  | Branch (r, yes, no) -> register r
  | Return r -> register r
[@@fn] [@@opaque] [@@decreases 0];;

let rec block_valid (b : block_physical) : bool =
  physical_valid b.body_physical && terminator_valid b.terminator_physical
[@@fn] [@@opaque] [@@decreases 0];;

let rec blocks_valid (blocks : (int * block_physical) list) : bool =
  match blocks with
  | [] -> true
  | pair :: rest ->
    let (label, b) = pair in block_valid b && blocks_valid rest
[@@fn] [@@opaque] [@@decreases Logic.size blocks];;

let rec physical_app_valid (c : physical list) (k : physical list) : unit =
  physical_app_unfold (c, k);
  physical_valid_unfold c;
  physical_valid_unfold (physical_app (c, k));
  match c with
  | [] -> ()
  | i :: rest -> physical_app_valid rest k
[@@ghost]
[@@spec fun c k ->
  assert (physical_valid c); assert (physical_valid k);
  ret (fun u -> assert (physical_valid (physical_app (c, k))))]
[@@decreases Logic.size c];;

let ending_valid (t : terminator) (n : int) : unit =
  ending_unfold t;
  block_valid_unfold (ending t);
  terminator_allocation_unfold (t, n);
  terminator_valid_unfold (ending t).terminator_physical;
  physical_valid_unfold [];
  match t with
  | Jump k -> ()
  | Branch (r, yes, no) ->
    temporary_valid r 29 n;
    fetch_valid r 29 n []
  | Return r ->
    temporary_valid r 29 n;
    fetch_valid r 29 n []
[@@ghost]
[@@spec fun t n ->
  assert (terminator_allocation (t, n)); assert (n <= 512);
  ret (fun u -> assert (block_valid (ending t)))];;

let lower_block_valid (b : block) (n : int) : unit =
  block_allocation_unfold (b, n);
  lower_block_unfold b;
  lower_valid b.body n;
  ending_valid b.terminator n;
  block_valid_unfold (ending b.terminator);
  physical_app_valid (lower b.body) (ending b.terminator).body_physical;
  block_valid_unfold (lower_block b)
[@@ghost]
[@@spec fun b n ->
  assert (block_allocation (b, n)); assert (n <= 512);
  ret (fun u -> assert (block_valid (lower_block b)))];;

let rec lower_blocks_valid (blocks : (int * block) list) (n : int) : unit =
  lower_blocks_unfold blocks;
  blocks_allocation_unfold (blocks, n);
  blocks_valid_unfold (lower_blocks blocks);
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (label, b) = pair in
    lower_block_valid b n;
    lower_blocks_valid rest n
[@@ghost]
[@@spec fun blocks n ->
  assert (blocks_allocation (blocks, n)); assert (n <= 512);
  ret (fun u -> assert (blocks_valid (lower_blocks blocks)))]
[@@decreases Logic.size blocks];;

(* ------------------------------------------------------------------ *)
(* Forward RV32I layout                                                *)
(* ------------------------------------------------------------------ *)

(* [Jal] always has destination x0. Branch displacements are byte offsets
   from the current instruction. Code and spill memory are separate. *)

type instruction =
  | Op of physical
  | Bne of int * int * int
  | Jal of int

let rec code_app ((c : instruction list), (k : instruction list)) : instruction list =
  match c with
  | [] -> k
  | i :: rest -> i :: code_app (rest, k)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let rec code_size (c : instruction list) : int =
  match c with [] -> 0 | i :: rest -> 1 + code_size rest
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let rec physical_size (c : physical list) : int =
  match c with [] -> 0 | i :: rest -> 1 + physical_size rest
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let rec emit (c : physical list) : instruction list =
  match c with [] -> [] | i :: rest -> Op i :: emit rest
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let rec terminator_size (t : terminator) : int =
  match t with Jump k -> 1 | Branch (r, yes, no) -> 2 | Return r -> 2
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec span (b : block_physical) : int =
  physical_size b.body_physical + terminator_size b.terminator_physical
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec extent (blocks : (int * block_physical) list) : int =
  match blocks with
  | [] -> 0
  | pair :: rest -> let (label, b) = pair in span b + extent rest
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size blocks];;

let rec offset ((blocks : (int * block_physical) list), (label : int)) : int option =
  match blocks with
  | [] -> None
  | pair :: rest ->
    let (k, b) = pair in
    if label = k then Some 0
    else match offset (rest, label) with
    | None -> None
    | Some n -> Some (span b + n)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size blocks];;

(* Return copies the result to x1 and transfers to the fragment exit, just
   after the final instruction. There is no calling convention yet. *)

let rec exits ((t : terminator), (blocks : (int * block_physical) list))
    : instruction list option =
  match t with
  | Jump k ->
    (match offset (blocks, k) with
     | None -> None
     | Some n -> Some [Jal (4 * (1 + n))])
  | Branch (r, yes, no) ->
    (match offset (blocks, yes) with
     | None -> None
     | Some n ->
       match offset (blocks, no) with
       | None -> None
       | Some m -> Some [Bne (r, 0, 4 * (2 + n)); Jal (4 * (1 + m))])
  | Return r -> Some [Op (Alu (Addi (1, r, 0l))); Jal (4 * (1 + extent blocks))]
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;
(* Successors must occur later in the block table. A missing or backward
   successor returns None; long-branch expansion is not implemented. *)
let rec layout (blocks : (int * block_physical) list) : instruction list option =
  match blocks with
  | [] -> Some []
  | pair :: rest ->
    let (label, b) = pair in
    match layout rest with
    | None -> None
    | Some tail ->
      match exits (b.terminator_physical, rest) with
      | None -> None
      | Some ending -> Some (code_app (emit b.body_physical, code_app (ending, tail)))
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size blocks];;

let rec skip ((n : int), (c : instruction list)) : instruction list option =
  if n < 0 then None
  else if n = 0 then Some c
  else match c with [] -> None | i :: rest -> skip (n - 1, rest)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

(* This executor supports forward transfers only. Backward or unaligned
   transfers and targets beyond the fragment fail explicitly. *)

let rec destination ((delta : int), (tail : instruction list)) : instruction list option =
  if delta < 4 || delta mod 4 <> 0 then None else skip (delta / 4 - 1, tail)
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

type execution_code =
  | Completed of machine
  | Fault of string
  | Out_of_fuel

let rec execute ((c : instruction list), (p : machine), (fuel : int)) : execution_code =
  if not p.ok then Fault "instruction memory access failed"
  else match c with
  | [] -> Completed p
  | i :: tail ->
    if fuel <= 0 then Out_of_fuel
    else match i with
    | Op op -> execute (tail, physical_step (op, p), fuel - 1)
    | Bne (a, b, delta) ->
      if Int32.equal (get (p.regs, a)) (get (p.regs, b)) then execute (tail, p, fuel - 1)
      else (match destination (delta, tail) with
       | None -> Fault "unsupported backward, unaligned, or out-of-range branch"
       | Some next -> execute (next, p, fuel - 1))
    | Jal delta ->
      (match destination (delta, tail) with
       | None -> Fault "unsupported backward, unaligned, or out-of-range jump"
       | Some next -> execute (next, p, fuel - 1))
[@@fn ghost] [@@impl] [@@opaque] [@@decreases fuel];;

let rec instruction_valid (i : instruction) : bool =
  match i with
  | Op op -> physical_wf op
  | Bne (a, b, delta) -> register a && register b && 4 <= delta && delta <= 4094
      && delta mod 4 = 0
  | Jal delta -> 4 <= delta && delta <= 1048574 && delta mod 4 = 0
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let rec code_valid (c : instruction list) : bool =
  match c with [] -> true | i :: rest -> instruction_valid i && code_valid rest
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size c];;

let rec physical_size_nonneg (c : physical list) : unit =
  physical_size_unfold c;
  match c with [] -> () | i :: rest -> physical_size_nonneg rest
[@@ghost]
[@@spec fun c -> ret (fun u -> assert (0 <= physical_size c))]
[@@decreases Logic.size c];;

let rec code_size_nonneg (c : instruction list) : unit =
  code_size_unfold c;
  match c with [] -> () | i :: rest -> code_size_nonneg rest
[@@ghost]
[@@spec fun c -> ret (fun u -> assert (0 <= code_size c))]
[@@decreases Logic.size c];;

let span_positive (b : block_physical) : unit =
  span_unfold b;
  physical_size_nonneg b.body_physical;
  terminator_size_unfold b.terminator_physical;
  match b.terminator_physical with
  | Jump k -> () | Branch (r, yes, no) -> () | Return r -> ()
[@@ghost]
[@@spec fun b -> ret (fun u -> assert (1 <= span b))];;

let rec extent_nonneg (blocks : (int * block_physical) list) : unit =
  extent_unfold blocks;
  match blocks with
  | [] -> ()
  | pair :: rest -> let (label, b) = pair in span_positive b; extent_nonneg rest
[@@ghost]
[@@spec fun blocks -> ret (fun u -> assert (0 <= extent blocks))]
[@@decreases Logic.size blocks];;

let rec emit_size (c : physical list) : unit =
  emit_unfold c;
  code_size_unfold (emit c);
  physical_size_unfold c;
  match c with [] -> () | i :: rest -> emit_size rest
[@@ghost]
[@@spec fun c -> ret (fun u -> assert (code_size (emit c) = physical_size c))]
[@@decreases Logic.size c];;

let rec code_app_size (c : instruction list) (tail : instruction list) : unit =
  code_app_unfold (c, tail);
  code_size_unfold c;
  code_size_unfold (code_app (c, tail));
  match c with [] -> () | i :: rest -> code_app_size rest tail
[@@ghost]
[@@spec fun c tail ->
  ret (fun u -> assert (code_size (code_app (c, tail)) = code_size c + code_size tail))]
[@@decreases Logic.size c];;

let rec skip_app (c : instruction list) (tail : instruction list) (n : int) : unit =
  code_app_unfold (c, tail);
  code_size_unfold c;
  skip_unfold (code_size c + n, code_app (c, tail));
  match c with
  | [] -> skip_unfold (n, tail)
  | i :: rest -> code_size_nonneg rest; skip_app rest tail n
[@@ghost]
[@@spec fun c tail n ->
  assert (0 <= n);
  ret (fun u -> assert (Logic.eq (skip (code_size c + n, code_app (c, tail)))
                               (skip (n, tail))))]
[@@decreases Logic.size c];;

let rec skip_congr (c : instruction list) (n : int) (m : int) : unit =
  skip_unfold (n, c);
  skip_unfold (m, c);
  if n <= 0 then ()
  else match c with [] -> () | i :: rest -> skip_congr rest (n - 1) (m - 1)
[@@ghost]
[@@spec fun c n m ->
  assert (n = m);
  ret (fun u -> assert (Logic.eq (skip (n, c)) (skip (m, c))))]
[@@decreases Logic.size c];;

let rec skip_end (c : instruction list) : unit =
  code_size_unfold c;
  skip_unfold (code_size c, c);
  match c with
  | [] -> ()
  | i :: rest ->
    code_size_nonneg rest;
    skip_congr rest (code_size c - 1) (code_size rest);
    skip_end rest
[@@ghost]
[@@spec fun c -> ret (fun u -> assert (Logic.eq (skip (code_size c, c)) (Some [])))]
[@@decreases Logic.size c];;

let rec physical_exec_failed (c : physical list) (p : machine) : unit =
  physical_exec_unfold (c, p);
  match c with [] -> () | i :: rest -> physical_exec_failed rest p
[@@ghost]
[@@spec fun c p ->
  assert (not p.ok);
  ret (fun u -> assert (Logic.eq (physical_exec (c, p)) p))]
[@@decreases Logic.size c];;

let rec emit_execute (c : physical list) (tail : instruction list)
                     (p : machine) (fuel : int) : unit =
  emit_unfold c;
  code_app_unfold (emit c, tail);
  physical_size_unfold c;
  physical_exec_unfold (c, p);
  match c with
  | [] -> ()
  | i :: rest ->
    physical_size_nonneg rest;
    execute_unfold (code_app (emit c, tail), p, physical_size c + fuel);
    if p.ok then emit_execute rest tail (physical_step (i, p)) fuel
    else begin
      physical_exec_failed c p;
      execute_unfold (tail, p, fuel)
    end
[@@ghost]
[@@spec fun c tail p fuel ->
  assert (0 <= fuel);
  ret (fun u -> assert (Logic.eq
    (execute (code_app (emit c, tail), p, physical_size c + fuel))
    (execute (tail, physical_exec (c, p), fuel))))]
[@@decreases Logic.size c];;

let rec offset_bound (blocks : (int * block_physical) list) (label : int) : unit =
  offset_unfold (blocks, label);
  extent_unfold blocks;
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (k, b) = pair in
    span_positive b;
    extent_nonneg rest;
    if label = k then () else offset_bound rest label
[@@ghost]
[@@spec fun blocks label ->
  ret (fun u -> assert (
    match offset (blocks, label) with
    | None -> true
    | Some n -> 0 <= n && n < extent blocks))]
[@@decreases Logic.size blocks];;

let exits_size (t : terminator) (blocks : (int * block_physical) list) : unit =
  exits_unfold (t, blocks);
  terminator_size_unfold t;
  code_size_unfold [];
  match t with
  | Jump k ->
    (match offset (blocks, k) with
     | None -> ()
     | Some n -> code_size_unfold [Jal (4 * (1 + n))])
  | Branch (r, yes, no) ->
    (match offset (blocks, yes) with
     | None -> ()
     | Some n ->
       match offset (blocks, no) with
       | None -> ()
       | Some m ->
         code_size_unfold [Jal (4 * (1 + m))];
         code_size_unfold [Bne (r, 0, 4 * (2 + n)); Jal (4 * (1 + m))])
  | Return r ->
    code_size_unfold [Jal (4 * (1 + extent blocks))];
    code_size_unfold [Op (Alu (Addi (1, r, 0l))); Jal (4 * (1 + extent blocks))]
[@@ghost]
[@@spec fun t blocks ->
  ret (fun u -> assert (
    match exits (t, blocks) with None -> true | Some c -> code_size c = terminator_size t))];;

let rec layout_size (blocks : (int * block_physical) list) : unit =
  layout_unfold blocks;
  extent_unfold blocks;
  match blocks with
  | [] -> code_size_unfold []
  | pair :: rest ->
    let (label, b) = pair in
    span_unfold b;
    layout_size rest;
    exits_size b.terminator_physical rest;
    emit_size b.body_physical;
    match layout rest with
    | None -> ()
    | Some tail ->
      match exits (b.terminator_physical, rest) with
      | None -> ()
      | Some ending ->
        code_app_size ending tail;
        code_app_size (emit b.body_physical) (code_app (ending, tail))
[@@ghost]
[@@spec fun blocks ->
  ret (fun u -> assert (
    match layout blocks with None -> true | Some c -> code_size c = extent blocks))]
[@@decreases Logic.size blocks];;

(* ------------------------------------------------------------------ *)
(* Fragment length                                                     *)
(* ------------------------------------------------------------------ *)

(* [cost e] bounds the instructions that [e] lays out to. It charges every
   virtual instruction the four of [lower_one], so it is not tight. *)

let rec cost (e : expr) : int =
  match e with
  | Cst c -> 8
  | Var i -> 4
  | Plus (a, b) ->
    (match literal b with
     | Some c -> 4 + cost a
     | None -> 4 + cost a + cost b)
  | Bind (a, b) -> 4 + cost a + cost b
  | If (c, t, e) -> 5 + cost c + cost t + cost e
[@@fn ghost] [@@impl] [@@opaque] [@@decreases Logic.size e];;

(* The instructions of a fragment: its open block and its closed blocks. *)

let fragment_extent (f : fragment) : int =
  span (lower_block f.head) + extent (lower_blocks f.blocks_new)
[@@fn];;

let rec physical_app_size (c : physical list) (k : physical list) : unit =
  physical_app_unfold (c, k);
  physical_size_unfold c;
  physical_size_unfold (physical_app (c, k));
  match c with [] -> () | i :: rest -> physical_app_size rest k
[@@ghost]
[@@spec fun c k ->
  ret (fun u -> assert (physical_size (physical_app (c, k))
                        = physical_size c + physical_size k))]
[@@decreases Logic.size c];;

let fetch_size (i : int) (t : int) (k : physical list) : unit =
  match locate i with
  | Reg r -> ()
  | Slot s -> physical_size_unfold (Lw (t, 0, 4 * s) :: k)
[@@ghost]
[@@spec fun i t k ->
  ret (fun u -> assert (physical_size (fetch (i, t, k)) <= 1 + physical_size k))];;

let save_size (d : int) (k : physical list) : unit =
  match locate d with
  | Reg r -> ()
  | Slot s -> physical_size_unfold (Sw (0, 31, 4 * s) :: k)
[@@ghost]
[@@spec fun d k ->
  ret (fun u -> assert (physical_size (save (d, k)) <= 1 + physical_size k))];;

let lower_one_size (i : instr) (k : physical list) : unit =
  let (d, a, b) = operands i in
  let op = Alu (rename (i, temporary (d, 31), temporary (a, 29), temporary (b, 30))) in
  let tail = save (d, k) in
  save_size d k;
  physical_size_unfold (op :: tail);
  fetch_size b 30 (op :: tail);
  fetch_size a 29 (fetch (b, 30, op :: tail))
[@@ghost]
[@@spec fun i k ->
  ret (fun u -> assert (physical_size (lower_one (i, k)) <= 4 + physical_size k))];;

let jump_span (k : int) : unit =
  lower_block_unfold { body = []; terminator = Jump k };
  span_unfold (lower_block { body = []; terminator = Jump k });
  lower_unfold [];
  physical_size_unfold [];
  ending_unfold (Jump k);
  physical_app_unfold ([], []);
  terminator_size_unfold (Jump k)
[@@ghost]
[@@spec fun k ->
  ret (fun u -> assert (span (lower_block { body = []; terminator = Jump k }) = 1))];;

let branch_span (r : int) (yes : int) (no : int) : unit =
  lower_block_unfold { body = []; terminator = Branch (r, yes, no) };
  span_unfold (lower_block { body = []; terminator = Branch (r, yes, no) });
  lower_unfold [];
  physical_size_unfold [];
  ending_unfold (Branch (r, yes, no));
  fetch_size r 29 [];
  physical_app_size [] (fetch (r, 29, []));
  terminator_size_unfold (Branch (temporary (r, 29), yes, no))
[@@ghost]
[@@spec fun r yes no ->
  ret (fun u -> assert (
    span (lower_block { body = []; terminator = Branch (r, yes, no) }) <= 3))];;

let return_span (r : int) : unit =
  lower_block_unfold { body = []; terminator = Return r };
  span_unfold (lower_block { body = []; terminator = Return r });
  lower_unfold [];
  physical_size_unfold [];
  ending_unfold (Return r);
  physical_app_unfold ([], []);
  terminator_size_unfold (Return (temporary (r, 29)))
[@@ghost]
[@@spec fun r ->
  assert (0 <= r); assert (r < 29);
  ret (fun u -> assert (span (lower_block { body = []; terminator = Return r }) = 2))];;

let prepend_one_extent (i : instr) (f : fragment) : unit =
  prepend_unfold ([i], f);
  app_unfold ([i], f.head.body);
  app_unfold ([], f.head.body);
  lower_unfold (i :: f.head.body);
  lower_one_size i (lower f.head.body);
  lower_block_unfold (prepend ([i], f)).head;
  lower_block_unfold f.head;
  span_unfold (lower_block (prepend ([i], f)).head);
  span_unfold (lower_block f.head);
  physical_app_size (lower (i :: f.head.body))
                    (ending f.head.terminator).body_physical;
  physical_app_size (lower f.head.body)
                    (ending f.head.terminator).body_physical
[@@ghost]
[@@spec fun i f ->
  ret (fun u -> assert (fragment_extent (prepend ([i], f))
                        <= 4 + fragment_extent f))];;

let prepend_two_extent (i : instr) (j : instr) (f : fragment) : unit =
  prepend_unfold ([i; j], f);
  app_unfold ([i; j], f.head.body);
  app_unfold ([j], f.head.body);
  app_unfold ([], f.head.body);
  lower_unfold (i :: j :: f.head.body);
  lower_unfold (j :: f.head.body);
  lower_one_size j (lower f.head.body);
  lower_one_size i (lower (j :: f.head.body));
  lower_block_unfold (prepend ([i; j], f)).head;
  lower_block_unfold f.head;
  span_unfold (lower_block (prepend ([i; j], f)).head);
  span_unfold (lower_block f.head);
  physical_app_size (lower (i :: j :: f.head.body))
                    (ending f.head.terminator).body_physical;
  physical_app_size (lower f.head.body)
                    (ending f.head.terminator).body_physical
[@@ghost]
[@@spec fun i j f ->
  ret (fun u -> assert (fragment_extent (prepend ([i; j], f))
                        <= 8 + fragment_extent f))];;

let close_extent (f : fragment) : unit =
  close_unfold f;
  jump_span f.fresh;
  lower_blocks_unfold (close f).blocks_new;
  extent_unfold (lower_blocks (close f).blocks_new)
[@@ghost]
[@@spec fun f ->
  ret (fun u -> assert (fragment_extent (close f) = 1 + fragment_extent f))];;

let resume_extent (head : block) (f : fragment) : unit =
  resume_unfold (head, f)
[@@ghost]
[@@spec fun head f ->
  ret (fun u -> assert (fragment_extent (resume (head, f))
                        = span (lower_block head)
                          + extent (lower_blocks f.blocks_new)))];;

let rec build_extent (whole : expr) (rs : int list) (d : int) (f : fragment)
    : unit =
  build_unfold (whole, rs, d, f);
  cost_unfold whole;
  match whole with
  | Cst c -> prepend_two_extent (Lui (d, hi c)) (Addi (d, d, lo c)) f
  | Var i -> prepend_one_extent (Addi (d, reg (rs, i), 0l)) f
  | Plus (a, b) ->
    (match literal b with
     | Some c ->
       prepend_one_extent (Addi (d, d, c)) f;
       build_extent a rs d (prepend ([Addi (d, d, c)], f))
     | None ->
       let tail = prepend ([Add (d, d, d + 1)], f) in
       prepend_one_extent (Add (d, d, d + 1)) f;
       build_extent b rs (d + 1) tail;
       build_extent a rs d (build (b, rs, d + 1, tail)))
  | Bind (a, b) ->
    let tail = prepend ([Addi (d, d + 1, 0l)], f) in
    prepend_one_extent (Addi (d, d + 1, 0l)) f;
    build_extent b (d :: rs) (d + 1) tail;
    build_extent a rs d (build (b, d :: rs, d + 1, tail))
  | If (c, t, e) ->
    let join = close f in
    close_extent f;
    close_unfold f;
    jump_span f.fresh;
    build_extent t rs d join;
    let yes = build (t, rs, d, join) in
    close_extent yes;
    close_unfold yes;
    jump_span yes.fresh;
    resume_extent join.head (close yes);
    build_extent e rs d (resume (join.head, close yes));
    let no = build (e, rs, d, resume (join.head, close yes)) in
    close_extent no;
    close_unfold no;
    jump_span no.fresh;
    branch_span d yes.fresh no.fresh;
    resume_extent { body = []; terminator = Branch (d, yes.fresh, no.fresh) }
                  (close no);
    build_extent c rs d
      (resume ({ body = []; terminator = Branch (d, yes.fresh, no.fresh) },
               close no))
[@@ghost]
[@@spec fun whole rs d f ->
  ret (fun u -> assert (fragment_extent (build (whole, rs, d, f))
                        <= cost whole + fragment_extent f))]
[@@decreases Logic.size whole];;

let graph_extent (e : expr) : unit =
  graph_unfold e;
  return_span 1;
  lower_blocks_unfold [];
  extent_unfold [];
  build_extent e [] 1 { head = { body = []; terminator = Return 1 };
                        blocks_new = []; fresh = 0 };
  let g = build (e, [], 1, { head = { body = []; terminator = Return 1 };
                             blocks_new = []; fresh = 0 }) in
  lower_blocks_unfold ((g.fresh, g.head) :: g.blocks_new);
  extent_unfold (lower_blocks ((g.fresh, g.head) :: g.blocks_new))
[@@ghost]
[@@spec fun e ->
  ret (fun u -> assert (extent (lower_blocks (graph e).blocks) <= 2 + cost e))];;

let rec emit_valid (c : physical list) : unit =
  emit_unfold c;
  physical_valid_unfold c;
  code_valid_unfold (emit c);
  match c with
  | [] -> ()
  | i :: rest -> instruction_valid_unfold (Op i); emit_valid rest
[@@ghost]
[@@spec fun c ->
  assert (physical_valid c);
  ret (fun u -> assert (code_valid (emit c)))]
[@@decreases Logic.size c];;

let rec code_app_valid (c : instruction list) (k : instruction list) : unit =
  code_app_unfold (c, k);
  code_valid_unfold c;
  code_valid_unfold (code_app (c, k));
  match c with
  | [] -> ()
  | i :: rest -> code_app_valid rest k
[@@ghost]
[@@spec fun c k ->
  assert (code_valid c); assert (code_valid k);
  ret (fun u -> assert (code_valid (code_app (c, k))))]
[@@decreases Logic.size c];;

(* Every displacement is four times a block offset, so it is forward and
   aligned. The branch field is the tight one. A branch to offset [n] has
   displacement [4 * (2 + n)], and the field holds 4094, so [n] is at most
   1021. An offset is below the extent, which gives the bound below. *)

let exits_valid (t : terminator) (blocks : (int * block_physical) list) : unit =
  exits_unfold (t, blocks);
  terminator_valid_unfold t;
  code_valid_unfold [];
  match t with
  | Jump k ->
    offset_bound blocks k;
    (match offset (blocks, k) with
     | None -> ()
     | Some n ->
       instruction_valid_unfold (Jal (4 * (1 + n)));
       code_valid_unfold [Jal (4 * (1 + n))])
  | Branch (r, yes, no) ->
    offset_bound blocks yes;
    offset_bound blocks no;
    (match offset (blocks, yes) with
     | None -> ()
     | Some n ->
       match offset (blocks, no) with
       | None -> ()
       | Some m ->
         instruction_valid_unfold (Bne (r, 0, 4 * (2 + n)));
         instruction_valid_unfold (Jal (4 * (1 + m)));
         code_valid_unfold [Jal (4 * (1 + m))];
         code_valid_unfold [Bne (r, 0, 4 * (2 + n)); Jal (4 * (1 + m))])
  | Return r ->
    extent_nonneg blocks;
    instruction_valid_unfold (Op (Alu (Addi (1, r, 0l))));
    instruction_valid_unfold (Jal (4 * (1 + extent blocks)));
    code_valid_unfold [Jal (4 * (1 + extent blocks))];
    code_valid_unfold [Op (Alu (Addi (1, r, 0l))); Jal (4 * (1 + extent blocks))]
[@@ghost]
[@@spec fun t blocks ->
  assert (terminator_valid t); assert (extent blocks <= 1022);
  ret (fun u -> assert (
    match exits (t, blocks) with None -> true | Some c -> code_valid c))];;

let rec layout_valid (blocks : (int * block_physical) list) : unit =
  layout_unfold blocks;
  blocks_valid_unfold blocks;
  extent_unfold blocks;
  match blocks with
  | [] -> code_valid_unfold []
  | pair :: rest ->
    let (label, b) = pair in
    span_positive b;
    extent_nonneg rest;
    block_valid_unfold b;
    layout_valid rest;
    exits_valid b.terminator_physical rest;
    (match layout rest with
     | None -> ()
     | Some tail ->
       match exits (b.terminator_physical, rest) with
       | None -> ()
       | Some ending ->
         emit_valid b.body_physical;
         code_app_valid ending tail;
         code_app_valid (emit b.body_physical) (code_app (ending, tail)))
[@@ghost]
[@@spec fun blocks ->
  assert (blocks_valid blocks); assert (extent blocks <= 1023);
  ret (fun u -> assert (
    match layout blocks with None -> true | Some c -> code_valid c))]
[@@decreases Logic.size blocks];;

let rec skip_exists (c : instruction list) (n : int) : unit =
  skip_unfold (n, c);
  code_size_unfold c;
  if n = 0 then ()
  else match c with [] -> () | i :: rest -> skip_exists rest (n - 1)
[@@ghost]
[@@spec fun c n ->
  assert (0 <= n); assert (n <= code_size c);
  ret (fun u -> assert (match skip (n, c) with None -> false | Some tail -> true))]
[@@decreases Logic.size c];;

let physical_step_length (i : physical) (p : machine) : unit =
  match i with
  | Alu op ->
    step_result op p.regs;
    let (d, a, b) = operands op in
    set_length p.regs d (result (op, get (p.regs, a), get (p.regs, b)))
  | Lw (d, a, imm) ->
    (match load32 (p.mem, address (get (p.regs, a), imm)) with
     | None -> () | Some x -> set_length p.regs d x)
  | Sw (a, b, imm) -> ()
[@@ghost]
[@@spec fun i p ->
  ret (fun u -> assert (Vec.length (physical_step (i, p)).regs = Vec.length p.regs))];;

let rec physical_exec_length (c : physical list) (p : machine) : unit =
  physical_exec_unfold (c, p);
  match c with
  | [] -> ()
  | i :: rest -> physical_step_length i p; physical_exec_length rest (physical_step (i, p))
[@@ghost]
[@@spec fun c p ->
  ret (fun u -> assert (Vec.length (physical_exec (c, p)).regs = Vec.length p.regs))]
[@@decreases Logic.size c];;

let rec layout_simulation ((p : execution_physical), (c : execution_code)) : bool =
  match p with
  | Returned_physical (x, q) ->
    (match c with
     | Completed { regs; mem; ok } -> ok && Int32.equal (get (regs, 1)) x
     | Fault reason -> false
     | Out_of_fuel -> false)
  | Failed_physical reason ->
    (match c with Completed { regs; mem; ok } -> false | Fault reason -> true | Out_of_fuel -> false)
[@@fn] [@@opaque] [@@decreases 0];;

let jump_execute (tail : instruction list) (next : instruction list)
                 (n : int) (p : machine) (fuel : int) : unit =
  execute_unfold (Jal (4 * (1 + n)) :: tail, p, fuel);
  destination_unfold (4 * (1 + n), tail);
  skip_congr tail ((4 * (1 + n)) / 4 - 1) n
[@@ghost]
[@@spec fun tail next n p fuel ->
  assert (0 <= n); assert (Logic.eq (skip (n, tail)) (Some next));
  assert (p.ok); assert (0 < fuel);
  ret (fun u -> assert (Logic.eq (execute (Jal (4 * (1 + n)) :: tail, p, fuel))
                               (execute (next, p, fuel - 1))))];;

let branch_execute (tail : instruction list) (yes : instruction list)
                   (no : instruction list) (n : int) (m : int) (r : int)
                   (p : machine) (fuel : int) : unit =
  let jump = Jal (4 * (1 + m)) in
  execute_unfold (Bne (r, 0, 4 * (2 + n)) :: jump :: tail, p, fuel);
  destination_unfold (4 * (2 + n), jump :: tail);
  skip_congr (jump :: tail) ((4 * (2 + n)) / 4 - 1) (1 + n);
  skip_unfold (1 + n, jump :: tail);
  skip_congr tail ((1 + n) - 1) n;
  if Int32.equal (get (p.regs, r)) 0l then jump_execute tail no m p (fuel - 1)
  else ()
[@@ghost]
[@@spec fun tail yes no n m r p fuel ->
  assert (0 <= n); assert (0 <= m); assert (p.ok); assert (1 < fuel);
  assert (Logic.eq (skip (n, tail)) (Some yes));
  assert (Logic.eq (skip (m, tail)) (Some no));
  ret (fun u -> assert (Logic.eq
    (execute (Bne (r, 0, 4 * (2 + n)) :: Jal (4 * (1 + m)) :: tail, p, fuel))
    (if Int32.equal (get (p.regs, r)) 0l then execute (no, p, fuel - 2)
     else execute (yes, p, fuel - 1))))];;

let return_execute (tail : instruction list) (r : int) (p : machine)
                   (fuel : int) : unit =
  let op = Alu (Addi (1, r, 0l)) in
  let q = physical_step (op, p) in
  code_size_nonneg tail;
  skip_end tail;
  execute_unfold (Op op :: Jal (4 * (1 + code_size tail)) :: tail, p, fuel);
  jump_execute tail [] (code_size tail) q (fuel - 1);
  execute_unfold ([], q, fuel - 2);
  get_set_at p.regs 1 (Int32.add (get (p.regs, r)) 0l);
  layout_simulation_unfold (Returned_physical (get (p.regs, r), p), Completed q)
[@@ghost]
[@@spec fun tail r p fuel ->
  assert (p.ok); assert (Vec.length p.regs = 32); assert (1 < fuel);
  ret (fun u -> assert (layout_simulation (Returned_physical (get (p.regs, r), p),
    execute (Op (Alu (Addi (1, r, 0l))) :: Jal (4 * (1 + code_size tail)) :: tail,
             p, fuel))))];;

let rec linked_physical ((blocks : (int * block_physical) list), (limit : int)) : bool =
  match blocks with
  | [] -> limit = 0
  | pair :: rest ->
    let (label, b) = pair in
    label = limit - 1 && 0 <= label && targets (b.terminator_physical, label)
      && linked_physical (rest, label)
[@@fn] [@@opaque] [@@decreases Logic.size blocks];;

let ending_targets (t : terminator) (limit : int) : unit =
  ending_unfold t;
  targets_unfold (t, limit);
  targets_unfold ((ending t).terminator_physical, limit);
  match t with Jump k -> () | Branch (r, yes, no) -> () | Return r -> ()
[@@ghost]
[@@spec fun t limit ->
  assert (targets (t, limit));
  ret (fun u -> assert (targets ((ending t).terminator_physical, limit)))];;

let rec lower_blocks_linked (blocks : (int * block) list) (limit : int) : unit =
  linked_unfold (blocks, limit);
  lower_blocks_unfold blocks;
  linked_physical_unfold (lower_blocks blocks, limit);
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (label, b) = pair in
    lower_block_unfold b;
    ending_targets b.terminator label;
    lower_blocks_linked rest label
[@@ghost]
[@@spec fun blocks limit ->
  assert (linked (blocks, limit));
  ret (fun u -> assert (linked_physical (lower_blocks blocks, limit)))]
[@@decreases Logic.size blocks];;

let rec offset_exists (blocks : (int * block_physical) list) (limit : int)
                      (label : int) : unit =
  linked_physical_unfold (blocks, limit);
  offset_unfold (blocks, label);
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (k, b) = pair in
    if label = k then () else offset_exists rest k label
[@@ghost]
[@@spec fun blocks limit label ->
  assert (linked_physical (blocks, limit)); assert (0 <= label); assert (label < limit);
  ret (fun u -> assert (match offset (blocks, label) with None -> false | Some n -> true))]
[@@decreases Logic.size blocks];;

let exits_exists (t : terminator) (blocks : (int * block_physical) list)
                 (limit : int) : unit =
  targets_unfold (t, limit);
  exits_unfold (t, blocks);
  match t with
  | Jump k -> offset_exists blocks limit k
  | Branch (r, yes, no) -> offset_exists blocks limit yes; offset_exists blocks limit no
  | Return r -> ()
[@@ghost]
[@@spec fun t blocks limit ->
  assert (targets (t, limit)); assert (linked_physical (blocks, limit));
  ret (fun u -> assert (match exits (t, blocks) with None -> false | Some c -> true))];;

let rec layout_exists (blocks : (int * block_physical) list) (limit : int) : unit =
  linked_physical_unfold (blocks, limit);
  layout_unfold blocks;
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (label, b) = pair in
    layout_exists rest label;
    exits_exists b.terminator_physical rest label
[@@ghost]
[@@spec fun blocks limit ->
  assert (linked_physical (blocks, limit));
  ret (fun u -> assert (match layout blocks with None -> false | Some c -> true))]
[@@decreases Logic.size blocks];;

(* A generated graph always lays out, and its code always meets the RV32I
   field ranges. *)

let graph_layout_valid (e : expr) : unit =
  graph_extent e;
  graph_linked e;
  graph_allocation e (Int.max 29 (1 + need e));
  lower_blocks_valid (graph e).blocks (slots (Int.max 29 (1 + need e)));
  lower_blocks_linked (graph e).blocks ((graph e).entry + 1);
  layout_exists (lower_blocks (graph e).blocks) ((graph e).entry + 1);
  layout_valid (lower_blocks (graph e).blocks)
[@@ghost]
[@@spec fun e ->
  assert (need e <= 540); assert (cost e <= 1021);
  ret (fun u -> assert (
    match layout (lower_blocks (graph e).blocks) with
    | None -> false
    | Some code -> code_valid code))];;

let rec layout_correct (blocks : (int * block_physical) list) (label : int)
                       (p : machine) (fuel : int) (code : instruction list)
                       (start : instruction list) (n : int) : unit =
  layout_unfold blocks;
  offset_unfold (blocks, label);
  follow_physical_unfold (blocks, label, p);
  extent_unfold blocks;
  match blocks with
  | [] -> ()
  | pair :: rest ->
    let (k, b) = pair in
    span_unfold b;
    terminator_size_unfold b.terminator_physical;
    span_positive b;
    physical_size_nonneg b.body_physical;
    extent_nonneg rest;
    layout_size rest;
    exits_size b.terminator_physical rest;
    emit_size b.body_physical;
    match layout rest with
    | None -> ()
    | Some tail ->
      match exits (b.terminator_physical, rest) with
      | None -> ()
      | Some ending ->
        if label <> k then begin
          match offset (rest, label) with
          | None -> ()
          | Some m ->
            offset_bound rest label;
            terminator_size_unfold b.terminator_physical;
            skip_app (emit b.body_physical) (code_app (ending, tail))
                     (terminator_size b.terminator_physical + m);
            skip_app ending tail m;
            layout_correct rest label p fuel tail start m
        end else begin
          skip_unfold (n, code);
          let q = physical_exec (b.body_physical, p) in
          let remaining = fuel - physical_size b.body_physical in
          emit_execute b.body_physical (code_app (ending, tail)) p remaining;
          physical_exec_length b.body_physical p;
          if not q.ok then begin
            execute_unfold (code_app (ending, tail), q, remaining);
            layout_simulation_unfold (follow_physical (blocks, label, p),
                                      execute (start, p, fuel))
          end else begin
            exits_unfold (b.terminator_physical, rest);
            terminator_size_unfold b.terminator_physical;
            code_app_unfold ([], tail);
            match b.terminator_physical with
            | Jump target ->
              (match offset (rest, target) with
               | None -> ()
               | Some m ->
                 offset_bound rest target;
                 skip_exists tail m;
                 match skip (m, tail) with
                 | None -> ()
                 | Some next ->
                   code_app_unfold ([Jal (4 * (1 + m))], tail);
                   jump_execute tail next m q remaining;
                   layout_correct rest target q (remaining - 1) tail next m)
            | Branch (r, yes, no) ->
              (match offset (rest, yes) with
               | None -> ()
               | Some m ->
                 match offset (rest, no) with
                 | None -> ()
                 | Some j ->
                   offset_bound rest yes;
                   offset_bound rest no;
                   skip_exists tail m;
                   skip_exists tail j;
                   match skip (m, tail) with
                   | None -> ()
                   | Some yes_code ->
                     match skip (j, tail) with
                     | None -> ()
                     | Some no_code ->
                       code_app_unfold ([Jal (4 * (1 + j))], tail);
                       code_app_unfold ([Bne (r, 0, 4 * (2 + m)); Jal (4 * (1 + j))], tail);
                       branch_execute tail yes_code no_code m j r q remaining;
                       if Int32.equal (get (q.regs, r)) 0l then
                         layout_correct rest no q (remaining - 2) tail no_code j
                       else layout_correct rest yes q (remaining - 1) tail yes_code m)
            | Return r ->
              code_app_unfold ([Jal (4 * (1 + extent rest))], tail);
              code_app_unfold ([Op (Alu (Addi (1, r, 0l))); Jal (4 * (1 + extent rest))], tail);
              return_execute tail r q remaining
          end
        end
[@@ghost]
[@@spec fun blocks label p fuel code start n ->
  assert (Logic.eq (layout blocks) (Some code));
  assert (Logic.eq (offset (blocks, label)) (Some n));
  assert (Logic.eq (skip (n, code)) (Some start));
  assert (p.ok); assert (Vec.length p.regs = 32); assert (extent blocks <= fuel);
  ret (fun u -> assert (layout_simulation (follow_physical (blocks, label, p),
                                          execute (start, p, fuel))))]
[@@decreases Logic.size blocks];;

let graph_offset (e : expr) : unit =
  graph_unfold e;
  lower_blocks_unfold (graph e).blocks;
  offset_unfold (lower_blocks (graph e).blocks, (graph e).entry)
[@@ghost]
[@@spec fun e -> ret (fun u -> assert (Logic.eq
  (offset (lower_blocks (graph e).blocks, (graph e).entry)) (Some 0)))];;

let graph_layout_correct (e : expr) (v : int32 vec) (p : machine)
                         (code : instruction list) : unit =
  graph_physical_correct e v p;
  graph_offset e;
  layout_size (lower_blocks (graph e).blocks);
  skip_unfold (0, code);
  layout_correct (lower_blocks (graph e).blocks) (graph e).entry p
                 (code_size code) code code 0;
  layout_simulation_unfold
    (follow_physical (lower_blocks (graph e).blocks, (graph e).entry, p),
     execute (code, p, code_size code));
  match follow_physical (lower_blocks (graph e).blocks, (graph e).entry, p) with
  | Failed_physical reason -> ()
  | Returned_physical (x, q) ->
    (match execute (code, p, code_size code) with
     | Completed { regs; mem; ok } -> ()
     | Fault reason -> ()
     | Out_of_fuel -> ())
[@@ghost]
[@@spec fun e v p code ->
  assert (simulation (v, p)); assert (1 + need e <= Vec.length v);
  assert (Logic.eq (layout (lower_blocks (graph e).blocks)) (Some code));
  ret (fun u -> assert (
    match execute (code, p, code_size code) with
    | Completed { regs; mem; ok } -> ok && Int32.equal (get (regs, 1)) (eval (e, []))
    | Fault reason -> false
    | Out_of_fuel -> false))];;

type assembly =
  | Compiled of instruction list * int
  | Unsupported of string

(* Code starts at byte address zero. Each instruction occupies four bytes.

   [need e <= 540] is for the fixed spill frame of 512 words. [cost e <= 1021]
   is for the branch instructions. A conditional branch has one signed 13-bit
   displacement, and this compiler emits no other form, so a branch must reach
   its target directly. *)
let rec assemble (e : expr) : assembly =
  if 540 < need e then Unsupported "spill frames larger than 512 words are unsupported"
  else if 1021 < cost e then
    Unsupported "expressions of more than 1021 instructions are unsupported"
  else match layout (lower_blocks (graph e).blocks) with
  | None -> Unsupported "CFG successor label is undefined or not forward"
  | Some code -> Compiled (code, 4 * slots (1 + need e))
[@@fn ghost] [@@impl] [@@opaque] [@@decreases 0];;

let assemble_valid (e : expr) : unit =
  assemble_unfold e;
  need_positive e;
  graph_layout_valid e;
  graph_extent e;
  layout_size (lower_blocks (graph e).blocks);
  match layout (lower_blocks (graph e).blocks) with
  | None -> ()
  | Some code -> code_size_nonneg code
[@@ghost]
[@@spec fun e ->
  assert (need e <= 540); assert (cost e <= 1021);
  ret (fun u -> assert (
    match assemble e with
    | Unsupported reason -> false
    | Compiled (code, bytes) -> code_valid code && 0 <= bytes && bytes <= 2048
      && bytes = 4 * slots (1 + need e)
      && 0 <= code_size code && 4 * code_size code <= 2147483647
      && Logic.eq (layout (lower_blocks (graph e).blocks)) (Some code)))];;

let assemble_correct (e : expr) : unit =
  assemble_unfold e;
  assemble_valid e;
  need_positive e;
  match assemble e with
  | Unsupported reason -> ()
  | Compiled (code, bytes) ->
    let n = Int.max 29 (1 + need e) in
    initial_simulation n;
    graph_layout_correct e (Vec.make n 0l) (initial n) code
[@@ghost]
[@@spec fun e ->
  assert (need e <= 540); assert (cost e <= 1021);
  ret (fun u -> assert (
    match assemble e with
    | Unsupported reason -> false
    | Compiled (code, bytes) ->
      let p = { regs = Vec.make 32 0l; mem = Vec.make bytes 0l; ok = true } in
      code_valid code &&
      (match execute (code, p, code_size code) with
       | Completed { regs; mem; ok } -> ok && Int32.equal (get (regs, 1)) (eval (e, []))
       | Fault reason -> false
       | Out_of_fuel -> false)))];;

(* An ordinary expression meets both bounds. This one assembles, and its code
   gives the source result. *)

let assembled_case (c : int32) : unit =
  let e = If (Cst c, Cst 7l, Cst 9l) in
  need_unfold e; need_unfold (Cst c); need_unfold (Cst 7l); need_unfold (Cst 9l);
  cost_unfold e; cost_unfold (Cst c); cost_unfold (Cst 7l); cost_unfold (Cst 9l);
  eval_unfold (e, []); eval_unfold (Cst c, []);
  eval_unfold (Cst 7l, []); eval_unfold (Cst 9l, []);
  assemble_correct e
[@@ghost]
[@@spec fun c -> ret (fun u -> assert (
  let e = If (Cst c, Cst 7l, Cst 9l) in
  match assemble e with
  | Unsupported reason -> false
  | Compiled (code, bytes) ->
    let p = { regs = Vec.make 32 0l; mem = Vec.make bytes 0l; ok = true } in
    code_valid code &&
    (match execute (code, p, code_size code) with
     | Completed { regs; mem; ok } ->
       ok && Int32.equal (get (regs, 1)) (if Int32.equal c 0l then 9l else 7l)
     | Fault reason -> false
     | Out_of_fuel -> false)))];;
