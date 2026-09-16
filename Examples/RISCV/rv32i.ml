open Mica

(* The RV32I base instruction set: an encoder, a decoder, and an interpreter.

   Every field of an instruction is an [int32]. A register is a 5-bit number.
   An immediate is sign-extended to 32 bits. An offset counts bytes.

   [encode] and [decode] are [@@fn] [@@impl]. The proofs use them as
   specification functions, and the interpreter runs them.

   Proved:
   - [decoded_wf_holds]: the decoder makes only well-formed instructions.
   - [faithful_holds]: a word that decodes is the encoding of its instruction.
   - [roundtrip]: a well-formed instruction decodes back from its encoding.
   - [step] and [run] access memory and registers only in bounds, and keep
     the register count, the memory size, and [x0].

   Not proved: what the interpreter computes. *)

type instr =
  | Add of int32 * int32 * int32
  | Sub of int32 * int32 * int32
  | Sll of int32 * int32 * int32
  | Slt of int32 * int32 * int32
  | Sltu of int32 * int32 * int32
  | Xor of int32 * int32 * int32
  | Srl of int32 * int32 * int32
  | Sra of int32 * int32 * int32
  | Or of int32 * int32 * int32
  | And of int32 * int32 * int32
  | Addi of int32 * int32 * int32
  | Slti of int32 * int32 * int32
  | Sltiu of int32 * int32 * int32
  | Xori of int32 * int32 * int32
  | Ori of int32 * int32 * int32
  | Andi of int32 * int32 * int32
  | Slli of int32 * int32 * int32
  | Srli of int32 * int32 * int32
  | Srai of int32 * int32 * int32
  | Lb of int32 * int32 * int32
  | Lh of int32 * int32 * int32
  | Lw of int32 * int32 * int32
  | Lbu of int32 * int32 * int32
  | Lhu of int32 * int32 * int32
  | Jalr of int32 * int32 * int32
  | Sb of int32 * int32 * int32
  | Sh of int32 * int32 * int32
  | Sw of int32 * int32 * int32
  | Beq of int32 * int32 * int32
  | Bne of int32 * int32 * int32
  | Blt of int32 * int32 * int32
  | Bge of int32 * int32 * int32
  | Bltu of int32 * int32 * int32
  | Bgeu of int32 * int32 * int32
  | Lui of int32 * int32
  | Auipc of int32 * int32
  | Jal of int32 * int32
  | Fence of int32
  | Ecall
  | Ebreak

(* Field ranges. [s12 x] says that [x] fits in 12 signed bits. *)

let u5 (x : int32) : bool = Int32.equal (Int32.logand x 0x1fl) x
[@@fn];;

let u12 (x : int32) : bool = Int32.equal (Int32.logand x 0xfffl) x
[@@fn];;

let s12 (x : int32) : bool =
  Int32.equal (Int32.shift_right (Int32.shift_left x 20) 20) x
[@@fn];;

let s13 (x : int32) : bool =
  Int32.equal (Int32.shift_right (Int32.shift_left x 19) 19) x
[@@fn];;

let s21 (x : int32) : bool =
  Int32.equal (Int32.shift_right (Int32.shift_left x 11) 11) x
[@@fn];;

let even (x : int32) : bool = Int32.equal (Int32.logand x 0x1l) 0l
[@@fn];;

let upper (x : int32) : bool = Int32.equal (Int32.logand x 0xfffl) 0l
[@@fn];;

(* An encoder truncates a field that is out of range, and [decode] cannot give
   it back. [wf] excludes such fields. *)

let wf (i : instr) : bool =
  match i with
  | Add (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Sub (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Sll (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Slt (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Sltu (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Xor (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Srl (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Sra (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Or (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | And (rd, rs1, rs2) -> u5 rd && u5 rs1 && u5 rs2
  | Addi (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Slti (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Sltiu (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Xori (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Ori (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Andi (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Slli (rd, rs1, shamt) -> u5 rd && u5 rs1 && u5 shamt
  | Srli (rd, rs1, shamt) -> u5 rd && u5 rs1 && u5 shamt
  | Srai (rd, rs1, shamt) -> u5 rd && u5 rs1 && u5 shamt
  | Lb (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Lh (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Lw (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Lbu (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Lhu (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Jalr (rd, rs1, imm) -> u5 rd && u5 rs1 && s12 imm
  | Sb (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s12 imm
  | Sh (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s12 imm
  | Sw (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s12 imm
  | Beq (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s13 imm && even imm
  | Bne (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s13 imm && even imm
  | Blt (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s13 imm && even imm
  | Bge (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s13 imm && even imm
  | Bltu (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s13 imm && even imm
  | Bgeu (rs1, rs2, imm) -> u5 rs1 && u5 rs2 && s13 imm && even imm
  | Lui (rd, imm) -> u5 rd && upper imm
  | Auipc (rd, imm) -> u5 rd && upper imm
  | Jal (rd, imm) -> u5 rd && s21 imm && even imm
  | Fence (mask) -> u12 mask
  | Ecall -> true
  | Ebreak -> true
[@@fn];;

(* ------------------------------------------------------------------ *)
(* The encoder                                                        *)
(* ------------------------------------------------------------------ *)

(* One encoder for each of the six instruction formats. *)

let enc_r ((opcode : int32), (funct3 : int32), (funct7 : int32),
           (rd : int32), (rs1 : int32), (rs2 : int32)) : int32 =
  Int32.logor opcode
    (Int32.logor (Int32.shift_left rd 7)
       (Int32.logor (Int32.shift_left funct3 12)
          (Int32.logor (Int32.shift_left rs1 15)
             (Int32.logor (Int32.shift_left rs2 20)
                (Int32.shift_left funct7 25)))))
[@@fn] [@@impl];;

let enc_i ((opcode : int32), (funct3 : int32), (rd : int32), (rs1 : int32),
           (imm : int32)) : int32 =
  Int32.logor opcode
    (Int32.logor (Int32.shift_left rd 7)
       (Int32.logor (Int32.shift_left funct3 12)
          (Int32.logor (Int32.shift_left rs1 15)
             (Int32.shift_left (Int32.logand imm 0xfffl) 20))))
[@@fn] [@@impl];;

let enc_s ((opcode : int32), (funct3 : int32), (rs1 : int32), (rs2 : int32),
           (imm : int32)) : int32 =
  Int32.logor opcode
    (Int32.logor (Int32.shift_left (Int32.logand imm 0x1fl) 7)
       (Int32.logor (Int32.shift_left funct3 12)
          (Int32.logor (Int32.shift_left rs1 15)
             (Int32.logor (Int32.shift_left rs2 20)
                (Int32.shift_left
                   (Int32.logand (Int32.shift_right imm 5) 0x7fl) 25)))))
[@@fn] [@@impl];;

let enc_b ((opcode : int32), (funct3 : int32), (rs1 : int32), (rs2 : int32),
           (imm : int32)) : int32 =
  Int32.logor opcode
    (Int32.logor
       (Int32.shift_left (Int32.logand (Int32.shift_right imm 11) 0x1l) 7)
       (Int32.logor
          (Int32.shift_left (Int32.logand (Int32.shift_right imm 1) 0xfl) 8)
          (Int32.logor (Int32.shift_left funct3 12)
             (Int32.logor (Int32.shift_left rs1 15)
                (Int32.logor (Int32.shift_left rs2 20)
                   (Int32.logor
                      (Int32.shift_left
                         (Int32.logand (Int32.shift_right imm 5) 0x3fl) 25)
                      (Int32.shift_left
                         (Int32.logand (Int32.shift_right imm 12) 0x1l) 31)))))))
[@@fn] [@@impl];;

let enc_u ((opcode : int32), (rd : int32), (imm : int32)) : int32 =
  Int32.logor opcode
    (Int32.logor (Int32.shift_left rd 7) (Int32.logand imm 0xfffff000l))
[@@fn] [@@impl];;

let enc_j ((opcode : int32), (rd : int32), (imm : int32)) : int32 =
  Int32.logor opcode
    (Int32.logor (Int32.shift_left rd 7)
       (Int32.logor
          (Int32.shift_left (Int32.logand (Int32.shift_right imm 12) 0xffl) 12)
          (Int32.logor
             (Int32.shift_left (Int32.logand (Int32.shift_right imm 11) 0x1l) 20)
             (Int32.logor
                (Int32.shift_left
                   (Int32.logand (Int32.shift_right imm 1) 0x3ffl) 21)
                (Int32.shift_left
                   (Int32.logand (Int32.shift_right imm 20) 0x1l) 31)))))
[@@fn] [@@impl];;

let encode (i : instr) : int32 =
  match i with
  | Add (rd, rs1, rs2) -> enc_r (0x33l, 0x0l, 0x00l, rd, rs1, rs2)
  | Sub (rd, rs1, rs2) -> enc_r (0x33l, 0x0l, 0x20l, rd, rs1, rs2)
  | Sll (rd, rs1, rs2) -> enc_r (0x33l, 0x1l, 0x00l, rd, rs1, rs2)
  | Slt (rd, rs1, rs2) -> enc_r (0x33l, 0x2l, 0x00l, rd, rs1, rs2)
  | Sltu (rd, rs1, rs2) -> enc_r (0x33l, 0x3l, 0x00l, rd, rs1, rs2)
  | Xor (rd, rs1, rs2) -> enc_r (0x33l, 0x4l, 0x00l, rd, rs1, rs2)
  | Srl (rd, rs1, rs2) -> enc_r (0x33l, 0x5l, 0x00l, rd, rs1, rs2)
  | Sra (rd, rs1, rs2) -> enc_r (0x33l, 0x5l, 0x20l, rd, rs1, rs2)
  | Or (rd, rs1, rs2) -> enc_r (0x33l, 0x6l, 0x00l, rd, rs1, rs2)
  | And (rd, rs1, rs2) -> enc_r (0x33l, 0x7l, 0x00l, rd, rs1, rs2)
  | Addi (rd, rs1, imm) -> enc_i (0x13l, 0x0l, rd, rs1, imm)
  | Slti (rd, rs1, imm) -> enc_i (0x13l, 0x2l, rd, rs1, imm)
  | Sltiu (rd, rs1, imm) -> enc_i (0x13l, 0x3l, rd, rs1, imm)
  | Xori (rd, rs1, imm) -> enc_i (0x13l, 0x4l, rd, rs1, imm)
  | Ori (rd, rs1, imm) -> enc_i (0x13l, 0x6l, rd, rs1, imm)
  | Andi (rd, rs1, imm) -> enc_i (0x13l, 0x7l, rd, rs1, imm)
  | Slli (rd, rs1, shamt) -> enc_r (0x13l, 0x1l, 0x00l, rd, rs1, shamt)
  | Srli (rd, rs1, shamt) -> enc_r (0x13l, 0x5l, 0x00l, rd, rs1, shamt)
  | Srai (rd, rs1, shamt) -> enc_r (0x13l, 0x5l, 0x20l, rd, rs1, shamt)
  | Lb (rd, rs1, imm) -> enc_i (0x03l, 0x0l, rd, rs1, imm)
  | Lh (rd, rs1, imm) -> enc_i (0x03l, 0x1l, rd, rs1, imm)
  | Lw (rd, rs1, imm) -> enc_i (0x03l, 0x2l, rd, rs1, imm)
  | Lbu (rd, rs1, imm) -> enc_i (0x03l, 0x4l, rd, rs1, imm)
  | Lhu (rd, rs1, imm) -> enc_i (0x03l, 0x5l, rd, rs1, imm)
  | Jalr (rd, rs1, imm) -> enc_i (0x67l, 0x0l, rd, rs1, imm)
  | Sb (rs1, rs2, imm) -> enc_s (0x23l, 0x0l, rs1, rs2, imm)
  | Sh (rs1, rs2, imm) -> enc_s (0x23l, 0x1l, rs1, rs2, imm)
  | Sw (rs1, rs2, imm) -> enc_s (0x23l, 0x2l, rs1, rs2, imm)
  | Beq (rs1, rs2, imm) -> enc_b (0x63l, 0x0l, rs1, rs2, imm)
  | Bne (rs1, rs2, imm) -> enc_b (0x63l, 0x1l, rs1, rs2, imm)
  | Blt (rs1, rs2, imm) -> enc_b (0x63l, 0x4l, rs1, rs2, imm)
  | Bge (rs1, rs2, imm) -> enc_b (0x63l, 0x5l, rs1, rs2, imm)
  | Bltu (rs1, rs2, imm) -> enc_b (0x63l, 0x6l, rs1, rs2, imm)
  | Bgeu (rs1, rs2, imm) -> enc_b (0x63l, 0x7l, rs1, rs2, imm)
  | Lui (rd, imm) -> enc_u (0x37l, rd, imm)
  | Auipc (rd, imm) -> enc_u (0x17l, rd, imm)
  | Jal (rd, imm) -> enc_j (0x6fl, rd, imm)
  | Fence (mask) -> enc_i (0x0fl, 0x0l, 0l, 0l, mask)
  | Ecall -> enc_i (0x73l, 0x0l, 0l, 0l, 0l)
  | Ebreak -> enc_i (0x73l, 0x0l, 0l, 0l, 1l)
[@@fn] [@@impl];;

(* ------------------------------------------------------------------ *)
(* The decoder                                                        *)
(* ------------------------------------------------------------------ *)

let decode (w : int32) : instr option =
  let opcode = Int32.logand w 0x7fl in
  let rd = Int32.logand (Int32.shift_right_logical w 7) 0x1fl in
  let funct3 = Int32.logand (Int32.shift_right_logical w 12) 0x7l in
  let rs1 = Int32.logand (Int32.shift_right_logical w 15) 0x1fl in
  let rs2 = Int32.logand (Int32.shift_right_logical w 20) 0x1fl in
  let funct7 = Int32.shift_right_logical w 25 in
  let imm_i = Int32.shift_right w 20 in
  let imm_s =
    Int32.logor (Int32.shift_left (Int32.shift_right w 25) 5)
      (Int32.logand (Int32.shift_right_logical w 7) 0x1fl) in
  let imm_b =
    Int32.logor (Int32.shift_left (Int32.shift_right w 31) 12)
      (Int32.logor
         (Int32.shift_left (Int32.logand (Int32.shift_right_logical w 7) 0x1l) 11)
         (Int32.logor
            (Int32.shift_left
               (Int32.logand (Int32.shift_right_logical w 25) 0x3fl) 5)
            (Int32.shift_left
               (Int32.logand (Int32.shift_right_logical w 8) 0xfl) 1))) in
  let imm_u = Int32.shift_left (Int32.shift_right_logical w 12) 12 in
  let imm_j =
    Int32.logor (Int32.shift_left (Int32.shift_right w 31) 20)
      (Int32.logor
         (Int32.shift_left
            (Int32.logand (Int32.shift_right_logical w 12) 0xffl) 12)
         (Int32.logor
            (Int32.shift_left
               (Int32.logand (Int32.shift_right_logical w 20) 0x1l) 11)
            (Int32.shift_left
               (Int32.logand (Int32.shift_right_logical w 21) 0x3ffl) 1))) in
  let imm_f = Int32.logand (Int32.shift_right_logical w 20) 0xfffl in
  (if Int32.equal opcode 0x33l then
     (if Int32.equal funct3 0x0l then
        (if Int32.equal funct7 0x00l then
           Some (Add (rd, rs1, rs2))
         else if Int32.equal funct7 0x20l then
           Some (Sub (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x1l then
        (if Int32.equal funct7 0x00l then
           Some (Sll (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x2l then
        (if Int32.equal funct7 0x00l then
           Some (Slt (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x3l then
        (if Int32.equal funct7 0x00l then
           Some (Sltu (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x4l then
        (if Int32.equal funct7 0x00l then
           Some (Xor (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x5l then
        (if Int32.equal funct7 0x00l then
           Some (Srl (rd, rs1, rs2))
         else if Int32.equal funct7 0x20l then
           Some (Sra (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x6l then
        (if Int32.equal funct7 0x00l then
           Some (Or (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x7l then
        (if Int32.equal funct7 0x00l then
           Some (And (rd, rs1, rs2))
         else
           None)
      else
        None)
   else if Int32.equal opcode 0x13l then
     (if Int32.equal funct3 0x0l then
        Some (Addi (rd, rs1, imm_i))
      else if Int32.equal funct3 0x1l then
        (if Int32.equal funct7 0x00l then
           Some (Slli (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x2l then
        Some (Slti (rd, rs1, imm_i))
      else if Int32.equal funct3 0x3l then
        Some (Sltiu (rd, rs1, imm_i))
      else if Int32.equal funct3 0x4l then
        Some (Xori (rd, rs1, imm_i))
      else if Int32.equal funct3 0x5l then
        (if Int32.equal funct7 0x00l then
           Some (Srli (rd, rs1, rs2))
         else if Int32.equal funct7 0x20l then
           Some (Srai (rd, rs1, rs2))
         else
           None)
      else if Int32.equal funct3 0x6l then
        Some (Ori (rd, rs1, imm_i))
      else if Int32.equal funct3 0x7l then
        Some (Andi (rd, rs1, imm_i))
      else
        None)
   else if Int32.equal opcode 0x03l then
     (if Int32.equal funct3 0x0l then
        Some (Lb (rd, rs1, imm_i))
      else if Int32.equal funct3 0x1l then
        Some (Lh (rd, rs1, imm_i))
      else if Int32.equal funct3 0x2l then
        Some (Lw (rd, rs1, imm_i))
      else if Int32.equal funct3 0x4l then
        Some (Lbu (rd, rs1, imm_i))
      else if Int32.equal funct3 0x5l then
        Some (Lhu (rd, rs1, imm_i))
      else
        None)
   else if Int32.equal opcode 0x67l then
     (if Int32.equal funct3 0x0l then
        Some (Jalr (rd, rs1, imm_i))
      else
        None)
   else if Int32.equal opcode 0x23l then
     (if Int32.equal funct3 0x0l then
        Some (Sb (rs1, rs2, imm_s))
      else if Int32.equal funct3 0x1l then
        Some (Sh (rs1, rs2, imm_s))
      else if Int32.equal funct3 0x2l then
        Some (Sw (rs1, rs2, imm_s))
      else
        None)
   else if Int32.equal opcode 0x63l then
     (if Int32.equal funct3 0x0l then
        Some (Beq (rs1, rs2, imm_b))
      else if Int32.equal funct3 0x1l then
        Some (Bne (rs1, rs2, imm_b))
      else if Int32.equal funct3 0x4l then
        Some (Blt (rs1, rs2, imm_b))
      else if Int32.equal funct3 0x5l then
        Some (Bge (rs1, rs2, imm_b))
      else if Int32.equal funct3 0x6l then
        Some (Bltu (rs1, rs2, imm_b))
      else if Int32.equal funct3 0x7l then
        Some (Bgeu (rs1, rs2, imm_b))
      else
        None)
   else if Int32.equal opcode 0x37l then
     Some (Lui (rd, imm_u))
   else if Int32.equal opcode 0x17l then
     Some (Auipc (rd, imm_u))
   else if Int32.equal opcode 0x6fl then
     Some (Jal (rd, imm_j))
   else if Int32.equal opcode 0x0fl then
     (if Int32.equal (Int32.logand w 0xfffffl) 0x0fl then
        Some (Fence (imm_f))
      else
        None)
   else if Int32.equal opcode 0x73l then
     (if Int32.equal w 0x00000073l then
        Some (Ecall)
      else if Int32.equal w 0x00100073l then
        Some (Ebreak)
      else
        None)
   else
     None)
[@@fn] [@@impl];;

(* ------------------------------------------------------------------ *)
(* Reference encodings                                                *)
(* ------------------------------------------------------------------ *)

(* Each word is the output of a RISC-V assembler. *)

let reference_encodings (u : unit) : unit = ()
[@@ghost]
[@@spec fun u ->
  ret (fun r ->
    (* add   x3, x1, x2 *)
    assert (Int32.equal (encode (Add (3l, 1l, 2l))) 0x002081b3l);
    (* add   x2, x2, x1 *)
    assert (Int32.equal (encode (Add (2l, 2l, 1l))) 0x00110133l);
    (* addi  x1, x0, 1 *)
    assert (Int32.equal (encode (Addi (1l, 0l, 1l))) 0x00100093l);
    (* addi  x1, x0, 10 *)
    assert (Int32.equal (encode (Addi (1l, 0l, 10l))) 0x00a00093l);
    (* addi  x2, x0, 0 *)
    assert (Int32.equal (encode (Addi (2l, 0l, 0l))) 0x00000113l);
    (* addi  x1, x1, -1 *)
    assert (Int32.equal (encode (Addi (1l, 1l, (-1l)))) 0xfff08093l);
    (* srai  x5, x6, 3 *)
    assert (Int32.equal (encode (Srai (5l, 6l, 3l))) 0x40335293l);
    (* lw    x7, 8(x2) *)
    assert (Int32.equal (encode (Lw (7l, 2l, 8l))) 0x00812383l);
    (* sw    x2, 4(x1) *)
    assert (Int32.equal (encode (Sw (1l, 2l, 4l))) 0x0020a223l);
    (* beq   x0, x0, -4 *)
    assert (Int32.equal (encode (Beq (0l, 0l, (-4l)))) 0xfe000ee3l);
    (* beq   x1, x0, 16 *)
    assert (Int32.equal (encode (Beq (1l, 0l, 16l))) 0x00008863l);
    (* lui   x5, 0x12345 *)
    assert (Int32.equal (encode (Lui (5l, 0x12345000l))) 0x123452b7l);
    (* jal   x1, 16 *)
    assert (Int32.equal (encode (Jal (1l, 16l))) 0x010000efl);
    (* jal   x0, -12 *)
    assert (Int32.equal (encode (Jal (0l, (-12l)))) 0xff5ff06fl);
    (* fence rw, rw *)
    assert (Int32.equal (encode (Fence (0x0ffl))) 0x0ff0000fl);
    (* ecall *)
    assert (Int32.equal (encode Ecall) 0x00000073l);
    (* ebreak *)
    assert (Int32.equal (encode Ebreak) 0x00100073l))];;

(* ------------------------------------------------------------------ *)
(* Decoder soundness                                                  *)
(* ------------------------------------------------------------------ *)

(* A specification cannot match on a sum. [decoded_wf] and [faithful] are
   [@@fn] predicates, so their [match] does the case split. *)

let decoded_wf (w : int32) : bool =
  match decode w with
  | Some i -> wf i
  | None -> true
[@@fn];;

let decoded_wf_holds (w : int32) : unit = ()
[@@ghost]
[@@spec fun w -> ret (fun r -> assert (decoded_wf w))];;

let faithful (w : int32) : bool =
  match decode w with
  | Some i -> Int32.equal (encode i) w
  | None -> true
[@@fn];;

let faithful_holds (w : int32) : unit = ()
[@@ghost]
[@@spec fun w -> ret (fun r -> assert (faithful w))];;

(* ------------------------------------------------------------------ *)
(* The round trip                                                     *)
(* ------------------------------------------------------------------ *)

(* The [match] splits [i] into its 40 cases. *)

let roundtrip (i : instr) : unit =
  match i with
  | Add (_, _, _) -> ()
  | Sub (_, _, _) -> ()
  | Sll (_, _, _) -> ()
  | Slt (_, _, _) -> ()
  | Sltu (_, _, _) -> ()
  | Xor (_, _, _) -> ()
  | Srl (_, _, _) -> ()
  | Sra (_, _, _) -> ()
  | Or (_, _, _) -> ()
  | And (_, _, _) -> ()
  | Addi (_, _, _) -> ()
  | Slti (_, _, _) -> ()
  | Sltiu (_, _, _) -> ()
  | Xori (_, _, _) -> ()
  | Ori (_, _, _) -> ()
  | Andi (_, _, _) -> ()
  | Slli (_, _, _) -> ()
  | Srli (_, _, _) -> ()
  | Srai (_, _, _) -> ()
  | Lb (_, _, _) -> ()
  | Lh (_, _, _) -> ()
  | Lw (_, _, _) -> ()
  | Lbu (_, _, _) -> ()
  | Lhu (_, _, _) -> ()
  | Jalr (_, _, _) -> ()
  | Sb (_, _, _) -> ()
  | Sh (_, _, _) -> ()
  | Sw (_, _, _) -> ()
  | Beq (_, _, _) -> ()
  | Bne (_, _, _) -> ()
  | Blt (_, _, _) -> ()
  | Bge (_, _, _) -> ()
  | Bltu (_, _, _) -> ()
  | Bgeu (_, _, _) -> ()
  | Lui (_, _) -> ()
  | Auipc (_, _) -> ()
  | Jal (_, _) -> ()
  | Fence _ -> ()
  | Ecall -> ()
  | Ebreak -> ()
[@@ghost]
[@@spec fun i ->
  assert (wf i);
  ret (fun r -> assert (Logic.eq (decode (encode i)) (Some i)))];;

(* ------------------------------------------------------------------ *)
(* Memory and registers                                               *)
(* ------------------------------------------------------------------ *)

(* Memory is an array of bytes. A load or a store outside the array gives
   [None]. *)

let load8 (mem : int32 array [@owned]) (addr : int32) : int32 option =
  let i = Int32.to_int addr in
  if 0 <= i && i < Array.length mem then Some mem.(i) else None
[@@spec fun mem addr ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  ret (fun r -> bind (arr mem) @@ fun (n : int32 vec) -> assert (Logic.eq n m))];;

let load16 (mem : int32 array [@owned]) (addr : int32) : int32 option =
  let i = Int32.to_int addr in
  if 0 <= i && i + 1 < Array.length mem then
    Some (Int32.logor mem.(i) (Int32.shift_left mem.(i + 1) 8))
  else None
[@@spec fun mem addr ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  ret (fun r -> bind (arr mem) @@ fun (n : int32 vec) -> assert (Logic.eq n m))];;

let load32 (mem : int32 array [@owned]) (addr : int32) : int32 option =
  let i = Int32.to_int addr in
  if 0 <= i && i + 3 < Array.length mem then
    Some
      (Int32.logor mem.(i)
         (Int32.logor (Int32.shift_left mem.(i + 1) 8)
            (Int32.logor (Int32.shift_left mem.(i + 2) 16)
               (Int32.shift_left mem.(i + 3) 24))))
  else None
[@@spec fun mem addr ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  ret (fun r -> bind (arr mem) @@ fun (n : int32 vec) -> assert (Logic.eq n m))];;

let store8 (mem : int32 array [@owned]) (addr : int32) (x : int32)
    : unit option =
  let i = Int32.to_int addr in
  if 0 <= i && i < Array.length mem then
    (mem.(i) <- Int32.logand x 0xffl;
     Some ())
  else None
[@@spec fun mem addr x ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  ret (fun r ->
    bind (arr mem) @@ fun (n : int32 vec) ->
    assert (Vec.length n = Vec.length m))];;

let store16 (mem : int32 array [@owned]) (addr : int32) (x : int32)
    : unit option =
  let i = Int32.to_int addr in
  if 0 <= i && i + 1 < Array.length mem then
    (mem.(i) <- Int32.logand x 0xffl;
     mem.(i + 1) <- Int32.logand (Int32.shift_right_logical x 8) 0xffl;
     Some ())
  else None
[@@spec fun mem addr x ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  ret (fun r ->
    bind (arr mem) @@ fun (n : int32 vec) ->
    assert (Vec.length n = Vec.length m))];;

let store32 (mem : int32 array [@owned]) (addr : int32) (x : int32)
    : unit option =
  let i = Int32.to_int addr in
  if 0 <= i && i + 3 < Array.length mem then
    (mem.(i) <- Int32.logand x 0xffl;
     mem.(i + 1) <- Int32.logand (Int32.shift_right_logical x 8) 0xffl;
     mem.(i + 2) <- Int32.logand (Int32.shift_right_logical x 16) 0xffl;
     mem.(i + 3) <- Int32.logand (Int32.shift_right_logical x 24) 0xffl;
     Some ())
  else None
[@@spec fun mem addr x ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  ret (fun r ->
    bind (arr mem) @@ fun (n : int32 vec) ->
    assert (Vec.length n = Vec.length m))];;

(* The register file has 32 cells. [x0] reads as zero and ignores writes. The
   index needs no bounds check, because [decode] masks it to 5 bits. *)

let read_reg (regs : int32 array [@owned]) (i : int32) : int32 =
  if Int32.equal i 0l then 0l else regs.(Int32.to_int i)
[@@spec fun regs i ->
  bind (arr regs) @@ fun (v : int32 vec) ->
  assert (Vec.length v = 32);
  assert (u5 i);
  ret (fun r -> bind (arr regs) @@ fun (w : int32 vec) -> assert (Logic.eq w v))];;

let write_reg (regs : int32 array [@owned]) (i : int32) (x : int32) : unit =
  if Int32.equal i 0l then () else regs.(Int32.to_int i) <- x
[@@spec fun regs i x ->
  bind (arr regs) @@ fun (v : int32 vec) ->
  assert (Vec.length v = 32);
  assert (u5 i);
  ret (fun r ->
    bind (arr regs) @@ fun (w : int32 vec) ->
    assert (Vec.length w = 32);
    assert (Int32.equal (Vec.get w 0) (Vec.get v 0)))];;

(* ------------------------------------------------------------------ *)
(* The interpreter                                                    *)
(* ------------------------------------------------------------------ *)

(* [Exit] is [ecall] or [ebreak]. [Trap] is a word that does not decode, or a
   memory access outside the array. *)

type stop =
  | Exit
  | Trap

type outcome =
  | Next of int32
  | Stopped of stop

let step (regs : int32 array [@owned]) (mem : int32 array [@owned])
         (pc : int32) : outcome =
  match load32 mem pc with
  | None -> Stopped Trap
  | Some word ->
  match decode word with
  | None -> Stopped Trap
  | Some i ->
  match i with
  | Add (rd, rs1, rs2) ->
    write_reg regs rd (Int32.add (read_reg regs rs1) (read_reg regs rs2));
    Next (Int32.add pc 4l)
  | Sub (rd, rs1, rs2) ->
    write_reg regs rd (Int32.sub (read_reg regs rs1) (read_reg regs rs2));
    Next (Int32.add pc 4l)
  | Sll (rd, rs1, rs2) ->
    let s = Int32.to_int (Int32.logand (read_reg regs rs2) 0x1fl) in
    write_reg regs rd (Int32.shift_left (read_reg regs rs1) s);
    Next (Int32.add pc 4l)
  | Slt (rd, rs1, rs2) ->
    let c = Int32.compare (read_reg regs rs1) (read_reg regs rs2) in
    write_reg regs rd (if c < 0 then 1l else 0l);
    Next (Int32.add pc 4l)
  | Sltu (rd, rs1, rs2) ->
    let c = Int32.unsigned_compare (read_reg regs rs1) (read_reg regs rs2) in
    write_reg regs rd (if c < 0 then 1l else 0l);
    Next (Int32.add pc 4l)
  | Xor (rd, rs1, rs2) ->
    write_reg regs rd (Int32.logxor (read_reg regs rs1) (read_reg regs rs2));
    Next (Int32.add pc 4l)
  | Srl (rd, rs1, rs2) ->
    let s = Int32.to_int (Int32.logand (read_reg regs rs2) 0x1fl) in
    write_reg regs rd (Int32.shift_right_logical (read_reg regs rs1) s);
    Next (Int32.add pc 4l)
  | Sra (rd, rs1, rs2) ->
    let s = Int32.to_int (Int32.logand (read_reg regs rs2) 0x1fl) in
    write_reg regs rd (Int32.shift_right (read_reg regs rs1) s);
    Next (Int32.add pc 4l)
  | Or (rd, rs1, rs2) ->
    write_reg regs rd (Int32.logor (read_reg regs rs1) (read_reg regs rs2));
    Next (Int32.add pc 4l)
  | And (rd, rs1, rs2) ->
    write_reg regs rd (Int32.logand (read_reg regs rs1) (read_reg regs rs2));
    Next (Int32.add pc 4l)
  | Addi (rd, rs1, imm) ->
    write_reg regs rd (Int32.add (read_reg regs rs1) imm);
    Next (Int32.add pc 4l)
  | Slti (rd, rs1, imm) ->
    let c = Int32.compare (read_reg regs rs1) imm in
    write_reg regs rd (if c < 0 then 1l else 0l);
    Next (Int32.add pc 4l)
  | Sltiu (rd, rs1, imm) ->
    let c = Int32.unsigned_compare (read_reg regs rs1) imm in
    write_reg regs rd (if c < 0 then 1l else 0l);
    Next (Int32.add pc 4l)
  | Xori (rd, rs1, imm) ->
    write_reg regs rd (Int32.logxor (read_reg regs rs1) imm);
    Next (Int32.add pc 4l)
  | Ori (rd, rs1, imm) ->
    write_reg regs rd (Int32.logor (read_reg regs rs1) imm);
    Next (Int32.add pc 4l)
  | Andi (rd, rs1, imm) ->
    write_reg regs rd (Int32.logand (read_reg regs rs1) imm);
    Next (Int32.add pc 4l)
  | Slli (rd, rs1, shamt) ->
    write_reg regs rd
      (Int32.shift_left (read_reg regs rs1) (Int32.to_int shamt));
    Next (Int32.add pc 4l)
  | Srli (rd, rs1, shamt) ->
    write_reg regs rd
      (Int32.shift_right_logical (read_reg regs rs1) (Int32.to_int shamt));
    Next (Int32.add pc 4l)
  | Srai (rd, rs1, shamt) ->
    write_reg regs rd
      (Int32.shift_right (read_reg regs rs1) (Int32.to_int shamt));
    Next (Int32.add pc 4l)
  | Lb (rd, rs1, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match load8 mem addr with
     | Some x ->
       write_reg regs rd (Int32.shift_right (Int32.shift_left x 24) 24);
       Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Lh (rd, rs1, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match load16 mem addr with
     | Some x ->
       write_reg regs rd (Int32.shift_right (Int32.shift_left x 16) 16);
       Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Lw (rd, rs1, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match load32 mem addr with
     | Some x ->
       write_reg regs rd x;
       Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Lbu (rd, rs1, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match load8 mem addr with
     | Some x ->
       write_reg regs rd (Int32.logand x 0xffl);
       Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Lhu (rd, rs1, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match load16 mem addr with
     | Some x ->
       write_reg regs rd (Int32.logand x 0xffffl);
       Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Jalr (rd, rs1, imm) ->
    let t = Int32.add (read_reg regs rs1) imm in
    write_reg regs rd (Int32.add pc 4l);
    Next (Int32.logand t (Int32.lognot 1l))
  | Sb (rs1, rs2, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match store8 mem addr (read_reg regs rs2) with
     | Some u -> Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Sh (rs1, rs2, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match store16 mem addr (read_reg regs rs2) with
     | Some u -> Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Sw (rs1, rs2, imm) ->
    let addr = Int32.add (read_reg regs rs1) imm in
    (match store32 mem addr (read_reg regs rs2) with
     | Some u -> Next (Int32.add pc 4l)
     | None -> Stopped Trap)
  | Beq (rs1, rs2, imm) ->
    if Int32.equal (read_reg regs rs1) (read_reg regs rs2)
    then Next (Int32.add pc imm) else Next (Int32.add pc 4l)
  | Bne (rs1, rs2, imm) ->
    if not (Int32.equal (read_reg regs rs1) (read_reg regs rs2))
    then Next (Int32.add pc imm) else Next (Int32.add pc 4l)
  | Blt (rs1, rs2, imm) ->
    if Int32.compare (read_reg regs rs1) (read_reg regs rs2) < 0
    then Next (Int32.add pc imm) else Next (Int32.add pc 4l)
  | Bge (rs1, rs2, imm) ->
    if Int32.compare (read_reg regs rs1) (read_reg regs rs2) >= 0
    then Next (Int32.add pc imm) else Next (Int32.add pc 4l)
  | Bltu (rs1, rs2, imm) ->
    if Int32.unsigned_compare (read_reg regs rs1) (read_reg regs rs2) < 0
    then Next (Int32.add pc imm) else Next (Int32.add pc 4l)
  | Bgeu (rs1, rs2, imm) ->
    if Int32.unsigned_compare (read_reg regs rs1) (read_reg regs rs2) >= 0
    then Next (Int32.add pc imm) else Next (Int32.add pc 4l)
  | Lui (rd, imm) ->
    write_reg regs rd imm;
    Next (Int32.add pc 4l)
  | Auipc (rd, imm) ->
    write_reg regs rd (Int32.add pc imm);
    Next (Int32.add pc 4l)
  | Jal (rd, imm) ->
    write_reg regs rd (Int32.add pc 4l);
    Next (Int32.add pc imm)
  | Fence (mask) ->
    Next (Int32.add pc 4l)
  | Ecall ->
    Stopped Exit
  | Ebreak ->
    Stopped Exit
[@@spec fun regs mem pc ->
  bind (arr regs) @@ fun (v : int32 vec) ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  assert (Vec.length v = 32);
  ret (fun r ->
    bind (arr regs) @@ fun (w : int32 vec) ->
    bind (arr mem) @@ fun (n : int32 vec) ->
    assert (Vec.length w = 32);
    assert (Vec.length n = Vec.length m);
    assert (Int32.equal (Vec.get w 0) (Vec.get v 0)))];;

(* [run] has no fuel, so its specification is partial correctness. *)

let rec run (regs : int32 array [@owned]) (mem : int32 array [@owned])
            (pc : int32) : stop =
  match step regs mem pc with
  | Next next -> run regs mem next
  | Stopped reason -> reason
[@@spec fun regs mem pc ->
  bind (arr regs) @@ fun (v : int32 vec) ->
  bind (arr mem) @@ fun (m : int32 vec) ->
  assert (Vec.length v = 32);
  ret (fun r ->
    bind (arr regs) @@ fun (w : int32 vec) ->
    bind (arr mem) @@ fun (n : int32 vec) ->
    assert (Vec.length w = 32);
    assert (Vec.length n = Vec.length m);
    assert (Int32.equal (Vec.get w 0) (Vec.get v 0)))];;

(* The sum of 1 to 10. The result is the stop reason and [x2]. A store of the
   program can fail, which gives [None]. *)

let sum_to_ten (u : unit) : (stop * int32) option =
  let mem = Array.make 32 0l [@owned] in
  let regs = Array.make 32 0l [@owned] in
  match store32 mem 0l (encode (Addi (1l, 0l, 10l))) with
  | None -> None
  | Some ok ->
  match store32 mem 4l (encode (Addi (2l, 0l, 0l))) with
  | None -> None
  | Some ok ->
  match store32 mem 8l (encode (Beq (1l, 0l, 16l))) with
  | None -> None
  | Some ok ->
  match store32 mem 12l (encode (Add (2l, 2l, 1l))) with
  | None -> None
  | Some ok ->
  match store32 mem 16l (encode (Addi (1l, 1l, (-1l)))) with
  | None -> None
  | Some ok ->
  match store32 mem 20l (encode (Jal (0l, (-12l)))) with
  | None -> None
  | Some ok ->
  match store32 mem 24l (encode Ecall) with
  | None -> None
  | Some ok ->
  Some (run regs mem 0l, read_reg regs 2l);;
