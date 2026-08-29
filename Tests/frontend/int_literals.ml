(* TEST: roundtrip *)
open Mica

let _ = assert (0xff = 255)
let _ = assert (0XFF = 255)
let _ = assert (0o377 = 255)
let _ = assert (0b1010_0101 = 165)
let _ = assert (1_000_000 = 1000000)
let _ = assert (0x1_f = 31)
let _ = assert (Float.equal 1_0.5_0 10.5)
let _ = assert (Float.equal 1_0e1_0 1e11)
