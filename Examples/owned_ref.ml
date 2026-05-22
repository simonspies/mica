let owned_ref_roundtrip (x : int) : unit =
  let r = ref 0 [@owned] in
  r := 7;
  assert (!r = 7)
;;
