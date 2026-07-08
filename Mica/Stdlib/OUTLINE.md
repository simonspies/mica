**Mica/Stdlib**

- `CharStd.lean` — Character intrinsics (`Char.code`, `Char.chr`, `Char.equal`) and their soundness instances.
- `Combinators.lean` — Embeddings and the pure-intrinsic builders (`Pure.Zero`/`Pure.Unary`/`Pure.Binary`) that emit an intrinsic and its soundness instance, plus the shared helper lemmas their soundness proofs use.
- `FloatStd.lean` — IEEE binary64 float intrinsics (`Float.abs`, `add`, `min`, `equal`, `nan`, …) and soundness instances.
- `FunStd.lean` — `Fun.id`
- `IntStd.lean` — Integer-arithmetic intrinsics (`Int.min`, `Int.max`) and their soundness instances.
- `StringStd.lean` — Byte-string intrinsics (`String.length`, `cat`, `equal`, `starts_with`, `ends_with`) and soundness instances.
