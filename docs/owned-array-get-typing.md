# Known gap: no SMT type constraints for owned `Array.get` results

Status: known limitation, deliberately not fixed yet.

For a **shared** array, `compile` translates `Array.get` by declaring a fresh
constant for the result and assuming `TinyML.typeConstraints ty sv` for it, so
the solver knows the result's type (e.g. that an `int` element is in the image
of `toInt`).

For an **owned** array, the result is the *term*
`vecGet (toVec contents) (toInt si)` built from the atom's snapshot. No type
constraints are assumed for it. Consequently, pure reasoning that depends on
the element's type (e.g. arithmetic on an element read from an owned
`int array`) can fail even though the corresponding shared-array program
verifies.

Semantically the information is available — the atom's interpretation carries
`ValHasType Θ (.vec vs) (.vec elemTy)` for the snapshot — but it is not
exported to the solver for the selected element.

Possible fixes, for later:

- Mirror the shared case: declare a fresh constant `sv`, assume
  `sv = vecGet (toVec contents) (toInt si)` plus
  `typeConstraints elemTy sv`. The correctness proof gets the semantic typing
  fact from the big-sep over the snapshot (`BigSepL.bigSepL_lookup`), as
  `wp_arrayGet_owned` already does.
- Alternatively, emit elementwise type constraints for the whole snapshot when
  an owned-array atom enters the context (as an atom-level fact, like the
  length fact), quantifying over indices.
