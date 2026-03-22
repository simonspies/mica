# N-ary Sum Types for Mica — Implementation Plan

## Context

Mica currently has partial binary sum type support: `Type_.sum t1 t2`, `Val.inl`/`Val.inr`, and `TinyML.UnOp.inl`/`.inr` exist in the AST/typing/op-sem but the verifier rejects them (`compileUnop` returns `none`, unsupported cases in `compile` call `VerifM.fatal`). We are replacing this with a complete n-ary sum type implementation that supports OCaml-style algebraic data types, including construction (`inj`), elimination (`match_`), and full verification through the SMT layer.

### Key design decisions

- **N-ary sums**: `Type_.sum (ts : List Type_)` replaces binary `sum t1 t2`
- **Uniform injection**: `Val.inj (tag : Nat) (arity : Nat) (payload : Val)` replaces `Val.inl`/`Val.inr`. Arity lives in the value because it is needed for principal types: without it, `inj 1 _ 4` could be `sum [⊥, int]` or `sum [⊥, int, ⊥]` etc.
- **Match with function branches**: `Expr.match_ (scrutinee : Expr) (branches : List Expr)` — branches are function expressions. Op-sem reduces via application (`match_ (inj i n v) [f0,...] → app fi [v]`). The compiler peeks inside lambdas and uses let-binding logic rather than compiling function application.
- **Constructor names resolved to numeric tags in the parser** — by the time we reach the verifier, constructors are gone. `type foo = A | B of int | C of int * int` produces a map `{A → (0,3), B → (1,3), C → (2,3)}`. Constructor applications are rewritten to `Expr.inj`.
- **FOL encoding**: `UnOp.mkInj tag arity : UnOp .value .value`, `UnOp.tagOf`/`UnOp.arityOf`/`UnOp.payloadOf`, `Atom.isinj tag arity`
- **SMT encoding**: extend `Value` datatype with `(of_inj (tag_of Int) (arity_of Int) (payload_of Value))`

---

## Phase 1: TinyML Layer (AST, Typing, OpSem)

### 1a. `Mica/TinyML/Expr.lean` — AST changes

**What changes:**

1. **`Type_.sum`** (line 21): `sum (t1 t2 : Type_)` → `sum (ts : List Type_)`
   - `Type_.decEq`: the `sum` case currently matches two fields. Change to match a single `List Type_` using the existing `typesDecEq` helper (same pattern as the `.tuple` case on line 39-41).
   - The negative cases in `decEq` (lines 42-60) use `.sum ..` wildcards, which will continue to work regardless of field count — no changes needed there.

2. **`Val`** (lines 89-97): Remove `.inl (v : Val)` and `.inr (v : Val)`. Add `.inj (tag : Nat) (arity : Nat) (payload : Val)`.
   - `Val.decEq`: remove `inl.inl`/`inr.inr` cases (lines 130-135). Add `inj.inj` case matching all three fields (tag, arity by `decEq` on `Nat`, payload by `Val.decEq`).

3. **`TinyML.UnOp`** (lines 82-86): Remove `.inl` and `.inr`. Construction is now via `Expr.inj`, not a unary operator.
   - `.neg`, `.not`, `.proj` remain.

4. **New `Expr` constructors** (add after `.tuple` on line 112):
   - `| inj (tag : Nat) (arity : Nat) (payload : Expr)` — injection into a sum
   - `| match_ (scrutinee : Expr) (branches : List Expr)` — elimination; branches are function expressions

5. **`Expr.decEq`**: add `inj.inj` case (3 fields) and `match_.match_` case (use `Expr.decEq` + `exprsDecEq`). Add negative cases for new constructors against all others.

6. **`Expr.subst`** (lines 310-325): add:
   ```
   | .inj tag arity payload => .inj tag arity (payload.subst σ)
   | .match_ scrut branches => .match_ (scrut.subst σ) (branches.subst σ)
   ```

7. **`Expr.freeVars`** (lines 401+): add:
   ```
   | .inj _ _ payload => payload.freeVars
   | .match_ scrut branches => scrut.freeVars ++ branches.freeVars
   ```

8. **Substitution lemmas** (`Expr.subst_none`, `Expr.subst_comp`, `Expr.subst_remove'_update'`): these are proven by structural induction with `Expr.rec`. The new cases for `inj` are trivial (one recursive subterm). The `match_` case follows the same pattern as `app` (which also has `List Expr` mapped over). The existing `motive_4` for lists of expressions should handle it.

### 1b. `Mica/TinyML/Typing.lean` — Type system

**What changes:**

1. **`Type_.Sub`** (lines 66-80): The current `.sum` case is:
   ```
   | sum : Type_.Sub s1 t1 → Type_.Sub s2 t2 → Type_.Sub (.sum s1 s2) (.sum t1 t2)
   ```
   Replace with pointwise subtyping on lists. Since this is a `Prop` inductive that would go through `List.Forall₂`, use the mutual inductive pattern (per CLAUDE.md):
   ```
   | sum : Type_.SubList ss ts → Type_.Sub (.sum ss) (.sum ts)
   ```
   where `Type_.SubList` is defined mutually (analogous to the tuple case if one exists, or following the pattern in CLAUDE.md). **Check first**: the tuple case on line 71 may already use a mutual `SubList` — if so, sums can reuse it. If tuples use a different mechanism, follow whatever pattern is established.

2. **`Type_.join` / `Type_.meet` / `Type_.sub`**: the `.sum` cases (lines 91, 102, 124) currently operate on two fields. Change to operate on lists:
   - `join`: zip with `Type_.join` (only if same length, else `.value`)
   - `meet`: zip with `Type_.meet` (only if same length, else `.empty`)
   - `sub`: pointwise check, must have same length

3. **`UnOp.typeOf`** (lines 298-304): Remove `.inl` and `.inr` cases. These were:
   ```
   | .inl, t => some (.sum t .empty)
   | .inr, t => some (.sum .empty t)
   ```

4. **New typing rules for `Expr.inj`**: Given `payload : t`, the result type is `Type_.sum ts` where `ts` is a list of length `arity` with `t` at position `tag` and `.empty` everywhere else.
   - Helper: `Type_.singletonSum (tag : Nat) (t : Type_) (arity : Nat) : List Type_` that builds `[.empty, ..., t, ..., .empty]`.

5. **New typing rules for `Expr.match_` if needed**: Scrutinee has `Type_.sum ts`, each branch `branches[i]` has type `ts[i] → t_i`, result type is `Type_.join` over all `t_i`. This requires:
   - Checking that `branches.length = ts.length`
   - Each branch is typeable as a function from `ts[i]`
   - Joining all return types

6. **`ValHasType`** (lines 307-351): Replace:
   ```
   | inl : ValHasType v t1 → ValHasType (.inl v) (.sum t1 t2)
   | inr : ValHasType v t2 → ValHasType (.inr v) (.sum t1 t2)
   ```
   with:
   ```
   | inj : (h_bound : tag < ts.length) → ValHasType payload (ts.get ⟨tag, h_bound⟩)
         → ValHasType (.inj tag ts.length payload) (.sum ts)
   ```
   Note: arity in the value must equal `ts.length`.

7. **`ValHasType_sub`** (line 330+): update the `.sum` case — was destructing on `.inl`/`.inr`, now destructs on `.inj` and uses pointwise list subtyping.

8. **`evalUnOp_typed`** (lines 396-422): Remove `case inl` and `case inr` (lines 400-407).

### 1c. `Mica/TinyML/OpSem.lean` — Operational semantics

**What changes:**

1. **`evalUnOp`** (lines 8-15): Remove:
   ```
   | .inl, v => some (.inl v)
   | .inr, v => some (.inr v)
   ```
   These are no longer unary operators.

2. **Evaluation contexts `K`** (lines 35-82): Add:
   - `| inj (tag : Nat) (arity : Nat) (k : K)` — evaluating the payload of an injection
   - `| match_ (branches : List Expr) (k : K)` — evaluating the scrutinee of a match

3. **`K.plug`**: add cases:
   ```
   | .inj tag arity k => .inj tag arity (k.plug e)
   | .match_ branches k => .match_ (k.plug e) branches
   ```

4. **Head reduction `Head`** (lines 90-132): Add:
   - `| inj_val : Head (.inj tag arity (val v)) (.val (.inj tag arity v))` — injection of a value
   - `| match_ : (h : i < branches.length) → n = branches.length -> Head (.match_ (.val (.inj i n v)) branches) (.app (branches.get ⟨i, h⟩) [.val v])` — match reduces to application of the i-th branch to the payload

5. **`Step`**: should work unchanged since it's defined in terms of `K` and `Head`.

### 1d. `Mica/TinyML/WeakestPre.lean` — Weakest Precondition

**What changes:**

This file contains axiomatized wp rules. Add:

1. **`wp.inj`** — analogous to `wp.tuple`: the payload evaluates, then gets wrapped.
   ```lean
   axiom wp.inj {tag arity : Nat} {payload : TinyML.Expr} {Q : TinyML.Val → Prop} :
     wp payload (fun v => Q (.inj tag arity v)) → wp (.inj tag arity payload) Q
   ```

2. **`wp.match_`** — the scrutinee evaluates to an injection, then the corresponding branch is applied. The continuation must *prove* the value is an injection (this is a proof obligation, not an assumption):
   ```lean
   axiom wp.match_ {scrut : TinyML.Expr} {branches : TinyML.Exprs} {Q : TinyML.Val → Prop} :
     wp scrut (fun v =>
       ∃ (tag : Nat) (arity : Nat) (payload : TinyML.Val),
         v = .inj tag arity payload ∧ tag < branches.length ∧
         wp (.app (branches[tag]'‹_›) [.val payload]) Q) →
     wp (.match_ scrut branches) Q
   ```
   Note the use of `∃`/`∧`, not `∀`/`→`: the caller must exhibit a tag and prove the scrutinee matches it. This is essential — matching on a non-injection value is a stuck term, so the wp must require evidence that the value is an injection.

### 1e. `Mica/TinyML/Lexer.lean` + `Parser.lean` + `Printer.lean`

**Lexer** (`Lexer.lean`):
- Remove `kw_inl` / `kw_inr` tokens (lines 28-29) and their keyword mappings (lines 97-98)
- Add tokens: `kw_match`, `kw_with`, `kw_type`, `pipe` (the `|` character for match arms)
- May already have some of these — check before adding

**Parser** (`Parser.lean`):
- **Type declarations**: Parse `type foo = A | B of int | C of int * int`. This produces a `CtorMap`:
  ```
  abbrev CtorMap := String → Option (Nat × Nat)
  -- maps constructor name to (tag, arity)
  ```
  Store in parser state or pass as parameter.
- **Constructor application**: When parsing an expression and encountering an identifier that's in the `CtorMap`, parse it as `Expr.inj tag arity payload_expr`. For nullary constructors, payload is `Expr.val .unit`.
- **Match expression**: Parse `match e with | A x -> e1 | B y -> e2 | ...`:
  - Resolve each constructor name to its tag index
  - Wrap each branch body in a lambda: `A x -> e1` becomes `fun x -> e1` at position 0
  - Produce `Expr.match_ e [fun x -> e1, fun y -> e2, ...]` with branches ordered by tag
- **Remove** `inl`/`inr` keyword handling from `parseUnary` (lines 287, 296)
- **Type parsing**: `(T1, T2) Either.t` syntax (line 99-105) → update or replace.

**Printer** (`Printer.lean`):
- Remove `Either.Left`/`Either.Right` printing (lines 12, 103-104, 127-128)
- Print `Val.inj tag arity v` as `(inj {tag}/{arity} {v})` or similar debug representation
- Print `Expr.inj` and `Expr.match_` in readable form

---

## Phase 2: FOL Layer (Terms, Formulas, Printing)

### 2a. `Mica/FOL/Terms.lean` — New operators

**Current state:** `UnOp` (lines 3-15) has coercions (`ofInt`, `ofBool`, `toInt`, `toBool`), negation (`neg`, `not`), and list ops (`ofValList`, `toValList`, `vhead`, `vtail`, `visnil`). All have `DecidableEq` and `Repr`.

**Add to `UnOp`:**
```lean
| mkInj (tag : Nat) (arity : Nat) : UnOp .value .value
| tagOf                           : UnOp .value .int
| arityOf                         : UnOp .value .int
| payloadOf                       : UnOp .value .value
```

`mkInj` bakes tag and arity into the operator since they are always statically known at injection sites. This avoids needing ternary term constructors.

**`UnOp.eval`** (lines 83-94 — add cases):
```lean
| .mkInj tag arity => fun v => Val.inj tag arity v
| .tagOf => fun v => match v with
  | .inj tag _ _ => (tag : Int)
  | _ => 0
| .arityOf => fun v => match v with
  | .inj _ arity _ => (arity : Int)
  | _ => 0
| .payloadOf => fun v => match v with
  | .inj _ _ payload => payload
  | _ => Val.unit
```

**`DecidableEq` for `UnOp`:** Currently derived. With `mkInj` carrying `Nat` parameters, `deriving DecidableEq` should still work since `Nat` has `DecidableEq`. Verify after implementation.

### 2b. `Mica/FOL/Printing.lean` — SMT-LIB serialization

**`UnOp.toSMTLIB`** (lines 21-32): Add cases:
```lean
| .mkInj tag arity => s!"(of_inj {tag} {arity} {arg})"
| .tagOf           => s!"(tag_of {arg})"
| .arityOf         => s!"(arity_of {arg})"
| .payloadOf       => s!"(payload_of {arg})"
```

**`UnOp.toString`** (human-readable, if it exists): add corresponding cases.

### 2c. `Mica/FOL/Formulas.lean` — Predicates

**`UnPred`** (lines 3-7) currently has `.isInt`, `.isBool`, `.isTuple`. These are used in `Formula` as `| pred : UnPred → Term .value → Formula`.

Add `.isInj (tag : Nat) (arity : Nat) : UnPred`. Its semantics:
```lean
| .isInj tag arity => fun v => match v with
  | .inj t a _ => t = tag ∧ a = arity
  | _ => False
```
This parallels `isInt`/`isBool` and integrates with `Atom.candidates`.


**SMT printing for `UnPred.isInj`:** Use `(and (is-of_inj {arg}) (= (tag_of {arg}) {tag}) (= (arity_of {arg}) {arity}))`. All three primitives are available: `is-of_inj` from the SMT datatype declaration, `tag_of` and `arity_of` from the corresponding `FOL.UnOp` operators.

---

## Phase 3: Engine Layer (SMT Preamble)

### 3a. `Mica/Engine/Driver.lean` — one-line change

**Current preamble** (lines 13-29, the SMT content is lines 18-25):
```smt2
(declare-datatypes ((Value 0) (ValueList 0)) (
  ((of_int (to_int Int))
   (of_bool (to_bool Bool))
   (of_other (to_other Other))
   (of_tuple (to_tuple ValueList)))
  ((vnil)
   (vcons (vhd Value) (vtl ValueList)))))
```

**New preamble** — add `of_inj` constructor to `Value`:
```smt2
(declare-datatypes ((Value 0) (ValueList 0)) (
  ((of_int (to_int Int))
   (of_bool (to_bool Bool))
   (of_other (to_other Other))
   (of_tuple (to_tuple ValueList))
   (of_inj (tag_of Int) (arity_of Int) (payload_of Value)))
  ((vnil)
   (vcons (vhd Value) (vtl ValueList)))))
```

This automatically gives us:
- Constructor: `(of_inj <tag> <arity> <payload>)`
- Destructors: `(tag_of v)`, `(arity_of v)`, `(payload_of v)`
- Tester: `(is-of_inj v)` (returns Bool)

---

## Phase 4: Verifier Layer (Atoms, Expressions, Correctness)

### 4a. `Mica/Verifier/Atoms.lean` — New atom

**Current atoms** (lines 19-21):
```lean
inductive Atom : Srt → Type where
  | isint  : Term .value → Atom .int
  | isbool : Term .value → Atom .bool
```

The sort index indicates what the atom *extracts*: `isint` asserts "this value is an int" and extracts an `Int`-sorted term. `isbool` similarly.

**Add:**
```lean
  | isinj (tag : Nat) (arity : Nat) : Term .value → Atom .value
```

`isinj tag arity v` asserts "v is an injection with this tag and arity" and extracts the **payload** as a `.value`-sorted term. The extracted sort is `.value` (not `.int` or `.bool`) because payloads are heterogeneous runtime values.

**`Atom.subst`** (lines 28-30): Add `| .isinj tag arity t => .isinj tag arity (t.subst σ)`.

**`Atom.toFormula`** (lines 38-40): This converts `Atom τ` applied to a `Term τ` into a `Formula`. For `isinj`:
```lean
| .isinj tag arity v, t => .eq .value v (.unop (.mkInj tag arity) t)
```
This says `v = of_inj tag arity t`, which is the same pattern as `isint v t ↔ v = of_int t`.

**`Formula.matchAtom`** (lines 43-52): Add pattern for `isinj`:
```lean
| .isinj tag arity v =>
  match φ with
  | .eq .value v' (.unop (.mkInj tag' arity') t) =>
    if v' = v ∧ tag = tag' ∧ arity = arity' then some t else none
  | _ => none
```

**`Atom.candidates`** (lines 200-202): Currently generates `isInt` and `isBool` candidates for a value-sorted term. For injection, we need to generate `isinj i n` candidates for each possible `(i, n)`. **Problem:** unlike `isInt`/`isBool` where there are exactly 2 sort predicates, injections are parameterized. The verifier needs to know which tags to try.

**Solution:** The verifier's `compile` for `match_` explicitly introduces `isinj` assumptions per branch — it doesn't need `candidates` to guess. The `resolve` mechanism (which uses `candidates`) is for resolving *unknown* sorts. For match branches, the sort is *known* (we assumed it). So `candidates` may not need injection cases at all — or we add them parameterized by the known type context. **Revisit during implementation.**

### 4b. `Mica/Verifier/Expressions.lean` — Compilation

**Remove old sum support:**
- `compileUnop` (line 76): the `| _ => none` catch-all currently covers `inl`/`inr`. After removing them from `TinyML.UnOp`, the catch-all is dead code (`.neg`, `.not`, `.proj` all have explicit cases) — remove it entirely.
- `compileUnop_eval` (line 101): remove `| inl | inr => simp [compileUnop] at hcomp`.
- `compile`, lines 196-198: remove `| .val (.inl _) | .val (.inr _)` from unsupported cases.

**Add `Expr.inj` compilation** (note: `compile` takes `(S B Γ)`):
```lean
| .inj tag arity payload => do
    let (ty, s) ← compile S B Γ payload
    let sumTy := Type_.sum (List.replicate arity .empty |>.set tag ty)
    pure (sumTy, Term.unop (.mkInj tag arity) s)
```
This compiles the payload, wraps it in `mkInj`, and returns a sum type with the payload type at the tag position.

**Add `Expr.match_` compilation** (note: `compile` takes `(S B Γ)`):
```lean
| .match_ scrut branches => do
    let (ty, s) ← compile S B Γ scrut
    match ty with
    | .sum ts =>
      if ts.length ≠ branches.length then VerifM.fatal "match arity mismatch"
      else
        VerifM.all (branches.enum.map fun ⟨i, fi⟩ => VerifM.bracket do
          -- fi must be a fix expression; extract its single binder and body
          match fi with
          | .fix self [(binder, _)] _ body =>
            -- Declare a fresh variable for the payload
            let xv ← VerifM.decl (.value)
            -- Assume the scrutinee is an injection with tag i
            VerifM.assume (.eq .value s (.unop (.mkInj i ts.length) (.var .value xv.name)))
            -- Compile the body with the payload bound
            let B' := B.extend binder xv
            let B'' := B'.extendSelf self  -- if self-recursive (usually .none for lambdas)
            compile S B'' Γ body
          | _ => VerifM.fatal "match branch is not a function"
        )
    | _ => VerifM.fatal "match on non-sum type"
```

Key insight: each branch is wrapped in `VerifM.bracket` (push/pop), and we `assume` the scrutinee equals `mkInj i n payload_var`. This is essentially the same pattern as `ifThenElse` compilation (assume condition true in one branch, false in the other), but generalized to n branches.

### 4c. Correctness proofs

**`compile_correct`**: The main soundness theorem. Must add cases for `inj` and `match_`.

**`inj` case:** Relatively straightforward. Need to show:
- If `compile (.inj tag arity payload) S B` succeeds
- And `VerifM.eval` holds
- Then `wp (.inj tag arity payload) Q` holds

This follows from the `payload` case of `compile_correct` (induction hypothesis) plus `wp.inj`. The key lemma is:
```
mkInj_eval : (Term.unop (.mkInj tag arity) s).eval ρ = Val.inj tag arity (s.eval ρ)
```

**`match_` case:** This is the hardest proof. Need:
1. `compile_correct` for the scrutinee (IH)
2. For each branch: `compile_correct` for the body (IH, under the bracket/assume context)
3. Connect `VerifM.all` semantics (verifier checks *all* branches) to `wp.match_` (existential: *some* branch works) — soundness: if all branches verify, then whichever branch the runtime takes is covered
4. Show that the `assume` of `s = mkInj i n payload_var` correctly models the case split

Helper lemmas needed:
- `eval_mkInj_inj`: if `v = Val.inj i n p` then `(mkInj i n).eval p = v` (round-trip)
- `tagOf_mkInj`: `tagOf (mkInj i n p) = i`
- `arityOf_mkInj`: `arityOf (mkInj i n p) = n`
- `payloadOf_mkInj`: `payloadOf (mkInj i n p) = p`
- Interaction between `VerifM.all`, `VerifM.bracket`, `VerifM.assume` and `VerifM.eval`

**Estimated effort:** The `inj` case is ~1 session. The `match_` case may need 2-3 sessions and possibly new lemmas about `VerifM.all`.

### 4d. `Mica/Verifier/Parser.lean` — Spec expressions

Specs need to reference sum types. At minimum:
- `inj tag arity e` syntax in spec expressions (so specs can assert "returns inj 0 2 x")
- Possibly match in specs (less clear if needed immediately)

This can be deferred if specs don't yet need sum types.

---

## Phase 5: Verification & Testing

- `lake build` must succeed with no errors
- `lean_diagnostic_messages` on all modified declarations — no sorry in dependency chain
- Test with example programs:
  ```ocaml
  type result = Ok of int | Err of int

  let classify (x : int) : result =
    if x >= 0 then Ok x else Err x

  (*@ spec classify (x : value) : value =
        if x >= 0 then inj 0 2 x else inj 1 2 x @*)
  ```
- Verify the SMT preamble works with Z3 (`lake exe mica` on a test file)
- Test match:
  ```ocaml
  type option_int = None | Some of int

  let unwrap_or (default : int) (opt : option_int) : int =
    match opt with
    | None -> default
    | Some x -> x

  (*@ spec unwrap_or (default : value) (opt : value) : value =
        match opt (fun _ -> default) (fun x -> x) @*)
  ```
  Note: the parser desugars each branch into a lambda, so `| None -> default` becomes `fun () -> default` at tag 0, and `| Some x -> x` becomes `fun x -> x` at tag 1. The spec uses the desugared form directly.

---

## Work Breakdown

| Phase | Files | Difficulty | Agent | Notes |
|-------|-------|-----------|-------|-------|
| 1a | Expr.lean | Medium | Sonnet | Mechanical but many cases in decEq |
| 1b | Typing.lean | Medium | Sonnet | Mutual inductive for SubList |
| 1c | OpSem.lean | Easy | Sonnet | New K contexts + head rules |
| 1d | WeakestPre.lean | Easy | Sonnet | Two new axioms |
| 1e | Lexer/Parser/Printer | Medium | Sonnet | Parser is the bulk |
| 2a | FOL/Terms.lean | Easy | Sonnet | 4 new UnOps + eval |
| 2b | FOL/Printing.lean | Easy | Haiku | SMT-LIB strings |
| 2c | FOL/Formulas.lean | Easy | Sonnet | Optional UnPred |
| 3 | Engine/Driver.lean | Trivial | Haiku | One line in preamble |
| 4a | Atoms.lean | Medium | Opus | New atom + integration |
| 4b | Expressions.lean | Hard | Opus | compile for inj + match_ |
| 4c | Correctness proofs | Hard | Opus | compile_correct cases |
| 4d | Parser.lean (specs) | Medium | Sonnet | Can defer |

### Dependency order

```
Phase 3 (SMT preamble) ──────────────────────────────────┐
Phase 1a (AST) ──┬── Phase 1b (Typing)                   │
                 ├── Phase 1c (OpSem)                    │
                 ├── Phase 1d (WeakestPre)               │
                 ├── Phase 1e (Lexer/Parser/Printer)     │
                 └── Phase 2 (FOL) ──────────────────────┼── Phase 4 (Verifier)
                                                         │
                      Phase 1b ──────────────────────────┘
```

Phase 3 and Phase 1a can start in parallel. Phase 2 depends only on 1a. Phases 1b-1e depend on 1a and are independent of each other. Phase 4 depends on everything.
