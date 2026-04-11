# CLAUDE.md

## Project Overview

Mica is a Lean 4 project (Lean 4.28.0, Mathlib) implementing a verified program verifier for a fragment of OCaml.
It has both an executable binary (`mica`) that verifies programs via Z3, and mechanized correctness proofs of the key verifier components.

The project lives under `Mica/` and consists of:

1. **FOL/** — First-order logic with Tarski semantics, designed for SMT solver integration.
2. **Frontend/** — Lexer, parser, AST, elaborator, pretty-printer, and spec parser for the OCaml-like surface syntax.
3. **TinyML/** — Core IR: expression AST, type system, operational semantics, and weakest preconditions.
4. **Engine/** — Generic interaction-tree infrastructure for SMT solver communication.
5. **Verifier/** — The verifier implementation, stratified into monadic layers with correctness proofs.
6. **Base/** — Shared utilities (fresh variable generation, `Except` helpers).

All modules have complete proofs except: `FOL/Deduction.lean` (2 sorries in the natural deduction soundness proof).

**Exploration/** contains experimental scratch work where sorries and incomplete proofs are acceptable.

**Main.lean** is the CLI entry point: parses an OCaml source file via the Frontend, elaborates into TinyML, runs `Program.verify` via a Z3 subprocess, and reports results.

---

## Architecture and File Map

### FOL/ — First-Order Logic

- **`FOL/Terms.lean`** — `Srt` (sorts: `int`, `bool`, `value`), `Term τ` (typed terms), `Subst`, `Env`. `Srt.denote` maps sorts to Lean types (`Int`, `Bool`, `TinyML.Val`). `Term.eval : Env → Term τ → τ.denote` is the denotational semantics.
- **`FOL/Formulas.lean`** — `Formula` inductive (equality, comparison, connectives, quantifiers, `isInt`/`isBool` predicates). `Formula.eval : Env → Formula → Prop` (Tarski semantics). `Formula.subst` (capture-avoiding), `Formula.freeVars`, and correctness proofs.
- **`FOL/Printing.lean`** — Serialization to SMT-LIB2 (`Srt.toSMTLIB`, `Term.toSMTLIB`, `Formula.toSMTLIB`) plus human-readable pretty-printers. No proofs.
- **`FOL/Deduction.lean`** — Natural deduction proof system (`Proof sig Γ φ`). Soundness w.r.t. `Formula.eval`. Contains 2 sorries.

The FOL layer has no knowledge of the Engine or Verifier layers.

### Frontend/ — Surface Language Frontend

Parses OCaml-like source into a standalone AST, then elaborates into the `TinyML.Expr` IR.

- **`Frontend/AST.lean`** — `Frontend.AST`: the surface-level expression type, distinct from `TinyML.Expr`.
- **`Frontend/Lexer.lean`** — Lexer for the OCaml-like surface syntax.
- **`Frontend/Parser.lean`** — Recursive descent parser producing `Frontend.AST`. `Frontend.parseFile : String → String → Except String Frontend.Program`.
- **`Frontend/Elaborate.lean`** — Elaboration from `Frontend.AST` to `TinyML.Expr`/`TinyML.Program`. `Frontend.Program.elaborate`.
- **`Frontend/Printer.lean`** — Pretty-printer for the frontend AST (targets OCaml syntax). `Frontend.Program.print`.
- **`Frontend/Spec.lean`** — Untyped spec AST (`Spec.Term`, `Spec.Pred`, `Spec.Assert`, `Spec.Pre`, `Spec.Post`, `Spec.Body`).
- **`Frontend/SpecParser.lean`** — Parses elaborated `TinyML.Expr` spec attributes into `Spec.Body`. `Spec.parse`.

The Frontend has no knowledge of the Verifier or Engine layers.

### Engine/ — Strategy Infrastructure

Generic SMT interaction framework. Does not know about verifier logic.

- **`Engine/Command.lean`** — `Command β`: SMT commands indexed by response type. `SmtState` (push/pop stack), serialization (`Command.query`, `Command.parseResponse`).
- **`Engine/Strategy.lean`** — `Strategy α`: interaction tree (`.done` | `.exec cmd k`). `Trace α`, `Generates` (relational semantics), `Strategy.eval`, `Strategy.bind`.
- **`Engine/Driver.lean`** — IO execution: `SmtSession` (Z3 subprocess), `run`, `execute`. Defines the SMT preamble declaring the `Value` datatype (`of_int`, `of_bool`, `of_other`).

### Verifier/ — The Verifier

Stratified into layers, from low-level SMT interaction to high-level program verification:

- **`Verifier/Scoped.lean`** — `ScopedM`: continuation monad over SMT ops (`ret`, `declareConst`, `assert`, `checkSat`, `bracket`). `ScopedM.translate` compiles to `Strategy`. `FlatCtx` (flattened SMT state). `ScopedM.eval` (extensional semantics). Inversion lemmas.

- **`Verifier/Monad.lean`** — `VerifM α`: free monad with ops `decl`, `assume`, `assert`, `fatal`, `failed`, `all`, `any`, `resolve`, `seq`. `VerifM.translate` compiles to `ScopedM`. `VerifM.eval` is the verification predicate. Adequacy theorem: `translate` success implies `eval`. Inversion lemmas: `eval_ret`, `eval_bind`, `eval_decl`, `eval_assume`, `eval_assert`, `eval_fatal`, `eval_seq`.

- **`Verifier/Atoms.lean`** — `Atom τ`: sort predicates that assert a value-sorted term has a specific sort and extract the underlying typed value (`isint`, `isbool`). Substitution and evaluation.

- **`Verifier/Assertions.lean`** — `Assertion` inductive: monadic structure for building logical assertions (`ret`, `assert`, `let_`, `pred`, `ite`). `Assertion.pre`/`Assertion.post` (Prop-valued semantics). `Assertion.assume`/`Assertion.prove` (VerifM functions). `Assertion.assume_correct`/`Assertion.prove_correct` (soundness).

- **`Verifier/PredicateTransformers.lean`** — `PredTrans` (predicate transformers built on `Assertion`), `SpecPredicate`. Well-formedness predicates.

- **`Verifier/Specifications.lean`** — `Spec` (complete specification pairing `PredTrans` with argument/return types), `SpecMap`, `Spec.isPrecondFor`, `Spec.complete`, `declareExpected`.

- **`Verifier/SpecTranslation.lean`** — Translates untyped `Spec.Body` (from the frontend spec parser) into typed `Assertion`/`SpecPredicate` values for the verifier.

- **`Verifier/Utils.lean`** — `Bindings` (association list `TinyML.Var × Var`), `Bindings.agreeOnLinked`, `Bindings.wf`, `Bindings.typedSubst`, and associated lemmas.

- **`Verifier/Expressions.lean`** — `compileOp` (lifts `TinyML.BinOp` to `Term .value`), `compile` (compiles `TinyML.Expr` to SMT terms via `VerifM`), `compile_correct` (soundness w.r.t. `wp`).

- **`Verifier/Functions.lean`** — `checkSpec` (verifies a function against a `Spec`), `checkSpec_strategy`, `checkSpec_correct` (soundness).

- **`Verifier/Programs.lean`** — `Program.check` (iterates over declarations, parses specs, verifies each via `checkSpec` using `seq` for scoping). `Program.verify` (wraps as `Strategy Outcome`). Uses explicit recursion for provability.

### TinyML/ — Core IR

The intermediate representation that the Frontend elaborates into. Three independent ASTs (Untyped, Typed, Runtime) sharing a common vocabulary, with erasure functions mapping the surface IRs down to the runtime IR.

**Dependency structure:**
```
Common  (Var, BinOp, UnOp, Const)
├── RuntimeExpr   
│   ├── Heap      
│   ├── OpSem     
│   └── WeakestPre 
├── Types         
│   ├── Untyped   
│   ├── Typed     
│   ├── LogicalRelation 
│   └── Typing    
└── Printer       
```

- **`TinyML/Common.lean`** — Shared non-type vocabulary: `Var`, `BinOp`, `UnOp`, `Const`.
- **`TinyML/Types.lean`** — `Typ` (types), `TyVar`, `TypeName`, `DataDecl`, `TypeEnv`. Subtyping (`Typ.Sub`, `Typ.SubList`), decision procedure (`Typ.sub`), `Typ.join`/`Typ.meet`, `BinOp.typeOf`, `UnOp.typeOf`.
- **`TinyML/Untyped.lean`** — `Untyped.Binder`, `Untyped.Expr`, `Untyped.Program`. Erasure to `Runtime.Expr` via `.runtime`.
- **`TinyML/Typed.lean`** — `Typed.Binder`, `Typed.Expr` (all nodes carry types, includes `cast`), `Typed.Program`. Erasure to `Runtime.Expr` via `.runtime`.
- **`TinyML/RuntimeExpr.lean`** — `Runtime.Val`, `Runtime.Expr`, `Runtime.Subst` (substitution with `update`, `removeAll`, `freeVars`). No type dependencies.
- **`TinyML/OpSem.lean`** — Small-step operational semantics. `evalBinOp`, `evalUnOp`, evaluation contexts (`K`), `Head`, `Step`, `Steps`.
- **`TinyML/Heap.lean`** — `Heap = Finmap Location Val`. `lookup`, `update`, `dom`, `Fresh`.
- **`TinyML/WeakestPre.lean`** — Axiomatized weakest precondition calculus (`wp`, `pwp`).
- **`TinyML/LogicalRelation.lean`** — `ValHasType`, `ValsHaveTypes` (logical relation between runtime values and types). Subsumption lemmas, type preservation for operators.
- **`TinyML/Typing.lean`** — `TyCtx`, `TypeError`, bidirectional type inference (`infer`, `check`), program elaboration (`Program.elaborate`). Runtime correctness proofs (`infer_runtime`, `elaborate_runtime`).
- **`TinyML/Printer.lean`** — Precedence-aware pretty-printer for the Untyped AST.

### Base/ — Shared Utilities

- **`Base/Fresh.lean`** — `fresh : (ℕ → X) → List X → X`. Key property: `fresh_not_mem`.
- **`Base/Except.lean`** — Auxiliary lemmas for `Except` (e.g., `bind_ok`).

### Key Cross-Cutting Concepts

**Data flow:**
```
OCaml source file
  → Frontend.parseFile (Frontend/Parser.lean) → Frontend.Program
  → Frontend.Program.elaborate (Frontend/Elaborate.lean) → TinyML.Program
  → Program.verify (Verifier/Programs.lean) → Strategy Outcome
    per declaration:
      → Spec.parse (Frontend/SpecParser.lean) → Spec.Body
      → SpecTranslation (Verifier/SpecTranslation.lean) → SpecPredicate
      → Spec.complete → Spec
      → checkSpec (Verifier/Functions.lean) → VerifM Unit
        → compile (Verifier/Expressions.lean) → VerifM (Type_ × Term .value)
        → VerifM → ScopedM.translate → Strategy → run via Z3
```


## Style Guide

### Naming conventions

- **Definitions and types** use `camelCase`: `Term.eval`, `Formula.subst`, `ScopedM.translate`.
- **Theorem and lemma names** describe what they prove, namespaced under the relevant definition with dots:
  - Constructor/destructor lemmas: `eval_var`, `eval_val`, `eval_app` (one per constructor).
  - Structural properties: `_refl`, `_symm`, `_trans`, `_comm`, `_assoc`.
  - Relational properties: `_mono`, `_injective`, `_iff`.
  - Derivation direction: `_of_X` (from X), `X_of_` (to X).
- **Consistency:** Pick one word for a concept and use it everywhere:
  - `eval` — denotational/extensional semantics.
  - `translate` — compilation between intermediate representations.
  - `correct` — soundness theorems linking `translate` to `eval`.
- **Avoid** fused names like `eval_bind_decl_assume`; prefer composing `eval_bind`, `eval_decl`, `eval_assume`.

### File and module organization

- **One definition + its API per section.** Layout: definition → simp lemmas → structural properties → relational properties.
- Definitions and their core lemmas should live together — importing a definition should give you its basic API without a separate import.

### Simp lemmas

- Tag constructor-unfolding lemmas with `@[simp]`. If the same `simp [foo, bar, baz]` appears in multiple proofs, the individual lemmas likely need `@[simp]`.
- Do not tag lemmas that cause simp loops or are only useful in specific contexts.

### Proof style

- Short equational rewrites → term-mode or `simp`/`rfl`.
- Complex case splits, inductions, or rewrites → tactic mode.
- Avoid mixing styles within a single proof without reason.

### Avoiding duplication

- Before writing a new lemma, search for existing ones.
- Prefer general lemmas over specific instantiations.

### Mututal Inductives 

When an inductive in `Prop` references itself through `List.Forall₂` (or similar), it becomes a *nested* inductive. This causes two problems (e.g., `sizeOf` is always 0 for `Prop` terms, so well-founded recursion via `termination_by sizeOf` on proof terms is impossible and structural recursion fails). 

**Fix:** Use an explicit mutual inductive block. For example, instead of:

```lean
inductive Type_.Sub : Type_ → Type_ → Prop where
  | tuple : List.Forall₂ Type_.Sub ss ts → Type_.Sub (.tuple ss) (.tuple ts)
  ...
```

Define:

```lean
mutual
  inductive Type_.Sub : Type_ → Type_ → Prop where
    | tuple : Type_.SubList ss ts → Type_.Sub (Type_.tuple ss) (Type_.tuple ts)
    ...
  inductive Type_.SubList : List Type_ → List Type_ → Prop where
    | nil  : Type_.SubList [] []
    | cons : Type_.Sub s t → Type_.SubList ss ts → Type_.SubList (s :: ss) (t :: ts)
end
```

Theorems that recurse over these mutual inductives should themselves be mutual, matching the structure of the types.

---

## Development Guidelines

### Building and running
- Build with `lake build`.
- Run the verifier: `lake exe mica <file.ml>`
- After completing proof work, run `lean_diagnostic_messages` filtered to the specific declaration (`declaration_name` parameter).

### Completion discipline
- A proof is done only when diagnostics (filtered to the declaration) show no errors and no `sorry` exists anywhere in the dependency chain.
- If a proof attempt fails or is abandoned, **delete** the sorried helper lemmas immediately. Do not leave dead code.
- When completing sorries in an existing proof (or adjusting an existing proof), do not sorry out the proof structure.
- A considerable amount of work has gone into the existing proofs in the code base. When they require changing, especially large ones, **ABSOLUTELY AVOID** sorrying out the entire proof, since it means it will have to be proven from scratch again. Consider whether there is a less invasive change like locally sorrying out a case or an assumption initially. 

### Top-down vs bottom-up
- **Top-down (exploration):** Sketch a proof to discover what helpers are needed.
- **Bottom-up (theory building):** Develop properties of definitions in their own right before using them in larger proofs.
- **Key rule:** If a top-down attempt requires more than ~2 helper lemmas, **stop and consult the user**. This usually signals that more foundational theory about the involved definitions is needed, and the user should decide the direction.

### Tidiness
Group lemmas related to a particular definition together. When helper lemmas are added to a file for convenience (to avoid a recompilation cycle), mark them with a comment about where they should be moved later.

### Generality
- Prefer general lemmas over specific instantiations.
- Before induction, **generalize any argument that changes in recursive calls**. Otherwise, the inductive hypothesis is too weak.

### Search tools
- **`lean_local_search`** and **`lean_loogle`** — Use freely. `lean_local_search` covers the project and Lean stdlib; `lean_loogle` covers Mathlib (runs locally, no rate limit).
- **`lean_leansearch`** — Use rarely, requires confirmation from the user. Try to avoid it.
- **`lean_leanfinder`**, **`lean_state_search`**, **`lean_hammer_premise`** — Do not use.