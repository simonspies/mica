# Iris Proof Mode Tactics (Lean)

Reference for the Iris proof mode tactics available in the `iris-lean` library.
See also `.lake/packages/iris/tactics.md` for the upstream reference.

## Entering Proof Mode

**`istart`** — enter Iris proof mode. Required before using any `i`-tactic. The goal must be an entailment `P ⊢ Q`.

## Introduction

**`iintro` *pats*** — the workhorse. Introduces hypotheses from wands (`-*`),
implications (`→`), and universal quantifiers (`∀`) at the head of the goal.
Multiple patterns can be given in sequence.

Patterns:

| Pattern | Meaning |
|---------|---------|
| `H` | Introduce into the spatial context as `H` |
| `□H` | Introduce into the intuitionistic context as `H` (proposition must be persistent) |
| `%x` | Introduce a universally quantified variable `x` into Lean's context |
| `%h` | Introduce a pure hypothesis `⌜φ⌝` as Lean hypothesis `h` (requires affine BI) |
| `-` | Drop / discard the hypothesis |
| `⟨H1, H2⟩` | Destruct a conjunction or separating conjunction |
| `(H1 \| H2)` | Destruct a disjunction (creates separate goals) |
| `!>` | Introduce the modality at the top of the goal |

**Nested destructuring** — patterns compose arbitrarily:

```
-- Given: P1 ∗ (□ P2 ∨ P3) ∗ ⌜φ⌝
iintro ⟨H1, □H2 | H3, ⌜hφ⌝⟩
```

**Multiple introductions** — space-separated patterns introduce in sequence:

```
-- Given: ⊢ P -∗ Q -∗ R
iintro HP HQ
```

**Combining quantifier and hypothesis introduction:**

```
-- Given: ⊢ ∀ x, P x -∗ Q
iintro %x HP
```

## Destructuring Without Introduction

**`icases` *pmTerm* `with` *pat*** — destruct an existing hypothesis.

```
-- HP : P1 ∗ P2 in context
icases HP with ⟨H1, H2⟩

-- HOR : P ∨ Q in context
icases HOR with (HP | HQ)   -- creates two goals
```

**`imod` *pmTerm* `with` *pat*** — eliminate a modality from a hypothesis and
destruct the result.

## Closing Goals

| Tactic | Description |
|--------|-------------|
| `iexact H` | Solve the goal with hypothesis `H` |
| `iassumption` | Solve the goal with any matching hypothesis (pure, intuitionistic, or spatial) |
| `iemp_intro` | Solve a goal of `emp`, discarding all hypotheses (context must be affine) |
| `ipure_intro` | Turn a `⌜φ⌝` goal into a standard Lean goal `φ` |
| `iex_falso` | Change the goal to `False` |

## Separating Conjunction

| Tactic | Description |
|--------|-------------|
| `isplitr` | Split `P ∗ Q` goal; entire spatial context goes to the **right** subgoal |
| `isplitl` | Split `P ∗ Q` goal; entire spatial context goes to the **left** subgoal |
| `isplitl [H1, H2]` | Split `P ∗ Q`; `H1, H2` go left, rest goes right |
| `isplitr [H1, H2]` | Split `P ∗ Q`; `H1, H2` go right, rest goes left |

**Key insight:** `isplitr`/`isplitl` decide where the *entire* spatial context
goes by default. The bracket variants give fine-grained control. You typically
use `isplitr` when the left goal is "easy" (pure, or you have a specific
hypothesis for it) and the right goal needs the bulk of the context.

## Conjunction and Disjunction

| Tactic | Description |
|--------|-------------|
| `isplit` | Split `P ∧ Q` into two goals (both get the full context) |
| `ileft` | Choose the left side of `P ∨ Q` |
| `iright` | Choose the right side of `P ∨ Q` |

## Existential Quantifiers

**`iexists` *t*** — provide a witness for `∃ x, P x` in the goal.
Multiple witnesses can be given in sequence: `iexists a, b, c`.

## Application

**`iapply` *pmTerm*** — match the conclusion of the goal against the conclusion
of the hypothesis/term, generating subgoals for each premise. Unused spatial
hypotheses flow to the last premise.

```
-- Hf : P -∗ Q -∗ R  in context, goal: R
iapply Hf    -- two subgoals: P and Q
```

Also works with Lean terms whose conclusion is an entailment:

```
iapply (some_lemma arg1 arg2)
```

## Specialization

**`ispecialize` *H* `$$` *spec1 ... specN*** — specialize a hypothesis by providing
arguments and/or proving premises.

```
ispecialize Hall $$ %42          -- instantiate ∀ with 42
ispecialize Hwand $$ HP          -- feed hypothesis HP to a wand
ispecialize Hf $$ HP1 %y HP2    -- mixed: spatial, pure, spatial
ispecialize Hf $$ [HP1 HP2]     -- subgoal with HP1, HP2 in context
```

Specialization patterns:

| Pattern | Meaning |
|---------|---------|
| `H` | Use hypothesis `H` to prove this premise |
| `%t` | Use pure Lean term `t` (for `∀` binders, or `%rfl`, `%.intro`, `%(by tac)`) |
| `[H1 H2]` | Generate a subgoal with hypotheses `H1, H2` in the spatial context |
| `[H1 H2] as G` | Same, but name the subgoal `G` |

## Hypothesis Management

| Tactic | Description |
|--------|-------------|
| `irename H1 into H2` | Rename hypothesis |
| `iclear H` | Discard hypothesis (must be affine, or goal must be absorbing) |
| `iclear #` | Clear all intuitionistic hypotheses |
| `iclear ∗` | Clear all spatial hypotheses |
| `iclear %x` | Clear Lean variable `x` |
| `iclear %` | Clear all Lean pure hypotheses |
| `ipure H` | Move hypothesis `H` to the pure (Lean) context |
| `iintuitionistic H` | Move `H` to the intuitionistic context |
| `ispatial H` | Move `H` to the spatial context |
| `irevert H` | Move `H` out of the context, turning it into a wand premise in the goal |

## Assertion

**`ihave` *pat* `:=` *pmTerm*** — copy a hypothesis into the context under a new
name/pattern (does not remove the original, unlike `icases`).

**`ihave` *pat* `:` *term* `$$` *specPat*** — assert a new hypothesis and prove it.

## Modalities

| Tactic | Description |
|--------|-------------|
| `imodintro` | Introduce the modality at the top of the goal |
| `inext` | Introduce a later modality `▷` |

## Proof Mode Terms

Some tactics (`iapply`, `icases`, `imod`, `ihave`) accept *proof mode terms*
that can include inline specialization:

```
iapply (Hwand $$ Hprem)     -- apply Hwand after feeding it Hprem
icases (Hf $$ %42) with pat -- specialize then destruct
```

The general form is `(H $$ spec1 ... specN)` where `H` is a hypothesis or
Lean term, and the specs are as described under Specialization above.

## Common Patterns in Mica Proofs

### Pure reasoning inside separation logic

```
istart
iintro ⟨%hpure, Hspatial⟩   -- destruct ⌜φ⌝ ∗ P
-- hpure : φ  is now a Lean hypothesis
-- Hspatial : P  is in the spatial context
```

### Existential witness + separating conjunction

```
-- Goal: ∃ x, ⌜φ x⌝ ∗ P x
iexists v
isplitr
· ipure_intro; exact hv
· iexact HP
```

### Chaining entailments in term mode (outside proof mode)

For simple entailment composition, Lean term mode often works better than
entering proof mode:

```
exact h.trans (sep_mono ha.1 hctx.1)
```

Key combinators: `BIBase.Entails.trans`, `sep_mono`, `sep_mono_l`, `sep_mono_r`,
`sep_assoc`, `sep_comm`.
