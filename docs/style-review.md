# Style review

## The goal

A code base that is easier to maintain, simpler, and clearer to a human reader.

The rules in this document are concretizations of that goal. They are not the
goal. Where a rule and the goal disagree, the goal wins — and you say so in the
finding, rather than quoting the rule at code that is fine as it stands.

This procedure reviews **files**, not diffs. The defects that cost the most are
usually older than whatever change is in front of you.

## Step 1 — Acquire context

Do this before you form any opinion about the code.

1. **Read every target file in full**, first line to last. Not the outline, not
   the declarations that look relevant, not a grep of the interesting parts. The
   whole file, into your context.
2. **Read the neighbourhood.** The definitions the target uses; the callers of
   what the target defines; the sibling files of the same layer. Read the parts
   of those files that touch the target — you do not need them whole. What a
   definition costs is usually paid by its callers, so this is where you find out
   what its shape is worth.
3. In two or three sentences, write down what the target is for and how its
   pieces fit together. If you cannot write those sentences, you have not read
   enough yet.

**Form no conclusions during this step.** An opinion settled while reading is an
opinion settled without the context the rest of the file supplies, and that is
the failure this step exists to prevent.

## Step 2 — The rules

### 1. Duplication and factoring

Inlining definitions or proofs is poor style. It hurts maintainability, because
a change in the future has to be made in several places at once, and a reader
has to recognize that two passages are the same idea.

Not every piece of duplication is wrong. Inlining a three-line proof script twice
can be the right call when there is no good, abstract concept to name. Factoring
out a single line can be the right call when it is a meaningful definition or
when useful lemmas can be proven about it. Finding the balance needs judgment.

A duplicated *decision* is harder to see than duplicated code: a `Bool`
predicate beside the `match` it has to mirror (boolean blindness), or two
definitions taking the same input apart the same way. Have the branch return
what it selects — `Option α`, a variant — so the data comes with the decision
and there is nothing to keep in sync. That is "parse, don't validate".

Suggest candidates for factoring out, and candidates for inlining. Optimize for
clarity, readability, and maintainability with a human reader in mind.

### 2. Comments

Comments are only useful if they carry non-obvious information that may itself be
useful in the future. A comment that restates the name, the signature, or the
list of cases underneath it carries nothing, and it will go stale: the code moves
and the prose stays. Then it is worse than nothing, because a reader has to work
out which of the two is lying.

What is worth writing down: an invariant the types do not carry, why a choice is
sound, why the obvious alternative was not taken, a precondition the callers
happen to satisfy.

Judgment: the test is not length or density, it is whether a maintainer a year
from now learns something. Match the surrounding file — a file that comments no
constructor should not gain one commented constructor.

### 3. Special cases

A definition whose cases are treated alike is easier to reason about than one
with an exception in it. An exception is sometimes genuinely necessary. More
often it is a caller's requirement that leaked into the definition — a flag, an
`Option`, a default argument that only one call site uses meaningfully.

Judgment: ask what the special case is buying. If the answer is "one caller",
the fix is usually at that caller, or a second definition. If a case really does
need different treatment, that reason is worth a comment (see rule 2).

### 4. Names

One concept, one word, everywhere: in the definition, in its lemmas, at the call
sites. A second spelling for the same idea (`scrut` beside `scrutinee`, `Len`
beside `LengthOf`) makes the reader stop to check whether they are the same
thing.

The same applies to binders. Reuse the name the code already uses for that
concept; a second variable of the same concept is primed or given a role suffix,
not spelled differently.

A definition should have a one-line meaning that does not mention its
implementation. If you cannot write that line, the definition is probably not a
concept, and its name will not help anyone.

Theorem names follow the suffix scheme in `AGENTS.md`.

### 5. Abstraction boundaries

Importing a definition should give you its API. A proof that case-splits on the
constructors of a type declared elsewhere is reaching past that API — either the
lemma it needs exists and should be called, or it does not exist and belongs next
to the definition, where the next caller will find it.

Judgment: one case split at the wrong level is a small cost. The same split
appearing in three proofs is a missing lemma, and the cost grows with every
future change to that type.

`private` is the default, and a public name is part of that API: ask of each one
which file outside this one uses it, and search for the answer (rule 7's
discipline) rather than assuming one.

### 6. Partiality

Code that does not handle a case should say so where a reader meets it, not fail
quietly. A silent default, a catch-all that discards information, a `TODO` that
does not say what breaks — each of these turns a known limitation into a surprise
later.

Where the function can fail, it should fail with a message naming what is not
supported. Where it must return a value for every input — a denotation, an
evaluator — the convention belongs in the docstring, stated once for the family.

### 7. Dead code

A declaration nothing calls still costs: it is read, maintained, and kept
compiling. Before you call something dead, search for it twice with different
patterns, and check `Tests/`, `Testsuite/`, `Examples/` and `Main.lean` as well
as `Mica/`. A too-specific pattern reports zero callers for code that has them.

Search for what consumes a thing, not for what mentions it. Something that is
built in ten places and taken apart in none is dead in the way that matters, and
no search for its name will tell you that.

Judgment: a lemma that exists to complete a family, or an API that is obviously
the counterpart of one in use, is not dead in the sense that matters. Say which
kind you found.

## Step 3 — Weigh each finding

Before a finding goes in the report:

- Would a maintainer of this code thank you for it? If the honest answer is that
  it is a matter of taste, drop it or mark it as such.
- Does the fix trade one defect for another — less duplication for a worse name,
  more uniformity for more inlining? If so, say what the trade is and let the
  reader decide.
- Can you support it from code you actually read? If it rests on a file you only
  grepped, go read that file or drop the finding. This includes anything you
  propose calling: check that the library lemma exists before you suggest it.
- What does the defect cost *here*? Duplication in a proved definition is paid
  again at every proof about it; the same duplication in an `IO` shim costs a
  typo. Much of this project is mechanized proof, and the two halves do not weigh
  the same.

The reader knows this code better than you do. Suggest, with the trade-off
visible; do not instruct.

## Step 4 — Report

- Order findings by what they cost, not by file position. The reader should meet
  the most valuable one first.
- For each: where it is, what the problem is, what it costs, and what you suggest
  instead. Show the evidence you actually used, and nothing else.
- Group the small, repetitive ones together instead of numbering each. Cheap to
  fix is not the same as not worth reporting — a small defect that is really a
  defect belongs in the report, at the end.
- Say which findings are one piece of work, so the report reads as something a
  person can act on in order.
- Open the report with the two or three sentences from step 1, and the list of
  what you read.
- Close with what you considered and chose not to flag, in one line each.

## Out of scope

Defects in what the code computes, proof repair, and formatting. Use
`/code-review` for correctness.
