# Folder cleanup

## The goal

Each file in the folder covers one subject. A reader who opens a file finds a
short statement of that subject, then the definitions, then the theorems,
divided into sections by concept. Names follow the conventions in `AGENTS.md`,
and proofs are no longer than their content needs. The behavior of the code
does not change unless the user agrees to a change.

The work is done together with the user. The user holds context that the code
does not show, and many of the best changes come from the user's questions
during review. Stop where this procedure says to stop.

## Step 1 — Survey

Change nothing in this step.

1. Acquire context as in step 1 of `docs/style-review.md`: read every file of
   the folder in full, then the parts of its neighbours that use it.
2. Write a plan in the conversation:
   - the subject of each file, in one line, and the files to split, merge,
     move, or rename so that each file has one subject;
   - the names that break the conventions;
   - the definitions to add, merge, or remove;
   - the proofs that are much longer than their content;
   - what you will leave alone, and why.
3. **Stop.** The user approves or changes the plan.

## Step 2 — Commits

Make one kind of change per commit, in this order. Skip a kind that has no
changes.

1. **Moves and splits.** Declarations change place, not content.
2. **Renames.** Update every use, also outside the folder.
3. **Content changes.** One idea per commit.
4. **Proof cleanup.**
5. **Formatting.**
6. **Documentation.** The module doc comments, the section structure, and the
   docstrings. This commit is last because the user edits it by hand. After the
   user has edited it, add new commits at the end of the series.

The shape of a file:

```lean
-- SUMMARY: <one line>
import ...

/-!
# <Subject>

<A short, high-level statement of what the file is about.>
-/

/-! ## <Concept> -/

<definitions, then theorems>
```

## Step 3 — Checks

For each commit:

- `lake build` passes.
- The test suite passes, unless the commit changes only proofs, comments, or
  formatting.
- If the commit changes a `SUMMARY` line or the set of files, it also contains
  the regenerated `OUTLINE.md` files (`lake run generate-overviews`).

## Step 4 — Review

1. List the commits and what you verified for each. Say what you left alone.
2. **Stop.** The user reviews the series commit by commit.
3. Put each fix into the commit that it belongs to, with a fixup commit and an
   autosquash rebase. Before you rewrite history, make sure that the working
   tree is clean — the user can have edits of their own in it — and make a
   backup tag.
