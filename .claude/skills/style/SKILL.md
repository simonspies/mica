---
name: style
description: Review named Lean files for maintainability, simplicity, and clarity - duplication that wants factoring, comments that carry nothing, special cases, drifting names, missing lemmas, undocumented partiality, and dead code. Use when the user asks to clean up, review, or improve the style of specific files or a directory. Reports suggestions with trade-offs; it does not change the code.
---

Read `docs/style-review.md` and obey the procedure in it.

The target is the file or the directory the user names. If the user names none,
ask which files to review — the procedure needs a bounded set it can read in
full.

Report as markdown, in the shape step 4 describes. Do not use `ReportFindings`:
these are suggestions that carry trade-offs, not defects to be listed.
