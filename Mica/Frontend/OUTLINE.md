**Mica/Frontend**

- `AST.lean` — Surface syntax trees and source locations for the OCaml frontend.
- `Elaborate.lean` — Elaboration of surface syntax into the verifier's core language, with frontend-specific checks.
- `Lexer.lean` — Lexical analysis for the OCaml frontend, including tokens and lexer errors.
- `Parser.lean` — Parsing of frontend tokens into surface syntax trees, with integrated frontend errors.
- `Printer.lean` — Pretty-printing of frontend syntax back into OCaml-like concrete syntax.
- `SpecParser.lean` — Structural translation from elaborated TinyML terms into the specification language.
