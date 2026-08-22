## Attributes

- id: WI-20260822-KY4SB-block-comment-delimiter
- created: 2026-08-22T09:47:51Z

- status: PreOpened
- status_agent: user
- status_at: 2026-08-22T09:48:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

BLOCK COMMENT DELIMITER `{- -}` COLLIDES WITH THE EFFECT-ROW LACKS CONSTRAINT `{-Label}`, and the failure is silent and misdirected. Proposal 045 sanctions `-E` as a row element (absence / lacks-constraint), so a row whose FIRST element is one is spelled `effects {-Model}` -- which lexes as a BLOCK COMMENT OPENER and swallows the rest of the file.

MEASURED, while building examples/guardians:

  operation choose(r: String) -> String
    effects {-Model}          -- silently a comment; rest of file eaten

  error: <file>:1:1: syntax error near `sort guardians.Model end namespace guard...`

The diagnostic points at LINE 1 and quotes text from the top of the file, so it reads as unrelated to what was typed. `effects { -Model }` (with a space) works, and `effects {Error, -Model}` works -- only the FIRST-element case collides. Confirmed by three loads: `{Model}` ok, `{Error, -Model}` ok, `{-Model}` eats the file.

MIGRATION COST IS ~ZERO, WHICH IS THE ARGUMENT. `{-` occurs in exactly TWO .anthill files repo-wide, and BOTH are comments WARNING ABOUT THIS COLLISION (examples/guardians/vocabulary.anthill:104, generation.anthill:63). No block comment is used anywhere in stdlib/, examples/, or anthill-todo. One tree-sitter corpus file uses it. The current spelling costs a real feature's natural surface and buys nothing anyone writes.

`{< >}` IS NOT AVAILABLE -- it is the DESCRIPTION BLOCK (kernel-language.md 4.1), which is STRUCTURAL: preserved as `anthill.reflect.DescriptionInfo(target, content, index)` facts, not discarded. Any replacement must leave it untouched, and the two must stay visually distinguishable, since 4.1's own table contrasts them on exactly that axis.

CANDIDATES, the collision question being 'can this open-token begin a legal construct':
  {* *}   RECOMMENDED. Needs a prefix `*`; anthill has none. Keeps the `{DELIM ... DELIM}` family anthill already has, so `{< >}` structural / `{* *}` discarded reads as ONE system rather than two conventions.
  {-- --} Smallest possible diff (opener 2 chars -> 3), familial with the `--` line comment, frees `{-X}` outright.
  (* *)   SML / OCaml / Coq / Isabelle precedent, and this repo has isabelleland/. Needs a prefix `*`; none. Reads oddly beside `--`.
  /* */   Zero collision; matches all four codegen backends, and `--` line + `/* */` block is exactly SQL's pairing. Leaves anthill's own bracket family.

SETTLE THE NESTING QUESTION IN THE SAME CHANGE. kernel-language.md 2.2 states 'Comments nest: {- outer {- inner -} still outer -}', but grammar.js's rule is a FLAT scan terminating at the FIRST `-}`. If that reading is right, the spec documents a behaviour the grammar does not implement, and the replacement should either implement nesting or the sentence should go. NOT VERIFIED BY RUNNING -- the machine was saturated when this was written, so it is read off the grammar and must be confirmed before acting on it.

ACCEPTANCE: `effects {-Model}` (no space) loads and means a lacks-constraint. `{< >}` description blocks unaffected -- DescriptionInfo facts still emitted, 4.1's examples still parse. The new delimiter round-trips through the tree-sitter corpus. 2.2 and the grammar agree on nesting, whichever way it is settled. The two warning comments in examples/guardians become deletable, and 4.1's syntax table is updated.

