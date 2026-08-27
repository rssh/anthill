## Attributes

- id: WI-20260827-EJ5F5-a-bare-nullary-entity-name-in
- created: 2026-08-27T14:09:59Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T14:09:59Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BARE NULLARY-ENTITY NAME IN A `case` PATTERN SILENTLY BINDS AS A VARIABLE, so the arm matches EVERYTHING and every later arm is dead. No diagnostic, and the operation returns a WRONG value.

MEASURED 2026-08-27 on the tree at b09aa9f1 (found while building the WI-20260827-P1TPE fixture, where the parenless spelling made the case-split silently decline):

  sort C
    entity red
    entity green
    operation pick(c: C) -> Int64 =
      match c
        case red -> 1        -- BARE: binds a fresh variable named `red`
        case green -> 2
    operation pickp(c: C) -> Int64 =
      match c
        case red() -> 1      -- PARENS: matches the constructor
        case green() -> 2
  end

  rule bare_green_is_1()  :- C.pick(green())  = 1   -> TRUE     <- WRONG
  rule bare_green_is_2()  :- C.pick(green())  = 2   -> no solutions
  rule paren_green_is_2() :- C.pickp(green()) = 2   -> TRUE     the control
  rule paren_green_is_1() :- C.pickp(green()) = 1   -> no solutions

`pick(green())` answers 1. The `red` arm is a catch-all and the `green` arm is unreachable.

THE MECHANISM IS THE GRAMMAR, not a resolution bug: `pattern_var: $ => $.identifier` (tree-sitter-anthill/grammar.js), and `pattern_constructor` requires the parentheses. So a bare identifier in a pattern is ALWAYS a binder, whether or not it names an entity in scope. The kernel's own variable spelling is `?name` everywhere else, which is what makes this read as a constructor to anyone writing it.

IT ALSO SILENTLY CHANGES RESOLUTION, not only evaluation: `folded_call_match` (kb/body_specialize.rs) case-splits only over DISJOINT constructor arms, so a bare-name arm makes the whole WI-580 unfold DECLINE. A relational query over such an operation suspends where the parenthesized spelling decides — a second, quieter symptom of the same cause.

THE CORPUS IS CLEAN, WHICH IS WHY NOTHING HAS FOUND IT. Census over every .anthill in stdlib/, examples/ and rustland/: exactly TWO bare-name case patterns, both `case other -> mirror_refusal(...)` in rustland/anthill-todo/anthill/main.anthill, and `other` names no entity — they are intentional catch-alls and must keep working.

DIRECTIONS, none chosen. (a) RESOLVE a bare pattern name that names a nullary entity constructor IN SCOPE to a constructor pattern (the two `other` sites are unaffected — no entity by that name), which makes the two spellings mean the same thing; (b) REFUSE it at load ("`red` names an entity of sort C; write `red()` to match it, or rename the binder"), which keeps binders explicit and costs nothing today; (c) leave it and document the trap in kernel-language.md. (b) is the smallest and the loudest; (a) is what a reader expects but silently changes the meaning of a legal program.

ACCEPTANCE: the four rows above driven as a test, with `bare_green_is_2` TRUE (direction a) or the program refused at load with a located error naming `red` (direction b); the two `case other ->` catch-alls in anthill-todo/anthill/main.anthill still load and still work (asserted, not assumed); the WI-580 unfold's decline on the bare spelling either goes away (a) or becomes unreachable (b); kernel-language.md states which of `case red` / `case red()` means what; full workspace green via rustland/scripts/test.sh.

REFERENCE: tree-sitter-anthill/grammar.js (`pattern_var` / `pattern_constructor`), `KnowledgeBase::fresh_pattern_occ` and `folded_call_match`'s disjoint-arm gate (rustland/anthill-core/src/kb/resolve.rs, kb/body_specialize.rs).

