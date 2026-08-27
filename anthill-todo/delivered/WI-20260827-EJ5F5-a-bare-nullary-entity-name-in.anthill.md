## Attributes

- id: WI-20260827-EJ5F5-a-bare-nullary-entity-name-in
- created: 2026-08-27T14:09:59Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T21:17:51Z

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

## Changes

### 2026-08-27T21:17:40Z — feedback — user

DELIVERED direction (a) — which the SPEC HAD ALREADY CHOSEN. kernel-language.md §8.6 already said a case name resolves type-directedly against the scrutinee's own constructors, and the typer already implemented that resolution (`pattern_var_ctor_sym`); only the EXHAUSTIVENESS check and the arm's Gamma fact ever asked it. Everything that RUNS read the stored Pattern, where the loader had left a fresh binder symbol. The three directions the ticket listed were written without reading that paragraph.

THE FIX. `bind_and_label_pattern` (kb/typing.rs) rewrites a resolved bare match-arm name into `Pattern::Constructor{name, [], []}`, inside the typer's tree-producing path, so the rewritten arm reaches the stored body through MatchFinal + set_op_body_node and every reader sees ONE answer. New `PatternRole` (MatchArm / Binder) — lambda and let pass Binder, and that they never rewrite is now a debug_assert, not a comment.

BEYOND THE HEADLINE, all measured:
 * DEPTH — a nested `case some(red)` was the SAME defect one level down (`nest(some(green()))` answered 1). Each position asks its OWN threaded type.
 * ARITY — `case suc` names a constructor that takes a field, so it stays a binder; rewriting it would build a 0-arg pattern `match_constructor_pattern` refuses arity-strictly, turning a working catch-all into a DEAD arm.
 * THE ARM'S OWN TEXT — the loader captures an arm's binder names into a local frame before any type exists, so removing the binder ORPHANED the body's reference: `case red -> red` stopped loading while `case red() -> red` kept working. `repoint_arm_binders` re-points the body and the guard, and the guard is threaded to `reassemble_match` so what is STORED is what was CHECKED.
 * cpp-gen was the third reader and had the defect BACKWARDS — its `Pattern::Var` arm emitted `std::holds_alternative<other>(c)` for every bare name, naming a C++ type that does not exist. Now a catch-all binding; `nullary_tag_check` deleted with its only caller.

/code-review (high) FOUND FOUR MORE, all fixed with driven rows:
 * the `: T` opt-out was honoured by ONE of the three readers, so `case (red: C)` was a catch-all at run time while coverage recorded `red` covered and Gamma carried a FALSE ground `eq(c, Ref(red))`. The gate moved into the shared `var_pattern_ctor`.
 * Gamma and coverage read the WRITTEN pattern while the matcher read the rewritten one: `case some(red)` stored `some(red())` yet emitted `some(var_ref(red))` at a binder that no longer existed, and gave later arms no `neq`. The branch loop is now TWO PASSES and both read the rewritten pattern — which also means nothing re-derives the nested candidate set.
 * `is_nullary_constructor` read a non-entity as nullary. Split into `takes_no_fields` (shared, permissive) and `declares_a_nullary_entity` (rewrite only) — the split was FORCED by the suite: the strict spelling in the shared predicate fails `wi537_local_interpretation_test::match_nullary_ctor_arms_accumulate_negations`, whose hand-built KB interns constructor names instead of declaring them.
 * nested sub-patterns reached a refusal worded 'let/lambda binder' about a match; `match_subpattern_name` now names the match.
 * finding 6 (cpp-gen depends on a typed body) has no predicate that could check it, so it is a stated caller contract at the site rather than an unreachable branch.

TESTS. `wi_ej5f5_bare_ctor_pattern_test` (9) and `wi_ej5f5_binder_arm_test` (3, cpp-gen). Six back-outs were RUN and the module doc carries the table of which rows each turns red; two take the whole file down because the fixture stops LOADING, and that is what they measure. ONE THING NOTHING COVERS, said at its site: feeding Gamma the written patterns again leaves every row green — the arm's FlowEnv is built and consumed inside one build_type frame and no test can read it; the reachable consumer is `guarded_atom_refuted`'s effect drop.

SPEC. kernel-language.md §8.6 now says the typer REWRITES, and adds nullary-only, at-every-depth, the `: T` opt-out reaching every reader, match-arm-only, and the arm's-own-text rule.

MEASURED: full workspace 36 binaries / 5901 passed / 0 failed; scaland sbt [success] 542 passed. No scaland change was needed — it has parse/load/kb/resolve/codegen but no typer or evaluator, so type-directed pattern resolution does not exist there.

