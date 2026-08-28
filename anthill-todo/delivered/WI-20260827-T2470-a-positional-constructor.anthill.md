## Attributes

- id: WI-20260827-T2470-a-positional-constructor
- created: 2026-08-27T14:09:45Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T04:15:20Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A POSITIONAL CONSTRUCTOR ARGUMENT IN AN OPERATION BODY BUILDS A VALUE THAT COMPARES UNEQUAL to the same constructor written anywhere else, so the operation silently answers NOTHING. Equality-independent, pre-existing, and it reaches the prelude: every `some(x)` in the stdlib is this shape.

MEASURED 2026-08-27 on the tree at b09aa9f1, isolated to ONE axis -- POSITIONAL vs NAMED constructor arguments inside an OPERATION BODY. The two rows differ in nothing else:

  enum test.pu3.MyEnum
    sort T = ?
    entity enone
    entity esome(value: T)
  end
  namespace test.pu3
    import anthill.prelude.{Int64, Option}
    import anthill.prelude.Option.{some}
    import test.pu3.MyEnum.{esome}
    sort C
      entity red
      operation ewrap (x: Int64) -> MyEnum[T = Int64] = esome(value: x)   -- NAMED
      operation ewrap2(x: Int64) -> MyEnum[T = Int64] = esome(x)          -- POSITIONAL
      operation owrapn(x: Int64) -> Option[T = Int64] = some(value: x)    -- NAMED
      operation olit  ()         -> Option[T = Int64] = some(1)           -- POSITIONAL
    end
    rule g1() :- C.ewrap(1)  = esome(value: 1)   -> true            NAMED body
    rule g2() :- C.ewrap2(1) = esome(value: 1)   -> no solutions    POSITIONAL body
    rule g4() :- C.owrapn(1) = some(value: 1)    -> true            NAMED body
    rule g5() :- C.olit()    = some(1)           -> no solutions    POSITIONAL body
    rule g6() :- some(1)     = some(1)           -> true            the CONTROL: positional
                                                                    on BOTH sides of a RULE
                                                                    body is fine
  end

`g6` is the control that puts the defect in the OPERATION BODY and not in the positional spelling: written in a rule body, `some(1)` is equal to itself. Only a value BUILT BY AN OPERATION BODY from positional arguments mismatches.

IT IS NOT ABOUT `Option`, NOT ABOUT `enum`, AND NOT ABOUT EQUALITY. Driven across four carriers, with `Int64` payloads and no `eq` override anywhere:
  `sort BoxI  entity boxi(v: Int64)`  named body   -> true
  `sort MyOptP[T] entity psome(value: T)` POSITIONAL body -> no solutions
  `enum MyEnum` (above)               both        -> named true, positional false
  `List` `cons(head: x, tail: nil)`   named body  -> true
So it is every entity constructor with at least one field, whatever the sort's kind or arity.

THE FAILURE IS A REFUTATION, NOT A SUSPENSION, so NAF over it concludes: a caller can prove `not(C.olit() = some(1))`.

ONE PLACE TO LOOK, stated as a hypothesis and NOT as a diagnosis -- I did not trace it. `unify_concrete` (rustland/anthill-core/src/kb/resolve.rs) fails fast on `pa != pb || na != nb`, i.e. a positional/named arity mismatch, before comparing anything. The PATTERN side of the same question already canonicalizes: `fresh_pattern_occ` (same file) says "Build a CANONICAL entity occurrence: positional sub-patterns map to the constructor's declaration field names, all args carried named + sorted (the system's canonical entity form)". The op-body constructor lowering appears not to do that mapping, so the built value stays `Fn{some, pos:[1], named:[]}` where every other producer has `Fn{some, pos:[], named:[value: 1]}`. Verify before fixing.

HOW IT WAS FOUND: while delivering WI-20260827-P1TPE. /code-review reported `C.gopt(?c, ae(k:1,tag:8)) = some(ae(k:1,tag:9))` answering 0 as a gap in that ticket's key; the `Int64` twin answers 0 too, and so does its GROUND twin, which took equality and the WI-580 unfold out of the picture entirely.

WHY NOTHING HAS FOUND IT: the workspace is green because the operation bodies that matter use NAMED arguments. The stdlib's own `Option.optionPure[A](a: A) -> Option[T = A] = some(a)` and `optionMap`'s `some(f(x))` are BOTH the broken spelling -- so `Monad[Option]`'s `pure` builds a value nothing can match. Whether any live path exercises it is the first thing this ticket should census.

ACCEPTANCE: the five rows above driven as a test, with `g2` and `g5` TRUE and `g6` still TRUE as the control; a census of positional constructor applications in operation bodies across stdlib/, examples/ and rustland/ with the count stated (the stdlib's `optionPure` / `optionMap` named explicitly, and whether either is reachable today); the NAF polarity asserted (`not(C.olit() = some(1))` must stop answering 1); the fix stated at the lowering site that owns the canonical entity form, beside `fresh_pattern_occ`'s note that the PATTERN side already does it; full workspace green via rustland/scripts/test.sh.

REFERENCE: `fresh_pattern_occ` and `unify_concrete` (rustland/anthill-core/src/kb/resolve.rs), `anf_flatten`'s `Expr::Constructor` arm, stdlib/anthill/prelude/option.anthill.

## Changes

### 2026-08-28T04:15:04Z — feedback — claude

DELIVERED at 74a06ec3. A constructor APPLICATION's positional arguments are now desugared to named where the value is BUILT, so an operation body's `some(x)` produces the same canonical entity every other producer does.

THE HYPOTHESIS IN THE TICKET WAS RIGHT AND WAS TRACED BEFORE FIXING. `unify_concrete`'s `pa != pb || na != nb` fail-fast is one of FOUR consumers keying on the literal shape — the others are `sem_eq_values`/`views_structurally_equal`, the discrimination tree's `DiscrimKey`, and hash-consing — so `Entity{some, pos:[x], named:[]}` met the `Entity{some, pos:[], named:[value: x]}` every other producer builds and all four read them as different values.

TWO SITES, NOT ONE, and the ticket named only the first. `finish_constructor` (eval/eval.rs) reaches every GROUND call. `anf_flatten`'s `Expr::Constructor` arm (kb/resolve.rs) reaches the arm-body residual the WI-580 unfold builds when the scrutinee is UNGROUND — that one rides as a `Value::Node` into a `unify` goal and is never reified, so the `Value -> Term` lowering never sees it. Backed out separately: `gm` is the ONLY row the `anf_flatten` half moves, and the only one it moves alone; every other row moves with `finish_constructor` alone. Four measured states are tabled in the test module doc.

NORMALIZE AT THE WRITER, NOT THE READER — the design choice, stated because the alternative is tempting. The four consumers above are independent, so teaching each that `f(1)` and `f(x: 1)` denote one value is four places to drift. Both new sites route through the shared owner `positional_to_named_plan`, which `alloc_from_value` and `value_to_term` already use, so the rank-among-NOT-named rule is stated ONCE: `two(2, a: 1)` puts 2 in `b`, which `gmix` drives (a repair that filled the LEADING fields keeps every single-field row green and that one red). The obligation is exactly on functors that HAVE a declared field schema and are not reflect FORM meta-ctors; the plan Skips everything else, which is what keeps `TupleLiteral` / `ListLiteral` / `SetLiteral` positional, since a tuple's order IS its identity. `a_tuple_and_a_list_literal_keep_their_positional_shape` is that control, and it says at its site that it passes both ways — it is a GUARD, not a measurement, written because the fix sits three lines above the arm that builds `Value::Tuple`.

THE CENSUS THE TICKET ASKED FOR, over each corpus' loaded `op_bodies_iter` and excluding what the plan would Skip: 49 in stdlib/anthill; 202 with the rustland CLIs (anthill-cli, anthill-todo, anthill-cpp-gen); +4 in examples/webots-modelling; +0 in the rest (github-todo, guardians, sql-store, classic-mini, anthill-testcases). `Option.optionPure` (`= some(a)`) and `optionMap` (`some(f(x))`) are BOTH the broken spelling and both back `provides Monad[M = Option, pure = optionPure, ..., map = optionMap]`, so `Monad[Option]`'s `pure` built a value nothing could match. BOTH ARE REACHABLE TODAY, which `gopp`/`gopm` prove by calling them and comparing the result: each answered (0,0) before and (1,1) after. The ticket asked whether any live path exercises them — this is that answer, and it is yes.

THE NAF POLARITY IS ASSERTED. `g5naf` — `not(C.olit() = some(1))` — was (1,1), a DEFINITE proof of a falsehood whose equation `g5` proves has a witness. Now (0,0), and that test goes red on a back-out.

WHY THE WORKSPACE WAS GREEN, which takes BOTH halves: the operation bodies exercised by tests mostly use NAMED arguments; and where they do not, the carrier often declares its own `eq`, which MASKS the divergence completely — `sem_eq_values` dispatches to the declared equality instead of comparing structurally, and a declared `eq` reads fields BY NAME through `project_field`, which handles both spellings. `Pair` is exactly that shape and `gpair` is (1,1) in all four states; `Option` is not, and `g5` is the defect. `a_carrier_with_a_declared_eq_masked_it` pins it.

THE READER POPULATION IS THE OTHER HALF OF A SPELLING CHANGE, and it cost two suites. `cli_parse_test` (the parse_ok / ParsedArgs / Binding payloads) and `wi733_relation_head_eval_test`'s `some_string` destructured `Value::Entity { pos, .. }` and both went red. The repair is NOT "read `named` instead", which is the same fault with the other branch taken: one entity reaches a reader on any of three carriers (`Value::Entity`, a hash-consed `Value::Term`, a `Value::Node`) and a leaf String on the same three, so an enum match lets the RECEIVER'S CARRIER decide whether its own field is reachable — the bug `project_field` exists to prevent, re-created once per suite. Both now go through new shared `tests/common` helpers — `entity_functor`, `entity_field`, `scalar_str` — which read via `TermView`, ask NAME first and positional rank second, and live in ONE place. MEASURED: with this change backed out both suites stay GREEN, which is the property that says they no longer depend on which spelling the producer chose.

A NEIGHBOUR THIS DOES NOT MAKE DEAD, and an earlier measurement of it that was WRONG. `project_field`'s POSITIONAL branch justified itself by "`finish_constructor` does not desugar", which this change makes false — but the branch stays LIVE and is not narrowed: a `Value::Entity` is still built directly in Rust by a host builtin or a bridge. Neutralized and run against the whole anthill-core suite, EXACTLY ONE test reddens, `field_access_projects_a_value_carried_entity_receiver`, which hand-builds `Point(7)` — so the branch has one witness and that witness is a unit test rather than a program. An earlier draft claimed the two wi733 rows redden with the branch off; they do not — that reading was taken with this ticket's own fix live and its reader repair not yet made, so it was measuring THIS change's regression and crediting the branch. Both comments now say what actually holds instead of naming a producer that no longer produces it.

DOC: docs/design/entity-term-mapping.md grows Rule 6 (build: source -> Value/occurrence) and corrects the sentence that hid this. Non-empty `pos_args` was said to mean "a pre-canonical / runtime-built value BEFORE LOWERING", which reads as though a positional entity is always on its way to Rule 1 and will be canonicalized there. An EVALUATED entity is not: it is compared, unified and indexed as it stands.

OVER-ARITY IS LOUD AT BOTH SITES and unreached by any source program, because the loader refuses the shape at load time. `finish_constructor` raises a new `EvalError::OverArityConstructor` naming the constructor (`ArityMismatch`'s `op` is a `&'static str` and cannot); `anf_flatten` has no error channel, so it `debug_assert!`s and residualizes — a bare `None` there is indistinguishable from "a body form I do not handle yet" and would take the whole case-split to a silent suspension while its ground twin errors by name. NO TEST DRIVES EITHER ARM, said at both sites rather than left to be rediscovered: reaching them means a broken invariant.

THREE THINGS DELIBERATELY NOT FIXED, each FILED and each PINNED by a test here so the next owner has a row to flip:
 * WI-20260827-XFB56 — this is Rule 1's desugar and NOT Rule 3's absent-field fill, so an UNDER-APPLIED `two(1)` in an operation body still keeps a smaller `named_arity` than its loader-canonical twin and `unify_concrete` decides it FALSE. Measured: the NAMED spelling `two(a: 1)` answers nothing either and never enters the desugar block at all, so it is a DIFFERENT axis that pre-dates this ticket. It also owns deciding what an operation body should build for an absent REQUIRED field, which is not the question the loader answers for a pattern.
 * WI-20260827-1F0QP — a mixed constructor PATTERN uses a different rule from a mixed APPLICATION. `case two(y, a: 1)` gives `y` the LEADING field `a`, which the named `a: 1` has already taken, so the arm silently does not match and a later arm answers. `gpat`/`gpat0` assert the CURRENT (wrong) values on purpose; that ticket must flip them to (1,1) and (0,0). Its open-coded `fields.get(i)` + `sort_by_key` in `fresh_pattern_occ` is the copy of the rank rule that disagrees.
 * WI-20260827-14EV6 — `Value::as_str` / `as_int` / `as_bool` are carrier-narrow with nothing saying so, the silent-drop class WI-477 already removed from `as_term` in the same file. Found while repairing the readers above.

GREEN: rustland via scripts/test.sh, 36 test binaries, 5923 passed, 0 failed, 11 ignored, on the tree as pushed (rebased onto WI-20260827-2YHZ3, which had landed on main meanwhile; the only conflict was the wi_tests.rs mod-registration tail and the suite was re-run on the merged tree). scaland `sbt test` green: 544 across three sub-projects (520 + 23 + 1), 0 failed. No scaland change was needed — it has parse/load/kb/resolve/codegen but no evaluator, so neither of the two sites exists there.

/code-review WAS NOT RUN on this ticket, recorded because it is a repo gate rather than an optional step: I flagged the omission before committing and the user chose to skip it. The eight tests, the four-state back-out table and the separate back-outs of the two halves are the evidence that stands in its place; the reader-population repair was found by the SUITE, not by review.

Tests: wi_t2470_positional_ctor_in_op_body_test (8).

