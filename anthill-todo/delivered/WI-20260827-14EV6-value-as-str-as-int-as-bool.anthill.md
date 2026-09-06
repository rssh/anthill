## Attributes

- id: WI-20260827-14EV6-value-as-str-as-int-as-bool
- created: 2026-08-27T22:50:02Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-06T18:03:29Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`Value::as_str` / `as_int` / `as_bool` ARE CARRIER-NARROW AND SAY SO NOWHERE, so a scalar that rides on a foreign carrier reads as ABSENT rather than as itself -- the silent-drop class WI-477 already removed from this same file's `as_term`.

Each of the three matches only its own variant:

  pub fn as_str(&self) -> Option<&str> {
      if let Value::Str(s) = self { Some(s.as_str()) } else { None }
  }

The SAME string also arrives as `Value::Term(id)` over `Term::Const(Literal::String)` and as `Value::Node(occ)` over `Expr::Const`. On either, `as_str` answers `None`, and a caller reads that as "not a string" instead of "I cannot see this carrier". `as_int` and `as_bool` are the same shape.

THE PRECEDENT IS IN THE SAME FILE AND SETTLES THE DESIGN. WI-477 replaced a silent `as_term() -> Option<TermId>` with a loudly-panicking `expect_term`, and its doc states the reason verbatim: the `None` on a `Value::Node`/`Entity`/scalar "was read as 'no term' and silently dropped the carrier (the binding-erasure class)". This ticket is that decision applied to the three scalar readers.

THE SPLIT IS FORCED BY WHAT NEEDS A KB, and it is not the same for all carriers:
  * `Value::Node(occ)` -> `occ.as_expr()` -> `Expr::Const(Literal::…)` needs NO KnowledgeBase. Pure, and the three accessors can absorb it with no signature change.
  * `Value::Term(id)` needs the term store to look the literal up. It CANNOT be answered from `&self` alone.

SO: widen the three to the `Node` carrier; RAISE LOUDLY on `Value::Term`, naming the KB-taking variant to use instead (`expect_term`'s wording is the model); and add that variant -- `as_str_in(&self, kb)` or equivalent -- for callers that legitimately hold a Term. A caller narrowing deliberately still writes `if let Value::Str(_)`.

THE BLAST RADIUS IS THE POINT AND MUST BE MEASURED, NOT ASSUMED. `as_str` alone has 109 call sites in `rustland/*/src`. Two distinct flips, and they are NOT the same finding:
  * a site that starts ANSWERING where it answered `None` (a Node-carried scalar) -- a masked bug surfacing, which is the point;
  * a site that now PANICS on a `Value::Term` -- each one is a reader that was silently dropping a Term-carried scalar, and each needs its own verdict: pass the kb, or narrow deliberately.
Run the workspace with the change in and triage every panic individually. A blanket `unwrap_or_default()` at a panicking site re-creates the defect the ticket removes.

WHY IT IS FILED SEPARATELY rather than inline in WI-20260827-T2470, which surfaced it: that ticket's own delivery showed twice that two live changes make the attribution wrong (its regression in `wi733` was credited to a neighbouring guard because both were live in one run). This one changes the answer at up to 109 readers and must be measured against a tree where nothing else moved.

ACCEPTANCE: the three accessors driven on ALL THREE carriers per type -- a `Value::Str`, a `Value::Node` over `Expr::Const`, and a `Value::Term` over `Term::Const` -- with the Node row asserting the VALUE (not merely `is_some`) and the Term row asserting the LOUD failure; the KB-taking variant driven on the Term carrier; the count of call sites that flipped, stated, with each panicking site's verdict named; `common::scalar_str` in `rustland/anthill-core/tests/common/mod.rs` collapsed to a call to the widened API (it exists only because the API was narrow); full workspace green via rustland/scripts/test.sh.

REFERENCE: `Value::as_str` / `as_int` / `as_bool` / `expect_term` (rustland/anthill-core/src/eval/value.rs), `ViewHead::Const` and `impl TermView for Value` (rustland/anthill-core/src/kb/term_view.rs), `common::scalar_str` / `entity_field` (rustland/anthill-core/tests/common/mod.rs).

## Changes

### 2026-09-06T18:03:29Z — feedback — user

DELIVERED, BUT NOT THE WAY THIS TICKET SPECIFIED — the accessors are DELETED, not widened,
and the reason is that the population the ticket was written against no longer existed.

THE BLAST-RADIUS PREMISE HAD AGED, and the number is not close. This ticket says "`as_str`
alone has 109 call sites in `rustland/*/src`" and asks for two flips triaged at up to 109
readers. MEASURED 2026-09-06 by marking the three `#[deprecated]` and running
`cargo check --workspace --all-targets` (the only census that cannot miss a caller):

  184 sites total
   164  anthill-core/tests/include/     test assertions
    18  `#[cfg(test)] mod tests` inside src/ (builtins.rs 12, cell_arena 2, value.rs 2, stl 2)
     2  PRODUCTION READS -- both in eval/effects.rs, the two Console write handlers

WI-20260827-3ZNBC (delivered 08-28, the day after this was filed) had consumed the entire
rest of the production population. What was left was not a surface to widen; it was two
readers and a hazard.

THE TWO SURVIVORS WERE A LIVE, IN-LANGUAGE DEFECT, driven before anything was changed.
`println(c, s)` read `args.get(1).and_then(Value::as_str)`, so:

  println(c, person_name.head.n)   Err(TypeMismatch{expected:"String",
                                       got:"missing or non-String argument"})
  println(c, "ada")                Ok(Unit), buffer "ada\n"        [CONTROL, same op/effect row]
  person_name.head.n               Value::Term(TermId(15865)); literal_string -> Some("ada")

Controls A and B isolate one axis: the fixture, the handler registration and `println` all
work, and the column IS "ada" -- it just rides hash-consed since WI-3ZNBC stopped
normalizing relation columns. The message was wrong twice over: it named "non-String" for
a String, and blamed the argument for the reader's blindness.

WHY DELETED RATHER THAN WIDENED. The ticket's plan -- widen to `Node`, PANIC on
`Value::Term`, add `as_str_in(kb)` -- would have made `as_str` answer THREE ways (`Some`;
`None` for "not a string"; panic for "a string I refuse to read"), landed that panic in 182
test assertions for no production gain, and added a FOURTH spelling beside
`TermView::literal_string`, which already answers the question correctly on every carrier.
Deleting instead means a future `v.as_str()` is a COMPILE ERROR rather than a silent narrow
answer, and it retires the naming constraint WI-20260827-2YHZ3 adopted only to dodge
inherent-wins-over-trait shadowing (that doc is rewritten to say the stem now stays for a
different reason). Decided with the user before starting.

WHAT LANDED
  * `eval/effects.rs` -- one `console_text`, shared by both handlers. Reads through
    `builtins::str_operand_opt`, split out of `str_operand` so the READ is shared and only
    the refusals differ: "no argument at index 1" (a handler bound at the wrong arity) and
    "denotes no string" are different bugs in the caller and the old message merged them.
    `Cow`, so a native `Value::Str` still borrows -- `print` in a loop allocates nothing new.
  * `Value::as_str` / `as_int` / `as_bool` -- GONE.
  * `common::scalar_str`/`scalar_int`/`scalar_bool` -- were byte-for-byte duplicates of
    `TermView::literal_string`/`literal_int64`/`literal_bool`; now one-line delegations.
  * 182 call sites migrated across 59 files. Where a test genuinely asserts the CARRIER it
    keeps `matches!` (`numeric_add_float` and its neighbours) -- a deliberate narrowing
    stays spelled as one.
  * `wi_50b2k`'s `int_through_any_carrier` lost its hand-rolled `Value::Node` ->
    `NodeKind::Expr` -> `Expr::Const(Literal::Int)` descent: `occ_head` IS that descent,
    reached through the same `as_expr`, so the branch was unreachable. Row still passes.

ACCEPTANCE, ITEM BY ITEM -- and one item is answered differently than asked.
  * three carriers per type: `String` is driven through the only production reader the
    family had left (native / `Value::Term` over `Term::Const` / `Value::Node` over
    `Expr::Const`, all printing "ada"/"hello"), plus the in-language relation-column row.
    `Int64` and `Bool` had NO production reader left at all, so their rows drive
    `literal_int64` / `literal_bool` directly and SAY at the site that they fail under no
    back-out of this ticket -- they guard `TermView`'s scalar arms, not this diff.
  * "the Term row asserting the LOUD failure" -- NO LONGER APPLIES, and that is the point.
    There is no loud failure to assert: the Term row asserts the VALUE, like the others.
  * "each panicking site's verdict named" -- there are no panicking sites; deletion, not panic.
  * `common::scalar_str` collapsed to the widened API: done.
  * scaland: nothing to port. `scaland/core/.../term/Value.scala` has no evaluator and no
    such accessors ("Scaland has no evaluator" -- its own doc); the enum carries no
    accessor methods at all.

CONTROL, MEASURED, and the RECIPE is part of it. In `console_text`, replace the
`str_operand_opt` call with `match arg { Value::Str(s) => Some(Cow::Borrowed(s.as_str())),
_ => None }` -- narrowing ONLY the read, keeping both `ok_or_else` arms -- and exactly THREE
of the eight rows fail: `a_term_carried_string_prints`, `a_node_carried_string_prints`,
`a_relation_column_prints`. Five pass either way by design, each saying why at its site.
/code-review caught that an earlier draft of the header wrote a COARSER recipe (collapsing
the helper to `args.get(1).and_then(...)`), which also deletes the absent-argument arm and
so fails two more rows -- two changes in one back-out credit neither. Re-measured with the
corrected recipe.

/code-review (high) FOUND SEVEN. All fixed. One was serious and my census could not have
caught it:

  1. HIGH -- `anthill-rust-gen/src/bundle.rs` EMITS `result.as_int()` INTO EVERY GENERATED
     BUNDLE's `main.rs`. It lives inside a `format!` string literal, so a compiler-driven
     census of a deleted method is STRUCTURALLY BLIND to it, and the one test that reads it
     (`emitted_bundle_compiles`) is `#[ignore]`d -- so the whole workspace stayed green
     while every bundle `anthill bundle` produced would have failed to compile on the
     user's machine. Fixed (emit the `TermView` import and `literal_int64(interp.kb())`),
     and MEASURED both ways: with the one line reverted the ignored test fails with
     `no method named `as_int``; with it in, it passes in 22s. Its doc now names the trigger
     -- run it whenever anthill-core's public API moves -- because that test is the only
     consumer of the API the compiler cannot see. IT IS STILL `#[ignore]`d (nested cargo
     check); making it a standing gate is a CI-cost decision left open.
  2. MEDIUM -- `console_text` duplicated `str_operand` and allocated on every write, the
     exact cost `str_operand`'s own doc records /code-review flagging once before. Fixed by
     splitting `str_operand_opt` out and sharing it, which also stops the two surfaces from
     drifting: a carrier that gains a literal head is read by both or by neither.
  3. LOW -- six comments still named the deleted accessors in the present tense
     (`eval/eval.rs`, `builtins.rs` x2, `tests/common/mod.rs`, `cli_parse_test`,
     `wi714_drain_test`, `wi_fc2x4`). A reader grepping `Value::as_bool` would have found
     only prose asserting it exists. All re-tensed.
  4. LOW -- the back-out recipe above.
  5. LOW -- `int_through_any_carrier`'s dead branch (deleted, see above).
  6. LOW/MEDIUM -- open ticket WI-20260904-EMVCB cites both `only_int` helpers and spells
     its acceptance "read through `as_int`". Re-measured against its own fixture and
     recorded there as feedback: its rows now read `Some(2)` while still ANSWERING a
     `Value::Node`, which is the half its own user feedback called fine. Its status is a
     decision for the user, not something this ticket took.
  7. LOW -- a doc-comment typo my migration script introduced in 12 files (it matched
     `expect_int(` inside a `///` block and appended the argument there too). Fixed;
     checked that no string literal or other comment took an insertion.
  Plus a pre-existing orphaned doc block in `term_view.rs` -- `index_var`'s doc had run
  into `as_literal`'s with no `fn` between, leaving `index_var` undocumented. Re-attached,
  since it sits in the paragraph this change edits.

FORMATTING, stated because this tree is not rustfmt-clean. Every touched file is at or
BELOW its HEAD hunk count under `cargo fmt -p ... -- --check`; none is worse. Ten files got
pre-existing hunks cleaned incidentally where they were entangled with edited lines. One
recovery is worth recording: running `rustfmt` on `tests/wi_tests.rs` follows every
`#[path]` module and reformatted 115 UNRELATED test files; recovered by reverting at file
granularity.

FULL WORKSPACE GREEN via rustland/scripts/test.sh: 36 binaries, 6524 passed, 0 failed.

