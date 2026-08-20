//! WI-20260819-33H3P — A LEAF OCCURRENCE CARRIES ITS OWN SPAN.
//!
//! THE TICKET'S FACE. The converter is scope-blind, so it flattens `p.join(q, λ)` into
//! ONE dotted functor symbol `"p.join"` applied to the arguments — there is no parse node
//! for the receiver `p`. `try_identifier_dot_call` (kb/load.rs) rediscovers the receiver
//! from that NAME once the scope is known and SYNTHESIZES its `var_ref(name: Ref(p))`
//! occurrence, which therefore had no span at all: `1:1`.
//!
//! WHY THAT REACHES A USER-VISIBLE DIAGNOSTIC. `splice_query_runner` (eval/builtins.rs)
//! anchors every node of a `where_run` / `join_run` splice on `relations.first()` — the
//! dot RECEIVER. So the whole expansion inherited whatever span that occurrence had. The
//! written argument `q` kept its location the whole time (it HAS a parse node), which is
//! what made the two operands disagree and pointed at the receiver.
//!
//! THE ROOT WAS ONE COORDINATE WIDER THAN THE TICKET'S FACE, and the ticket's premise —
//! "fix the receiver and the splice anchor needs no rule of its own" — held only for the
//! spelling it was written against. `build_expr_leaf` read the span from `kb.term_spans`,
//! and that table ASKS A DIFFERENT QUESTION than the one a leaf occurrence needs answered:
//! it is keyed by the HASH-CONSED `TermId` and filled first-write-wins, so it says "where
//! was this TERM first seen", while an occurrence is per-SITE. `var_ref(name: Ref(p))` is
//! ONE term for every mention of `p` in an operation, and a rule reference's is one term
//! for every mention in the whole KB. So the span is now PASSED to the builder from the
//! parse node the occurrence IS (`Loader::push_leaf_occ`), and `term_spans` — which still
//! serves its other readers — is no longer consulted for this.
//!
//! FIVE ARMS, ONE ROOT. Three of the four faces were found by review, not by the ticket,
//! and the last is the one that matters most. Each arm's parenthesis is the wrong location
//! it reports under the BACK-OUT below — measured, not predicted:
//!  * `..._reports_at_the_written_call` — the SYNTHESIZED receiver, no parse node (`1:1`).
//!  * `..._when_the_same_binder_was_used_earlier` — a second DOT mention of one binder
//!    (`1:1`; see the SECOND back-out, where this arm is the one that separates the two
//!    candidate fixes).
//!  * `..._when_the_call_is_written_without_the_dot` — the same program spelled
//!    `join(p, q, λ)` (the earlier `takeN(p, 9)`, `20:25`). One keystroke defeated the
//!    receiver-only repair: the operand is an ORDINARY WRITTEN leaf, and it took the
//!    first-write span too. This arm is why the fix moved to the leaf builder.
//!  * `..._not_at_an_earlier_mention_of_the_rule` — a bare-qualified citation (`18:13`, the
//!    `let` that binds the rule — neither of the two citations).
//!  * `..._when_the_rule_is_cited_from_another_file` — a rule reference's term is shared
//!    across the WHOLE KB, so the offset came from the OTHER file. A load error's FILE is
//!    stamped separately, per operation body (WI-745), so the two halves disagreed and the
//!    rendering named `10:1` OF A NINE-LINE FILE — a location that does not exist. This is
//!    the hazard the WI-757 `debug_assert` guards for macro rejections, live on a channel
//!    with no guard.
//!
//! TWO BACK-OUT MEASUREMENTS, each mutating the site rather than deleting it so the fixture
//! still loads. They answer different questions, and the second is why arm 2 exists:
//!  * RESTORE THE LOOKUP — `push_leaf_occ` builds with
//!    `kb.term_span(kb_id).unwrap_or_else(empty_span)` instead of the parse node's span.
//!    All five arms fail, each at the location named above; the control still passes.
//!  * WRITE THE SPAN INTO THE TABLE INSTEAD — the receiver-only first cut, which called
//!    `create_occurrence(parse_id, receiver_kb)` and left the builder reading `term_spans`.
//!    Arm 1 PASSES (its receiver is `p`'s first mention, so first-write-wins IS this site);
//!    arm 2 fails at the earlier `p.takeN(9)` (`20:19`) and arms 3-5 fail exactly as under
//!    the first back-out. A one-arm suite would have blessed that fix.
//!
//! ONE ARM CANNOT MEASURE THIS. The first two were the whole suite while the fix was
//! receiver-only, and both passed while arms 3-5 were broken. That is why the arms vary the
//! CHANNEL (synthesized / repeated / written / qualified / cross-file), not the error.
//!
//! PASSES EITHER WAY BY DESIGN, and named because it is what bounds the change:
//! `wi757_macro_diagnostic_test::rejection_is_located_at_the_offending_condition` (a macro
//! rejection is located at the CONDITION, a written sub-occurrence with a parse node of its
//! own, so no leaf's span is its anchor) and the `wi714_join` / `wi714_where` /
//! `wi731_rename` suites, which drive the successful expansions rather than the refusals.
//!
//! STILL NOT FIXED, and out of this ticket's acceptance: the message names `join_run`, the
//! operation the `conjoin_of` macro splices, rather than the `join` the author wrote. Only
//! the LOCATION is repaired here. Naming needs a provenance channel from the splice to
//! `TypeErrorContext` (16 construction sites), which is a different mechanism — owned by
//! WI-20260820-5R2XT.

use crate::common::{try_load_kb_with, try_load_kb_with_files};

fn one_error(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => panic!("expected the column collision to fail the load"),
        Err(e) => match &e[..] {
            [only] => only.clone(),
            _ => panic!("expected exactly one error, got: {e:?}"),
        },
    }
}

/// The shared domain: two relations that BOTH carry a `name` column, so `join` refuses the
/// pair (§4.5 — a merged schema requires disjoint field names) and the refusal has
/// somewhere to be reported.
const DOMAIN: &str = r#"
namespace test.wi33h3p
  import anthill.prelude.{String, Int64, Bool, List}
  import anthill.prelude.Relation.{join, takeN}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(id: Int64, name: String, age: Int64)
    entity pet(owner: Int64, name: String)
  end
  fact person(id: 1, name: "alice", age: 30)
  fact pet(owner: 1, name: "cat")

  rule person_row(?id, ?name, ?age) :- person(id: ?id, name: ?name, age: ?age)
  rule pet_row(?owner, ?name) :- pet(owner: ?owner, name: ?name)
"#;

/// The domain plus one operation whose `let` lines are `body`, so every arm shares one
/// preamble and the line numbers the assertions compute stay derived from the source.
fn program(body: &str) -> String {
    format!(
        "{DOMAIN}\n  operation owners() -> Bool effects Error =\n    let p = person_row\n    \
         let q = pet_row\n{body}    true\nend\n",
    )
}

/// `line:col` of `needle` on the line containing `anchor`, computed from the source so an
/// edit to a fixture cannot silently un-anchor an assertion (the `wi757_macro_diagnostic_test`
/// convention). `anchor` must be unique enough to name one line.
fn location_of(src: &str, anchor: &str, needle: &str) -> String {
    let line = src
        .lines()
        .position(|l| l.contains(anchor))
        .unwrap_or_else(|| panic!("the fixture has no `{anchor}` line"));
    let col = src.lines().nth(line).unwrap().find(needle).unwrap() + 1;
    format!("{}:{}:", line + 1, col)
}

fn assert_at(err: &str, expected: &str, instead_of: &str) {
    assert!(
        err.starts_with(expected),
        "expected the collision at {expected} — not {instead_of} — got: {err}",
    );
    assert!(
        err.contains("share the field name `name`"),
        "expected the column-collision refusal, got: {err}",
    );
}

/// FACE 1 — the ticket's own. The receiver is SYNTHESIZED (the converter flattened
/// `p.join` to one symbol), so it had no span at all and the refusal rendered `1:1`.
///
/// `1:1` is asserted ABSENT as well as the real location asserted present: it is the exact
/// value this ticket exists to remove, and a `starts_with` on some other fixture could be
/// satisfied by a wrong span that happened to land on line 1.
#[test]
fn wi33h3p_a_join_collision_reports_at_the_written_call() {
    let src = program("    let j = p.join(q, lambda (c, d) -> eq(c.id, d.owner))\n");
    let err = one_error(&src);
    assert_at(&err, &location_of(&src, "p.join(", "p.join("), "1:1");
    assert!(
        !err.starts_with("1:1:"),
        "the receiver's absent span rendered as 1:1; got: {err}",
    );
}

/// FACE 2 — a SECOND dot mention of one binder. Both share the hash-consed
/// `var_ref(name: Ref(p))`, so a span read from (or written to) `term_spans` is the FIRST
/// mention's. The earlier call is `takeN`, which is fine on its own, so the fixture holds
/// exactly one error and an assertion about where it is cannot be satisfied by a second.
#[test]
fn wi33h3p_a_join_collision_reports_at_the_join_when_the_same_binder_was_used_earlier() {
    let src = program(
        "    let earlier = p.takeN(9)\n    \
         let j = p.join(q, lambda (c, d) -> eq(c.id, d.owner))\n",
    );
    let err = one_error(&src);
    let earlier = location_of(&src, "p.takeN(", "p.takeN(");
    assert_at(
        &err,
        &location_of(&src, "p.join(", "p.join("),
        &format!("the earlier unrelated call on the same binder ({earlier})"),
    );
}

/// FACE 3 — THE SAME PROGRAM WITHOUT THE DOT. `join(p, q, λ)` reaches the same macro with
/// the same anchor, but `p` is now an ORDINARY WRITTEN leaf rather than a synthesized one.
/// It took the first-write span too, so a receiver-only repair was defeated by a spelling.
/// This arm is why the fix moved from the synthesis site to the leaf builder.
#[test]
fn wi33h3p_a_join_collision_reports_at_the_join_when_the_call_is_written_without_the_dot() {
    let src = program(
        "    let earlier = takeN(p, 9)\n    \
         let j = join(p, q, lambda (c, d) -> eq(c.id, d.owner))\n",
    );
    let err = one_error(&src);
    let earlier = location_of(&src, "takeN(p,", "takeN(p,");
    assert_at(
        &err,
        &location_of(&src, "join(p, q,", "p, q,"),
        &format!("the earlier unrelated call on the same binder ({earlier})"),
    );
}

/// FACE 4a — a bare-QUALIFIED rule citation. `try_qualified_rule_ref` synthesizes the same
/// `var_ref(Ref(person_row))` the unqualified reference lowers to, so ALL THREE mentions
/// here — the `let p = person_row` binding and the two citations — are one term. The
/// refusal was reported at the `let`, which is neither citation.
#[test]
fn wi33h3p_a_join_collision_reports_at_the_citation_not_at_an_earlier_mention_of_the_rule() {
    let src = program(
        "    let earlier = takeN(test.wi33h3p.person_row, 9)\n    \
         let j = join(test.wi33h3p.person_row, pet_row, lambda (c, d) -> eq(c.id, d.owner))\n",
    );
    let err = one_error(&src);
    let binding = location_of(&src, "let p = person_row", "person_row");
    assert_at(
        &err,
        &location_of(&src, "join(test.", "test.wi33h3p.person_row"),
        &format!("the `let` that binds the same rule ({binding})"),
    );
}

/// A rule declared in one file and cited from another.
const CROSS_A: &str = r#"namespace test.wi33h3p.a
  import anthill.prelude.{String, Int64, Bool, List}
  import anthill.prelude.Relation.{takeN}
  sort Person
    entity person(id: Int64, name: String, age: Int64)
    entity pet(owner: Int64, name: String)
  end
  fact person(id: 1, name: "alice", age: 30)
  fact pet(owner: 1, name: "cat")
  rule person_row(?id, ?name, ?age) :- person(id: ?id, name: ?name, age: ?age)
  rule pet_row(?owner, ?name) :- pet(owner: ?owner, name: ?name)
  operation mentionA() -> Bool effects Error =
    let z = person_row
    true
end
"#;

/// DELIBERATELY SHORTER THAN `CROSS_A`, and that is the assertion's instrument: the stale
/// offset comes from A, so rendering it against B's line index runs off the end and names a
/// line B does not have. A same-length pair would have shown a merely wrong line, which is
/// easy to read as a rounding error rather than as two files disagreeing.
const CROSS_B: &str = r#"namespace test.wi33h3p.b
  import anthill.prelude.{String, Int64, Bool, List}
  import anthill.prelude.Relation.{join}
  import anthill.prelude.PartialEq.{eq}
  import test.wi33h3p.a.{person_row, pet_row}
  operation owners() -> Bool effects Error =
    let j = join(person_row, pet_row, lambda (c, d) -> eq(c.id, d.owner))
    true
end
"#;

/// FACE 4b — THE SEVERE ONE. A rule SYMBOL is KB-global, so its `var_ref` term is shared
/// across FILES, and the first-write span came from `CROSS_A`. A load error's file is
/// stamped separately from its offset (per operation body, WI-745), so the rendering
/// combined B's file with A's offset and named a line PAST THE END OF B.
///
/// The out-of-range line is asserted explicitly, not just the right location: "reports
/// somewhere in B" is satisfied by any in-range wrong answer, and what made this worth
/// fixing is that the answer was not even a place.
#[test]
fn wi33h3p_a_join_collision_reports_in_its_own_file_when_the_rule_is_cited_from_another() {
    let errs = match try_load_kb_with_files(&[CROSS_A, CROSS_B]) {
        Ok(_) => panic!("expected the column collision to fail the load"),
        Err(e) => e,
    };
    let [err] = &errs[..] else {
        panic!("expected exactly one error, got: {errs:?}");
    };
    let expected = location_of(CROSS_B, "join(person_row", "person_row");
    assert_at(err, &expected, "an offset carried over from the other file");
    let line: usize = err.split(':').next().unwrap().parse().expect("a line number");
    assert!(
        line <= CROSS_B.lines().count(),
        "the reported line {line} is past the end of the {}-line file it names, so the \
         offset came from the other file; got: {err}",
        CROSS_B.lines().count(),
    );
}

/// CONTROL: the shared domain loads on its own, so every arm above is shown to fail on its
/// `join` and not on something the preamble does. Without it a fixture typo would read as
/// the refusal under test.
#[test]
fn wi33h3p_control_the_domain_without_a_join_loads() {
    let src = format!("{DOMAIN}\n  operation ok() -> Bool effects Error =\n    true\nend\n");
    if let Err(e) = try_load_kb_with(&src) {
        panic!("the shared domain must load on its own, got: {e:?}");
    }
}
