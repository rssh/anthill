//! WI-733 — `Stream.head` / `headOption` / `tail` EVALUATE on a `Relation`, the
//! resolver-backed `LogicalStream` carrier proposal 052 is written about.
//!
//! THE ORIGINAL DEFECT. The three ops were defined ONLY by equational laws
//! (`rule head(?s) = fst(?p) :- splitFirst(?s) = some(?p)`). A law is an SLD
//! clause, so the ops RESOLVED as goals — but the interpreter has no
//! equational-rewrite fallback, so a `.head` CALL found no body and no builtin
//! and fell through to `UnknownOperation`. The typer accepted both spellings,
//! so `r.head` type-checked and then died at run time. It bit exactly the
//! carriers that INHERIT: a concrete `List` overrides `head` with its own body
//! (`list.anthill:229`), while `Relation` → `LogicalStream` supplies only
//! `splitFirst` and inherits the rest from `Stream`.
//!
//! WI-733 IS NOT THE FIX. WI-818 fixed it, by ruling that BACKING IS EXECUTABLE
//! — a spec-level rule is a LAW, not backing — and giving `headOption`/`head`/
//! `tail` default bodies over `splitFirst` (`stream.anthill:30-58`, annotated
//! WI-818 there). This file is WI-733's remaining half: the DEFENCE for the
//! carrier WI-733 named, which WI-818 left uncovered.
//!
//! ── CONTROL ─────────────────────────────────────────────────────────────
//!
//! MEASUREMENT 1, the DISCRIMINATING one. MUTATE the three spec-default bodies
//! in `stream.anthill` so they stay PRESENT but WRONG — `headOption`'s some-arm
//! returns `none`, `head`'s raises, `tail`'s returns `s` instead of `rest`. The
//! stdlib still LOADS, so only tests that actually EVALUATE an inherited read
//! can notice. Across the whole `wi_tests` binary EXACTLY NINE fail (2994
//! passed; 9 failed):
//!
//!   * this file — `…head_evaluates`, `…head_option_evaluates`,
//!     `…a_matching_literal_yields_a_row`, `…head_and_tail_decompose_the_stream`,
//!     `…head_reads_an_unboundedly_generating_relation`
//!   * `wi818_…` — `stream_defaults_evaluate_on_inheriting_carriers`,
//!     `stdlib_stream_reads_evaluate`, `stdlib_head_of_empty_raises_empty_stream`
//!   * `wi714_relation_reference_test::wi714_negate_materializes_unit` — which
//!     became a witness only because WI-733 respelled it from a hand-rolled
//!     `splitFirst` walk to `.headOption`.
//!
//! Read honestly, that says this file is NOT the sole witness for the
//! spec-default eval path — WI-818 already covered it over `MappedStream` and
//! `List`. What it adds is the RESOLVER-BACKED carrier: the reads run against a
//! `splitFirst` that advances an SLD search, including one relation that
//! GENERATES WITHOUT END.
//!
//! WHAT IS STILL UNPINNED, and it is the property that description leans on:
//! LAZINESS. No test here separates "take one search step" from "enumerate, then
//! take element 0", because the resolver's DEPTH CAP bounds even a full drain —
//! an eager `head` on the unbounded fixture returns the same row from a
//! truncated list, 117 ms slower and not one value different. An eager
//! reimplementation of the `Stream` defaults would keep all nine tests green.
//! The reasoning and the measurement are at
//! `wi733_head_reads_an_unboundedly_generating_relation`; naming the gap here so
//! the header cannot be read as claiming more than the tests do.
//!
//! The FOUR tests here that survive that mutation are named, not hidden: the
//! three empty-case rows — the mutated `head`/`tail` still raise and the mutated
//! `headOption` still takes its `none` arm, so all three see what they already
//! expect — and the guard test (typing only, see below). MEASUREMENT 2 is what
//! covers the first three; nothing but the declaration covers the fourth.
//!
//! MEASUREMENT 2, WEAK, and labelled as such. Deleting the three default bodies
//! outright (the pre-WI-818 shape) fails most of this file — but it proves
//! little: a `LoadError` BLOCKS the load (`load.rs`), so the STDLIB stops
//! loading with seven `UnbackedProviderOperation` errors naming
//! MappedStream/FilteredStream/List (never Relation), and ~1943 of 3004 tests in
//! this binary fail alongside. It measures LOADABILITY, which
//! `wi363_provider_operations_test::provider_with_spec_default_rule_is_rejected`
//! already pins, and it would fail a test whose body were `assert!(true)`. An
//! earlier revision of this header cited it as THE control; that was wrong.
//! MEASUREMENT 1 is the control; this one only covers the two empty-case rows.
//!
//! PASSES EITHER WAY, BY DESIGN: `wi733_head_guard_does_not_discharge_on_a_relation`
//! — it pins an effect ROW, which lives on the DECLARATION and survives any
//! change to the body. It is evidence about typing, never about backing.
//!
//! A FRESH INTERPRETER PER CALL is not a style choice: a raised error leaves the
//! frame stack dirty, and the next `call` on the same interpreter dies with
//! `Internal("deliver: parent frame had no awaiting state")`. Reusing one here
//! reported a phantom `tail` bug during this ticket's investigation.

use crate::common::{expect_load_errors, interp_for, try_load_kb_with};
use anthill_core::eval::{EvalError, Interpreter, Value};

/// THREE facts, and three relations over them at different arities of match:
/// `one_name` (exactly one solution — an unambiguous head VALUE), `person_name`
/// (all three — so `head`/`tail` can be shown to decompose), and the pair
/// `rare_name` / `no_name`, which differ ONLY in the age literal. That pair is
/// deliberate: every `no_name` assertion is an ABSENCE, and an absence proves
/// nothing unless a POSITIVE neighbour in the same risky position shows the
/// literal reaches the goal atom at all. `rare_name` is that neighbour.
const SRC: &str = r#"
namespace test.wi733
  import anthill.prelude.{String, Int64, Option, List, Bool, EmptyStream}
  import anthill.prelude.List.{length}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  fact person(name: "carol", age: 41)

  -- One free head var → Relation[(name: String)] (WI-20260818-YQB1Y: the schema names
  -- the column; it used to 1-collapse to `Relation[String]`).
  rule person_name(?name) :- person(name: ?name, age: ?)
  rule one_name(?name) :- person(name: ?name, age: 30)
  rule rare_name(?name) :- person(name: ?name, age: 41)
  rule no_name(?name) :- person(name: ?name, age: 999)

  operation oneHeadOption() -> Option[T = (name: String)] effects Error =
    one_name.headOption
  operation oneHead() -> (name: String) effects {Error, Error[T = EmptyStream]} =
    one_name.head

  -- The POSITIVE neighbour for the empty rows below: same shape, same column,
  -- an age literal that DOES match.
  operation rareHeadOption() -> Option[T = (name: String)] effects Error =
    rare_name.headOption

  operation emptyHeadOption() -> Option[T = (name: String)] effects Error =
    no_name.headOption
  operation emptyHead() -> (name: String) effects {Error, Error[T = EmptyStream]} =
    no_name.head
  operation emptyTailHeadOption() -> Option[T = (name: String)] effects {Error, Error[T = EmptyStream]} =
    no_name.tail.headOption

  -- head/tail decomposition. Both are drained off ONE interpreter, so `takeN`
  -- and `tail` walk the same load's `splitFirst` chain and the assertion is
  -- structural rather than a coincidence of two searches agreeing: rows 1..2 of
  -- `all3` ARE `tailAll`, positionally.
  operation all3() -> List[T = (name: String)] effects Error =
    person_name.takeN(10)
  operation tailAll() -> List[T = (name: String)] effects {Error, Error[T = EmptyStream]} =
    person_name.tail.takeN(10)
  operation tailLength() -> Int64 effects {Error, Error[T = EmptyStream]} =
    length(person_name.tail.takeN(10))
end
"#;

/// `.headOption` on a Relation returns the first materialized row. THE ticket's
/// headline acceptance: before WI-818 this was `UnknownOperation` at run time.
#[test]
fn wi733_relation_head_option_evaluates() {
    let mut interp = interp_for(SRC);
    let got = interp.call("test.wi733.oneHeadOption", &[]);
    assert_eq!(
        some_string(&mut interp, &got),
        Some("alice".to_string()),
        "one_name has exactly one solution, so `.headOption` is some(\"alice\"); got {got:?}"
    );
}

/// `.head` — the ergonomic form — returns the row itself, not an Option.
#[test]
fn wi733_relation_head_evaluates() {
    let mut interp = interp_for(SRC);
    let got = interp.call("test.wi733.oneHead", &[]);
    assert!(
        got.as_ref()
            .ok()
            .map(crate::common::sole_column)
            .and_then(|c| crate::common::scalar_str(interp.kb(), &c))
            .as_deref()
            == Some("alice"),
        "`.head` on a one-solution relation yields the row; got {got:?}"
    );
}

/// THE POSITIVE NEIGHBOUR for the three empty-case tests below. `rare_name` and
/// `no_name` differ only in the age literal, so this says the literal reaches
/// the goal atom and a matching one PRODUCES a row. Without it, every way of
/// building a wrong-but-also-empty query — a mis-numbered column, a literal that
/// never reaches the atom — reproduces the empty results exactly.
#[test]
fn wi733_a_matching_literal_yields_a_row() {
    let mut interp = interp_for(SRC);
    let got = interp.call("test.wi733.rareHeadOption", &[]);
    assert_eq!(
        some_string(&mut interp, &got),
        Some("carol".to_string()),
        "rare_name matches age 41, so its `.headOption` is some(\"carol\"); got {got:?}"
    );
}

/// The empty case behaves per the DECLARED type: `headOption` is total in its
/// VALUE, so an exhausted relation is `none` — not an error, and not a hang.
#[test]
fn wi733_relation_head_option_on_empty_is_none() {
    let mut interp = interp_for(SRC);
    let got = interp.call("test.wi733.emptyHeadOption", &[]);
    assert!(
        entity_functor_is(&mut interp, &got, "anthill.prelude.Option.none"),
        "`.headOption` on a relation with no solution is none; got {got:?}"
    );
}

/// ...while `.head` is PARTIAL, and its declared `Error[EmptyStream]` is what
/// actually arrives — the default body's raise arm, reached on a carrier whose
/// emptiness is an effectful observation.
#[test]
fn wi733_relation_head_on_empty_raises_empty_stream() {
    let mut interp = interp_for(SRC);
    assert_raises_empty_stream(&mut interp, "test.wi733.emptyHead");
}

/// `tail` is the third op the ticket named, and it is as partial as `head` —
/// WI-818 gave its row the same guarded label rather than promising a totality
/// the some-case-only law never delivered.
#[test]
fn wi733_relation_tail_on_empty_raises_empty_stream() {
    let mut interp = interp_for(SRC);
    assert_raises_empty_stream(&mut interp, "test.wi733.emptyTailHeadOption");
}

/// `head` and `tail` DECOMPOSE the relation: `all3 == [head] ++ tail`.
///
/// Order-free BY CONSTRUCTION rather than by assertion. A relation is an
/// unordered bag and enumeration order VARIES BETWEEN KB LOADS (measured on
/// THIS fixture: six fresh interpreters gave four distinct orders of the three
/// rows), so nothing here may name a specific row. Both drains are therefore
/// read off ONE interpreter — one load, one enumeration order — which is what
/// makes the claim structural rather than set-wise: whatever order this load
/// picked, `all3` MINUS ITS FIRST ROW must equal the tail's own drain,
/// positionally. Read from two loads instead (as this test first did) it
/// degrades to "the tail is 2 of the 3", which a `tail` that dropped the LAST
/// row would also satisfy.
#[test]
fn wi733_relation_head_and_tail_decompose_the_stream() {
    let mut i1 = interp_for(SRC);
    let got_all = i1.call("test.wi733.all3", &[]);
    let all = string_list(&mut i1, &got_all);
    let mut sorted = all.clone();
    sorted.sort();
    assert_eq!(
        sorted,
        vec!["alice".to_string(), "bob".to_string(), "carol".to_string()],
        "the relation's three solutions are exactly the three people; got {all:?}"
    );

    // SAME interpreter, so `tailAll` walks the same load's `splitFirst` chain.
    // (Safe reuse: `all3` returned Ok — the poisoning footgun is a TRAPPED call,
    // and a trapped `all3` fails the assertion above before we get here.)
    let got_tail = i1.call("test.wi733.tailAll", &[]);
    let tail = string_list(&mut i1, &got_tail);
    assert_eq!(
        tail,
        all[1..].to_vec(),
        "`tail` IS the whole drain minus its first row: all={all:?} tail={tail:?}"
    );

    let mut i3 = interp_for(SRC);
    let n = i3.call("test.wi733.tailLength", &[]);
    assert_eq!(
        n.as_ref().ok().and_then(Value::as_int),
        Some(2),
        "tail's length agrees with its drain; got {n:?}"
    );
}

/// `.head` and `.headOption` work on an UNBOUNDED relation — one whose full
/// drain is TRUNCATED. `reach` walks an a↔b cycle, so clause 2 regenerates
/// forever; no other test in the repo reads an inherited `Stream` op off a
/// relation that cannot be drained.
///
/// WHAT THIS DOES **NOT** MEASURE, stated because the header's framing invites
/// the mistake: it does not separate LAZY from EAGER. The intuition is that an
/// eager `head` (drain, then take element 0) would diverge here — it would not.
/// The resolver's depth cap bounds every drain, so `reach.takeN(100000)` RETURNS,
/// silently truncated to 50 rows, and an eager `head` would hand back the same
/// `"b"` from that truncated list. Measured, the only difference is work done:
/// `.head` 0 ms against the full drain's 117 ms. That is a timing gap, not a
/// value gap, and a timing assertion is not a sound pin in a shared test suite,
/// so none is made here. Laziness on this carrier therefore remains UNPINNED —
/// an eager reimplementation of the `Stream` defaults would keep this file green.
/// Pinning it needs a fixture where an eager drain changes the ANSWER, not just
/// the clock; the depth cap is what stands in the way of building one.
#[test]
fn wi733_head_reads_an_unboundedly_generating_relation() {
    let src = r#"
namespace test.wi733lazy
  import anthill.prelude.{String, Int64, Option, List, Bool, EmptyStream}
  import anthill.prelude.List.{length}

  sort Edge
    entity edge(from: String, to: String)
  end
  fact edge(from: "a", to: "b")
  fact edge(from: "b", to: "a")

  -- Clause 1 yields "b" in ONE step; clause 2 walks the cycle forever.
  rule reach(?x) :- edge(from: "a", to: ?x)
  rule reach(?x) :- reach(?y), edge(from: ?y, to: ?x)

  operation firstReach() -> (x: String) effects {Error, Error[T = EmptyStream]} =
    reach.head
  -- Proof the relation really does keep generating: a 2-fact graph has only two
  -- vertices, so a THIRD row can only come from the recursive clause.
  operation threeRows() -> Int64 effects Error = length(reach.takeN(3))
end
"#;
    let mut i1 = interp_for(src);
    let got = i1.call("test.wi733lazy.firstReach", &[]);
    assert!(
        got.as_ref()
            .ok()
            .map(crate::common::sole_column)
            .and_then(|c| crate::common::scalar_str(i1.kb(), &c))
            .as_deref()
            == Some("b"),
        "`.head` on an unbounded relation returns its first solution; got {got:?}"
    );

    let mut i2 = interp_for(src);
    let n = i2.call("test.wi733lazy.threeRows", &[]);
    assert_eq!(
        n.as_ref().ok().and_then(Value::as_int),
        Some(3),
        "the relation keeps generating past its two vertices — so the read above \
         was against a stream with no end; got {n:?}"
    );
}

/// The `Error[EmptyStream]` ROW is present on a `.head` call against a relation:
/// declaring only `effects Error` is REFUSED AT LOAD, and the refusal is the
/// ONLY load error the fixture produces.
///
/// WHAT THIS DOES NOT SAY. It is tempting to read this as "the guard stays
/// because the carrier is lazy, unlike `head(cons(h, t))` on a `List`".
///
/// THAT READING IS NOW THE CORRECT ONE, AND THE PARAGRAPH THAT STOOD HERE SAID
/// THE OPPOSITE — rewritten by WI-567 (delivered 2026-08-20), which this site's
/// own closing instruction anticipated. What it used to record, as measured
/// fact, was that `head(cons(7, nil))` and `head(xs)` under `if not(isEmpty(xs))`
/// were BOTH refused, that discharge "simply never fires for `isEmpty`, on ANY
/// carrier", and that WI-502 type erasure was "the real wall". Every one of those
/// four claims is now false, and the last was already refuted by WI-567's own
/// 2026-08-20 re-measurement before this change. They are quoted rather than
/// deleted because the wrong diagnosis outlived its measurement once and cost a
/// re-derivation; anyone who reads it elsewhere should know it was retired here.
///
/// WHAT IS TRUE NOW. Discharge fires for `isEmpty` on a CONCRETE `List` — by
/// literal abstract interpretation (`head(cons(7, nil))`, since WI-818 gave
/// `List.head`/`headOption`/`splitFirst` foldable bodies) and, since WI-567, from
/// a flow fact too (`if not(isEmpty(xs)) then List.head(xs)`). It must still NOT
/// fire here, because on an abstract/lazy `Stream` emptiness is an EFFECTFUL
/// observation with no static value — WI-567's LOAD-BEARING SCOPING, and the
/// reason this test exists. So this is no longer a relation-shaped instance of a
/// global refusal: it is now the DISCRIMINATING half, and the only thing standing
/// between a correct fix and one that discharges too widely.
///
/// The Γ-fed shape is pinned separately by
/// [`wi733_guarded_relation_head_still_does_not_discharge`] below — this test's
/// operation has no `if`, so its Γ is EMPTY and it cannot detect over-discharge
/// through the flow path WI-567 opened.
///
/// `expect_load_errors`, not `.any()`: an earlier revision scanned with `.any`
/// and PASSED while the stdlib itself was failing to load with seven unrelated
/// errors. Pinning the exact error set is what makes the refusal mean something.
#[test]
fn wi733_head_guard_does_not_discharge_on_a_relation() {
    let src = r#"
namespace test.wi733guard
  import anthill.prelude.{String, Int64, Option, List, Bool}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule one_name(?name) :- person(name: ?name, age: 30)

  operation underDeclared() -> (name: String) effects Error =
    one_name.head
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &["type mismatch in underDeclared.effects (op-effects): expected declared: [Error], \
           got undeclared effect: Error[T = EmptyStream]"],
    );
}

/// THE SAME REFUSAL, REACHED THROUGH Γ — the control the test above cannot be.
///
/// WI-567 made a `not(P)` goal consult the proposal-050 flow environment Γ before
/// negation-as-failure claims it, and made an `if` condition's `Bool.not` enter Γ
/// in goal vocabulary. That path is CARRIER-AGNOSTIC by construction: Γ knows
/// nothing about `List` versus `Relation`, it matches a fact against a goal
/// structurally. So "the `List` half discharges and this half must not" needs a
/// fixture that actually PUTS the emptiness fact in Γ — and
/// [`wi733_head_guard_does_not_discharge_on_a_relation`] cannot, because its
/// operation has no `if` and its Γ is empty.
///
/// Here the relation IS narrowed by `if not(one_name.isEmpty)`, the exact shape
/// that discharges on a `List` (`wi567_flow_guard_discharge_test::
/// then_branch_not_is_empty_discharges`). It must still be refused: on an
/// abstract/lazy `Stream` the guard `isEmpty(s)` is an EFFECTFUL observation, so
/// the Γ fact and the guard are not the same proposition and the discharge is not
/// available — WI-567's LOAD-BEARING SCOPING, now exercised on the path that
/// could actually violate it.
///
/// WHAT WOULD TURN THIS GREEN, i.e. what it detects: a `goal_form` /
/// `refute_guard` that discharged on "Γ mentions a `not(isEmpty(..))` fact"
/// without the per-receiver structural match, or any widening of the Γ overlay's
/// `views_structurally_equal` filter.
#[test]
fn wi733_guarded_relation_head_still_does_not_discharge() {
    let src = r#"
namespace test.wi733gguard
  import anthill.prelude.{String, Int64, Option, List, Bool}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule one_name(?name) :- person(name: ?name, age: 30)

  operation underDeclared() -> (name: String) effects Error =
    if not(one_name.isEmpty) then one_name.head else (name: "none")
end
"#;
    expect_load_errors(
        try_load_kb_with(src),
        &["type mismatch in underDeclared.effects (op-effects): expected declared: [Error], \
           got undeclared effect: Error[T = EmptyStream]"],
    );
}

// ── helpers ────────────────────────────────────────────────────────────

fn entity_functor_is(interp: &mut Interpreter, r: &Result<Value, EvalError>, qn: &str) -> bool {
    matches!(r, Ok(Value::Entity { functor, .. })
        if interp.kb().qualified_name_of(*functor) == qn)
}

/// The one-column ROW inside a `some(..)` — the payload rides positionally — read down to
/// its `String` column. WI-20260818-YQB1Y: `.headOption` on a one-column relation yields
/// `some((name: "alice"))`, not `some("alice")`.
fn some_string(interp: &mut Interpreter, r: &Result<Value, EvalError>) -> Option<String> {
    match r {
        Ok(v) => {
            // WI-20260827-T2470: read `some`'s payload through the CARRIER-NEUTRAL
            // `common::entity_field`, not as `pos.first()`. `some(x)` written in an
            // operation body used to evaluate to `Entity{some, pos:[x]}` — the
            // un-canonicalized shape that ticket removes — so a `pos`-only read silently
            // answered `None` and this test failed at its assert. Matching
            // `Value::Entity` would fix that row and keep the deeper fault: the same
            // `some` also rides as a `Value::Term` or a `Value::Node`, so the enum match
            // lets the receiver's CARRIER decide whether its own field is reachable. The
            // functor is read through the view for the same reason, and the leaf String
            // through `scalar_str`.
            let sym = crate::common::entity_functor(interp.kb(), v)?;
            if interp.kb().qualified_name_of(sym) != "anthill.prelude.Option.some" {
                return None;
            }
            let col = crate::common::sole_column(&crate::common::entity_field(
                interp.kb(),
                v,
                "value",
                0,
            ));
            crate::common::scalar_str(interp.kb(), &col)
        }
        _ => None,
    }
}

/// A `cons`-list of one-column relation rows, flattened to their `String` column.
///
/// Every step CHECKS THE FUNCTOR — `cons` or `nil`, by qualified name — and
/// panics otherwise. Shape alone is not enough: a `pair` and a 2-column tuple
/// are also 2-field entities, and `none`/`unit`/`empty_stream` are also nullary
/// ones, so a shape-only walk would silently treat a `none`-terminated chain as
/// a SHORT list instead of failing. `builtins.rs`'s production cons reader is
/// loud for the same reason. Handles both carriers: `build_list_value` emits
/// NAMED head/tail while `classify_ctor_arg` pushes POSITIONALLY.
fn string_list(interp: &mut Interpreter, r: &Result<Value, EvalError>) -> Vec<String> {
    const CONS: &str = "anthill.prelude.List.cons";
    const NIL: &str = "anthill.prelude.List.nil";
    let mut out = Vec::new();
    let mut cur = match r {
        Ok(v) => v.clone(),
        other => panic!("expected a List of rows, got {other:?}"),
    };
    loop {
        let (functor, pos, named) = match &cur {
            Value::Entity { functor, pos, named } => (*functor, pos.clone(), named.clone()),
            other => panic!("expected a cons/nil entity, got {other:?}"),
        };
        let qn = interp.kb().qualified_name_of(functor).to_string();
        if qn == NIL {
            return out;
        }
        assert_eq!(qn, CONS, "expected `{CONS}` or `{NIL}` in the list spine");
        let (head, tail) = if pos.len() == 2 {
            (pos[0].clone(), pos[1].clone())
        } else if named.len() == 2 {
            (named[0].1.clone(), named[1].1.clone())
        } else {
            panic!("`cons` must carry head+tail, got pos={pos:?} named={named:?}")
        };
        match head {
            Value::Tuple { .. } => out.push(match crate::common::sole_column(&head) {
                Value::Str(s) => s,
                other => panic!("expected a String column in the row, got {other:?}"),
            }),
            other => panic!("expected a one-column relation row, got {other:?}"),
        }
        cur = tail;
    }
}

/// The unhandled raise surfaces as `Raised` carrying `empty_stream` VERBATIM —
/// asserting the payload's functor, not merely that something failed, is what
/// separates the declared partiality from an unrelated eval error.
fn assert_raises_empty_stream(interp: &mut Interpreter, op: &str) {
    match interp.call(op, &[]) {
        Err(EvalError::Raised { payload }) => match &payload {
            Value::Entity { functor, .. } => assert_eq!(
                interp.kb().qualified_name_of(*functor),
                "anthill.prelude.EmptyStream.empty_stream",
                "the raise carries the declared guarded label's payload"
            ),
            other => panic!("expected an empty_stream payload, got {other:?}"),
        },
        other => panic!("expected Raised(empty_stream) from {op}, got {other:?}"),
    }
}
