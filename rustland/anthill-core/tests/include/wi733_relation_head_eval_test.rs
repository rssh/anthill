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
//! can notice. Across the whole `wi_tests` binary EXACTLY EIGHT fail (2994
//! passed; 8 failed):
//!
//!   * this file — `…head_evaluates`, `…head_option_evaluates`,
//!     `…a_matching_literal_yields_a_row`, `…head_and_tail_decompose_the_stream`
//!   * `wi818_…` — `stream_defaults_evaluate_on_inheriting_carriers`,
//!     `stdlib_stream_reads_evaluate`, `stdlib_head_of_empty_raises_empty_stream`
//!   * `wi714_relation_reference_test::wi714_negate_materializes_unit` — which
//!     became a witness only because WI-733 respelled it from a hand-rolled
//!     `splitFirst` walk to `.headOption`.
//!
//! Read honestly, that says this file is NOT the sole witness for the
//! spec-default eval path — WI-818 already covered it over `MappedStream` and
//! `List`. What it adds is the RESOLVER-BACKED carrier, where `splitFirst`
//! advances an SLD search instead of walking a cons spine.
//!
//! The three tests here that survive that mutation are named, not hidden: both
//! empty-case tests (the mutation makes `head` raise, which is what they already
//! expect) and the guard test (typing only, see below). They are defended by
//! MEASUREMENT 2 instead.
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

  -- One free head var → Relation[String] (1-collapse).
  rule person_name(?name) :- person(name: ?name, age: ?)
  rule one_name(?name) :- person(name: ?name, age: 30)
  rule rare_name(?name) :- person(name: ?name, age: 41)
  rule no_name(?name) :- person(name: ?name, age: 999)

  operation oneHeadOption() -> Option[T = String] effects Error =
    one_name.headOption
  operation oneHead() -> String effects {Error, Error[T = EmptyStream]} =
    one_name.head

  -- The POSITIVE neighbour for the empty rows below: same shape, same column,
  -- an age literal that DOES match.
  operation rareHeadOption() -> Option[T = String] effects Error =
    rare_name.headOption

  operation emptyHeadOption() -> Option[T = String] effects Error =
    no_name.headOption
  operation emptyHead() -> String effects {Error, Error[T = EmptyStream]} =
    no_name.head
  operation emptyTailHeadOption() -> Option[T = String] effects {Error, Error[T = EmptyStream]} =
    no_name.tail.headOption

  -- head/tail decomposition. Read as ONE list off ONE stream, so the assertion
  -- is structural rather than a coincidence of two searches agreeing: `takeN`
  -- and `tail` walk the same `splitFirst` chain, so row 0 of `all3` IS the row
  -- `head` returns and rows 1..2 ARE `tail`.
  operation all3() -> List[T = String] effects Error =
    person_name.takeN(10)
  operation tailAll() -> List[T = String] effects {Error, Error[T = EmptyStream]} =
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
        matches!(&got, Ok(Value::Str(s)) if s == "alice"),
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
/// rows), so nothing here may name a specific row. Comparing `all3`
/// against `tailAll` — each a full drain of one stream — makes the claim
/// structural: whatever order this load picked, dropping row 0 of the whole
/// drain must equal the tail's own drain.
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

    let mut i2 = interp_for(SRC);
    let got_tail = i2.call("test.wi733.tailAll", &[]);
    let tail = string_list(&mut i2, &got_tail);
    assert_eq!(
        tail.len(),
        2,
        "a 3-solution relation's tail drains to exactly 2 rows; got {tail:?}"
    );
    // `all` and `tail` come from two loads, so compare as SETS: the tail is the
    // whole relation minus exactly one row, whichever row this load put first.
    let mut tail_sorted = tail.clone();
    tail_sorted.sort();
    let missing: Vec<&String> = sorted.iter().filter(|n| !tail_sorted.contains(n)).collect();
    assert_eq!(
        missing.len(),
        1,
        "tail drops exactly one of the three rows; all={all:?} tail={tail:?}"
    );

    let mut i3 = interp_for(SRC);
    let n = i3.call("test.wi733.tailLength", &[]);
    assert_eq!(
        n.as_ref().ok().and_then(Value::as_int),
        Some(2),
        "tail's length agrees with its drain; got {n:?}"
    );
}

/// The `Error[EmptyStream]` ROW is present on a `.head` call against a relation:
/// declaring only `effects Error` is REFUSED AT LOAD, and the refusal is the
/// ONLY load error the fixture produces.
///
/// WHAT THIS DOES NOT SAY. It is tempting to read this as "the guard stays
/// because the carrier is lazy, unlike `head(cons(h, t))` on a `List`". MEASURED,
/// that is false: `operation pureHead() -> Int64 = head(cons(7, nil))` is refused
/// with the same `undeclared effect: Error[T = EmptyStream]`, and so is `head(xs)`
/// under `if not(isEmpty(xs))`. Guard discharge IS implemented and DOES fire —
/// `Int64.div(a, 5)` against a literal divisor loads clean while `div(a, b)` is
/// refused — it simply never fires for `isEmpty`, on ANY carrier. That gap is
/// WI-567 (Open), whose acceptance names these two shapes verbatim. So this test
/// is a relation-shaped instance of a currently-global refusal; when WI-567
/// lands, the `List` half starts discharging and THIS half must not.
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

  operation underDeclared() -> String effects Error =
    one_name.head
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

/// The `String` inside a `some(..)` — the payload rides positionally.
fn some_string(interp: &mut Interpreter, r: &Result<Value, EvalError>) -> Option<String> {
    match r {
        Ok(Value::Entity { functor, pos, .. })
            if interp.kb().qualified_name_of(*functor) == "anthill.prelude.Option.some" =>
        {
            match pos.first() {
                Some(Value::Str(s)) => Some(s.clone()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A `cons`-list of `String`s, flattened.
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
            Value::Str(s) => out.push(s),
            other => panic!("expected a String element, got {other:?}"),
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
