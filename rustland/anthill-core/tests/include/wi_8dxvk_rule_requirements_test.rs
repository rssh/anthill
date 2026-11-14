//! 8DXVK: retain instance bindings and validate source-written domain queries.
//! Back-out: this small binary plus WI-582 and dictionary/carrier controls had
//! 199 passed, 2 ignored; reverting production changes gave 193 passed, 6 failed.
//! The five capability regressions here and WI-582 alias member fail without the fix.
//! Operation-free Marker and invalid-binding cases pass either way as controls.

use crate::common::{load_kb_with, pattern_last_ints};
use anthill_core::kb::KnowledgeBase;

/// `answer(?y) :- keep(?x, ?y)` over `src(red(), 10)` and `src(blue(), 20)` is refused at
/// load: `?x` is a `Red` in one fact and a `Blue` in the other, so no caller can pass `keep`
/// its requirement, and none is read from the value (proposal 073 §6.2). The rows ask `keep`
/// at each value instead, where the query's own type builds the dictionary.
fn answer_is_refused(keep: &str) {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&tagger(&format!("{keep}\n rule answer(?y) :- keep(?x, ?y)"))),
        &["answer.body", "`Tagger`"],
        keep,
    );
}

/// The query `keep(<value>, ?y)` is refused where it is read: no provider answers the
/// instance the guard writes at that value's type.
fn refused_at(kb: &mut KnowledgeBase, value: &str) {
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(kb, &format!("test.dxvkTag.keep({value}, ?y)")),
        &["Tagger"],
        value,
    );
}

fn source(provision: bool, rule: &str) -> String {
    let provider = if provision {
        "namespace anthill.prelude.Int64\n import test.dxvk.Marker\n provides Marker[T = Int64]\nend\n"
    } else {
        ""
    };
    format!("namespace test.dxvk\n import anthill.prelude.{{Int64, Bool}}\n sort Marker\n  sort T = ?\n end\n fact src(1)\n fact src(true)\n {rule}\nend\n{provider}")
}

#[test]
fn operation_free_spec_requirement_executes_with_and_without_a_provider() {
    for provision in [false, true] {
        let mut kb = load_kb_with(&source(
            provision,
            "rule keep[A](?x: A) :- src(?x), Marker[A]",
        ));
        // A query is typed where it is read (073 §6.2): one leaving `A` open is refused, and
        // one at a value passes the guard that value's dictionary or is refused for none.
        crate::common::assert_refused_naming(
            &crate::common::query_pattern_refusals(&mut kb, "test.dxvk.keep(?x)"),
            &["`Marker` at `keep`'s `A`"],
            "a query leaving `A` open",
        );
        let refused = |kb: &mut KnowledgeBase, pattern: &str| {
            crate::common::assert_refused_naming(
                &crate::common::query_pattern_refusals(kb, pattern),
                &["Marker"],
                pattern,
            )
        };
        if provision {
            assert_eq!(crate::common::pattern_hits(&mut kb, "test.dxvk.keep(1)"), 1);
            refused(&mut kb, "test.dxvk.keep(true)");
        } else {
            refused(&mut kb, "test.dxvk.keep(1)");
        }
    }
}

#[test]
fn query_domain_refuses_a_parameter_spec_instead_of_answering_by_provision() {
    use anthill_core::kb::resolve::ResolveConfig;
    use anthill_core::kb::term::{Literal, Term, Var};
    use smallvec::smallvec;
    let mut kb = load_kb_with(&source(true, ""));
    let domain = kb.try_resolve_symbol("anthill.kernel.domain").unwrap();
    let negation = kb.try_resolve_symbol("anthill.kernel.not").unwrap();
    let marker = kb.try_resolve_symbol("test.dxvk.Marker").unwrap();
    let bound = kb.make_sort_ref(marker);
    let integer = kb.alloc(Term::Const(Literal::Int(1)));
    let boolean = kb.alloc(Term::Const(Literal::Bool(true)));
    let name = kb.intern("x");
    let vid = kb.fresh_var(name);
    let variable = kb.alloc(Term::Var(Var::Global(vid)));
    for (value, negate) in [(integer, false), (variable, false), (boolean, true)] {
        let membership = kb.alloc(Term::Fn {
            functor: domain,
            pos_args: smallvec![value, bound],
            named_args: smallvec![],
        });
        let goal = if negate {
            kb.alloc(Term::Fn {
                functor: negation,
                pos_args: smallvec![membership],
                named_args: smallvec![],
            })
        } else {
            membership
        };
        let (answers, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
        assert!(
            answers.iter().all(|answer| !answer.is_definite()),
            "unexpected definite answer"
        );
        assert!(
            stats
                .errors
                .iter()
                .any(|error| error.message.contains("a `domain` goal")
                    && error.message.contains("Marker")),
            "{:?}",
            stats.errors
        );
    }
    // CONTROL: ordinary value-type membership remains a definite answer.
    let int_sort = kb.try_resolve_symbol("anthill.prelude.Int64").unwrap();
    let int_bound = kb.make_sort_ref(int_sort);
    let goal = kb.alloc(Term::Fn {
        functor: domain,
        pos_args: smallvec![integer, int_bound],
        named_args: smallvec![],
    });
    let (answers, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert_eq!(answers.len(), 1);
    assert!(answers[0].is_definite() && stats.errors.is_empty());

    // Drive source conversion too: a dotted sort operand is a sort value,
    // rather than an unevaluated field_access that evades this validation.
    let goal =
        crate::common::query_pattern_term(&mut kb, "anthill.kernel.domain(1, test.dxvk.Marker)");
    let (answers, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(answers.iter().all(|answer| !answer.is_definite()));
    assert!(
        stats
            .errors
            .iter()
            .any(|error| error.message.contains("Marker")),
        "{:?}",
        stats.errors
    );
}

fn tagger(rule: &str) -> String {
    format!(
        r#"namespace test.dxvkTag
 import anthill.prelude.{{Int64, Bool}}
 sort Tagger
  sort C = ?
  sort Out = ?
  operation tag(x: C) -> Out
  operation code() -> Int64
 end
 sort IntTagger = Tagger[Out = Int64]
 sort Red
  entity red
  provides Tagger[C = Red, Out = Int64]
  operation tag(x: Red) -> Int64 = 7
  operation code() -> Int64 = 7
 end
 sort Blue
  entity blue
  provides Tagger[C = Blue, Out = Bool]
  operation tag(x: Blue) -> Bool = true
  operation code() -> Int64 = 9
 end
 fact src(red(), 10)
 fact src(blue(), 20)
 {rule}
end"#
    )
}

#[test]
fn named_positional_and_aliased_guards_preserve_the_written_instance() {
    for guard in [
        "Tagger[C = A, Out = Int64]",
        "Tagger[A, Int64]",
        "IntTagger[A]",
    ] {
        let keep = format!("rule keep[A](?x: A, ?y) :- src(?x, ?y), {guard}");
        answer_is_refused(&keep);
        let mut kb = load_kb_with(&tagger(&keep));
        assert_eq!(pattern_last_ints(&mut kb, "test.dxvkTag.keep(test.dxvkTag.Red.red(), ?y)"), [10], "{guard}");
        // The written `Out = Int64` is kept: `Blue`'s `Out` is `Bool`.
        refused_at(&mut kb, "test.dxvkTag.Blue.blue()");
    }
    let mut kb = load_kb_with(&tagger("rule keep[A](?x: A, ?y) :- src(?x, ?y), Tagger[A]"));
    assert_eq!(pattern_last_ints(&mut kb, "test.dxvkTag.keep(test.dxvkTag.Red.red(), ?y)"), [10]);
    assert_eq!(
        pattern_last_ints(&mut kb, "test.dxvkTag.keep(test.dxvkTag.Blue.blue(), ?y)"),
        [20],
        "the partial guard admits both providers"
    );
}

#[test]
fn a_partially_applied_alias_member_retains_its_instance() {
    for annotation in ["?x: IntTagger.C", "x: IntTagger.C"] {
        let variable = if annotation.starts_with('?') {
            "?x"
        } else {
            "x"
        };
        let keep = format!("rule keep({annotation}, ?y) :- src({variable}, ?y)");
        answer_is_refused(&keep);
        let mut kb = load_kb_with(&tagger(&keep));
        assert_eq!(
            pattern_last_ints(&mut kb, "test.dxvkTag.keep(test.dxvkTag.Red.red(), ?y)"),
            [10],
            "{annotation}"
        );
        refused_at(&mut kb, "test.dxvkTag.Blue.blue()");
    }
}

/// The written instance answers a carrier-less call (`Tagger.code()`) made through the
/// requirement's name, `require t: Tagger[C = A, Out = Int64], t.code(?r)`: only its written
/// `Out = Int64` selects `Red`'s `7`, and with `Out` left open both providers answer. An
/// unnamed guard is refused before such a call, as an operation's `requires` line is before
/// `Tagger.code()` — the requirement supplies the evidence for an instance a call names and
/// does not say which instance that is — and the refusal names the call through a name.
/// (The clause read the dictionary as `?d = require[Tagger[Out = Int64]]` beside the guard,
/// which proposal 060.1 §5 removed.)
#[test]
fn the_written_instance_is_consumed_through_the_existing_dictionary_channel() {
    for guard in [
        "Tagger[C = A, Out = Int64]",
        "Tagger[A, Int64]",
        "IntTagger[A]",
    ] {
        let keep = format!("rule keep[A](?x: A, ?r) :- src(?x, ?), require t: {guard}, t.code(?r)");
        answer_is_refused(&keep);
        let mut kb = load_kb_with(&tagger(&keep));
        assert_eq!(pattern_last_ints(&mut kb, "test.dxvkTag.keep(test.dxvkTag.Red.red(), ?y)"), [7], "{guard}");
        refused_at(&mut kb, "test.dxvkTag.Blue.blue()");
    }
    let mut kb = load_kb_with(&tagger(
        "rule keep[A](?x: A, ?r) :- src(?x, ?), require t: Tagger[C = A], t.code(?r)",
    ));
    // `Out` left open: both providers.
    assert_eq!(pattern_last_ints(&mut kb, "test.dxvkTag.keep(test.dxvkTag.Red.red(), ?y)"), [7]);
    assert_eq!(pattern_last_ints(&mut kb, "test.dxvkTag.keep(test.dxvkTag.Blue.blue(), ?y)"), [9]);
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&tagger(
            "rule keep[A](?x: A, ?r) :- src(?x, ?), Tagger[C = A, Out = Int64], Tagger.code(?r)",
        )),
        &["`Tagger[C = …].code(…)`", "`require s: Tagger[…]`", "`s.code(…)`"],
        "an unnamed guard before a call that writes no instance",
    );
}

#[test]
fn applying_an_introduced_bound_keeps_the_guards_other_bindings() {
    for (carrier, expected) in [("Red", None), ("Blue", Some(20))] {
        for sigil in [true, false] {
            let annotation = if sigil {
                format!("?x: A[C = {carrier}]")
            } else {
                format!("x: A[C = {carrier}]")
            };
            let variable = if sigil { "?x" } else { "x" };
            let keep = format!(
                "rule keep[A]({annotation}, ?r) :- src({variable}, ?r), Tagger[C = A, Out = Bool]"
            );
            answer_is_refused(&keep);
            let mut kb = load_kb_with(&tagger(&keep));
            let value = format!("test.dxvkTag.{carrier}.{}()", carrier.to_lowercase());
            match expected {
                Some(expected) => assert_eq!(
                    pattern_last_ints(&mut kb, &format!("test.dxvkTag.keep({value}, ?y)")),
                    [expected]
                ),
                // The Red provider's Out is Int64, not Bool.
                None => refused_at(&mut kb, &value),
            }
        }
    }
}

#[test]
fn invalid_guard_bindings_are_load_errors() {
    for guard in [
        "IntTagger[C = A, Out = Bool]",
        "Tagger[C = A, Unknown = Int64]",
        "Tagger[A, Int64, Bool]",
        "Tagger[C = Int64, Out = A]",
    ] {
        let src = tagger(&format!("rule keep[A](?x: A, ?r) :- src(?x, ?r), {guard}"));
        assert!(
            crate::common::try_load_kb_with(&src).is_err(),
            "{guard} must be refused"
        );
    }
}
