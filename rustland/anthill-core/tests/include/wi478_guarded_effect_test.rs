//! WI-478 (proposal 048 phase 1): guarded effect-row elements `E :- guard`
//! parse, load, and store as `EffectExpression.guarded(label, guard)`. Discharge
//! (refuting the guard to drop the effect) is WI-067 and out of scope here, so a
//! guarded atom is CONSERVATIVELY PRESENT — `decompose_effect_row` treats it like
//! `present(label)`. Covered:
//!   * the GROUND-label path (a bare effect sort → the hash-consed-term `guarded`
//!     atom), including the conjunctive paren form `( E :- p, q )`;
//!   * the NODE path (a value-parameterized `Modify[c]` label → the occurrence
//!     `guarded` atom, poisoning the row to the Node carrier as a denoted label
//!     already does);
//!   * the conservative-presence behaviour at a call site (the guarded effect
//!     propagates exactly like an unconditional one until WI-067 lands).

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

/// Load stdlib + user source together (the path the effect check runs on) and
/// surface load errors as strings rather than panicking. Mirrors the WI-377
/// effect-row harness.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

#[test]
fn ground_label_guarded_effect_loads() {
    // `Boom` is a bare effect sort → the guarded atom lowers to the hash-consed
    // term `guarded(Boom, [eq(b, 0)])`. `risky2` uses the parenthesized conjunctive
    // guard `( Boom :- eq(b, 0), eq(a, 0) )`. Both are bodyless declarations (the
    // guarded effect is declared, not performed — over-declaration is fine), so a
    // clean load proves grammar → loader → representation end to end.
    let src = r#"
namespace anthill.test.wi478ground
  import anthill.prelude.{Unit, Int64}

  sort Boom
    entity Bang
  end

  operation risky(b: Int64) -> Unit
    effects { Boom :- eq(b, 0) }

  operation risky2(a: Int64, b: Int64) -> Unit
    effects { ( Boom :- eq(b, 0), eq(a, 0) ) }
end
"#;
    let res = load_result(src);
    assert!(
        res.is_ok(),
        "a guarded effect with a ground (bare-sort) label — bare and paren forms — \
         must parse, load, and store as `guarded(…)`; got: {:#?}",
        res.err()
    );
}

#[test]
fn denoted_label_guarded_effect_loads() {
    // The guarded label is the value-parameterized `Modify[c]` (`c` is a value), so
    // the guarded atom rides the occurrence (Node) carrier — `make_guarded_occ` —
    // poisoning the row exactly as a denoted `Modify[c]` already does. Must load
    // clean (no malformed-shape rejection from the row fold / decompose).
    let src = r#"
namespace anthill.test.wi478node
  import anthill.prelude.{Unit, Cell, Int64}

  operation maybe_modify(c: Cell, b: Int64) -> Unit
    effects { Modify[c] :- eq(b, 0) }
end
"#;
    let res = load_result(src);
    assert!(
        res.is_ok(),
        "a guarded effect with a denoted `Modify[c]` label must load clean on the \
         occurrence carrier; got: {:#?}",
        res.err()
    );
}

#[test]
fn guarded_effect_is_conservatively_present_at_call() {
    // `risky` carries a guarded `Boom`. Because phase 1 has NO discharge, the
    // guarded effect is conservatively present: calling `risky` propagates `Boom`
    // exactly like an unconditional effect. A caller that omits it must fail.
    let undeclared = r#"
namespace anthill.test.wi478call
  import anthill.prelude.{Unit, Int64}

  sort Boom
    entity Bang
  end

  operation risky(b: Int64) -> Unit
    effects { Boom :- eq(b, 0) }

  operation caller(b: Int64) -> Unit =
    risky(b)
end
"#;
    let errs = load_result(undeclared).expect_err(
        "a guarded effect is conservatively present (no discharge in phase 1), so \
         calling `risky` without declaring `Boom` must surface an undeclared effect",
    );
    assert!(
        errs.iter().any(|e| e.contains("Boom")),
        "expected the conservatively-present guarded `Boom` to surface as an \
         undeclared effect at the call; got: {errs:#?}"
    );

    // Declaring the effect at the caller (here unconditionally) makes it load clean
    // — the guarded `Boom` is subsumed by a plain `Boom`.
    let declared = r#"
namespace anthill.test.wi478call2
  import anthill.prelude.{Unit, Int64}

  sort Boom
    entity Bang
  end

  operation risky(b: Int64) -> Unit
    effects { Boom :- eq(b, 0) }

  operation caller(b: Int64) -> Unit
    effects Boom =
    risky(b)
end
"#;
    let res = load_result(declared);
    assert!(
        res.is_ok(),
        "declaring `Boom` at the caller must subsume the conservatively-present \
         guarded effect and load clean; got: {:#?}",
        res.err()
    );
}

#[test]
fn ground_guarded_effect_renders_with_guard_not_dropped() {
    // Regression: the GROUND-form effect-row printer (`collect_effect_atoms`) must
    // render a guarded atom's surface `Label :- goal` — a missing `guarded` arm
    // would drop it through the `_ => {}` fallthrough and emit `{}` (silent
    // round-trip data loss). Build `effects_rows(merge(guarded(Boom, [g]), …))`
    // directly and render it through the public `print_term` path
    // (EffectsRows → write_effect_row → collect_effect_atoms).
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib loads");

    let label = kb.make_name_term("Boom");
    let goal = kb.make_name_term("g");
    let guard = kb.build_list(&[goal]);
    let atom = kb.make_effect_expression_guarded(label, guard);
    let row = kb.build_canonical_effects_rows(&[atom]);

    let rendered = TermPrinter::new(&kb).print_term(row);
    assert!(
        rendered.contains(":-") && rendered.contains("Boom") && rendered.contains('g'),
        "a ground guarded effect must render its `Boom :- g` surface (not be dropped \
         to `{{}}`); got: {rendered:?}"
    );
}
