//! WI-363 — provider-side operation coverage.
//!
//! The op-level twin of WI-343 (`check_provider_requires`). When a carrier
//! provides a spec (`fact Spec[X]`), every *operation* the spec declares must
//! be backed for `X` by something EXECUTABLE (WI-818): a spec-level default
//! BODY (`operation … = …`), a registered builtin, or an op `X` supplies
//! itself. A derivation RULE on `Spec` no longer counts — a rule is a LAW the
//! SLD world resolves, not a body the evaluator can dispatch to, so counting
//! it (as this file pinned before WI-818) certified programs that loaded
//! clean and then died at run time. A declared op with no executable backing
//! makes the satisfaction fact unsound, so the loader rejects it with a hard
//! `UnbackedProviderOperation` error.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

fn load_capturing_errors(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => (kb, vec![]),
        Err(errs) => (kb, errs),
    }
}

fn errors_text(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

fn unbacked(errs: &[LoadError]) -> Vec<&LoadError> {
    errs.iter()
        .filter(|e| matches!(e, LoadError::UnbackedProviderOperation { .. }))
        .collect()
}

// ── A carrier providing a spec must back every declared op ─────────────

#[test]
fn provider_missing_op_backing_errors() {
    // `Spec` declares `needed` with NO body and NO rule — the abstract
    // primitive. `Carrier` claims `fact Spec[Carrier]` but supplies no own
    // `needed` either → the op has no implementation anywhere → unsound.
    let src = r#"
        namespace wi363.missing
          sort Spec
            sort T = ?
            operation needed(x: T) -> Int64
          end
          sort Carrier
            entity carrier(id: Int64)
            fact Spec[T = Carrier]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!unbacked(&errs).is_empty(),
        "expected an UnbackedProviderOperation error: Carrier provides Spec but \
         backs no `needed` (no spec default, no own op); got:\n{text}");
    assert!(text.contains("Carrier") && text.contains("Spec") && text.contains("needed"),
        "expected the diagnostic to name Carrier, Spec, and needed; got:\n{text}");
}

// ── A spec-level default RULE is a law, not backing (WI-818 reversal) ───

#[test]
fn provider_with_spec_default_rule_is_rejected() {
    // REVERSED by WI-818 — this test previously pinned the opposite. `rule
    // needed(?x) = 0` on `Spec` is a LAW: the SLD resolver can use it, but the
    // evaluator cannot (a rule is not a body), so counting it as backing let
    // exactly this program load clean and then die at run time
    // (`UnknownOperation` through the `requires` path, `OperationBodyMissing`
    // on a direct call). The rejection message is (A)'s from the WI-818
    // measurement: its "no default on <spec>" condition now means no
    // EXECUTABLE default.
    let src = r#"
        namespace wi363.specdefault
          sort Spec
            sort T = ?
            operation needed(x: T) -> Int64
            rule needed(?x) = 0
          end
          sort Carrier
            entity carrier(id: Int64)
            fact Spec[T = Carrier]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!unbacked(&errs).is_empty(),
        "a rule-only spec default must NOT back Spec.needed (WI-818: a rule is \
         not executable backing); the load passed clean instead");
    assert!(text.contains("Carrier") && text.contains("needed"),
        "expected the diagnostic to name Carrier and needed; got:\n{text}");
}

// ── A carrier supplying its own op backs it (carrier-refined) ──────────

#[test]
fn provider_with_own_op_loads() {
    // `Spec.needed` is abstract (no default), but `Carrier` supplies its own
    // `operation needed(x: Carrier) -> Int64 = 0`. Pins that a carrier-refined op
    // counts as backing.
    let src = r#"
        namespace wi363.carrierop
          sort Spec
            sort T = ?
            operation needed(x: T) -> Int64
          end
          sort Carrier
            entity carrier(id: Int64)
            fact Spec[T = Carrier]
            operation needed(x: Carrier) -> Int64 = 0
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(unbacked(&errs).is_empty(),
        "Carrier supplies its own `needed`; provider should load clean; got:\n{}",
        errors_text(&errs));
}

// ── The stdlib itself (post WI-362) is op-complete ─────────────────────

#[test]
fn stdlib_with_bindings_is_op_complete() {
    // Loads stdlib + the Rust host bindings (`fact Eq[Int64]`, `fact
    // VectorSpace[Vec3, Float]`, List's five provisions, Stream-provides-
    // Iterable, …). After WI-362 every provided spec is op-complete; host
    // carriers (Int64/Float/…) are backed by their artifacts and skipped. Pins
    // that WI-363 does not regress the standard library.
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let errs = match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs,
    };
    assert!(unbacked(&errs).is_empty(),
        "stdlib + Rust bindings should have no unbacked provider operations; got:\n{}",
        errors_text(&unbacked(&errs).into_iter().cloned().collect::<Vec<_>>()));
}
