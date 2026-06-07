//! WI-363 — provider-side operation coverage.
//!
//! The op-level twin of WI-343 (`check_provider_requires`). When a carrier
//! provides a spec (`fact Spec[X]`), every *operation* the spec declares must
//! be backed for `X`: a spec-level default (an `operation … = …` body or a
//! derivation rule on `Spec`), a registered builtin, or an op `X` supplies
//! itself. A declared op with none of these makes the satisfaction fact unsound
//! — a call resolves to nothing at runtime — so the loader rejects it with a
//! hard `UnbackedProviderOperation` error.

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
          export Spec, Carrier
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

// ── A spec-level default rule backs the op for every provider ──────────

#[test]
fn provider_with_spec_default_rule_loads() {
    // `Spec.needed` has a derivation rule on `Spec` (`rule needed(?x) = 0`),
    // so providing `Spec` is complete without the carrier redefining it. Pins
    // that the check recognizes spec-level equational defaults.
    let src = r#"
        namespace wi363.specdefault
          export Spec, Carrier
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
    assert!(unbacked(&errs).is_empty(),
        "Spec.needed has a spec-level default rule; provider should load clean; got:\n{}",
        errors_text(&errs));
}

// ── A carrier supplying its own op backs it (carrier-refined) ──────────

#[test]
fn provider_with_own_op_loads() {
    // `Spec.needed` is abstract (no default), but `Carrier` supplies its own
    // `operation needed(x: Carrier) -> Int64 = 0`. Pins that a carrier-refined op
    // counts as backing.
    let src = r#"
        namespace wi363.carrierop
          export Spec, Carrier
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
