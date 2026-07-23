//! WI-281 — spec-satisfaction dot dispatch.
//!
//! The runtime/value twin of WI-344 (provider admissibility in the typer): a
//! method coming from a spec the receiver's sort *satisfies* dispatches via the
//! satisfaction fact. `?a.pick(?b)` where `a: Widget` and `fact Comparable[T =
//! Widget]` resolves `pick` to `Comparable.pick` — even though `Widget` itself
//! declares no `pick`. The synthesized `Apply(Comparable.pick, [a, b])` rides
//! the normal spec-op dispatch + `req_insertion`, so the requirement
//! (`Comparable[Widget]`, and transitively any spec `Comparable requires`) is
//! threaded by the existing machinery — not re-implemented in the dot path.
//!
//! This closes the gap WI-279 deliberately left open: WI-279's default fallback
//! resolves only operations *declared on* the receiver's sort, so a
//! spec-satisfaction method (the `(3).min(5) -> Ordered.min` shape) did not
//! dispatch.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

/// Load stdlib + `extra` source; return the KB plus any load errors
/// (type-check errors surface here via the load pipeline).
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

// ── The core case: dispatch via a spec the receiver's sort provides ─────

#[test]
fn dot_method_dispatches_via_provided_spec() {
    // `Widget` declares no `pick`, but provides `Comparable` (which does).
    // `?a.pick(?b)` resolves `pick` to `Comparable.pick` via the satisfaction
    // fact and synthesizes `pick(a, b)` → Widget. (The `(3).min(5) ->
    // Ordered.min` shape, self-contained so it needs no anthill-stl Int64 facts.)
    let src = r#"
        namespace wi281.provided
          sort Comparable
            sort T = ?
            operation pick(a: T, b: T) -> T = a
          end
          sort Widget
            entity widget(id: Int64)
            fact Comparable[T = Widget]
            operation choose(a: Widget, b: Widget) -> Widget = ?a.pick(?b)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?a.pick(?b) to dispatch to Comparable.pick via fact \
         Comparable[Widget] and type-check; got:\n{}",
        errors_text(&errs));
}

// ── The dispatched call threads the spec's own `requires` ───────────────

#[test]
fn dot_spec_method_threads_requires() {
    // `Comparable requires Nameable[T]`. `Widget` provides BOTH. The dispatched
    // `pick(a, b)` rides spec-op dispatch, which threads `Comparable[Widget]`;
    // resolving that requirement pulls in `Nameable[Widget]`, found via the
    // carrier's `fact Nameable[T = Widget]`. So the dot call type-checks only
    // because the requirement chain is satisfied.
    let src = r#"
        namespace wi281.requires
          sort Nameable
            sort T = ?
            operation tag(x: T) -> Int64 = 0
          end
          sort Comparable
            sort T = ?
            requires Nameable[T = T]
            operation pick(a: T, b: T) -> T = a
          end
          sort Widget
            entity widget(id: Int64)
            fact Nameable[T = Widget]
            fact Comparable[T = Widget]
            operation choose(a: Widget, b: Widget) -> Widget = ?a.pick(?b)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?a.pick(?b) to dispatch and thread Comparable[Widget] \
         (which requires Nameable[Widget], provided); got:\n{}",
        errors_text(&errs));
}

// ── Regression: the no-match path still fires when no spec provides it ──

#[test]
fn dot_no_provided_spec_still_reports_no_match() {
    // `Widget` provides `Comparable` (which has `pick`), but `zonk` is on
    // neither `Widget` nor any provided spec → the WI-279 no-match diagnostic
    // is unchanged (the spec fallback only adds matches, never hides them).
    let src = r#"
        namespace wi281.nomatch
          sort Comparable
            sort T = ?
            operation pick(a: T, b: T) -> T = a
          end
          sort Widget
            entity widget(id: Int64)
            fact Comparable[T = Widget]
            operation use_bad(a: Widget, b: Widget) -> Widget = ?a.zonk(?b)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(), "expected a no-match error for ?a.zonk(?b)");
    assert!(text.contains("no such member (dot dispatch)") && text.contains("zonk"),
        "expected a dot-dispatch no-match diagnostic naming 'zonk'; got:\n{text}");
    assert!(text.contains("Widget"),
        "expected the no-match diagnostic to name the receiver's sort Widget; got:\n{text}");
}

// ── The acceptance shape on a real builtin: Int64 → Ordered.min ───────────

/// Like `load_capturing_errors` but also loads the Rust host bindings
/// (`anthill-stl/anthill/`), where `fact Eq/Ordered/Numeric[T = Int64]` live.
fn load_capturing_errors_with_stl(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let files = crate::common::collect_stdlib_and_rust_bindings();
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

#[test]
fn dot_min_dispatches_via_int_ordered() {
    // `?x.min(?y)` where `x, y: Int64`. `Int64` declares no `min`, but provides
    // `Ordered` (`fact Ordered[T = Int64]` in anthill-stl), so `min` resolves to
    // `Ordered.min` and dispatches — the `(3).min(5) -> Ordered.min` acceptance
    // shape, threading `Ordered[Int64]` (and its required `Eq[Int64]`, also
    // provided). Without WI-281 this is a `DotDispatchNoMatch` (Int64.min = None).
    let src = r#"
        namespace wi281.intmin
          sort Calc
            entity calc(v: Int64)
            operation pick_min(x: Int64, y: Int64) -> Int64 = ?x.min(?y)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors_with_stl(src);
    assert!(errs.is_empty(),
        "expected ?x.min(?y) to dispatch to Ordered.min via fact Ordered[Int64]; got:\n{}",
        errors_text(&errs));
}

// ── Unsatisfied spec-level requires is now diagnosed (WI-343) ───────────

#[test]
fn dot_spec_method_unsatisfied_requires_errors_wi343() {
    // `Comparable requires Nameable[T]`, and `Gadget` provides `Comparable` but
    // NOT `Nameable`. WI-343 (provider-side requires coverage) rejects the
    // `fact Comparable[Gadget]` outright — the satisfaction fact is unsound, so
    // the dispatched `?a.pick(?b)` never gets a sound spec to ride. (Was a
    // known gap pinned here before WI-343 landed.)
    let src = r#"
        namespace wi281.unsat
          sort Nameable
            sort T = ?
            operation tag(x: T) -> Int64 = 0
          end
          sort Comparable
            sort T = ?
            requires Nameable[T = T]
            operation pick(a: T, b: T) -> T = a
          end
          sort Gadget
            entity gadget(id: Int64)
            fact Comparable[T = Gadget]
            operation choose(a: Gadget, b: Gadget) -> Gadget = ?a.pick(?b)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(),
        "WI-343: Gadget provides Comparable (which requires Nameable) without \
         providing Nameable → should be rejected; got clean load");
    assert!(text.contains("Comparable") && text.contains("Nameable"),
        "expected the diagnostic to name Comparable and its unmet Nameable; got:\n{text}");
}
