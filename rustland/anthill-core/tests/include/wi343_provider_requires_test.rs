//! WI-343 — provider-side requires coverage.
//!
//! When a carrier provides a spec (`fact Spec[Carrier = X]`), the spec's own
//! `requires` must hold for that carrier: a `Spec requires Other` means every
//! `X` claiming to be a `Spec` must also be an `Other`. Today's loader checks
//! requirements only at CALL sites; a satisfaction fact whose spec's `requires`
//! is unmet loads silently — the gap this WI closes with a hard load error.
//!
//! This is the provider-side twin of the call-site `MissingRequiresForSpecOp`
//! check, and it reuses the same binding-aware resolution
//! (`candidate_sub_goals_owned` + `collect_provides_candidates`).

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

// ── A carrier providing a spec must satisfy that spec's `requires` ──────

#[test]
fn provider_missing_required_subspec_errors() {
    // `Comparable requires Nameable[T]`. `Widget` provides `Comparable` but
    // NOT `Nameable` → the satisfaction fact is unsound and must be rejected.
    let src = r#"
        namespace wi343.missing
          export Nameable, Comparable, Widget
          sort Nameable
            sort T = ?
            operation tag(x: T) -> Int
            rule tag(?x) = 0
          end
          sort Comparable
            sort T = ?
            requires Nameable[T = T]
            operation pick(a: T, b: T) -> T
            rule pick(?a, ?b) = ?a
          end
          sort Widget
            entity widget(id: Int)
            fact Comparable[T = Widget]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(),
        "expected an UnsatisfiedProviderRequires error: Widget provides Comparable \
         (which requires Nameable) without providing Nameable; got clean load");
    assert!(text.contains("Comparable") && text.contains("Nameable") && text.contains("Widget"),
        "expected the diagnostic to name Widget, Comparable, and Nameable; got:\n{text}");
}

// ── A complete provision (carrier provides the spec AND its requires) ───

#[test]
fn provider_with_required_subspec_loads() {
    // `Widget` provides BOTH `Comparable` and its required `Nameable` → the
    // contract holds, so the load is clean. (Pins that the check does not
    // false-positive on a satisfied requirement.)
    let src = r#"
        namespace wi343.complete
          export Nameable, Comparable, Widget
          sort Nameable
            sort T = ?
            operation tag(x: T) -> Int
            rule tag(?x) = 0
          end
          sort Comparable
            sort T = ?
            requires Nameable[T = T]
            operation pick(a: T, b: T) -> T
            rule pick(?a, ?b) = ?a
          end
          sort Widget
            entity widget(id: Int)
            fact Nameable[T = Widget]
            fact Comparable[T = Widget]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "Widget provides both Nameable and Comparable; should load clean; got:\n{}",
        errors_text(&errs));
}

// ── A spec with no `requires` provided by a carrier is fine ─────────────

#[test]
fn provider_of_requireless_spec_loads() {
    // `Tagged` has no `requires`, so providing it imposes no further
    // obligation. (Guards against flagging providers of requirement-free
    // specs — the common case.)
    let src = r#"
        namespace wi343.requireless
          export Tagged, Gizmo
          sort Tagged
            sort T = ?
            operation label(x: T) -> Int
            rule label(?x) = 0
          end
          sort Gizmo
            entity gizmo(id: Int)
            fact Tagged[T = Gizmo]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "providing a requirement-free spec should load clean; got:\n{}",
        errors_text(&errs));
}
