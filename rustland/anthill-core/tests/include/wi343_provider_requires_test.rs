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

// ── WI-356: binding-precise — a provider satisfying the sub-spec at the
//    WRONG bindings must error (v0 base-level passed it) ──────────────────

#[test]
fn provider_satisfies_subspec_at_wrong_bindings_errors() {
    // `VS[V, F] requires Ring[F]`. `Carrier` provides `VS[V=Carrier, F=NonRing]`
    // and also `Ring[F=Carrier]`. So *some* sort named in the provision (the
    // carrier) provides `Ring` — v0's base-level check passes. But the
    // requirement at THIS provision's bindings is `Ring[F=NonRing]`, and
    // `NonRing` does not provide `Ring`. The binding-precise check (σ grounds
    // `F` to the concrete `NonRing`, so the goal resolves precisely) must
    // reject it. Pins WI-356 point (a).
    let src = r#"
        namespace wi356.wrongbind
          export Ring, VS, Carrier, NonRing
          sort Ring
            sort F = ?
            operation rtag(x: F) -> Int
            rule rtag(?x) = 0
          end
          sort VS
            sort V = ?
            sort F = ?
            requires Ring[F = F]
            operation vtag(v: V) -> Int
            rule vtag(?v) = 0
          end
          sort NonRing
            entity nonring(id: Int)
          end
          sort Carrier
            entity carrier(id: Int)
            fact Ring[F = Carrier]
            fact VS[V = Carrier, F = NonRing]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(),
        "expected an UnsatisfiedProviderRequires error: VS[V=Carrier, F=NonRing] \
         requires Ring[F=NonRing], and NonRing does not provide Ring (the carrier \
         providing Ring at a different binding must not satisfy it); got clean load");
    assert!(text.contains("wi356.wrongbind.VS") && text.contains("wi356.wrongbind.Ring"),
        "expected the diagnostic to name VS and its unmet Ring requirement; got:\n{text}");
}

// ── WI-356: transitive — a gap two hops down the `requires` chain errors ──

#[test]
fn provider_transitive_requires_gap_errors() {
    // `Spec requires A`, `A requires B`, all at the carrier's binding.
    // `Thing` provides `Spec` and `A` but NOT `B`. The chain `Spec → A → B`
    // is checked at the concrete binding `T=Thing`: `A`'s contract (`requires
    // B[T=Thing]`) is unmet, so providing `A` (and transitively `Spec`) is
    // unsound. Pins WI-356 point (c).
    let src = r#"
        namespace wi356.transitive
          export B, A, Spec, Thing
          sort B
            sort T = ?
            operation btag(x: T) -> Int
            rule btag(?x) = 0
          end
          sort A
            sort T = ?
            requires B[T = T]
            operation atag(x: T) -> Int
            rule atag(?x) = 0
          end
          sort Spec
            sort T = ?
            requires A[T = T]
            operation stag(x: T) -> Int
            rule stag(?x) = 0
          end
          sort Thing
            entity thing(id: Int)
            fact A[T = Thing]
            fact Spec[T = Thing]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(),
        "expected an UnsatisfiedProviderRequires error: Thing provides A (and Spec, \
         which requires A which requires B) but does not provide B; got clean load");
    assert!(text.contains("wi356.transitive.B"),
        "expected the diagnostic to name the unmet transitive requirement B; got:\n{text}");
}

// ── WI-359: the SHORTHAND `requires Ring[F]` (Ring's param is named `T`, so
//    the names differ) preserves the cross-param binding, so the check is
//    binding-precise. Before WI-359 the `F` was dropped (stored `Ring[T =
//    Ring.T]`), the goal stayed abstract, and this provision passed via the
//    existence fallback — a false negative. ───────────────────────────────

#[test]
fn shorthand_requires_binding_precise_wrong_field_errors() {
    // `VS[V, F] requires Ring[F]` — positional shorthand; Ring's own param is
    // `T`. `Carrier` provides `VS[V=Carrier, F=NonRing]` and `Ring[T=Carrier]`.
    // The requirement at this provision is `Ring` over `NonRing`, which has no
    // `Ring` — must error, even though the carrier provides `Ring` at `Carrier`.
    let src = r#"
        namespace wi359.shorthand
          export Ring, VS, Carrier, NonRing
          sort Ring
            sort T = ?
            operation rtag(x: T) -> Int
            rule rtag(?x) = 0
          end
          sort VS
            sort V = ?
            sort F = ?
            requires Ring[F]
            operation vtag(v: V) -> Int
            rule vtag(?v) = 0
          end
          sort NonRing
            entity nonring(id: Int)
          end
          sort Carrier
            entity carrier(id: Int)
            fact Ring[T = Carrier]
            fact VS[V = Carrier, F = NonRing]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(),
        "expected an UnsatisfiedProviderRequires error: VS[F=NonRing] requires Ring over \
         NonRing (which provides no Ring); the shorthand `requires Ring[F]` must now carry \
         the F binding so the check is binding-precise; got clean load");
    assert!(text.contains("wi359.shorthand.VS") && text.contains("wi359.shorthand.Ring"),
        "expected the diagnostic to name VS and its unmet Ring requirement; got:\n{text}");
}

#[test]
fn shorthand_requires_binding_precise_right_field_loads() {
    // The positive twin: `Carrier`'s field `F` is `Carrier` itself, which DOES
    // provide `Ring` — so `VS[V=Carrier, F=Carrier]` loads clean through the
    // precise path. Pins that WI-359 didn't just make everything error.
    let src = r#"
        namespace wi359.shorthand_ok
          export Ring, VS, Carrier
          sort Ring
            sort T = ?
            operation rtag(x: T) -> Int
            rule rtag(?x) = 0
          end
          sort VS
            sort V = ?
            sort F = ?
            requires Ring[F]
            operation vtag(v: V) -> Int
            rule vtag(?v) = 0
          end
          sort Carrier
            entity carrier(id: Int)
            fact Ring[T = Carrier]
            fact VS[V = Carrier, F = Carrier]
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "VS[V=Carrier, F=Carrier] requires Ring over Carrier, which provides Ring; \
         should load clean; got:\n{}", errors_text(&errs));
}
