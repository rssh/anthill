//! WI-346 — requires-shadow warning.
//!
//! A sort that `requires` a spec and declares a local operation whose short
//! name matches one of that spec's own operations *shadows* the inherited name.
//! Per kernel-language.md §8.7 the two are distinct, unrelated symbols
//! (`requires` never overrides — override is the `provides` direction), so the
//! program loads, but it is a frequent footgun: the author usually meant to
//! override. The loader emits a non-fatal `LoadWarning::RequiresShadow` (the
//! first consumer of the WI-345 channel), surfaced via `LoadResult::warnings`.
//!
//! A sort that *provides* the spec (`fact Spec[sort]`) is NOT flagged: there
//! the own op IS the override (own-op-beats-inherited).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Load the stdlib plus `extra`, expecting a clean load (warnings are
/// non-fatal), and return the warning strings.
fn load_warnings(extra: &str) -> Vec<String> {
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
        Ok(result) => result.warnings.iter().map(|w| w.to_string()).collect(),
        Err(errs) => panic!(
            "expected a clean load (the shadow is advisory, not fatal); got errors:\n{}",
            errs.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n")),
    }
}

// ── requires + same-named op → warning ──────────────────────────────────

#[test]
fn requires_shadow_emits_warning() {
    // `Req requires Sp` and declares its own `s_op`, whose short name shadows
    // the inherited `Sp.s_op`. `requires` does not override, so the two are
    // distinct ops — the satisfaction the author probably intended does not
    // hold, so flag it.
    let src = r#"
        namespace wi346.shadow
          export Sp, Carrier, Req
          sort Sp
            sort T = ?
            operation s_op(x: T) -> T
          end
          sort Carrier
            entity c(id: Int)
          end
          sort Req
            requires Sp[T = Carrier]
            operation s_op(x: Carrier) -> Carrier = x
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        warnings.iter().any(|w|
            w.contains("wi346.shadow.Req") && w.contains("s_op") && w.contains("wi346.shadow.Sp")),
        "expected a RequiresShadow warning naming Req, s_op, and Sp; got: {warnings:?}");
}

// ── requires + DIFFERENTLY-named op → no warning ────────────────────────

#[test]
fn requires_disjoint_op_name_no_warning() {
    // `Req requires Sp` but its own op `other_op` does not collide with any of
    // `Sp`'s ops — no shadow, no warning. (Guards against false positives.)
    let src = r#"
        namespace wi346.disjoint
          export Sp, Carrier, Req
          sort Sp
            sort T = ?
            operation s_op(x: T) -> T
          end
          sort Carrier
            entity c(id: Int)
          end
          sort Req
            requires Sp[T = Carrier]
            operation other_op(x: Carrier) -> Carrier = x
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        !warnings.iter().any(|w| w.contains("wi346.disjoint")),
        "a requires-user with a non-colliding op must NOT warn; got: {warnings:?}");
}

// ── provides + same-named op → no warning (legitimate override) ─────────

#[test]
fn provider_override_no_warning() {
    // `Prov` *provides* `Sp` (`fact Sp[...]`) and supplies its own `s_op`. That
    // is a legitimate override (own-op-beats-inherited), NOT a requires-shadow,
    // so it must not be flagged. `Prov` does not `requires Sp`, so it never
    // enters the shadow check.
    let src = r#"
        namespace wi346.provides
          export Sp, Carrier, Prov
          sort Sp
            sort T = ?
            operation s_op(x: T) -> T
            rule s_op(?x) = ?x
          end
          sort Carrier
            entity c(id: Int)
          end
          sort Prov
            entity p(id: Int)
            fact Sp[T = Prov]
            operation s_op(x: Prov) -> Prov = x
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        !warnings.iter().any(|w| w.contains("wi346.provides")),
        "a provider's own same-named op is an override, not a shadow; got: {warnings:?}");
}

// ── BOTH requires AND provides + same-named op → no warning (guard) ─────

#[test]
fn requires_and_provides_no_warning() {
    // `Both` both `requires Sp` AND `provides Sp` (`fact Sp[...]`) with its own
    // `s_op`. The `sort_provides` guard skips it: it is in its own requires
    // chain, but providing the spec makes the own op a real override.
    let src = r#"
        namespace wi346.both
          export Sp, Both
          sort Sp
            sort T = ?
            operation s_op(x: T) -> T
          end
          sort Both
            entity b(id: Int)
            requires Sp[T = Both]
            fact Sp[T = Both]
            operation s_op(x: Both) -> Both = x
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        !warnings.iter().any(|w| w.contains("wi346.both")),
        "a sort that both requires and provides the spec is overriding, not \
         shadowing; got: {warnings:?}");
}
