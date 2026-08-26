//! WI-20260825-N2865 — a spec's `provides` CONVERSION opens the provided sort, not the
//! NAMESPACE around it.
//!
//! ## What was wrong
//!
//! `load::wire_provides_scope_parent` and the `requires` linker both wrote a plain
//! `ScopeInclusion { is_enclosing: false }`, and `resolve_in_scope_recursive_with_mode`
//! RE-ENTERS a reached scope's enclosing parents afterwards — only an IMPORT edge stopped
//! that (`EnclosingLinks::StoppedByImport`, WI-1089: "below an import edge, the ENCLOSING
//! chain is not re-entered — `import a.b.C` opens `C`, not the `a.b` around it").
//!
//! So a `provides` ACROSS NAMESPACES opened a path all the way to `<global>` at every
//! consumer that merely `requires` the providing spec, and every global name became a
//! rival there. Surfaced by WI-20260825-1WBZT, whose `anthill.prelude.algebra.Ring
//! provides anthill.prelude.Additive` is the tree's first cross-namespace provision:
//! `anthill-testcases/ring-polynom/ring.anthill`'s top-level `sort Ring` turned seven
//! references inside `algebra.anthill` into `ambiguous symbol 'Ring'`, and that file
//! carried a sibling-import workaround until this landed.
//!
//! ## Why `requires` is NOT stopped, which is the whole shape of the fix
//!
//! Stopping the chain below EVERY non-enclosing edge is the one-line version, and it is
//! wrong: measured, it fails exactly one row out of 5,724 —
//! `wi1089_import_binds_one_name_test::adding_an_import_beside_a_requires_takes_no_name_away`,
//! which pins that `requires lib.Spec` must still reach `lib`'s sibling `Sib`. A
//! `requires` clause is written BY the author naming the target; a conversion edge is
//! crossed TRANSITIVELY, by a consumer that never wrote the far sort's name. So the stop
//! is keyed on a new `ImportOrigin::Provision`, and `parent_edge_is_provision_only` keeps
//! an edge that a `requires` ALSO justifies un-stopped — `parent_edge_is_import_only`'s
//! exact argument, for the same reason.
//!
//! ## The back-out these rows are stated against
//!
//! Point `wire_provides_scope_parent` back at `add_parent` (or drop `Provision` from
//! `parent_edge_stops_enclosing`'s admitted set). MEASURED by doing it: exactly ONE row
//! fails — `a_cross_namespace_provides_does_not_leak_the_global_scope`. The other three
//! pass either way BY DESIGN and each says so at its own site; this summary claimed
//! "both rows below fail" until `/code-review` drove the back-out and counted.
//!
//! Their jobs are not the same, which is why three of them are here for a one-row
//! back-out: the same-namespace control says the fix addressed the right AXIS,
//! `a_requires_still_reaches_the_targets_siblings` is WI-1089's rule restated so a later
//! "simplification" to `!edge_is_enclosing` fails HERE rather than there, and
//! `a_provides_beside_an_import_still_stops` is the two-writers shape whose first cut
//! `/code-review` found broken.

use crate::common::try_load_kb_with_files;

/// THE DEFECT, MINIMIZED: a spec providing one in ANOTHER namespace made its own NAME
/// ambiguous at a consumer that only `requires` it.
///
/// `probe.alg.User -> requires Base -> provides anthill.prelude.Additive ->
/// anthill.prelude -> <global>`, where the second file's top-level `sort Base` sits. Two
/// errors before the fix, both `ambiguous symbol 'Base' in scope 'probe.alg.User':
/// candidates ["probe.alg.Base", "Base"]` — one at the `requires`, one at `Base.b`.
///
/// The SAME pair with the `provides` line removed loaded clean, which is what made the
/// clause the cause rather than the file.
#[test]
fn a_cross_namespace_provides_does_not_leak_the_global_scope() {
    let providing = r#"
namespace probe.alg
  import anthill.prelude.{Int64, Additive}
  sort Base
    sort T = ?
    provides Additive[T = T]
    operation b(x: T) -> T
  end
  sort User
    sort V = ?
    requires Base[V]
    operation f(x: V) -> V
    rule f_def: f(?x) <=> Base.b(?x)
  end
end
"#;
    // A top-level sort sharing the PROVIDING spec's short name — the rival the leaked
    // path put in reach.
    let global_rival = r#"
sort Base
  sort T = ?
  operation g(a: T) -> T
end
"#;
    let errs = try_load_kb_with_files(&[providing, global_rival])
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e);
    assert!(
        errs.is_empty(),
        "a `provides` opens the PROVIDED sort, not the namespace around it — a global \
         `sort Base` must not become a rival of `probe.alg.Base` at a consumer that only \
         `requires` it; got {errs:?}"
    );
}

/// …AND THE SAME-NAMESPACE CASE WAS ALWAYS FINE, which is the control that says the fix
/// addressed the right axis. `Cat` declared beside `Base` in `probe.alg` loaded clean
/// before the change and after it: nothing about `provides` itself was broken, only the
/// namespace hop it dragged along.
#[test]
fn control_a_same_namespace_provides_was_never_the_problem() {
    let same_ns = r#"
namespace probe.alg2
  import anthill.prelude.{Int64}
  sort Cat
    sort T = ?
    operation c(x: T) -> T
  end
  sort Base
    sort T = ?
    provides Cat[T = T]
    operation b(x: T) -> T
  end
  sort User
    sort V = ?
    requires Base[V]
    operation f(x: V) -> V
    rule f_def: f(?x) <=> Base.b(?x)
  end
end
"#;
    let global_rival = r#"
sort Base
  sort T = ?
  operation g(a: T) -> T
end
"#;
    let errs = try_load_kb_with_files(&[same_ns, global_rival])
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e);
    assert!(errs.is_empty(), "passes either way BY DESIGN; got {errs:?}");
}

/// TWO STOPPING WRITERS ON ONE EDGE MUST NOT CANCEL — the row `/code-review` found the
/// first cut failing.
///
/// `provides Base[T = T]` and `import Base.*` write the SAME `(scope, parent)` inclusion,
/// and an origin list is per pair — so the first predicate, `parent_edge_is_import_only(..)
/// || parent_edge_is_provision_only(..)`, saw `[Provision, File(f)]` and satisfied
/// NEITHER all-origins test. Two writers that each stop the chain alone stopped nothing
/// together, and the exact two `ambiguous symbol 'Base'` errors came back. One predicate
/// over both stopping kinds (`parent_edge_stops_enclosing`) is the fix.
///
/// FAILS IF the disjunction is restored, which is the shape a future reader is most
/// likely to reach for when adding a third stopping kind.
#[test]
fn a_provides_beside_an_import_still_stops() {
    let providing = r#"
namespace probe.alg4
  import anthill.prelude.{Int64, Additive}
  sort Base
    sort T = ?
    provides Additive[T = T]
    import anthill.prelude.Additive.*
    operation b(x: T) -> T
  end
  sort User
    sort V = ?
    requires Base[V]
    operation f(x: V) -> V
    rule f_def: f(?x) <=> Base.b(?x)
  end
end
"#;
    let global_rival = r#"
sort Base
  sort T = ?
  operation g(a: T) -> T
end
"#;
    let errs = try_load_kb_with_files(&[providing, global_rival])
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e);
    assert!(
        errs.is_empty(),
        "an edge written by BOTH a `provides` and a wildcard import is stopped by each \
         writer alone, so it must be stopped by the pair; got {errs:?}"
    );
}

/// THE RESIDUAL, PINNED RATHER THAN CLAIMED AWAY: `requires X` beside `provides X` leaves
/// the leak live, and that is the price of not taking WI-1089's rule away.
///
/// Both clauses write the same `(scope, parent)` inclusion, `requires` files
/// `Declaration`, and `parent_edge_stops_enclosing` admits no `Declaration` — so the
/// enclosing chain is re-entered and the global rival is back in reach. Driven: adding
/// one `requires Additive[T]` line to the repro above reproduces both ambiguity errors
/// verbatim.
///
/// NOT A BUG TO FIX HERE. Stopping an edge a `requires` justifies is exactly what fails
/// `wi1089_import_binds_one_name_test::adding_an_import_beside_a_requires_takes_no_name_away`.
/// The real repair is to key the stop per CLAUSE rather than per `(scope, parent)` pair,
/// which is a change to how inclusions are stored; this row exists so the residual is a
/// KNOWN shape with a failing witness rather than a surprise, and it INVERTS the day that
/// lands. Found by `/code-review`.
#[test]
fn a_requires_beside_a_provides_still_leaks() {
    let providing = r#"
namespace probe.alg3
  import anthill.prelude.{Int64, Additive}
  sort Base
    sort T = ?
    requires Additive[T]
    provides Additive[T = T]
    operation b(x: T) -> T
  end
  sort User
    sort V = ?
    requires Base[V]
    operation f(x: V) -> V
    rule f_def: f(?x) <=> Base.b(?x)
  end
end
"#;
    let global_rival = r#"
sort Base
  sort T = ?
  operation g(a: T) -> T
end
"#;
    let errs = try_load_kb_with_files(&[providing, global_rival])
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e);
    assert!(
        errs.iter().any(|e| e.contains("ambiguous symbol 'Base'")),
        "RECORDING THE RESIDUAL: a `requires` on the same edge keeps the enclosing chain, \
         so this shape still leaks — if it now loads, the stop went per-CLAUSE and this \
         row should become the positive test it wants to be; got {errs:?}"
    );
}

/// THE RULE THE STOP MUST NOT TAKE: `requires lib.Spec` still reaches `lib`'s SIBLING.
///
/// WI-1089 measured this and `adding_an_import_beside_a_requires_takes_no_name_away` owns
/// it; the row is restated here because it is the reason this fix is keyed on a new
/// origin instead of on `is_enclosing` alone. Stopping the chain below every
/// non-enclosing edge makes `Sib` unresolvable — driven, that one-line version fails
/// exactly WI-1089's row and nothing else in 5,724.
///
/// Passes either way BY DESIGN. Its job is to fail if someone later "simplifies" the
/// predicate to `!edge_is_enclosing`.
#[test]
fn a_requires_still_reaches_the_targets_siblings() {
    let src = r#"
namespace n2865.two.lib
  import anthill.prelude.{Int64}
  sort Sib
    entity sib(v: Int64)
  end
  sort Spec
    operation op1(x: Int64) -> Int64
  end
end

namespace n2865.two.app
  sort User
    requires n2865.two.lib.Spec
    entity user(n: Sib)
  end
end
"#;
    let errs = try_load_kb_with_files(&[src])
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e);
    assert!(
        errs.is_empty(),
        "`requires` is written BY the author naming the target, so it keeps the target's \
         enclosing chain — narrowing the stop to `provides` is what preserves this; got \
         {errs:?}"
    );
}
