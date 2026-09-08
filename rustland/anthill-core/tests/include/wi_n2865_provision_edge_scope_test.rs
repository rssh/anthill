//! WI-20260825-N2865 — a spec's `provides` CONVERSION opens the provided sort, not the
//! NAMESPACE around it.
//!
//! ## What was wrong
//!
//! `load::wire_provides_scope_parent` and the `requires` linker both wrote a plain
//! `ScopeInclusion { is_enclosing: false }`, and `resolve_in_scope_recursive_with_mode`
//! RE-ENTERS a reached scope's enclosing parents afterwards — only an IMPORT edge stopped
//! that (`EnclosingLinks::Stopped`, WI-1089: "below an import edge, the ENCLOSING
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
//! ## Why `requires` was NOT stopped here — and why it is now
//!
//! Stopping the chain below EVERY non-enclosing edge was the one-line version, and it
//! failed exactly one row out of 5,724:
//! `wi1089_import_binds_one_name_test::adding_an_import_beside_a_requires_takes_no_name_away`,
//! which pinned that `requires lib.Spec` reaches `lib`'s sibling `Sib`. The argument
//! recorded for keeping it was that a `requires` is written BY the author naming the
//! target while a conversion is crossed TRANSITIVELY — so this fix minted
//! `ImportOrigin::Provision` and stopped that edge alone.
//!
//! WI-20260906-6BX85 REVERSED THE `requires` HALF, on this file's own predicate read
//! twice: `import a.b.C.*` is written by the author naming the target too, and WI-1089
//! stops it. What the author named is `Spec`; the enclosing chain delivered `Spec`'s
//! SIBLINGS — 78 of the 79 one-segment `anthill.prelude` names, at every consumer of a
//! prelude spec. `requires` now files `ImportOrigin::Requirement` and joins the admitted
//! set, so the two rows below that recorded the residual are inverted rather than
//! deleted, and each says which back-out re-reds it.
//!
//! ## The back-out these rows are stated against
//!
//! Point `wire_provides_scope_parent` back at `add_parent` (or drop `Provision` from
//! `parent_edge_stops_enclosing`'s admitted set). MEASURED by doing it: exactly ONE row
//! failed — `a_cross_namespace_provides_does_not_leak_the_global_scope`. The other three
//! passed either way BY DESIGN and each says so at its own site; this summary claimed
//! "both rows below fail" until `/code-review` drove the back-out and counted.
//!
//! The `Requirement` half is a SECOND back-out, and it moves a different set. MEASURED
//! over `wi_tests` and `algebra_tests`: FIVE rows, of which TWO are here —
//! `a_requires_beside_a_provides_no_longer_leaks` and
//! `a_requires_does_not_reach_the_targets_siblings`. The other three are
//! `wi_6bx85_requires_opens_the_spec_test`'s two subject rows and
//! `algebra_spec_test::requiring_ring_across_namespaces_costs_a_consumer_nothing`.
//! The two `provides` rows above pass under it, which is what says the two stops are
//! independent rather than one restated.

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

/// THE RESIDUAL, NOW CLOSED — and this row is the inversion it was written to become.
///
/// It shipped asserting the LEAK: `requires X` beside `provides X` is one `(scope,
/// parent)` inclusion with two writers, `requires` filed `ImportOrigin::Declaration`,
/// and `parent_edge_stops_enclosing` admitted no `Declaration` — so the `all` quantifier
/// found a non-stopping writer, the enclosing chain was re-entered, and the global rival
/// came back. Its own note said the row "INVERTS the day that lands".
///
/// WI-20260906-6BX85 landed it, though not by the mechanism that note predicted. The
/// repair is not a per-CLAUSE stop: `requires` simply joined the admitted set as
/// `ImportOrigin::Requirement`, because a `requires` opens the spec it names and not the
/// module around it for the same reason a `provides` does. Both writers stop, so the
/// `all` quantifier is satisfied and the shape loads.
///
/// FAILS IF the `requires` stop is backed out — the two `ambiguous symbol 'Base'` errors
/// return verbatim, which is what this row asserted before.
#[test]
fn a_requires_beside_a_provides_no_longer_leaks() {
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
        errs.is_empty(),
        "a `requires` beside a `provides` is one edge both of whose writers stop the \
         enclosing chain, so the global `sort Base` must not be a rival of \
         `probe.alg3.Base`; got {errs:?}"
    );
}

/// THE RULE THIS FIX WAS KEPT NARROW FOR, AND WHICH WI-20260906-6BX85 THEN TOOK.
///
/// N2865 narrowed its stop to `provides` because stopping every non-enclosing edge made
/// `Sib` unresolvable, failing WI-1089's row and nothing else in 5,724. That trade was
/// re-measured on this ticket's own terms — the reach it preserved was 78 of the 79
/// one-segment `anthill.prelude` names, shadowable at every consumer of a prelude spec —
/// and reversed. So the row is REPLACED rather than deleted: same fixture, opposite
/// verdict, plus the one-line repair.
///
/// ITS ORIGINAL JOB — failing if the predicate is "simplified" to `!edge_is_enclosing` —
/// is now carried by `wi1089_import_binds_one_name_test::an_import_of_the_enclosing_namespace_is_not_a_stop`
/// alone, and only for the ENCLOSING half. The other origin the predicate still excludes,
/// `Exposure`, cannot be driven from here: a variant-exposure edge runs from a scope to a
/// sort DECLARED IN IT, so the enclosing hop back out lands on a scope the walk has
/// already visited. Stating that rather than claiming a row for it.
///
/// FAILS IF the `requires` stop is backed out: `Sib` resolves and the first arm's
/// expected refusal disappears.
#[test]
fn a_requires_does_not_reach_the_targets_siblings() {
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
        errs.iter()
            .any(|e| e.contains("unresolved name 'Sib'")),
        "`requires n2865.two.lib.Spec` names ONE sort; `Sib` is its sibling and the \
         clause never named it or the namespace holding both; got {errs:?}"
    );

    // THE REPAIR, in the same fixture: one import, and the sibling is back. Without this
    // arm the row above says only that a name stopped resolving, not that the author has
    // a way to ask for it.
    let repaired = src.replace(
        "    requires n2865.two.lib.Spec\n",
        "    requires n2865.two.lib.Spec\n    import n2865.two.lib.{Sib}\n",
    );
    let errs = try_load_kb_with_files(&[&repaired])
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e);
    assert!(errs.is_empty(), "the import repair must load; got {errs:?}");
}
