//! WI-20260906-6BX85 — A `requires` OPENS THE SPEC IT NAMES, AND NOT THE MODULE AROUND IT.
//!
//! `requires lib.Spec` names ONE sort. It used to deliver `lib` as well, and the namespace
//! above `lib`, because the parent walk re-entered the target's ENCLOSING chain — the
//! reach WI-1089 removed for `import a.b.C.*` and WI-20260825-N2865 removed for a
//! `provides` conversion, and which a `requires` kept on the argument that its clause is
//! "written BY the author naming the target". That predicate does not separate the cases:
//! `import a.b.C.*` is written by the author naming the target too, and is stopped. What
//! the author named is `Spec`; `Spec`'s SIBLINGS are what the chain delivered.
//!
//! HOW WIDE IT WAS, measured on the tree this landed on. A consumer declaring one sort of
//! its own beside one `requires anthill.prelude.Field[T]`, run once per one-segment name
//! of `anthill.prelude`:
//!
//!                                   BEFORE          AFTER
//!   `ambiguous symbol '<N>'`        78 of 79        0 of 79
//!   loads clean                      1 of 79       79 of 79
//!
//! The one clean row before was `Field` ITSELF, which the consumer imports — a local alias
//! answers at §8.6 step 2, before the parent walk runs at all. The CONTROL is the same 79
//! fixtures with the `requires` line deleted: 0 ambiguous, 79 clean, both before and
//! after, so the clause was the whole cause.
//!
//! WHAT THIS DOES NOT NARROW, and the controls below drive each: a `requires` still
//! reaches its target WHOLE — the spec's own members, and whatever the spec's own
//! `requires` / `provides` / imports reach beneath it. Only the hop OUT of the target,
//! into the namespace that declares it, is gone.
//!
//! THE PRICE, and it is the rule WI-1089 recorded as the reason not to do this: a sibling
//! of the target now costs one `import lib.{Sib}` line, which also says what the sort
//! depends on. [`the_repair_for_a_sibling_is_one_import`] drives it.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT — drop `ImportOrigin::Requirement` from
//! `SymbolTable::parent_edge_stops_enclosing`'s admitted set (or point `load.rs`'s
//! `Item::RequiresDecl` arm back at `add_parent`). MEASURED by doing it over `wi_tests`
//! and `algebra_tests`: FIVE rows fail, 4,277 pass either way.
//!   * [`a_requires_does_not_reach_the_targets_siblings`] — `Sib` resolves again.
//!   * [`a_consumers_own_sort_may_share_a_prelude_name`] — all six names go ambiguous.
//!   * `wi_n2865_provision_edge_scope_test::a_requires_beside_a_provides_no_longer_leaks`
//!     — the two `ambiguous symbol 'Base'` errors come back.
//!   * `wi_n2865_provision_edge_scope_test::a_requires_does_not_reach_the_targets_siblings`
//!     — that file's own restatement of the rule, on its own fixture.
//!   * `algebra_spec_test::requiring_ring_across_namespaces_costs_a_consumer_nothing`.
//! The four CONTROLS here pass either way BY DESIGN; they are what fails if the stop
//! over-reaches and takes the target's own contents with it.
//!
//! Scaland's twin back-out (drop `ImportOrigin.Requirement` from `resolveRecursive`'s
//! `namesItsTarget`) moves exactly ONE row of 540:
//! `ImportOpensWhatItNamesTest`'s "a requires does not open the module around the spec
//! it names".

use crate::common::{expect_load_errors, load_kb_with, try_load_kb_with};

/// A library whose spec has a member, and a SIBLING sort next to it in the same
/// namespace — the thing the clause never named.
const LIB: &str = r#"namespace bx85.lib
  import anthill.prelude.{Int64}
  sort Sib
    entity sib(v: Int64)
  end
  sort Spec
    operation op1(x: Int64) -> Int64
  end
end
"#;

/// THE RULE. `requires bx85.lib.Spec` opens `Spec`. `Sib` is a sibling of `Spec` in
/// `bx85.lib`, named nowhere in the consumer, and is refused.
///
/// This is `wi1089_import_binds_one_name_test::a_wildcard_opens_what_it_names_and_not_the_module_around_it`
/// with the clause changed and nothing else — which is the point: the two spellings now
/// mean the same thing about the module around the target.
#[test]
fn a_requires_does_not_reach_the_targets_siblings() {
    expect_load_errors(
        try_load_kb_with(&format!(
            "{LIB}
namespace bx85.sibling
  sort User
    requires bx85.lib.Spec
    entity user(n: Sib)
  end
end
"
        )),
        &["unresolved name 'Sib' in scope 'bx85.sibling.User'"],
    );
}

/// THE REPAIR, DRIVEN — the half that makes the row above a trade rather than a loss.
/// Same fixture, one `import` line added, and the sibling is back. Qualifying the use site
/// (`lib.Sib`) is the other spelling and is not tested here; the import is the one
/// WI-1089's own rule points at.
#[test]
fn the_repair_for_a_sibling_is_one_import() {
    load_kb_with(&format!(
        "{LIB}
namespace bx85.repaired
  sort User
    requires bx85.lib.Spec
    import bx85.lib.{{Sib}}
    entity user(n: Sib)
  end
end
"
    ));
}

/// CONTROL — the spec's OWN member still resolves bare, which is what a `requires` is
/// for. DRIVEN by a bare call in an operation body, so the row cannot pass on a name that
/// denotes nothing.
///
/// Passes either way BY DESIGN. Its job is to fail if the stop is widened from the
/// ENCLOSING link to the `requires` edge itself.
#[test]
fn control_a_requires_still_reaches_the_specs_own_members() {
    load_kb_with(&format!(
        "{LIB}
namespace bx85.member
  import anthill.prelude.{{Int64}}
  sort User
    requires bx85.lib.Spec
    operation use_it(y: Int64) -> Int64 = op1(y)
  end
end
"
    ));
}

/// CONTROL — and the harder half: what the TARGET reaches beneath itself travels with it.
/// `Mid requires Deep`, so a consumer that `requires Mid` calls `Deep`'s operation bare,
/// two edges out. §8.6's own sentence — "a `requires`, a variant exposure and the imported
/// scope's own imports are contents of the thing imported, and stay reachable" — and the
/// link `WI-1110` calls load-bearing (`Ord provides WeakOrd`, `WeakOrd requires
/// PartialOrd`) is this shape.
///
/// Passes either way BY DESIGN, and it is the row that says the stop is on the ENCLOSING
/// link alone. Note `Deep` sits in a namespace of its OWN: were the stop applied to the
/// `requires` edge rather than to the enclosing hop, `deep_op` would be unreachable here.
#[test]
fn control_a_requires_reaches_through_the_targets_own_requires() {
    load_kb_with(
        r#"namespace bx85.deep
  import anthill.prelude.{Int64}
  sort Deep
    operation deep_op(x: Int64) -> Int64
  end
end

namespace bx85.mid
  import anthill.prelude.{Int64}
  sort Mid
    requires bx85.deep.Deep
    operation mid_op(x: Int64) -> Int64
  end
end

namespace bx85.consumer
  import anthill.prelude.{Int64}
  sort User
    requires bx85.mid.Mid
    operation use_both(y: Int64) -> Int64 = deep_op(mid_op(y))
  end
end
"#,
    );
}

/// THE CENSUS, in six rows. A consumer's own sort of a `anthill.prelude` name, declared
/// beside one `requires Field[T]`, must load — each of these was `ambiguous symbol` before
/// the change, and they are the names a user is most likely to reach for.
///
/// SIX AND NOT SEVENTY-NINE: each row is a full stdlib load, and this file is run on every
/// suite. The full 78-of-79 count is in the header, measured by the same fixture over
/// every one-segment prelude name.
#[test]
fn a_consumers_own_sort_may_share_a_prelude_name() {
    for name in ["List", "Map", "Set", "Option", "Error", "Type"] {
        let src = format!(
            "namespace bx85.census
  import anthill.prelude.{{Field, Int64}}
  sort {name}
    entity mk(v: Int64)
  end
  sort Poly
    sort T = ?
    requires Field[T]
    entity poly(a: T, b: {name})
  end
end
"
        );
        let errs = try_load_kb_with(&src)
            .map(|_| Vec::new())
            .unwrap_or_else(|e| e);
        assert!(
            errs.is_empty(),
            "a consumer's own `sort {name}` beside one `requires Field[T]` must load — \
             `{name}` is a SIBLING of `Field` in `anthill.prelude` and the clause named \
             neither it nor the namespace; got {errs:?}"
        );
    }
}

/// TWO WRITERS ON ONE EDGE MUST NOT CANCEL, in the shape this ticket left behind.
///
/// `parent_edge_stops_enclosing` asks `all` over the origin list: the chain is stopped
/// only where EVERY writer of the edge stops it, so one non-stopping writer keeps the
/// reach. WI-1089 minted that quantifier and drove it with `requires Spec` beside
/// `import Spec.*`; since this ticket BOTH of those stop, so that pair answers `all` and
/// `any` alike and measures the quantifier no longer.
///
/// THE PAIR THAT STILL DOES is an edge that is the ENCLOSING link and a `requires` at
/// once. `sort Outer { sort Inner { requires Outer } }` writes two distinct
/// `ScopeInclusion`s — `{Outer, is_enclosing: true}` and `{Outer, is_enclosing: false}` —
/// onto ONE `(Inner, Outer)` origin list, `[Declaration, Requirement]`. Under `all` the
/// `Declaration` keeps the chain and `Inner` still sees its own namespace; under `any`
/// the `requires` stops it and `Inner` loses `Shared`, `Int64` and everything above.
///
/// FAILS IF `parent_edge_stops_enclosing`'s `.all(` becomes `.any(`. MEASURED: that flip
/// leaves every other row in `wi_tests` green except
/// `wi1089_import_binds_one_name_test::an_import_of_the_enclosing_namespace_is_not_a_stop`,
/// which is the same rule at the import writer. Those two are the whole witness.
#[test]
fn a_requires_on_the_enclosing_sort_is_not_a_stop() {
    load_kb_with(
        r#"namespace bx85.nested
  import anthill.prelude.{Int64}
  sort Shared
    entity shared(v: Int64)
  end
  sort Outer
    operation outer_op(x: Int64) -> Int64
    sort Inner
      requires Outer
      entity inner(a: Shared, b: Int64)
    end
  end
end
"#,
    );
}

/// CONTROL for the census: the SAME six fixtures with the `requires` line deleted loaded
/// clean before the change too. Without it the row above cannot say whether the clause was
/// the cause or whether a user sort of that name was refused for some other reason
/// entirely.
///
/// Passes either way BY DESIGN.
#[test]
fn control_the_census_fixtures_load_with_no_requires_at_all() {
    for name in ["List", "Map", "Set", "Option", "Error", "Type"] {
        let src = format!(
            "namespace bx85.census_ctl
  import anthill.prelude.{{Field, Int64}}
  sort {name}
    entity mk(v: Int64)
  end
  sort Poly
    sort T = ?
    entity poly(a: T, b: {name})
  end
end
"
        );
        let errs = try_load_kb_with(&src)
            .map(|_| Vec::new())
            .unwrap_or_else(|e| e);
        assert!(errs.is_empty(), "the no-`requires` control must load; got {errs:?}");
    }
}
