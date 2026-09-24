//! WI-20260923-N3W68 — the typer's suspected TWIN DIVERGENCES (duplication review items
//! #3–#15): pairs of functions answering one question where a fix landed in one copy
//! only.
//!
//! Every item was REPORTED by reading; this file holds the program that decided each one.
//! An item that reproduced is fixed and its test drives the fixed path; an item that did
//! not reproduce had its doc corrected instead, and the note at its section says what was
//! run. Each test states its back-out at its own site.

use crate::common::{expect_loaded, try_load_kb_with};

fn load_errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(es) => es.iter().map(|e| e.to_string()).collect(),
    }
}

// ── #3: two different PARAMETERIZED bindings "agreed" ────────────────────────────
//
// `provision_bindings_agree` (coherence.rs) and its twin in the route merge
// (`provision_values_agree`, carrier.rs — now deleted, the merge calls the one predicate)
// compared the HEAD SORT of a binding, so `List[T = Int64]` agreed with `List[T = String]`;
// the route merge's copy read the functor of ANY `Term::Fn`, so any two arrows agreed too.

/// One carrier providing one spec twice at ONE application, `Element` bound to two
/// parameterized types. The WI-842 shape (`wi842_bracketless_readers_test`'s
/// `conflicting_provisions_are_refused_in_either_order`), one level deeper.
fn one_carrier_two_provisions(ns: &str, first: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Iter
    sort Self = ?
    sort Element = ?
  end
  sort C
    entity c
    provides Iter[Self = C, Element = {first}]
    provides Iter[Self = C, Element = {second}]
  end
  sort Use
    operation takes(i: Iter[Self = C, Element = List[T = String]]) -> Int64 = 1
    operation go(n: Int64) -> Int64 = Use.takes(c())
  end
end
"#
    )
}

/// MEASURED before the fix: with `List[T = String]` written first the program LOADED
/// CLEAN, and with `List[T = Int64]` first it was refused by the ordinary mismatch at
/// `takes(c())` — the program's meaning decided by provision order, the defect WI-842's
/// load refusal exists to remove, because `check_provision_binding_agreement` read the
/// two bindings as one.
///
/// BACK-OUT (A), MEASURED: restoring the head-sort compare (`sort_functor_of_view`) in
/// `provision_bindings_agree` fails this test — the `Int64`-first row is refused only by
/// the ordinary mismatch, with no named conflict — and, since the route merge now asks
/// the same predicate, the `list, MidB first` row of the route test below. 2 of the 4
/// tests here fail; the two controls pass.
#[test]
fn a_parameterized_binding_conflict_is_refused_in_either_order() {
    for (ns, first, second) in [
        ("n3w68.p3.intfirst", "List[T = Int64]", "List[T = String]"),
        ("n3w68.p3.strfirst", "List[T = String]", "List[T = Int64]"),
    ] {
        let errs = load_errors(&one_carrier_two_provisions(ns, first, second));
        let text = errs.join("\n");
        for want in ["conflicting provisions", "Element", "List[T = Int64]", "List[T = String]"] {
            assert!(
                text.contains(want),
                "`{ns}`: two provisions binding `Element` to `{first}` and `{second}` are \
                 two answers for one application and must be refused by name (`{want}` \
                 missing):\n{text}"
            );
        }
    }
}

/// THE CONTROL: the same two provisions binding `Element` to ONE parameterized type are
/// one view, and load. Passes either way by design — the fix makes agreement stricter
/// for DIFFERENT types, and one type is still one hash-consed `TermId`.
#[test]
fn a_parameterized_binding_written_twice_the_same_still_loads() {
    expect_loaded(try_load_kb_with(&one_carrier_two_provisions(
        "n3w68.p3.same",
        "List[T = String]",
        "List[T = String]",
    )));
}

/// One carrier reaching `Spec` through TWO intermediates, each binding `P` — the
/// `wi_gnpg7_transitive_provider_view_test` shape with structured values. `provides`
/// is the carrier's two lines, so a caller can swap them.
fn two_routes(ns: &str, via_a: &str, via_b: &str, provides: &str, want: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Spec
    sort P = ?
    operation touch(c: Spec) -> Int64
  end
  sort MidA
    sort A = ?
    provides Spec[P = {via_a}]
    operation touch(c: MidA) -> Int64 = 1
  end
  sort MidB
    sort B = ?
    provides Spec[P = {via_b}]
    operation touch(c: MidB) -> Int64 = 2
  end
  sort Carrier
    sort T = ?
    entity carrier(v: T)
{provides}
  end
  operation ti(c: Spec[P = {want}]) -> Int64 = 1
  operation drive(x: Carrier[T = Int64]) -> Int64 = ti(x)
end
"#
    )
}

const A_FIRST: &str = "    provides MidA[A = T]\n    provides MidB[B = T]";
const B_FIRST: &str = "    provides MidB[B = T]\n    provides MidA[A = T]";

/// MEASURED before the fix, for both value shapes: `Spec[P = …]` at `MidB`'s value was
/// REFUSED with `MidA` written first and LOADED with `MidB` first — the route merge kept
/// whichever route it walked first, because its agreement read the two values as one.
/// For the arrows that was not even the head sort: `load::sort_ref_functor` answers the
/// functor of any `Term::Fn`, and two arrows share one.
///
/// BACK-OUT (B), MEASURED: pointing the route merge back at its deleted copy (`TermId`
/// equality, else `load::sort_ref_functor` on both sides) fails this test and only this
/// one — `list, MidB first` and `arrow, MidB first` load clean. The one-carrier test above
/// never reaches the merge. Back-out (A) above opens the `list` row alone: the head-sort
/// compare it restores has no head for an arrow.
#[test]
fn two_routes_binding_different_structured_types_refuse_in_either_order() {
    // Every row is run before anything is asserted, so a back-out names ALL the rows it
    // opens rather than the first.
    let mut admitted = Vec::new();
    for (shape, via_a, via_b) in [
        ("list", "List[T = Int64]", "List[T = String]"),
        ("arrow", "(Int64) -> Int64", "(String) -> String"),
    ] {
        for (order, provides) in [("MidA first", A_FIRST), ("MidB first", B_FIRST)] {
            let src = two_routes(&format!("n3w68.p3r.{shape}"), via_a, via_b, provides, via_b);
            let errs = load_errors(&src);
            if !errs.iter().any(|e| e.contains("type mismatch in ti.c")) {
                admitted.push(format!("{shape}, {order}: {errs:?}"));
            }
        }
    }
    assert!(
        admitted.is_empty(),
        "two routes binding `P` to two different types disagree, so the composed view has \
         no answer and the argument is the ordinary located mismatch — under either \
         declaration order. Not refused that way:\n{}",
        admitted.join("\n")
    );
}

/// THE CONTROL: both routes binding `P` to ONE structured type agree, and the carrier is
/// accepted at it. Passes either way by design, like the one-carrier control.
#[test]
fn two_routes_binding_one_structured_type_still_load() {
    for (shape, value) in [("list", "List[T = String]"), ("arrow", "(String) -> String")] {
        expect_loaded(try_load_kb_with(&two_routes(
            &format!("n3w68.p3r.same.{shape}"),
            value,
            value,
            A_FIRST,
            value,
        )));
    }
}

// ── #6: the NARROW projection predicate walked a SHALLOWER tree ──────────────────
//
// `value_contains_expr_carried` (the predicate behind WI-20260909-S8CBV's two refusals)
// descended only `Parameterized` and `NamedTuple`; its wide twin
// `value_contains_projection` also descends `Arrow`, `EffectsRows` and `PolyType`. The two
// are now one walk that differs only in whether a `RigidTypeProjection` counts.
//
// THE TICKET'S SPELLING IS NOT WRITABLE: `requires Desc[T = (a: x.E) -> Int64]` is refused
// as `unresolved name '(a: x.E) -> Int64'` — an arrow does not lower in a `requires`
// binding at all, with or without a projection in it. The EFFECT ROW is the carrier that
// reaches the two refusals: `requires Desc[T = {x.E}]` lowers, and hides its `x.E` in the
// row.

/// The S8CBV fixture (`wi_s8cbv_projection_requirement_test`), trimmed to what the
/// refusal reads.
fn s8cbv_fixture(ns: &str, tail: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation tag() -> Int64
  end
  sort Red
    import anthill.prelude.Int64
    entity red
    provides Desc[T = Red]
    operation tag() -> Int64 = 7
  end
  sort Box
    sort E = ?
    entity box(v: E)
  end
{tail}
end
"#
    )
}

/// `outer` hands `pick` its own abstract parameter and declares nothing to forward, so no
/// call can supply `pick`'s requirement — the S8CBV caller-coverage refusal's own shape,
/// with the projection inside an effect row.
///
/// MEASURED before the fix: refused, but by the WRONG verdict. The narrow predicate saw no
/// projection, so the call fell to the STRUCTURAL-FORMER refusal, which read `{x.E}` as a
/// former nothing provides and told the author to write `provides Desc[… = {…x.E…}]` —
/// a provision over a projection, which no sort can declare. After it: the caller-coverage
/// refusal, which names the projection and the actual repair (annotate the caller with
/// this requirement, or pass a receiver whose member is known).
///
/// BACK-OUT, MEASURED: restoring the shallow walk (`Parameterized` / `NamedTuple` only)
/// fails this test and only this one in the file — the refusal reverts to
/// "a STRUCTURAL FORMER". The control below passes either way.
#[test]
fn a_projection_inside_an_effect_row_gets_the_projection_refusal() {
    let errs = load_errors(&s8cbv_fixture(
        "n3w68.p6.row",
        "  operation pick(x: Box) -> Int64 requires Desc[T = {x.E}] = Desc.tag()\n  \
         operation outer(b: Box) -> Int64 = pick(b)",
    ));
    let text = errs.join("\n");
    assert!(
        text.contains("its carrier is a projection this call does not ground")
            && !text.contains("STRUCTURAL FORMER"),
        "an `x.E` inside an effect row is still a projection this call cannot ground, and \
         the refusal must say so rather than call the row a former nothing provides:\n{text}"
    );
}

/// THE CONTROL: the same program with the projection written BARE (`Desc[T = x.E]`) — the
/// shape both walks always saw. Passes either way by design; it is what the row above is
/// read against.
#[test]
fn a_bare_projection_gets_the_same_refusal() {
    let errs = load_errors(&s8cbv_fixture(
        "n3w68.p6.bare",
        "  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()\n  \
         operation outer(b: Box) -> Int64 = pick(b)",
    ));
    let text = errs.join("\n");
    assert!(
        text.contains("its carrier is a projection this call does not ground"),
        "the S8CBV refusal for a bare projection:\n{text}"
    );
}

// ── #8: one question, two answers, chosen by cache warmth ────────────────────────
//
// `requires_chain_flat` returned `RequiresEntry`s from the flattened `requires_tree` when
// it was cached and from an unsubstituted global-visited walk when it was not; the two
// differed in multiplicity (and bindings), and `check_obligations` reported one obligation
// per entry. It is now `transitive_required_sorts`, returning each reachable sort once.

/// `A` requires `B` and `C`, both of which require `D`, which requires `E` — the shared
/// sub-requirement `D` and the tail under it are what the two paths walked differently.
/// Only `E` declares an operation, and `A` provides none of them.
const DIAMOND: &str = r#"
namespace n3w68.p8
  import anthill.prelude.Int64
  sort E
    sort T = ?
    operation e_op(x: T) -> Int64
  end
  sort D
    sort T = ?
    requires E[T = T]
  end
  sort B
    sort T = ?
    requires D[T = T]
  end
  sort C
    sort T = ?
    requires D[T = T]
  end
  sort A
    entity a
    requires B[T = A]
    requires C[T = A]
  end
end
"#;

/// MEASURED on this fixture with the old reader: COLD `[B, D, E, C, D]` (5 entries), WARM
/// `[B, D, E, C, D, E]` (6) — and `check_obligations(A)` reported ONE missing `e_op` cold
/// and TWO warm. Now both paths answer `[B, D, E, C]`, and the report is one obligation.
///
/// BACK-OUT, MEASURED: pointing `check_obligations` back at the old per-entry chain fails
/// this test at the obligation-count assertion (1 cold, 2 warm). The sort-list assertion
/// has no back-out of its own — the old reader did not return sorts — and it is what the
/// new reader is FOR: the same list on both paths, each sort once.
#[test]
fn the_required_sorts_do_not_depend_on_cache_warmth() {
    use anthill_core::kb::typing::{check_obligations, requires_chain, transitive_required_sorts};
    let mut kb = crate::common::load_kb_with(DIAMOND);
    let a = kb.resolve_symbol("n3w68.p8.A");
    let names = |kb: &anthill_core::kb::KnowledgeBase, sorts: &[anthill_core::intern::Symbol]| {
        sorts
            .iter()
            .map(|s| kb.local_name_of(*s).rsplit('.').next().unwrap().to_string())
            .collect::<Vec<_>>()
    };

    kb.invalidate_requires_chain_cache();
    let cold = transitive_required_sorts(&kb, a);
    let cold_obligations = check_obligations(&kb, a).len();

    let _ = requires_chain(&mut kb, a); // warms the tree cache for `A`
    let warm = transitive_required_sorts(&kb, a);
    let warm_obligations = check_obligations(&kb, a).len();

    assert_eq!(names(&kb, &cold), ["B", "D", "E", "C"], "each reachable sort once, depth-first");
    assert_eq!(cold, warm, "the answer must not depend on whether `requires_tree` ran first");
    assert_eq!(
        (cold_obligations, warm_obligations),
        (1, 1),
        "`A` owes `e_op` once, however many paths reach `E`"
    );
}

// ── #11: a NAMESPACE's `requires` was invisible to the requires readers ──────────
//
// A standalone `requires` in a namespace body is legal and emits a `SortRequiresInfo`
// fact scoped to the namespace (kernel-language.md, "Requires declaration"). Its
// `sort_ref` field is `make_name_term_from_sym(namespace)`, which the CZJ2N canon spells
// `Ref` for a non-sort owner — and both requires-side readers (`build_requires_index`,
// `collect_sort_requires`) decoded that field with a `Term::Fn` shape test, so both
// skipped it: a declared requirement nothing could read, with no diagnostic. They now
// decode it with `sort_ref_functor`, as every provides-side reader does.

const NAMESPACE_REQUIRES: &str = r#"
namespace n3w68.p11
  import anthill.prelude.Int64
  sort Spec
    sort T = ?
    operation f(x: T) -> Int64
  end
  requires Spec[T = Int64]
end
"#;

/// Both paths: the INDEX (built by the typer, so a full load) and the SCAN (a partial
/// `run_typer: false` load leaves the index unbuilt, and the per-sort reader scans).
///
/// MEASURED before the fix: both answered `[]`. BACK-OUT, MEASURED: restoring the shape
/// test in `collect_sort_requires` alone fails both rows — the index only BUCKETS the facts
/// and the scan's filter still reads every rid — and restoring it in `build_requires_index`
/// alone fails the full-load row, whose bucket then holds nothing for the namespace.
#[test]
fn a_namespace_requirement_is_visible_to_the_requires_readers() {
    use anthill_core::kb::typing::transitive_required_sorts;
    // Every row is run before anything is asserted, so a back-out names ALL the rows it
    // opens rather than the first.
    let mut missing = Vec::new();
    for (label, kb) in [
        ("full load (index)", crate::common::load_kb_with(NAMESPACE_REQUIRES)),
        (
            "partial load (scan)",
            crate::common::expect_loaded(crate::common::try_load_kb_untyped_with(
                NAMESPACE_REQUIRES,
            )),
        ),
    ] {
        let ns = kb.resolve_symbol("n3w68.p11");
        let spec = kb.resolve_symbol("n3w68.p11.Spec");
        let got = transitive_required_sorts(&kb, ns);
        if got != vec![spec] {
            missing.push(format!("{label}: {got:?}"));
        }
    }
    assert!(
        missing.is_empty(),
        "the namespace declared `requires Spec[T = Int64]`, and a reader answered otherwise:\n{}",
        missing.join("\n")
    );
}

// ── #9: the positional-to-parameter rule, spelled many ways ──────────────────────
//
// The ticket named one copy — `check_provider_requires`' positional fill, which TRUNCATED
// an extra positional with `zip`. Reproducing it found the family: the rule "a positional
// binds the next declared parameter not already bound by name" was spelled at every site
// that pairs positionals, some pairing by RAW INDEX instead. It now has one owner,
// `KnowledgeBase::positional_param_slots`.

/// `Spec2` declares `T` then `U`; `Use.takes` demands `Spec2[T = C, U = String]`.
fn spec2_provision(ns: &str, provides: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}
  sort Spec2
    sort T = ?
    sort U = ?
    operation f(x: T) -> U
  end
  sort C
    entity c
    provides {provides}
    operation f(x: C) -> String = "a"
  end
  sort Use
    operation takes(i: Spec2[T = C, U = String]) -> Int64 = 1
    operation go(n: Int64) -> Int64 = Use.takes(c())
  end
end
"#
    )
}

/// A MIXED spelling — a name first, then a positional — binds the positional to the next
/// FREE parameter, in a `provides` clause as in a type position.
///
/// MEASURED before the fix: `provides Spec2[T = C, String]` stored `T` twice and no `U`,
/// and the use at `Spec2[T = C, U = String]` was REFUSED ("expected Spec2[T = C, U =
/// String], got C"); `Spec[T = Map[K = Int64, String]]` diverted `String` out of the
/// binding VALUE, refused the same way. The all-named, all-positional and name-last
/// spellings loaded either way — they are the CONTROLS, and the raw-index pairing happened
/// to agree with the rule on each.
///
/// BACK-OUT, MEASURED: restoring the raw-index pairing in `sort_inst_to_value` fails the
/// `Spec2[T = C, String]` row; restoring it in `sort_binding_to_value` fails the
/// `Map[K = Int64, String]` row. Nothing else in this file moves under either.
#[test]
fn a_mixed_positional_binds_the_next_free_parameter() {
    let mut refused = Vec::new();
    for provides in [
        "Spec2[T = C, String]",
        "Spec2[T = C, U = String]",
        "Spec2[C, String]",
        "Spec2[U = String, C]",
    ] {
        let errs = load_errors(&spec2_provision("n3w68.p9.clause", provides));
        if !errs.is_empty() {
            refused.push(format!("provides {provides}: {errs:?}"));
        }
    }
    for value in [
        "Map[K = Int64, String]",
        "Map[K = Int64, V = String]",
        "Map[Int64, String]",
        "Map[V = String, Int64]",
    ] {
        let src = format!(
            r#"
namespace n3w68.p9.value
  import anthill.prelude.{{Int64, String, Map}}
  sort Spec
    sort T = ?
  end
  sort C
    entity c
    provides Spec[T = {value}]
  end
  sort Use
    operation takes(i: Spec[T = Map[K = Int64, V = String]]) -> Int64 = 1
    operation go(n: Int64) -> Int64 = Use.takes(c())
  end
end
"#
        );
        let errs = load_errors(&src);
        if !errs.is_empty() {
            refused.push(format!("provides Spec[T = {value}]: {errs:?}"));
        }
    }
    assert!(
        refused.is_empty(),
        "every spelling here names the same provision — a positional binds the next \
         parameter no name took:\n{}",
        refused.join("\n")
    );
}

/// An OVER-APPLIED parametric spec in a `provides` clause is refused where it is written.
///
/// MEASURED before the fix: `provides Spec2[C, String, Bool]` loaded CLEAN — the loader
/// carried `Bool` as a `SortView` positional, and `check_provider_requires` zipped it away.
///
/// BACK-OUT, MEASURED: removing the arity refusal from `sort_inst_to_value` fails this test
/// (the program loads clean). The control below passes either way.
#[test]
fn an_over_applied_provision_is_refused_where_it_is_written() {
    let errs = load_errors(&spec2_provision("n3w68.p9.over", "Spec2[C, String, Bool]"));
    let text = errs.join("\n");
    assert!(
        text.contains("invalid type argument") && text.contains("over-applied"),
        "three positionals for two parameters:\n{text}"
    );
}

/// An over-applied parametric spec in an OPERATION's `requires` is refused as well — the
/// loader's arity gate exempted the clause as a top-level term.
///
/// MEASURED before the fix: `operation g(x: C) -> Int64 requires Spec2[C, String, Bool]`
/// loaded CLEAN, and every reader of the op-scoped entry dropped `Bool`
/// (`goal_from_op_requires_entry` answered no goal at all).
///
/// BACK-OUT, MEASURED: removing the op-contract branch of `convert_term`'s arity gate fails
/// this test (the program loads clean).
///
/// THE BOUNDARY'S CONTROLS live elsewhere, and are measured: an `ensures` clause names its
/// existential CARRIER as a leftover positional (`-> C ensures KVStore[C, K = String, V =
/// String]`, WI-402), so a first cut that gated every top-level application failed all of
/// `wi402_existential_return_test` and `wi954_published_type_param_var_test` (10 rows).
/// The gate is scoped to `requires`, and they pass.
#[test]
fn an_over_applied_op_requirement_is_refused_where_it_is_written() {
    let src = r#"
namespace n3w68.p9.opreq
  import anthill.prelude.{Int64, String, Bool}
  sort Spec2
    sort T = ?
    sort U = ?
  end
  sort C
    entity c
  end
  operation g(x: C) -> Int64 requires Spec2[C, String, Bool] = 1
end
"#;
    let text = load_errors(src).join("\n");
    assert!(
        text.contains("invalid type argument") && text.contains("over-applied"),
        "three positionals for two parameters, in an operation's `requires`:\n{text}"
    );
}

/// THE CONTROL: on a spec with NO type parameters a positional is the WI-407 carrier slot,
/// not an over-application, and a `provides` clause writing one still loads. Passes either
/// way by design.
#[test]
fn a_positional_on_a_parameterless_spec_is_still_the_carrier_slot() {
    expect_loaded(try_load_kb_with(
        r#"
namespace n3w68.p9.slot
  sort Marker
  end
  sort C
    entity c
    provides Marker[C]
  end
end
"#,
    ));
}
