//! WI-20260829-GNPG7 — A SPEC VIEW ADMITS A CARRIER THAT PROVIDES IT TRANSITIVELY.
//!
//! THE TICKET WAS FILED AS A QUESTION and its table measured the wrong axis. It read, off
//! five rows with one argument (`rs: List[T = Row]`):
//!
//!   * `ti(c: Iterable)` LOADS, `ti(c: Iterable[Element = Row])` REFUSED
//!   * `ti(c: Stream)` LOADS, `ti(c: Stream[T = Row, E = {}])` LOADS
//!
//! and concluded "what changes the verdict is only whether the parameter's spec type
//! carries BINDINGS", leaving open whether that was a gap (a) or the design (b) — "a spec
//! type with bindings is a VIEW, structurally distinct from the carrier".
//!
//! IT IS A CONFOUND. Those rows also differ in HOP COUNT. `List` declares `provides
//! Stream[T, {}]` (list.anthill) and reaches `Iterable` only through `Stream provides
//! Iterable[C = Stream, Element = T, E = E]` (stream.anthill); it never declares `provides
//! Iterable`. So every refusing row is 2-hop and the accepting `Stream` row is 1-hop, and
//! the table cannot tell the two explanations apart.
//!
//! `a_direct_provider_accepts_the_fully_bound_spec_view` IS THE SEPARATOR, and it refutes
//! (b) outright: `MutableStack` declares `provides Iterable[C = MutableStack[T], Element =
//! T, E = {}]` itself, and a `MutableStack[T = Row]` is admissible at
//! `Iterable[C = MutableStack[T = Row], Element = Row, E = {}]` — the fully-bound spec view
//! NAMING ITS OWN CARRIER, which is exactly the shape (b) says must be a distinct view.
//! Same spec, same binding shape, opposite verdict from `List`. Bindings were never the
//! axis.
//!
//! THE CAUSE — one relation, two readers, disagreeing on transitivity. The bare-spec arms
//! reach `sort_provides_admissibly` → `sort_provides` → `sort_provides_reach`, which WALKS
//! the provision chain. The bindings-carrying arms read `provider_spec_view_bindings`,
//! which matches a single DIRECT `SortProvidesInfo` fact. Both subtype sites now go through
//! `transitive_provider_spec_view_bindings`, the composer that already existed for exactly
//! this chain — its sibling `transitive_provision_view`'s doc names "`List provides Stream`
//! + `Stream provides Iterable`, with no direct `List provides Iterable` fact" as the case
//! it is for (WI-495/WI-714). Nothing new was built; two readers were pointed at the
//! answer the third already had.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT (both `transitive_provider_spec_view_bindings`
//! calls restored to `provider_spec_view_bindings`):
//!
//!   * `a_two_hop_carrier_conforms_to_a_bound_spec_view` — RED, both rows.
//!   * `a_bare_two_hop_carrier_conforms_to_a_bound_spec_view` — RED. It is the SECOND
//!     SITE: `bare_provider_binding_precise`, reached when the actual is a bare sort_ref
//!     (`nil()` : `List`) rather than parameterized. One gap, two arms — measured
//!     separately because they are separate call sites and a fix to one says nothing
//!     about the other. THE ATTRIBUTION IS MEASURED, not assumed: backing out ONLY the
//!     `parameterized_compatible_view` site reddens only the first test and leaves this
//!     one green, so the pair is not two spellings of one fixture.
//!   * `a_direct_provider_accepts_the_fully_bound_spec_view` — GREEN EITHER WAY, by
//!     design. One hop needs no composition. It is the control that makes the rows above
//!     attributable to transitivity rather than to bindings, and it is the row that
//!     settles the ticket's design question.
//!   * `the_carrier_param_of_a_composed_view_names_the_carrier` — the ONE row that did not
//!     move with this ticket (refused before and after). Its separate cause was the
//!     composed view keeping the intermediate's SELF-reference in the carrier param, and
//!     WI-20260829-XZMGC closed it; the assertion is flipped to LOADS and the test kept, so
//!     backing THIS ticket out still reddens it — for the original reason, the chain being
//!     unreachable at all.
//!
//! MEASURED ACROSS THE WORKSPACE: routing both sites through the transitive reader moved
//! exactly ONE test, `typer_capability_matrix_test::a_spec_typed_parameter_and_its_carrier`
//! — the ticket's own cell, whose failure message asks to be updated when GNPG7 is settled.
//! 6126 passed / 1 failed before that cell was rewritten; no other row in the corpus
//! changed verdict.
//!
//! WI-20261005-KSSA4 — THE ROWS OVER `Iterable` ARE WRITTEN AS REQUIREMENTS NOW. `Iterable`
//! is a spec over its parameter `C`: a `List` provides it and is not one, so `ti(c:
//! Iterable[Element = Row])` no longer takes a `List` and the subtype relation is not asked
//! about its provision view ([`a_carrier_is_not_a_value_of_the_spec_it_provides`]). What
//! the rows measured — that a carrier's view of a spec is composed through the chain, with
//! its bindings — is asked where a requirement is SUPPLIED: `ti[P](c: P) requires
//! Iterable[C = P, Element = Row]` called with a `List[T = Row]`. The back-out ledger
//! above was measured on the spec-typed spelling and describes the subtype relation's
//! reader. RE-MEASURED on these rows, with that reader's provider view read one hop deep:
//! [`a_bare_two_hop_carrier_conforms_to_a_bound_spec_view`] and
//! [`provision_routes_do_not_depend_on_declaration_order`] fail — both over specs that are
//! their own carriers — with `wi_xzmgc`'s two rows of the same kind, its rule-bound row
//! (a bound reads `Iterable` as standing for its providers, through the chain), and
//! `wi_n3w68 …two_routes_binding_one_structured_type_still_load`. The requirement rows
//! over `Iterable` pass either way: a requirement is supplied by resolution, which
//! composes the chain itself.

use crate::common::{expect_loaded, try_load_kb_with};

/// The two-hop carrier is `List`, reaching `Iterable` through `Stream`.
fn program(param: &str, arg_ty: &str) -> String {
    format!(
        r#"
namespace test.gnpg7
  import anthill.prelude.{{Int64, Bool, List, Iterable, Stream, MutableStack}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
  end
  operation ti(c: {param}) -> Int64 = 1
  operation drive(rs: {arg_ty}) -> Int64 = ti(rs)
end
"#
    )
}

/// [`program`] with the consumer written over ANY sort that provides the spec: `c` is a
/// value of `P`, and `requirement` — a spec bound at `C = P` — is required of `P`.
fn bound_program(requirement: &str, arg_ty: &str) -> String {
    format!(
        r#"
namespace test.gnpg7
  import anthill.prelude.{{Int64, Bool, List, Iterable, Stream, MutableStack}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
  end
  operation ti[P](c: P) -> Int64 requires {requirement} = 1
  operation drive(rs: {arg_ty}) -> Int64 = ti(rs)
end
"#
    )
}

fn load_errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(es) => es.iter().map(|e| e.to_string()).collect(),
    }
}

/// The ticket's row 3, and the effect-row spelling beside it. `Element` composes through
/// the chain to `List.T`, which this instance binds to `Row`; `E` composes to the `{}`
/// that `List provides Stream[T, {}]` supplies.
#[test]
fn a_two_hop_carrier_conforms_to_a_bound_spec_view() {
    for requirement in [
        "Iterable[C = P, Element = Row]",
        "Iterable[C = P, Element = Row, E = {}]",
    ] {
        expect_loaded(try_load_kb_with(&bound_program(requirement, "List[T = Row]")));
    }

    // CONTROL — the spec with only its carrier written, which the chain has always
    // answered.
    expect_loaded(try_load_kb_with(&bound_program("Iterable[C = P]", "List[T = Row]")));

    // AND THE BINDINGS ARE COMPARED, not merely carried: a `List[T = Row]` walks `Row`s,
    // so the requirement at another element is one nothing supplies.
    let errs = load_errors(&bound_program("Iterable[C = P, Element = Bool]", "List[T = Row]"));
    assert!(
        errs.iter().any(|e| e.contains("requirement `anthill.prelude.Iterable[C = anthill.prelude.List[T = test.gnpg7.Row], Element = anthill.prelude.Bool")
            && e.contains("cannot be supplied for call to `test.gnpg7.ti`")),
        "a requirement at the wrong element is refused, naming it: {errs:?}"
    );
}

/// THE SPEC-TYPED SPELLING OF THE SAME ROWS. `Iterable` is a spec over `C`; a `List`
/// provides it, so `Iterable`'s operations may be used on a `List`, and that does not make
/// a `List` an `Iterable`. Refused at the argument, with or without bindings, naming the
/// spelling that says "a value of a sort that provides it".
#[test]
fn a_carrier_is_not_a_value_of_the_spec_it_provides() {
    for param in [
        "Iterable",
        "Iterable[Element = Row]",
        "Iterable[C = List[T = Row], Element = Row, E = {}]",
    ] {
        let errs = load_errors(&program(param, "List[T = Row]"));
        assert!(
            errs.iter().any(|e| e.contains("ti.c (op-arg): expected Iterable")
                && e.contains("got List[T = Row] — `anthill.prelude.Iterable` is a spec over its parameter `C`")
                && e.contains("Type this position `anthill.prelude.Iterable.C`")),
            "`{param}` must refuse a `List`, naming `Iterable.C`: {errs:?}"
        );
    }
    // A sort that receives on itself is its own carrier, and a `List` is one of those.
    expect_loaded(try_load_kb_with(&program("Stream", "List[T = Row]")));
    expect_loaded(try_load_kb_with(&program("Stream[T = Row, E = {}]", "List[T = Row]")));
}

/// THE SECOND SITE. A BARE actual (a constructor with no arguments, whose type is its sort
/// with no bindings) reaches `bare_provider_binding_precise`, not
/// `parameterized_compatible_view`. Its provider lookup was one-hop for the same reason and
/// is now transitive too.
///
/// The parameter writes ONLY the effect row, which is the binding the provision chain
/// determines without help from the actual: a bare `Deep` offers no `D`, so an element
/// binding genuinely could not be satisfied here and is not what this row is about. Holding
/// the available information fixed is what makes hop count the only difference between the
/// two rows.
///
/// OVER A SPEC THAT IS ITS OWN CARRIER (WI-20261005-KSSA4): the rows were `Stream[E = {}]`
/// and `Iterable[E = {}]` at `nil()`, and a `List` is no value of the second. `Mid` and
/// `Walk` receive on `Self`, so a `Deep` is a `Mid` in one hop and a `Walk` in two. FAILS
/// with the provider view read one hop deep (re-measured on this fixture).
#[test]
fn a_bare_two_hop_carrier_conforms_to_a_bound_spec_view() {
    let src = |param: &str| {
        format!(
            r#"
namespace test.gnpg7_bare
  import anthill.prelude.{{Int64}}
  sort Walk
    import anthill.prelude.Int64
    sort Element = ?
    effects WE = ?
    operation steps(w: Self) -> Int64
  end
  sort Mid
    import anthill.prelude.Int64
    sort Item = ?
    effects ME = ?
    provides Walk[Element = Item, WE = {{}}]
    operation steps(w: Self) -> Int64 = 2
  end
  sort Deep
    import anthill.prelude.Int64
    sort D = ?
    entity deep(d: D)
    entity hollow
    provides Mid[Item = D, ME = {{}}]
    operation steps(w: Self) -> Int64 = 3
  end
  import test.gnpg7_bare.Deep.{{hollow}}
  operation ti(c: {param}) -> Int64 = 1
  operation drive() -> Int64 = ti(hollow())
end
"#
        )
    };
    // CONTROL, one hop: `Deep provides Mid` directly. Green either way.
    expect_loaded(try_load_kb_with(&src("Mid[ME = {}]")));
    // Two hops, same binding, same information available.
    expect_loaded(try_load_kb_with(&src("Walk[WE = {}]")));
}

/// THE ROW THAT SETTLES THE DESIGN QUESTION. `MutableStack` provides `Iterable` DIRECTLY,
/// binding `C` to its own carrier, and the fully-bound spec view naming that carrier is
/// admissible. Reading (b) of the ticket — "a spec type with bindings is a VIEW,
/// structurally distinct from the carrier, and an author who wants one writes the
/// conversion" — has to refuse this, and the loader accepts it.
///
/// GREEN EITHER WAY across this ticket's change: one hop needs no composition. That is
/// precisely its value — it holds the spec and the binding shape fixed against the `List`
/// rows above so their movement is attributable to hop count and to nothing else.
#[test]
fn a_direct_provider_accepts_the_fully_bound_spec_view() {
    for requirement in [
        "Iterable[C = P, Element = Row]",
        "Iterable[C = P, Element = Row, E = {}]",
    ] {
        expect_loaded(try_load_kb_with(&bound_program(
            requirement,
            "MutableStack[T = Row]",
        )));
    }
}

/// TWO ROUTES TO ONE SPEC ARE NOT DECIDED BY SOURCE ORDER. Found by /code-review on the
/// first cut, and DRIVEN twice — the second time against the FIX for the first, which is
/// why this test now carries two shapes:
///
///   * SAME PARAM, DIFFERENT VALUES (`MidA provides Spec[P = Int64]`, `MidB provides
///     Spec[P = Bool]`). `transitive_provider_spec_view_bindings` returns the FIRST
///     intermediate that reaches the spec, so swapping the two `provides` lines and
///     changing nothing else flipped `Spec[P = Bool]` from REFUSED to LOADS.
///   * DISJOINT PARAMS (`MidA provides Spec[P = Int64]`, `MidB provides Spec[Q = Bool]`).
///     The first repair checked the routes for CONFLICTS and then returned one of them —
///     and two views with no labels in common trivially "agree", so the answer was still
///     whichever route came last. MEASURED: `Spec[Q = Bool]` loaded under one ordering and
///     was refused under the other, and `Spec[P = Int64]` did the reverse.
///
/// `subtype_provider_view` now MERGES every reachable route and answers `None` only on a
/// genuine per-param disagreement, which is order-independent by construction. Both shapes
/// are asserted in BOTH orderings, because one ordering of each passes under the defect —
/// a single ordering would measure nothing.
///
/// Before this ticket the subtype relation had no transitive route at all, so every row
/// here was refused; the determinism property is one this ticket had to supply, not one it
/// inherited.
#[test]
fn provision_routes_do_not_depend_on_declaration_order() {
    let program = |spec_body: &str, mid_a: &str, mid_b: &str, provides: &str, want: &str| {
        format!(
            r#"
namespace test.gnpg7_routes
  import anthill.prelude.{{Int64, Bool}}
  sort Spec
{spec_body}
    operation touch(c: Self) -> Int64
  end
  sort MidA
    sort A = ?
    provides Spec[{mid_a}]
    operation touch(c: Self) -> Int64 = 1
  end
  sort MidB
    sort B = ?
    provides Spec[{mid_b}]
    operation touch(c: Self) -> Int64 = 2
  end
  sort Carrier
    sort T = ?
    entity carrier(v: T)
{provides}
  end
  operation ti(c: Spec[{want}]) -> Int64 = 1
  operation drive(x: Carrier[T = Int64]) -> Int64 = ti(x)
end
"#
        )
    };
    let a_first = "    provides MidA[A = T]\n    provides MidB[B = T]";
    let b_first = "    provides MidB[B = T]\n    provides MidA[A = T]";

    // (1) SAME PARAM, DIFFERENT VALUES — a genuine disagreement, refused BOTH ways, and
    // the refusal is the ordinary located mismatch at the argument (not merely "some
    // error": a bare `is_empty()` check would pass if the fixture stopped loading for an
    // unrelated reason).
    for (label, provides) in [("MidA first", a_first), ("MidB first", b_first)] {
        let errs = load_errors(&program(
            "    sort P = ?",
            "P = Int64",
            "P = Bool",
            provides,
            "P = Bool",
        ));
        assert!(
            errs.iter().any(|e| e.contains("expected Spec[P = Bool]")),
            "{label}: two routes binding `P` differently must refuse, by the located \
             argument mismatch: {errs:?}"
        );
    }

    // (2) DISJOINT PARAMS — no disagreement, so the routes MERGE and each param is
    // available from the route that supplies it, under either ordering.
    for (label, provides) in [("MidA first", a_first), ("MidB first", b_first)] {
        for want in ["P = Int64", "Q = Bool"] {
            expect_loaded(try_load_kb_with(&program(
                "    sort P = ?\n    sort Q = ?",
                "P = Int64",
                "Q = Bool",
                provides,
                want,
            )));
        }
    }

    // (3) THE SINGLE-ROUTE CONTROL, so the rows above measure the merge and not the
    // fixture: one intermediate, nothing to disagree with, loads clean.
    expect_loaded(try_load_kb_with(&program(
        "    sort P = ?",
        "P = Int64",
        "P = Int64",
        "    provides MidA[A = T]",
        "P = Int64",
    )));
}

/// THE ONE ROW THAT DID NOT MOVE WITH THIS TICKET, kept as the boundary marker between the
/// two defects on this chain. It refused BEFORE and AFTER the transitive routing — so it
/// measures nothing about that routing — and it was closed separately by
/// WI-20260829-XZMGC.
///
/// The cause was the SECOND defect: `Stream provides Iterable[C = Stream, …]` binds `C` to
/// STREAM ITSELF, and `compose_provision_views` substitutes the intermediate's PARAMS but
/// keeps a non-param value verbatim — its own doc names `C ↦ Stream` as that case — so the
/// composed view for `List` said `C = Stream`. `subtype_provider_view` now excludes the
/// carrier param from a composed view and its callers supply the actual;
/// `wi_xzmgc_composed_carrier_param_test` owns the rows.
///
/// KEPT AND FLIPPED rather than deleted, because the pairing is what makes THIS ticket's
/// attribution legible: with the carrier binding still refusing, the four rows that moved
/// here moved for transitivity alone. Backing out GNPG7 reddens it again — the argument is
/// refused for the ORIGINAL reason, since a `List` reaches `Iterable` only through the
/// chain.
#[test]
fn the_carrier_param_of_a_composed_view_names_the_carrier() {
    // The requirement written AT the carrier, every element stated: it is constructed
    // from `List`'s composed provision, whose carrier is the list and not the `Stream`
    // the chain passes through.
    let at_the_carrier = |requirement: &str| {
        format!(
            r#"
namespace test.gnpg7_at
  import anthill.prelude.{{Int64, Bool, List, Iterable, Stream}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
  end
  operation ti(c: List[T = Row]) -> Int64 requires {requirement} = 1
  operation drive(rs: List[T = Row]) -> Int64 = ti(rs)
end
"#
        )
    };
    expect_loaded(try_load_kb_with(&at_the_carrier(
        "Iterable[C = List[T = Row], Element = Row, E = {}]",
    )));
}
