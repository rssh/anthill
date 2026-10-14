//! WI-20261013-9HKJV — a `default provides` at a TUPLE or an ARROW arbitrates as one at a sort.
//!
//! `sort Apply { sort F = ?  operation run(f: F) -> Int64 }`, `P1` and `P2` both providing it
//! at `F = (Int64, Int64)`, `P1` marked default: a call that says nothing,
//! `Apply.run((1, 2))`, takes `P1` — 10. It was refused, "2 instances provide `Apply` (P1, P2)
//! and the call selects none" (MEASURED): the defaults index keyed a row by its carrier's base
//! SORT, a tuple has none, and the mark was filed at carrier `P1` — the provider's own name, a
//! row no goal asks for — so it was read by nothing, and two marks at one tuple were not
//! refused.
//!
//! The reading (proposed to the user on 2026-10-13 and taken on their "continue"): the mark
//! means the same at every carrier. Where a provision's dictionary dispatches is now one classifier
//! (`provision_dispatch_carrier`: the provider itself, another sort, or a type that is no sort),
//! read by the `default_provider` relation's builtin and by the index, which files a
//! structural carrier under its head; and two carriers overlap as the provision lookup pairs
//! them (`carrier_views_overlap`): two arrows where their parameter lists pair — the names
//! lining up, or one list written without names — and two tuples where their labels are one.
//! That pairing is no equivalence, and it is asked of two carriers at a time: two marks at
//! `(a: Int64, b: Int64) -> Int64` and `(x: Int64, y: Int64) -> Int64` coexist, and a call at
//! `(Int64, Int64) -> Int64`, served by both, takes neither.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS and its value says which provider
//! answered (`P1` 10, `P2` 30); a refusal is asserted by the words that name it.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! FOUR PARTS, each backed out in place and RUN over this file's 10 rows and the suites beside
//! it — `wi860`, `wi861`, `wi862`, `wi508`, `wi_x9pb4` and `wi_4dyr6`, 105 rows in all:
//!
//! 1. A CARRIER BINDING THAT IS A TUPLE OR AN ARROW IS A WITNESS (`provision_structural_carrier`
//!    answering nothing, so the classifier reads the provider). 8 FAIL:
//!    [`a_default_at_a_tuple_or_an_arrow_answers_the_call`],
//!    [`a_requirement_at_a_tuple_takes_the_default`],
//!    [`a_default_at_an_aliased_tuple_answers_the_call`],
//!    [`two_defaults_at_one_tuple_or_arrow_are_a_load_error`],
//!    [`two_arrows_are_one_carrier_where_their_parameter_lists_pair`],
//!    [`two_tuples_are_one_carrier_where_their_labels_are_one`],
//!    [`the_relation_and_the_index_hold_the_row_at_the_tuple`] and, at its tuple,
//!    [`a_default_for_a_spec_receiving_on_no_parameter_answers_the_call`].
//! 2. SUCH A CARRIER HAS A BUCKET, ITS HEAD (`structural_bucket` answering nothing): the same
//!    8 FAIL — the row is filed nowhere and a goal at the tuple asks nowhere.
//! 3. TWO ARROWS, AND TWO TUPLES, OVERLAP AS THE LOOKUP PAIRS THEM (`carrier_views_overlap`
//!    comparing them by structure, as before). 2 FAIL:
//!    [`two_arrows_are_one_carrier_where_their_parameter_lists_pair`] — a mark at a named list
//!    no longer answers a call at the unnamed one — and
//!    [`two_tuples_are_one_carrier_where_their_labels_are_one`] — a mark at `(E, Int64)` beside
//!    one at `(Int64, Int64)` loads.
//! 4. A PROVISION'S CARRIER PARAMETER IS READ AS A GOAL'S (`provision_dispatch_carrier` asking
//!    `spec_carrier_param` alone, the parameter some operation receives on). 1 FAILS:
//!    [`a_default_for_a_spec_receiving_on_no_parameter_answers_the_call`].
//!
//! PASS EITHER WAY, BY DESIGN: [`a_provider_at_a_tuple_with_no_mark_is_not_reported`] and
//! [`the_mark_at_a_sort_answers_as_before`], the ticket's controls.

use crate::common::{assert_refused_naming, load_errors_of, run_int64, try_load_kb_with};

/// What a row varies: declarations above `Apply`, each provider's mark and carrier, facts
/// below them, and — when there is one — the call's parameter type and the value `go` passes.
struct Shape<'a> {
    above: &'a str,
    p1: (&'a str, &'a str),
    p2: (&'a str, &'a str),
    facts: &'a str,
    call: Option<(&'a str, &'a str)>,
}

const PAIR: &str = "(Int64, Int64)";
const ARROW: &str = "(Int64, Int64) -> Int64";
const NAMED_AB: &str = "(a: Int64, b: Int64) -> Int64";
const NAMED_XY: &str = "(x: Int64, y: Int64) -> Int64";
const PAIR_VALUE: &str = "(1, 2)";
const ARROW_VALUE: &str = "lambda (a: Int64, b: Int64) -> a + b";

fn program(ns: &str, shape: &Shape<'_>) -> String {
    let Shape {
        above,
        p1: (m1, f1),
        p2: (m2, f2),
        facts,
        call,
    } = shape;
    let call = match call {
        Some((ty, value)) => format!(
            "  operation via(f: {ty}) -> Int64 = Apply.run(f)\n  operation go() -> Int64 = via({value})\n"
        ),
        None => String::new(),
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
{above}
  sort Apply
    sort F = ?
    operation run(f: F) -> Int64
  end
  sort P1
    {m1}provides Apply[F = {f1}]
    operation run(f: {f1}) -> Int64 = 10
  end
  sort P2
    {m2}provides Apply[F = {f2}]
    operation run(f: {f2}) -> Int64 = 30
  end
{facts}
{call}end
"#
    )
}

/// `program`, run to its `go`.
fn runs(ns: &str, shape: &Shape<'_>) -> Result<i64, String> {
    run_int64(&program(ns, shape), &format!("{ns}.go"))
}

/// THE TICKET'S (1), (2), (3): the mark at a tuple, the same at an arrow, and the default
/// declared by reference, `fact DefaultProvider(spec: Apply, provider: P1)`, at the tuple — `P1`
/// answers, 10. All three were refused as a tie (MEASURED).
#[test]
fn a_default_at_a_tuple_or_an_arrow_answers_the_call() {
    for (tag, carrier, value) in [("tuple", PAIR, PAIR_VALUE), ("arrow", ARROW, ARROW_VALUE)] {
        let shape = Shape {
            above: "",
            p1: ("default ", carrier),
            p2: ("", carrier),
            facts: "",
            call: Some((carrier, value)),
        };
        assert_eq!(runs(&format!("wi9hkjv.marked_{tag}"), &shape), Ok(10), "{tag}");
    }
    let shape = Shape {
        above: "",
        p1: ("", PAIR),
        p2: ("", PAIR),
        facts: "  fact anthill.reflect.typing.DefaultProvider(spec: Apply, provider: P1)",
        call: Some((PAIR, PAIR_VALUE)),
    };
    assert_eq!(runs("wi9hkjv.by_reference", &shape), Ok(10));
}

/// … AND AT A TUPLE WRITTEN THROUGH AN ALIAS, `sort IntPair = (Int64, Int64)`: the mark is at
/// the type the alias stands for — 10.
#[test]
fn a_default_at_an_aliased_tuple_answers_the_call() {
    let shape = Shape {
        above: "  sort IntPair = (Int64, Int64)",
        p1: ("default ", "IntPair"),
        p2: ("", PAIR),
        facts: "",
        call: Some((PAIR, PAIR_VALUE)),
    };
    assert_eq!(runs("wi9hkjv.alias", &shape), Ok(10));
}

/// THE TICKET'S (4): BOTH providers marked at one tuple — and at one arrow — is a load error
/// naming both and the carrier, with a call and without one. Both loaded clean without a call,
/// and with one were refused as the tie alone (MEASURED).
#[test]
fn two_defaults_at_one_tuple_or_arrow_are_a_load_error() {
    for (tag, carrier, value, shown) in [
        ("tuple", PAIR, PAIR_VALUE, "(_1: Int64, _2: Int64)"),
        ("arrow", ARROW, ARROW_VALUE, "(_1: Int64, _2: Int64) -> Int64"),
    ] {
        for call in [None, Some((carrier, value))] {
            let shape = Shape {
                above: "",
                p1: ("default ", carrier),
                p2: ("default ", carrier),
                facts: "",
                call,
            };
            let src = program(&format!("wi9hkjv.both_{tag}_{}", call.is_some()), &shape);
            assert_refused_naming(
                &load_errors_of(&src),
                &[
                    "ambiguous default",
                    &format!("carrier '{shown}'"),
                    "P1' at carrier",
                    "P2' at carrier",
                ],
                &format!("two marks at one {tag}, a call: {}", call.is_some()),
            );
        }
    }
}

/// A PROVIDER AT A TUPLE WITH NO MARK IS NOT REPORTED: the two providers load clean, and a
/// call that says nothing is the tie it always was. Passes either way by design.
#[test]
fn a_provider_at_a_tuple_with_no_mark_is_not_reported() {
    let mut shape = Shape {
        above: "",
        p1: ("", PAIR),
        p2: ("", PAIR),
        facts: "",
        call: None,
    };
    assert!(load_errors_of(&program("wi9hkjv.unmarked", &shape)).is_empty());
    shape.call = Some((PAIR, PAIR_VALUE));
    assert_refused_naming(
        &load_errors_of(&program("wi9hkjv.unmarked_call", &shape)),
        &["Apply.run`: 2 instances provide", ".P2) and the call selects none"],
        "two unmarked providers at one tuple",
    );
}

/// THE CONTROLS, AT A SORT: the mark at `Box[T = Int64]` and at `Int64` answers — 10 — and two
/// marks at `Box[T = Int64]` are a load error, with a call and without. Passes either way by
/// design.
#[test]
fn the_mark_at_a_sort_answers_as_before() {
    let boxed = "  sort Box\n    sort T = ?\n    entity box(v: T)\n  end";
    for (tag, above, carrier, value) in [
        ("box", boxed, "Box[T = Int64]", "Box.box(v: 1)"),
        ("int", "", "Int64", "1"),
    ] {
        let shape = Shape {
            above,
            p1: ("default ", carrier),
            p2: ("", carrier),
            facts: "",
            call: Some((carrier, value)),
        };
        assert_eq!(runs(&format!("wi9hkjv.sort_{tag}"), &shape), Ok(10), "{tag}");
    }
    for call in [None, Some(("Box[T = Int64]", "Box.box(v: 1)"))] {
        let shape = Shape {
            above: boxed,
            p1: ("default ", "Box[T = Int64]"),
            p2: ("default ", "Box[T = Int64]"),
            facts: "",
            call,
        };
        let src = program(&format!("wi9hkjv.sort_both_{}", call.is_some()), &shape);
        assert_refused_naming(
            &load_errors_of(&src),
            &["ambiguous default", "carrier 'Box[T = Int64]'"],
            &format!("two marks at one sort, a call: {}", call.is_some()),
        );
    }
}

/// TWO ARROWS ARE ONE CARRIER WHERE THEIR PARAMETER LISTS PAIR, asked of two at a time:
///
///  * `P1` marked at `(a: Int64, b: Int64) -> Int64`, `P2` unmarked at the unnamed list or at
///    `(x: Int64, y: Int64) -> Int64`: a call at the unnamed list is served by both and takes
///    the mark — 10, where each was the tie (MEASURED);
///  * both marked, at the two named lists: they coexist at load — the two lists do not pair —
///    and the call at the unnamed list, served by both, takes neither and is the tie; a call at
///    `(a: Int64, b: Int64) -> Int64` is served by `P1` alone — 10;
///  * both marked, at `(a: Int64, b: Int64) -> Int64` and the unnamed list: those pair, and
///    the two marks are a load error.
#[test]
fn two_arrows_are_one_carrier_where_their_parameter_lists_pair() {
    let one_mark = |f2: &'static str| Shape {
        above: "",
        p1: ("default ", NAMED_AB),
        p2: ("", f2),
        facts: "",
        call: Some((ARROW, ARROW_VALUE)),
    };
    assert_eq!(runs("wi9hkjv.pair_unnamed", &one_mark(ARROW)), Ok(10));
    assert_eq!(runs("wi9hkjv.pair_other", &one_mark(NAMED_XY)), Ok(10));

    let both = |call: Option<(&'static str, &'static str)>| Shape {
        above: "",
        p1: ("default ", NAMED_AB),
        p2: ("default ", NAMED_XY),
        facts: "",
        call,
    };
    assert!(load_errors_of(&program("wi9hkjv.pair_both", &both(None))).is_empty());
    assert_refused_naming(
        &load_errors_of(&program("wi9hkjv.pair_both_unnamed", &both(Some((ARROW, ARROW_VALUE))))),
        &["Apply.run`: 2 instances provide", ".P2) and the call selects none"],
        "two marks at two named lists, a call at the unnamed one",
    );
    assert_eq!(
        runs("wi9hkjv.pair_both_named", &both(Some((NAMED_AB, ARROW_VALUE)))),
        Ok(10)
    );

    let pairing = Shape {
        above: "",
        p1: ("default ", NAMED_AB),
        p2: ("default ", ARROW),
        facts: "",
        call: None,
    };
    assert_refused_naming(
        &load_errors_of(&program("wi9hkjv.pair_collide", &pairing)),
        &["overlapping defaults", "P1' at carrier", "P2' at carrier"],
        "two marks at a named list and the unnamed one",
    );
}

/// TWO TUPLES ARE ONE CARRIER WHERE THEIR LABELS ARE ONE: a named tuple is another type than
/// the positional one, so a mark at `(a: Int64, b: Int64)` beside one at `(Int64, Int64)` loads,
/// and a call at the positional tuple, served by `P2` alone, answers 30. A mark at `(E, Int64)`
/// — `E` a parameter of `P1` — overlaps `(Int64, Int64)`: beside a mark there it is a load
/// error. Alone, beside an unmarked `P2` at `(Int64, Int64)`, it does not answer the call at
/// `(Int64, Int64)`: `P2`'s carrier is the more specific, and specificity ranks before the
/// default, which only arbitrates a tie — 30.
#[test]
fn two_tuples_are_one_carrier_where_their_labels_are_one() {
    let named = "(a: Int64, b: Int64)";
    let both = Shape {
        above: "",
        p1: ("default ", named),
        p2: ("default ", PAIR),
        facts: "",
        call: None,
    };
    assert!(load_errors_of(&program("wi9hkjv.tuple_labels", &both)).is_empty());
    let one = Shape {
        above: "",
        p1: ("default ", named),
        p2: ("", PAIR),
        facts: "",
        call: Some((PAIR, PAIR_VALUE)),
    };
    assert_eq!(runs("wi9hkjv.tuple_labels_call", &one), Ok(30));

    let open = |m2: &'static str, call: Option<(&'static str, &'static str)>| {
        program(
            &format!("wi9hkjv.tuple_open_{}", m2.is_empty()),
            &Shape {
                above: "",
                p1: ("default ", "(E, Int64)"),
                p2: (m2, PAIR),
                facts: "",
                call,
            },
        )
        .replacen("  sort P1\n", "  sort P1\n    sort E = ?\n", 1)
    };
    assert_refused_naming(
        &load_errors_of(&open("default ", None)),
        &["overlapping defaults", "P1' at carrier", "P2' at carrier"],
        "a mark at `(E, Int64)` beside one at `(Int64, Int64)`",
    );
    let src = open("", Some((PAIR, PAIR_VALUE)));
    assert_eq!(run_int64(&src, "wi9hkjv.tuple_open_true.go"), Ok(30));
}

/// THE RELATION AND THE INDEX AGREE AT A TUPLE: `default_provider(?S, ?C, ?W)` answers the mark
/// at the tuple as written, and the materialized index holds the same row — where both
/// answered `Apply | P1 | P1`, the provider standing for its carrier, and the unmarked `P2`
/// had an inferred row `Apply | P2 | P2` beside it (MEASURED).
#[test]
fn the_relation_and_the_index_hold_the_row_at_the_tuple() {
    let shape = Shape {
        above: "",
        p1: ("default ", PAIR),
        p2: ("", PAIR),
        facts: "",
        call: None,
    };
    assert_rows_of(
        &program("wi9hkjv.rows", &shape),
        "Apply",
        "Apply | (_1: Int64, _2: Int64) | P1",
    );
}

/// The `default_provider(?S, ?C, ?W)` relation and the materialized index each hold exactly
/// `want` among their rows of `spec`.
fn assert_rows_of(src: &str, spec: &str, want: &str) {
    let mut kb = try_load_kb_with(src).expect("loads clean");
    let relation =
        crate::wi860_default_provider_relations_test::relation_rows(&mut kb, "default_provider", 3);
    let index = kb
        .default_provider_index()
        .expect("a loaded KB carries the index")
        .rendered_rows(&kb);
    let prefix = format!("{spec} |");
    for (what, rows) in [("relation", &relation), ("index", &index)] {
        let of_spec: Vec<&str> = rows
            .iter()
            .filter(|r| r.starts_with(&prefix))
            .map(String::as_str)
            .collect();
        assert_eq!(of_spec, vec![want], "the {what}'s rows of `{spec}`");
    }
}

/// A REQUIREMENT AT A TUPLE TAKES THE DEFAULT AS A CALL DOES: `viaG[X](f: X) requires Apply[F =
/// X]`, called at `(1, 2)`, has its requirement supplied by the marked `P1` — 10. It was refused
/// where the requirement is resolved, "`Apply[F = (_1: Int64, _2: Int64)]` cannot be supplied
/// for call to `viaG`" (MEASURED). FAILS under parts 1 and 2.
#[test]
fn a_requirement_at_a_tuple_takes_the_default() {
    let shape = Shape {
        above: "",
        p1: ("default ", PAIR),
        p2: ("", PAIR),
        facts: "  operation viaG[X](f: X) -> Int64 requires Apply[F = X] = Apply.run(f)\n  operation go() -> Int64 = viaG((1, 2))",
        call: None,
    };
    assert_eq!(runs("wi9hkjv.requirement", &shape), Ok(10));
}

/// `sort Tag { sort T = ?  operation name() -> Int64 }`, `P1` and `P2` providing it at
/// `carrier`, `P1` marked by `m1` and `P2` by `m2`, and `go` calling `Tag.name[T = carrier]()`.
fn tag_program(ns: &str, above: &str, (m1, m2): (&str, &str), carrier: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
{above}
  sort Tag
    sort T = ?
    operation name() -> Int64
  end
  sort P1
    {m1}provides Tag[T = {carrier}]
    operation name() -> Int64 = 10
  end
  sort P2
    {m2}provides Tag[T = {carrier}]
    operation name() -> Int64 = 30
  end
  operation go() -> Int64 = Tag.name[T = {carrier}]()
end
"#
    )
}

/// A MARK FOR A SPEC WHOSE OPERATIONS RECEIVE ON NO PARAMETER: `Tag`'s one parameter is its
/// carrier, as a goal reads it, and a row is filed there too — the relation and the index hold
/// `P1` at it — at `Box[T = Int64]`, at `Int64` and at a tuple the call answers by `P1`, 10, a
/// requirement `viaG[X]() requires Tag[T = X]` at `Box[T = Int64]` is supplied by it, 10, and
/// two marks are a load error naming the carrier. Each call was the tie, the requirement "a
/// requirement suppliable at this call site", at a sort carrier on the tree before 9HKJV as
/// well, and the two marks loaded clean (MEASURED): the row was filed at the provider, read off
/// the parameter some operation receives on, of which `Tag` has none. FAILS with the provision
/// read on that ladder (part 4).
#[test]
fn a_default_for_a_spec_receiving_on_no_parameter_answers_the_call() {
    let boxed = "  sort Box\n    sort T = ?\n    entity box(v: T)\n  end";
    let via_g = "  operation viaG[X]() -> Int64 requires Tag[T = X] = Tag.name[T = X]()\n  \
                 operation goG() -> Int64 = viaG[X = Box[T = Int64]]()";
    let above = format!("{boxed}\n{via_g}");
    let src = tag_program("wi9hkjv.tag_requirement", &above, ("default ", ""), "Box[T = Int64]");
    assert_eq!(run_int64(&src, "wi9hkjv.tag_requirement.goG"), Ok(10), "requirement");
    for (tag, above, carrier, shown) in [
        ("box", boxed, "Box[T = Int64]", "Box[T = Int64]"),
        ("int", "", "Int64", "Int64"),
        ("tuple", "", PAIR, "(_1: Int64, _2: Int64)"),
    ] {
        let ns = format!("wi9hkjv.tag_{tag}");
        let src = tag_program(&ns, above, ("default ", ""), carrier);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(10), "{tag}");
        assert_rows_of(&src, "Tag", &format!("Tag | {shown} | P1"));
        let src = tag_program(&format!("{ns}_both"), above, ("default ", "default "), carrier);
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                "ambiguous default",
                &format!("carrier '{shown}'"),
                "P1' at carrier",
                "P2' at carrier",
            ],
            &format!("two marks at one {tag}"),
        );
    }
}
