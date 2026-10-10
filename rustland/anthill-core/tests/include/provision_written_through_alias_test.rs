//! A provision keeps the alias a binding of it was written through.
//!
//! THE RULE. `provides Show[T = Money]` over `sort Money = Int64` is the provision `Show[T =
//! Int64]` to everything that reads it — the provider search and its index, the member rule,
//! the check of what the provided spec requires, coherence and the default rows, the
//! operations a provider inherits, a rule over the reflect relation. The clause that is
//! stored holds the binding on an occurrence that keeps the name, and a refusal about the
//! provision names it as the clause wrote it: `the spec's is Money (Int64)`.
//!
//! HOW. A clause binding written as an alias is lowered to `TypeNode::Aliased`
//! (`Loader::clause_binding_as_written`) and the provision is stored as that value
//! (`Loader::clause_spec_to_store`). A row of the relation holds its spec as a value
//! (`ProvidesRow::spec_view`), and every reader takes the spec and its bindings through
//! the view. A reader that keys on a type — the default rows, a projection grounded in a
//! term walk — takes the type's term there.
//!
//! BEFORE. The binding was replaced by the type where it was lowered, and the member rule
//! said `the spec's is Int64` for a clause that wrote `Money`.
//!
//! NOT YET. A provision's `:-` condition is stored at its type and its messages name the
//! type. One provision written twice on a provider, once through the alias and once
//! written out, is two rows of the relation where either spelling twice is one — nothing
//! that reads them answers differently (`one_provision_in_two_spellings_provides_once`).
//!
//! CONTROLS — measured, each piece backed out on its own. `the message rows` are the four
//! under "the name in a refusal"; `the three wi_zy11j rows` are that file's
//! `a_provision_written_at_an_alias_is_a_provision_at_its_type`,
//! `a_provision_and_a_value_meet_through_an_alias_on_either_side` and
//! `a_clause_binding_naming_its_sorts_parameter_through_an_alias_is_about_that_parameter`.
//!
//!   the provision stored as the term of its type (`load_provides_clause` lowering every
//!   spec), or the pre-scan handing it a lowered one (`prelowered_provision_specs` holding
//!   a term) — FAIL, each on its own: the message rows.
//!   a row decoded from a term alone (`decode_provides_row` refusing a spec that is no
//!   term) — FAIL: every row here but the two about a row's label and the specialization
//!   records, and the three wi_zy11j rows.
//!   the index filed from a term alone (`build_provides_index` skipping a value-headed
//!   fact) — FAIL: a_provision_written_through_an_alias_provides_at_its_type,
//!   a_provision_at_an_alias_of_a_sort_is_at_that_sort,
//!   one_provision_in_two_spellings_provides_once,
//!   provisions_listed_in_a_refusal_are_named_as_written,
//!   a_provision_written_through_an_alias_has_its_specialization_records, and the three
//!   wi_zy11j rows.
//!   each of these reading a term alone, on its own:
//!     the operations a provider inherits (`build_sort_ops_table`'s pairs), a projection
//!     grounded from a provision (`ground_rigid_projection_if_concrete`), the default
//!     rows' key (`kb::defaults`), an instance told by its bound operation
//!     (`provision_binds_any_op`), an instance's identity in the coherence grouping
//!     (`InstanceIdentity` its own fact for every instance) — FAIL:
//!       a_provision_written_through_an_alias_provides_at_its_type
//!     the specialization records (`register_specialization_witnesses`) — FAIL:
//!       a_provision_written_through_an_alias_has_its_specialization_records
//!     the `NonEq` leaves (`eq_derive::noneq_provider_sorts`) — FAIL:
//!       a_noneq_leaf_claimed_through_an_alias_is_a_leaf
//!     the `Modifiable` claims (`kb::region`) — FAIL:
//!       a_modifiable_claim_written_through_an_alias_is_about_its_sort
//!     the written-row check over provisions (`all_spec_clause_views`) — FAIL:
//!       a_row_beside_a_provisions_binding_written_through_an_alias_is_judged
//!     the rows listed for a partly pinned requirement (`no_provision_agrees_with_pins`)
//!     — FAIL: provisions_listed_in_a_refusal_are_named_as_written
//!     the rows asked whether any could answer (`some_row_could_answer` admitting a row it
//!     does not read) — FAIL:
//!       a_row_written_through_an_alias_is_read_where_none_answers_at_the_carrier
//!     the completion of a host entry (`unique_provider_completion`) — FAIL:
//!       a_host_entry_is_completed_from_a_provision_written_through_an_alias
//!     a projection's subject taken only where it is a term (`entity_type_on_builders`)
//!     — FAIL: a_projection_rebuilt_at_a_binding_written_through_an_alias_is_read_at_its_type
//!     the scan that stands in for the spec bucket (`spec_has_any_providers`) — FAIL: the
//!     unit row `typing::tests::…::the_scan_counts_a_provision_whose_spec_is_held_as_a_value`,
//!     and no row here or under the node-carrier control.
//!     the place of a sealed load's refusal (`sealed::written_view_site` answering for a
//!     term alone) — FAIL: `wi_9bkz4_sealed_bodies_test::
//!     the_refusal_of_a_provision_written_through_an_alias_points_at_its_binding`
//!   each message naming the type alone, on its own:
//!     the parameter's line (`declared_type_display` there), and the member's own side of
//!     it alone — FAIL, each:
//!       a_member_that_does_not_fit_is_told_the_binding_as_written
//!     the spec's signature (`render_op_signature`) — FAIL: that row, and
//!       the_other_member_refusals_name_the_binding_as_written
//!     the narrower member's types (`member_type_display`) — FAIL:
//!       the_other_member_refusals_name_the_binding_as_written
//!     the requirement nothing provides, and the one naming an unwritten parameter
//!     (`requirement_failure_of`) — FAIL, each:
//!       an_unmet_requirement_of_a_provision_names_the_binding_as_written
//!     the conflicting bindings, and the rows listed — FAIL, each:
//!       provisions_listed_in_a_refusal_are_named_as_written
//!
//!   PASS EITHER WAY, by design: the `written` half of every row.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of, load_kb_with, sort_provisions};

fn source(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Int64, String, Bool, List, Error}}
  sort Money = Int64
  sort Oops = String
  sort Box
    sort V = ?
    entity mk(v: V)
  end
  sort IntBox = Box[V = Int64]
  sort AnyBox = Box
  sort Show[T]
    operation show(x: T) -> Int64
  end
{body}
end
"#
    )
}

/// What a program does: the integer `test.<ns>.go()` answers, or its refusals with the
/// namespace written `NS` so two spellings' can be compared.
fn outcome(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    if !errs.is_empty() {
        let errs: Vec<String> = errs.iter().map(|e| e.replace(ns, "NS")).collect();
        return format!("REFUSED {errs:?}");
    }
    let mut interp = interp_for(&source(ns, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => format!("RUNS {n}"),
        other => format!("{other:?}").replace(ns, "NS"),
    }
}

/// The one refusal of a source that must not load.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
    errs.into_iter().next().unwrap()
}

const AW: [(&str, &str); 2] = [("alias", "Money"), ("written", "Int64")];

// ── what a provision provides ───────────────────────────────────────────────

/// Each shape of provision does the same thing with its binding written through the alias
/// as with it written out: the same value, or the same refusal.
#[test]
fn a_provision_written_through_an_alias_provides_at_its_type() {
    // (shape, the program at a binding, what the written-out program does)
    let shapes: [(&str, fn(&str) -> String, &str); 11] = [
        (
            "witness",
            |at| format!(
                "  sort W\n    entity w\n    provides Show[T = {at}]\n    \
                 operation show(x: Int64) -> Int64 = x + 1\n  end\n  \
                 operation go() -> Int64 = Show.show(5)"
            ),
            "RUNS 6",
        ),
        (
            "twowitnesses",
            |at| format!(
                "  sort W1\n    entity w1\n    provides Show[T = {at}]\n    \
                 operation show(x: Int64) -> Int64 = 1\n  end\n  \
                 sort W2\n    entity w2\n    provides Show[T = Int64]\n    \
                 operation show(x: Int64) -> Int64 = 2\n  end\n  \
                 operation go() -> Int64 = Show.show(5)"
            ),
            "ambiguous dispatch",
        ),
        (
            "opbinding",
            |at| format!(
                "  sort Monoid[T]\n    operation combine(a: T, b: T) -> T\n  end\n  \
                 operation plus(a: Int64, b: Int64) -> Int64 = a + b\n  \
                 sort W\n    entity w\n    provides Monoid[T = {at}, combine = plus]\n  end\n  \
                 operation go() -> Int64 = Monoid.combine(2, 3)"
            ),
            "RUNS 5",
        ),
        (
            // The same instance, its operation bound, written again with the binding
            // written out: one instance, not two that disagree.
            "opbindingtwice",
            |at| format!(
                "  sort Monoid[T]\n    operation combine(a: T, b: T) -> T\n  end\n  \
                 operation plus(a: Int64, b: Int64) -> Int64 = a + b\n  \
                 sort W\n    entity w\n    provides Monoid[T = {at}, combine = plus]\n    \
                 provides Monoid[T = Int64, combine = plus]\n  end\n  \
                 operation go() -> Int64 = Monoid.combine(2, 3)"
            ),
            "RUNS 5",
        ),
        (
            // Two instances of one spec at one carrier that bind its operation differently.
            "opbindingrivals",
            |at| format!(
                "  sort Monoid[T]\n    operation combine(a: T, b: T) -> T\n  end\n  \
                 operation plus(a: Int64, b: Int64) -> Int64 = a + b\n  \
                 operation times(a: Int64, b: Int64) -> Int64 = a * b\n  \
                 sort W\n    entity w\n    provides Monoid[T = {at}, combine = plus]\n  end\n  \
                 namespace W\n    provides Monoid[T = {at}, combine = times]\n  end\n  \
                 operation go() -> Int64 = Monoid.combine(2, 3)"
            ),
            "REFUSED",
        ),
        (
            "conditional",
            |at| format!(
                "  sort Pr[T]\n    operation pr(x: T) -> Int64\n  end\n  \
                 sort PW\n    entity pw\n    provides Pr[T = Int64]\n    \
                 operation pr(x: Int64) -> Int64 = 4\n  end\n  \
                 sort W\n    entity w\n    provides Show[T = {at}] :- Pr[T = {at}]\n    \
                 operation show(x: Int64) -> Int64 = Pr.pr(x)\n  end\n  \
                 operation go() -> Int64 = Show.show(5)"
            ),
            "RUNS 4",
        ),
        (
            // The provided spec requires another, which the same provider provides.
            "requires",
            |at| format!(
                "  sort FEq[T]\n    requires Show[T]\n    operation feq(a: T) -> Int64\n  end\n  \
                 sort W\n    entity w\n    provides Show[T = {at}]\n    provides FEq[T = {at}]\n    \
                 operation show(x: Int64) -> Int64 = 1\n    \
                 operation feq(a: Int64) -> Int64 = 2\n  end\n  \
                 operation go() -> Int64 = FEq.feq(5)"
            ),
            "RUNS 2",
        ),
        (
            "default",
            |at| format!(
                "  sort W1\n    entity w1\n    default provides Show[T = {at}]\n    \
                 operation show(x: Int64) -> Int64 = 1\n  end\n  \
                 sort W2\n    entity w2\n    provides Show[T = Int64]\n    \
                 operation show(x: Int64) -> Int64 = 2\n  end\n  \
                 operation go() -> Int64 = Show.show(5)"
            ),
            "RUNS 1",
        ),
        (
            "entry",
            |at| format!(
                "  sort Car\n    entity car\n    operation show(x: Int64) -> Int64 = 3\n  end\n  \
                 namespace Car\n    provides Show[T = {at}]\n  end\n  \
                 operation go() -> Int64 = Show.show(5)"
            ),
            "RUNS 3",
        ),
        (
            // An element the call leaves open, completed from the one provision's row.
            "completed",
            |at| format!(
                "  sort Cap\n    sort C = ?\n    sort Element = ?\n    \
                 operation cap(c: C) -> Int64\n  end\n  \
                 sort Direct\n    entity direct(v: Int64)\n    \
                 provides Cap[C = Direct, Element = {at}]\n    \
                 operation cap(c: Direct) -> Int64 = 1\n  end\n  \
                 operation sink[P](x: P) -> Int64 requires Cap[C = P] = Cap.cap(x)\n  \
                 operation go() -> Int64 = sink(direct(v: 7))"
            ),
            "RUNS 1",
        ),
        (
            // A projection off the requirement's member, grounded from the provision.
            "projection",
            |at| format!(
                "  sort Resource\n    sort C = ?\n    sort V = ?\n    \
                 operation peek(c: C) -> C\n  end\n  \
                 sort Counter\n    entity counter(n: Int64)\n    \
                 provides Resource[C = Counter, V = {at}]\n    \
                 operation peek(c: Counter) -> Counter = c\n  end\n  \
                 operation valueOf[T](target: T, v: T.V) -> T.V requires Resource[C = T] = v\n  \
                 operation go() -> Int64 = valueOf(counter(n: 1), 8)"
            ),
            "RUNS 8",
        ),
    ];
    for (shape, program, written_does) in shapes {
        let does: Vec<String> = AW
            .iter()
            .map(|(spelling, at)| outcome(&format!("pwa{shape}{spelling}"), &program(at)))
            .collect();
        assert!(does[1].contains(written_does), "{shape}, written out: {}", does[1]);
        assert_eq!(does[0], does[1], "{shape}: the alias row and the written one");
    }
}

/// A carrier's own provision at an alias of the carrier, and a provision at an alias of a
/// sort applied to arguments, are the provisions at those types.
#[test]
fn a_provision_at_an_alias_of_a_sort_is_at_that_sort() {
    for (spelling, at) in [("alias", "LeafAlias"), ("written", "Leaf")] {
        let ns = format!("pwaself{spelling}");
        let body = format!(
            "  sort Leaf\n    entity leaf\n    provides Show[T = {at}]\n    \
             operation show(x: Leaf) -> Int64 = 7\n  end\n  sort LeafAlias = Leaf\n  \
             operation go() -> Int64 = Show.show(leaf)"
        );
        assert_eq!(outcome(&ns, &body), "RUNS 7", "{ns}");
    }
    for (spelling, at) in [
        ("alias", "IntBox"),
        ("nested", "Box[V = Money]"),
        ("written", "Box[V = Int64]"),
    ] {
        let ns = format!("pwabox{spelling}");
        let body = format!(
            "  sort Tag[T]\n    operation tag(x: T) -> Int64\n  end\n  \
             sort Holder\n    entity holder\n    provides Tag[T = {at}]\n    \
             operation tag(x: Box[V = Int64]) -> Int64 = 9\n  end\n  \
             operation go() -> Int64 = Tag.tag(Box.mk(1))"
        );
        assert_eq!(outcome(&ns, &body), "RUNS 9", "{ns}");
    }
}

/// One provision written twice on a provider — in either spelling or in both — provides
/// once: a call, an operation's requirement, a sort's requirement and a provision
/// forwarded from it are all supplied, and the forwarded provision is one row.
///
/// The relation itself holds the mixed pair as two rows, where either spelling twice is
/// one: the clause written through the alias is stored on another carrier than its twin.
#[test]
fn one_provision_in_two_spellings_provides_once() {
    for (spelling, first, second) in [
        ("both", "Money", "Int64"),
        ("reversed", "Int64", "Money"),
        ("written", "Int64", "Int64"),
        ("aliases", "Money", "Money"),
    ] {
        let ns = format!("pwatwice{spelling}");
        let body = format!(
            "  sort Lo\n    sort T = ?\n    operation lo(x: T) -> Int64\n  end\n  \
             sort Hi\n    sort T = ?\n    provides Lo[T = T]\n    operation hi(x: T) -> Int64\n  end\n  \
             sort W\n    entity w\n    provides Hi[T = {first}]\n    provides Hi[T = {second}]\n    \
             operation hi(x: Int64) -> Int64 = x + 1\n    \
             operation lo(x: Int64) -> Int64 = x + 2\n  end\n  \
             operation useLo[P](x: P) -> Int64 requires Lo[T = P] = Lo.lo(x)\n  \
             sort Holder\n    entity holder\n    requires Hi[T = Int64]\n    \
             operation h(x: Int64) -> Int64 = Hi.hi(x)\n  end\n  \
             operation go() -> Int64 = useLo(5) + Hi.hi(1) + Holder.h(10)"
        );
        assert_eq!(outcome(&ns, &body), "RUNS 20", "{ns}");
        let kb = load_kb_with(&source(&ns, &body));
        let forwarded = sort_provisions(&kb)
            .into_iter()
            .filter(|(provider, spec)| provider.ends_with(".W") && spec.ends_with(".Lo"))
            .count();
        assert_eq!(forwarded, 1, "{ns}: one forwarded `Lo` row");
    }
}

// ── the name in a refusal ───────────────────────────────────────────────────

/// A member that does not fit is told the spec's side as the provision wrote it: the
/// alias first and the type beside it, in the parameter's line and in the signature. The
/// member's own side is led the same way where the member wrote an alias.
#[test]
fn a_member_that_does_not_fit_is_told_the_binding_as_written() {
    // (row, the provision's binding, the member's parameter type, how each is named)
    let rows = [
        ("alias", "Money", "String", "Money (Int64)", "String"),
        ("written", "Int64", "String", "Int64", "String"),
        ("applied", "IntBox", "Box[V = String]", "IntBox (Box[V = Int64])", "Box[V = String]"),
        (
            "nested",
            "Box[V = Money]",
            "Box[V = String]",
            "Box[V = Money] (Box[V = Int64])",
            "Box[V = String]",
        ),
        ("nestedwritten", "Box[V = Int64]", "Box[V = String]", "Box[V = Int64]", "Box[V = String]"),
        ("member", "Int64", "Oops", "Int64", "Oops (String)"),
    ];
    for (row, at, member, spec_named, member_named) in rows {
        let ns = format!("pwanofit{row}");
        let body = format!(
            "  sort W\n    entity w\n    provides Show[T = {at}]\n    \
             operation show(x: {member}) -> Int64 = 1\n  end"
        );
        let rendered = refusal(&ns, &body);
        for wanted in [
            format!("parameter 1 is `{member_named}` where the spec's is `{spec_named}`"),
            format!(
                "the spec declares `show(x: {spec_named}) -> Int64` (at this provision's bindings)"
            ),
            format!("the member is `show(x: {member_named}) -> Int64`"),
        ] {
            assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");
        }
    }
}

/// …and so are a member of another arity, and one that takes less than the spec's.
#[test]
fn the_other_member_refusals_name_the_binding_as_written() {
    for (spelling, at, named) in [("alias", "Money", "Money (Int64)"), ("written", "Int64", "Int64")] {
        let ns = format!("pwaarity{spelling}");
        let body = format!(
            "  sort W\n    entity w\n    provides Show[T = {at}]\n    \
             operation show(x: Int64, y: Int64) -> Int64 = 1\n  end"
        );
        let rendered = refusal(&ns, &body);
        let wanted = format!("the spec declares `show(x: {named}) -> Int64` (1 parameter(s))");
        assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");
    }
    for (spelling, at, named) in [("alias", "AnyBox", "AnyBox (Box)"), ("written", "Box", "Box")] {
        let ns = format!("pwanarrow{spelling}");
        let body = format!(
            "  sort W\n    entity w\n    provides Show[T = {at}]\n    \
             operation show(x: Box[V = Int64]) -> Int64 = 1\n  end"
        );
        let rendered = refusal(&ns, &body);
        for wanted in [
            format!("admits at this provision's bindings (`{named}`)"),
            format!("The spec declares `show(x: {named}) -> Int64`"),
        ] {
            assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");
        }
    }
}

/// What the provided spec requires is named at the provision's binding as written: where
/// nothing provides it, and where it names a parameter the provision does not write.
#[test]
fn an_unmet_requirement_of_a_provision_names_the_binding_as_written() {
    for (spelling, at, named) in [
        ("alias", "Money", "NS.Money (anthill.prelude.Int64)"),
        ("written", "Int64", "anthill.prelude.Int64"),
    ] {
        let ns = format!("pwanoprov{spelling}");
        let body = format!(
            "  sort FEq[T]\n    requires Show[T]\n    operation feq(a: T) -> Int64\n  end\n  \
             sort W\n    entity w\n    provides FEq[T = {at}]\n    \
             operation feq(a: Int64) -> Int64 = 2\n  end"
        );
        let named_here = named.replace("NS", &format!("test.{ns}"));
        let wanted = format!("but nothing provides `test.{ns}.Show[T = {named_here}]`");
        let rendered = refusal(&ns, &body);
        assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");

        let ns = format!("pwaunwritten{spelling}");
        let body = format!(
            "  sort P2\n    sort X = ?\n    sort Y = ?\n    operation p(x: X) -> Int64\n  end\n  \
             sort Sp\n    sort A = ?\n    sort B = ?\n    requires P2[X = A, Y = B]\n    \
             operation sp(a: A) -> Int64\n  end\n  \
             sort W\n    entity w\n    provides Sp[A = {at}]\n    \
             operation sp(a: Int64) -> Int64 = 1\n  end"
        );
        let named_here = named.replace("NS", &format!("test.{ns}"));
        let wanted = format!("at `test.{ns}.P2[X = {named_here}, Y = test.{ns}.Sp.B]`");
        let rendered = refusal(&ns, &body);
        assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");
    }
}

/// Two provisions of one carrier that bind a parameter differently are told both bindings
/// as written, and the provisions listed for a requirement none of them answers are too.
#[test]
fn provisions_listed_in_a_refusal_are_named_as_written() {
    for (spelling, at, short, qualified) in [
        ("alias", "Money", "Money (Int64)", "NS.Money (anthill.prelude.Int64)"),
        ("written", "Int64", "Int64", "anthill.prelude.Int64"),
    ] {
        let ns = format!("pwaconflict{spelling}");
        let body = format!(
            "  sort Two\n    sort A = ?\n    sort B = ?\n    operation two(a: A) -> Int64\n  end\n  \
             sort W\n    entity w\n    provides Two[A = W, B = {at}]\n    \
             provides Two[A = W, B = String]\n    operation two(a: W) -> Int64 = 1\n  end"
        );
        let wanted = format!("binding 'B' to 2 ({short}, String)");
        let rendered = refusal(&ns, &body);
        assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");

        let ns = format!("pwarows{spelling}");
        let body = format!(
            "  sort Cap\n    sort C = ?\n    sort Element = ?\n    operation cap(c: C) -> Int64\n  end\n  \
             sort Direct\n    entity direct(v: Int64)\n    \
             provides Cap[C = Direct, Element = {at}]\n    \
             operation cap(c: Direct) -> Int64 = 1\n  end\n  \
             sort Opaque\n    entity opaque(v: Int64)\n  end\n  \
             operation sink[P](x: P) -> Int64 requires Cap[C = P] = Cap.cap(x)\n  \
             operation go() -> Int64 = sink(opaque(v: 7))"
        );
        let qualified = qualified.replace("NS", &format!("test.{ns}"));
        let wanted = format!(
            "`test.{ns}.Direct` provides `test.{ns}.Cap[C = test.{ns}.Direct, Element = {qualified}]`"
        );
        let rendered = refusal(&ns, &body);
        assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");
    }
}

// ── the readers that need their own program ─────────────────────────────────

/// A row beside a binding written through an alias is judged as it is beside one written
/// out: a label that is no effect kind is refused, once.
#[test]
fn a_row_beside_a_provisions_binding_written_through_an_alias_is_judged() {
    for (spelling, at) in AW {
        let ns = format!("pwarow{spelling}");
        let body = format!(
            "  sort Chan\n    sort T = ?\n    effects E = ?\n    \
             operation send(x: T) -> Int64 effects {{E, Error}}\n  end\n  \
             sort Beep\n    entity beep\n  end\n  \
             sort W\n    entity w\n    provides Chan[T = {at}, E = {{Beep}}]\n    \
             operation send(x: Int64) -> Int64 effects {{Error}} = 1\n  end"
        );
        let errs = load_errors_of(&source(&ns, &body));
        let judged = errs
            .iter()
            .filter(|e| e.contains("is not a REGISTERED effect kind") && e.contains("`Beep`"))
            .count();
        assert_eq!(judged, 1, "{ns}: {errs:#?}");
    }
}

/// A provision written through an alias has the specialization record of each law its
/// spec requires, as the one written out has, named by the type.
#[test]
fn a_provision_written_through_an_alias_has_its_specialization_records() {
    for (spelling, at) in AW {
        let ns = format!("pwaspec{spelling}");
        let body = format!(
            "  sort FEq[T]\n    requires Show[T]\n    operation feq(a: T) -> Int64\n  end\n  \
             sort W\n    entity w\n    provides Show[T = {at}]\n    provides FEq[T = {at}]\n    \
             operation show(x: Int64) -> Int64 = 1\n    \
             operation feq(a: Int64) -> Int64 = 2\n  end"
        );
        let mut kb = load_kb_with(&source(&ns, &body));
        let records: Vec<String> =
            crate::common::rendered_facts(&mut kb, "anthill.realization.ProofRecord")
                .into_iter()
                .filter(|record| record.contains(&format!("test.{ns}.W.provides.")))
                .map(|record| record.replace(&ns, "NS"))
                .collect();
        assert!(
            records.iter().any(|record| record.contains("test.NS.W.provides.FEq.")),
            "{ns}: a record for the law `FEq` requires: {records:#?}"
        );
    }
}

/// A claim that a sort is `Modifiable`, written through an alias of the sort, is the claim
/// about the sort: the reflect read answers for it as for the claim written out.
#[test]
fn a_modifiable_claim_written_through_an_alias_is_about_its_sort() {
    for (spelling, at) in [("alias", "SlotAlias"), ("written", "Slot")] {
        let ns = format!("pwamod{spelling}");
        let src = format!(
            "namespace test.{ns}\n  import anthill.prelude.{{Int64, Bool, Modifiable}}\n  \
             import anthill.reflect.{{is_modifiable}}\n  \
             sort Slot\n    entity slot(v: Int64)\n    provides Modifiable[T = {at}]\n  end\n  \
             sort SlotAlias = Slot\n  sort Other\n    entity other\n  end\n  \
             operation slot_is() -> Bool = is_modifiable(Slot)\n  \
             operation other_is() -> Bool = is_modifiable(Other)\nend\n"
        );
        let mut interp = interp_for(&src);
        for (op, want) in [("slot_is", true), ("other_is", false)] {
            let got = interp.call(&format!("test.{ns}.{op}"), &[]);
            assert!(matches!(got, Ok(Value::Bool(b)) if b == want), "{ns}.{op}: {got:?}");
        }
    }
}

/// A leaf that is `NonEq` by a provision written through an alias of itself makes a sort
/// holding it partial, as the provision written out does.
#[test]
fn a_noneq_leaf_claimed_through_an_alias_is_a_leaf() {
    let classes = |spelling: &str, at: &str| {
        let ns = format!("pwanoneq{spelling}");
        let src = format!(
            "namespace test.{ns}\n  import anthill.prelude.{{Int64, Bool, PartialEq, NonEq}}\n  \
             sort Leaf\n    entity leaf(n: Int64)\n    provides PartialEq[T = Leaf]\n    \
             provides NonEq[T = {at}]\n    \
             operation eq(a: Leaf, b: Leaf) -> Bool = false\n    \
             operation nonEqRefl() -> Leaf = leaf(n: 0)\n  end\n  \
             sort LeafAlias = Leaf\n  \
             sort Holds\n    entity holds(l: Leaf)\n  end\nend\n"
        );
        let kb = load_kb_with(&src);
        let mut specs: Vec<String> = sort_provisions(&kb)
            .into_iter()
            .filter(|(provider, _)| provider == &format!("test.{ns}.Holds"))
            .map(|(_, spec)| spec)
            .collect();
        specs.sort();
        specs
    };
    let written = classes("written", "Leaf");
    assert!(written.iter().any(|s| s.ends_with(".NonEq")), "{written:?}");
    assert_eq!(classes("alias", "LeafAlias"), written);
}

/// A projection off a spec's parameter, inside a tuple the member rule rebuilds at the
/// provision's bindings, is read at the binding's type where the binding was written
/// through an alias: the provision is judged as the one written out is.
#[test]
fn a_projection_rebuilt_at_a_binding_written_through_an_alias_is_read_at_its_type() {
    let judged = |spelling: &str, at: &str| {
        let ns = format!("pwarigid{spelling}");
        let src = format!(
            "namespace test.{ns}\n  import anthill.prelude.{{Int64, String, List, Error}}\n  \
             sort Storage\n    sort C = ?\n    sort Key = ?\n    sort Val = ?\n    \
             operation get(s: C, k: Key) -> Val\n  end\n  \
             sort MemStore\n    provides Storage[C = MemStore, Key = String, Val = Int64]\n    \
             entity memStore\n    operation get(s: MemStore, k: String) -> Int64 = 0\n  end\n  \
             sort MS = MemStore\n  \
             sort Sp\n    sort P = ?\n    effects E = ?\n    requires Storage[C = P]\n    \
             operation size(s: Self) -> Int64\n    \
             operation op(s: Self, x: (a: P.Key, b: List)) -> Int64\n  end\n  \
             sort Car\n    entity car(n: Int64)\n    provides Sp[P = {at}, E = {{Error}}]\n    \
             operation size(c: Car) -> Int64 = c.n\n    \
             operation op(c: Car, x: (a: MemStore.Key, b: List)) -> Int64 = 42\n  end\nend\n"
        );
        load_errors_of(&src)
    };
    // The comparison the member rule makes, which names no binding: the same in both.
    let compared = "the spec's `(a: MemStore.Key, b: List[T = ?T])` admits arguments the \
                    member's `(a: String, b: List[T = ?T])` does not";
    for (spelling, at) in [("alias", "MS"), ("written", "MemStore")] {
        let errs = judged(spelling, at);
        assert_eq!(errs.len(), 2, "{spelling}: {errs:#?}");
        assert!(errs[0].contains("which requires") && errs[0].contains("but nothing provides"));
        assert!(errs[1].contains(compared), "{spelling}: {}", errs[1]);
    }
}

/// A provision whose row is held with an alias in it is READ where a call names a carrier
/// no row answers at: the call is told the carrier provides nothing, as beside the row
/// written out — not that an element is left open, which a row that might answer means.
#[test]
fn a_row_written_through_an_alias_is_read_where_none_answers_at_the_carrier() {
    for (spelling, at) in AW {
        let ns = format!("pwanone{spelling}");
        let body = format!(
            "  sort Cap\n    sort C = ?\n    sort Element = ?\n    operation tag(c: C) -> Int64\n  end\n  \
             sort Direct\n    entity direct(v: Int64)\n  end\n  \
             sort Opaque\n    entity opaque(v: Int64)\n  end\n  \
             sort DirectCap\n    entity directCap\n    provides Cap[C = Direct, Element = {at}]\n    \
             operation tag(c: Direct) -> Int64 = 5\n  end\n  \
             operation sink[P, El](c: P) -> Int64 requires Cap[C = P, Element = El] = Cap.tag(c)\n  \
             operation go() -> Int64 = sink(opaque(v: 7))"
        );
        let rendered = refusal(&ns, &body);
        let wanted = format!("`test.{ns}.Opaque` provides no `test.{ns}.Cap`");
        assert!(rendered.contains(&wanted), "{ns}: wants {wanted}: {rendered}");
    }
}

/// An operation entered from the host with an element nothing pins takes it from the one
/// provision that answers, where that provision's binding was written through an alias as
/// where it was written out.
#[test]
fn a_host_entry_is_completed_from_a_provision_written_through_an_alias() {
    for (spelling, at) in AW {
        let ns = format!("pwahost{spelling}");
        let body = format!(
            "  sort Scale\n    sort V = ?\n    sort F = ?\n    operation scale(a: V) -> Int64\n  end\n  \
             sort Vec\n    entity vec(n: Int64)\n    provides Scale[V = Vec, F = {at}]\n    \
             operation scale(a: Vec) -> Int64 = a.n + 1\n  end\n  \
             operation mk() -> Vec = vec(n: 4)\n  \
             operation twice[V, F](a: V) -> Int64 requires Scale[V = V, F = F] = Scale.scale(a)"
        );
        let mut interp = interp_for(&source(&ns, &body));
        let made = interp.call(&format!("test.{ns}.mk"), &[]).expect("a Vec");
        let got = interp.call(&format!("test.{ns}.twice"), &[made]);
        assert!(matches!(got, Ok(Value::Int(5))), "{ns}: {got:?}");
    }
}
