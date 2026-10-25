//! WI-885 — A `@[simp]` EQUATION IS NO DICTIONARY ENTRY, so a member a provision puts
//! where a spec operation's implementation goes may not be defined by one alone
//! (kernel-language.md §5.3, §8.7; `check_provider_operations`, kb/typing/coherence.rs).
//!
//! A `@[simp]` equation runs by INLINING: the typer rewrites a call that NAMES the operation
//! where the carrier is known. A call through a spec runs the operation symbol its
//! dictionary holds — builtin, body, host mapping — and an equation is none of them. So a
//! `@[simp]`-defined member that a provision supplies answers one route and not the other.
//! MEASURED before this check, one program that loaded clean: `C.f(c)` answered the
//! equation's 2, `Sp.f(c)` the spec default's 1, and the call through a requirement died
//! `OperationBodyMissing`. Without a spec default the provision was refused already, with
//! a message that said the carrier has no own member of that name.
//!
//! Refused for every route a provision supplies a member by: the carrier's own member, a
//! witness sort's, and the operation an instance fact binds.
//!
//! THE `eq` A CARRIER'S EQUALITY DISPATCHES TO is the one member a dispatch runs by its
//! CLAUSES (the eval→SLD bridge, WI-625), so for it a `@[simp]` equation is no definition at
//! all — and neither is an untagged one. One with no clause, on a namespace or a sort with
//! constructors, is refused at its DECLARATION (`check_operations_have_a_definition`), which
//! counted every `eq` dispatch target defined, clauses or not, and so let WI-1092's fixture
//! load and die at its first comparison. An `eq` an EARLIER load declared is not judged there
//! again — it was no `eq` dispatch target until a later provision bound it — so the
//! provision check judges it, `@[simp]`-alone. NOT covered: the `eq` of a sort that may be
//! provided with nothing behind it. `Map.eq` is one, and a comparison of two `Map`s is
//! refused where it is written (`check_eq_override_backing`, which asks of a carrier's OWN
//! `eq`); a witness's `eq` with no clause loads, and a comparison through it fails when it
//! runs (`wi1092_dispatched_rule_defined_target_test`'s witness row drives that).
//!
//! BACKED OUT, MEASURED: see the table at the end of this header.
//!
//! PASS EITHER WAY, BY DESIGN — the controls: a `@[simp]`-defined operation no provision
//! supplies still loads and runs where it is named (the half of §5.3 this keeps), a member
//! with a body beside its `@[simp]` equation answers one value on all three routes
//! (`Float.recip`'s shape), and a carrier `eq` defined by clauses with a `@[simp]` equation
//! beside them still loads and runs through a dictionary. That the standard library itself
//! raises none of these refusals is asserted by every test that loads it.
//!
//! BACK-OUT TABLE — MEASURED 2026-10-25, one mutation at a time:
//!
//!   * the provision check disabled: the six provision rows fail (five load clean, the
//!     no-default row is refused with the old "backs no operation" text);
//!   * the declaration's `eq` skip restored (`|| kb.is_eq_dispatch_target(op)` among its
//!     legs): the two `eq` rows fail, and so does
//!     `wi1092_dispatched_rule_defined_target_test::a_declared_but_undefined_eq_is_refused_at_its_declaration`;
//!   * `defined_by_simp_alone`'s "the declaration owns it" leg dropped: the `eq` row with a
//!     provision fails, reported twice; made unconditional (any `eq` of a sort that cannot
//!     be provided exempt, wherever it was declared): the cross-load row loads and fails;
//!   * its host-claim leg dropped: the host-claimed row is refused twice and fails;
//!   * its clause leg dropped (an `eq` dispatch target with clauses not exempt): the
//!     witness `eq` control fails. The `Color` `eq` control passes, by design: a sort with
//!     constructors is exempt here by the leg above, and its `eq` is the declaration's.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

const SPEC_WITH_DEFAULT: &str =
    "  sort Sp\n    sort T = ?\n    operation f(x: T) -> Int64 = 1\n  end\n";
const SPEC_WITHOUT_DEFAULT: &str =
    "  sort Sp\n    sort T = ?\n    operation f(x: T) -> Int64\n  end\n";
const VIA_DICT: &str = "  operation viaDict[A](x: A) -> Int64 requires Sp[T = A] = Sp.f(x)\n";

/// A carrier `C` that provides `Sp` and declares its own `f`, `member` following the
/// signature (`""` for no body, `" = 2"` for one), with a `@[simp]` equation beside it.
fn carrier(member: &str) -> String {
    format!(
        "  sort C\n    entity c(n: Int64)\n    provides Sp[T = C]\n    \
         operation f(x: C) -> Int64{member}\n    rule f(?x) <=> 2 @[simp]\n  end\n"
    )
}

fn program(ns: &str, decls: &str, drive: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Bool, PartialEq}}\n{decls}  \
         operation drive() -> Int64 = {drive}\nend\n"
    )
}

// ── refused ──────────────────────────────────────────────────────────────────────────

/// THE TICKET'S SHAPE. A spec default plus a carrier override defined by `@[simp]` alone:
/// it loaded clean and the call answered by the name it was written with.
#[test]
fn a_simp_alone_override_of_a_defaulted_spec_operation_is_refused() {
    let errs = load_errors_of(&program(
        "w885a",
        &format!("{SPEC_WITH_DEFAULT}{}{VIA_DICT}", carrier("")),
        "C.f(C.c(1)) * 100 + Sp.f(C.c(1)) * 10 + viaDict(C.c(1))",
    ));
    assert_refused_naming(
        &errs,
        &[
            "`w885a.C.f` is what `w885a.C`'s `provides w885a.Sp[…]` supplies for `w885a.Sp.f`",
            "nothing a dispatch can run defines it — a `@[simp]` equation does",
            "`w885a.Sp.f` has a default body",
            "Give `w885a.C.f` a body",
        ],
        "a `@[simp]`-alone override of a defaulted spec op",
    );
}

/// The call through a requirement, alone in its program: it died `OperationBodyMissing` when
/// it ran, and is now a load error.
#[test]
fn the_call_through_a_requirement_does_not_load() {
    let errs = load_errors_of(&program(
        "w885h",
        &format!("{SPEC_WITH_DEFAULT}{}{VIA_DICT}", carrier("")),
        "viaDict(C.c(1))",
    ));
    assert_refused_naming(
        &errs,
        &["`w885h.C.f` is what `w885h.C`'s `provides w885h.Sp[…]` supplies"],
        "a dictionary call of a `@[simp]`-alone member",
    );
}

/// No spec default: refused before as `UnbackedProviderOperation`, whose text said `C` has
/// no own `f`. It has one, and this says what is wrong with it.
#[test]
fn without_a_spec_default_the_refusal_names_the_member_it_has() {
    let errs = load_errors_of(&program(
        "w885b",
        &format!("{SPEC_WITHOUT_DEFAULT}{}", carrier("")),
        "C.f(C.c(1))",
    ));
    assert_refused_naming(
        &errs,
        &["`w885b.C.f` is what `w885b.C`'s `provides w885b.Sp[…]` supplies"],
        "a `@[simp]`-alone member of a spec without a default",
    );
    let joined = errs.join(" | ");
    assert!(
        !joined.contains("backs no operation") && !joined.contains("has a default body"),
        "one refusal, the accurate one: {joined}"
    );
}

/// An INSTANCE FACT that binds the spec operation to a `@[simp]`-alone operation.
#[test]
fn an_instance_fact_binding_to_a_simp_alone_operation_is_refused() {
    let errs = load_errors_of(&program(
        "w885f",
        &format!(
            "{SPEC_WITH_DEFAULT}  sort C\n    entity c(n: Int64)\n  end\n  \
             operation cF(x: C) -> Int64\n  rule cF(?x) <=> 2 @[simp]\n  \
             sort Bind\n    provides Sp[T = C, f = cF]\n  end\n{VIA_DICT}"
        ),
        "viaDict(C.c(1))",
    ));
    assert_refused_naming(
        &errs,
        &["`w885f.cF` is what `w885f.Bind`'s `provides w885f.Sp[…]` supplies for `w885f.Sp.f`"],
        "an instance-fact binding to a `@[simp]`-alone operation",
    );
}

/// A WITNESS sort whose member of the spec operation's name is `@[simp]`-alone.
#[test]
fn a_witness_member_defined_by_simp_alone_is_refused() {
    let errs = load_errors_of(&program(
        "w885g",
        &format!(
            "{SPEC_WITH_DEFAULT}  sort C\n    entity c(n: Int64)\n  end\n  \
             sort W\n    provides Sp[T = C]\n    operation f(x: C) -> Int64\n    \
             rule f(?x) <=> 2 @[simp]\n  end\n{VIA_DICT}"
        ),
        "viaDict(C.c(1))",
    ));
    assert_refused_naming(
        &errs,
        &["`w885g.W.f` is what `w885g.W`'s `provides w885g.Sp[…]` supplies"],
        "a witness member defined by `@[simp]` alone",
    );
}

/// A carrier's `eq` with a `@[simp]` equation and no clause, on a sort with constructors:
/// refused at its DECLARATION (`check_operations_have_a_definition`), which judged it
/// defined while it was an `eq` dispatch target, clauses or not. The bridge proves
/// clauses and finds none (WI-1092); the equation, tagged or not, is indexed under its
/// connective. Reported ONCE: the provision check leaves an `eq` the declaration owns.
#[test]
fn a_carrier_eq_with_no_clause_is_refused_at_its_declaration() {
    let errs = load_errors_of(&program(
        "w885i",
        "  sort Color\n    entity red\n    entity blue\n    provides PartialEq[T = Color]\n    \
         operation eq(a: Color, b: Color) -> Bool\n    rule eq(red, red) <=> true @[simp]\n  end\n",
        "if Color.eq(Color.red, Color.red) then 1 else 0",
    ));
    assert_refused_naming(
        &errs,
        &[
            "operation `w885i.Color.eq` has no definition",
            "it is the `eq` a carrier's equality dispatches to",
            "whether tagged `@[simp]` or not",
            "Define it by cases with predicate-headed clauses (`rule eq(…) :- true`",
        ],
        "a carrier `eq` with no clause",
    );
    assert!(
        !errs
            .join(" | ")
            .contains("is what `w885i.Color`'s `provides"),
        "the declaration's refusal alone — the provision check leaves this `eq` to it: {errs:#?}"
    );
}

/// The same with NO provision at all: a carrier's own `eq` is what its equality dispatches
/// to whether or not it writes `provides PartialEq` (route 1, WI-616), so the refusal does
/// not wait for one. An untagged equation is the WI-1092 shape.
#[test]
fn a_carriers_own_eq_with_no_clause_is_refused_without_a_provision() {
    let errs = load_errors_of(&program(
        "w885n",
        "  sort Color\n    entity red\n    entity blue\n    \
         operation eq(a: Color, b: Color) -> Bool\n    rule eq(red, red) <=> true\n  end\n",
        "if PartialEq.eq(Color.red, Color.blue) then 1 else 0",
    ));
    assert_refused_naming(
        &errs,
        &[
            "operation `w885n.Color.eq` has no definition",
            "1 equation with `w885n.Color.eq` as its subject is indexed under the connective",
        ],
        "a carrier's own `eq` with no clause and no provision",
    );
}

/// An `eq` an EARLIER load declared, bound by a later load's provision: the declaration
/// check judged `ceq` in the load that wrote it, when nothing dispatched to it and its
/// `@[simp]` equation was a definition, and does not judge it again. The provision does.
#[test]
fn an_eq_bound_in_a_later_load_is_judged_at_the_provision() {
    use anthill_core::kb::load::LoadOptions;
    let mut kb = crate::common::load_kb_with(
        "namespace w885x\n  import anthill.prelude.{Int64, Bool}\n  \
         sort Color\n    entity red\n    entity blue\n  end\n  \
         operation ceq(a: Color, b: Color) -> Bool\n  rule ceq(red, red) <=> true @[simp]\nend\n",
    );
    let later = crate::common::load_in_a_later_call(
        &mut kb,
        "namespace w885y\n  import anthill.prelude.{PartialEq}\n  \
         sort ColorEq\n    provides PartialEq[T = w885x.Color, eq = w885x.ceq]\n  end\nend\n",
        LoadOptions::default(),
    );
    let errs = match later {
        Err(errors) => crate::common::rendered_load_errors(errors),
        Ok(_) => {
            panic!("binding an earlier load's `@[simp]`-alone operation as an `eq` must not load")
        }
    };
    assert_refused_naming(
        &errs,
        &[
            "`w885x.ceq` is what `w885y.ColorEq`'s `provides anthill.prelude.PartialEq[…]` supplies",
            "the clauses the bridge proves",
            "`rule ceq(…) :- true`",
        ],
        "an `eq` bound in a later load",
    );
}

/// A member claimed `@[host_implemented]` whose mapping is missing has a refusal of its own,
/// whose repair is the mapping; "give it a body" beside it would send the author into
/// `HostImplementedWithBody`. So a `@[simp]` law on it adds nothing here.
#[test]
fn a_host_claimed_member_is_left_to_its_own_refusal() {
    let errs = load_errors_of(&program(
        "w885c",
        &format!(
            "{SPEC_WITH_DEFAULT}  sort C\n    entity c(n: Int64)\n    provides Sp[T = C]\n    \
             operation f(x: C) -> Int64 @[host_implemented]\n    rule f(?x) <=> 2 @[simp]\n  end\n"
        ),
        "C.f(C.c(1))",
    ));
    assert_refused_naming(
        &errs,
        &["`@[host_implemented]`"],
        "a host claim with no mapping",
    );
    assert!(
        !errs.join(" | ").contains("is what `w885c.C`'s `provides"),
        "the host claim's refusal alone: {errs:#?}"
    );
}

// ── controls ─────────────────────────────────────────────────────────────────────────

/// A `@[simp]` definition no provision supplies is a definition (§5.3): it loads, and a call
/// that names it runs.
#[test]
fn a_simp_definition_no_provision_supplies_still_runs() {
    assert_eq!(
        run_int64(
            &program(
                "w885e",
                "  sort C\n    entity c(n: Int64)\n    operation f(x: C) -> Int64\n    \
                 rule f(?x) <=> 2 @[simp]\n  end\n",
                "C.f(C.c(1))",
            ),
            "w885e.drive",
        ),
        Ok(2),
    );
}

/// A BODY beside the `@[simp]` equation — `Float.recip`'s shape, where the two agree: the
/// three routes answer alike. Which mechanism answers which route is the next row's.
#[test]
fn a_body_beside_the_equation_answers_on_every_route() {
    assert_eq!(
        run_int64(
            &program(
                "w885d",
                &format!("{SPEC_WITH_DEFAULT}{}{VIA_DICT}", carrier(" = 2")),
                "C.f(C.c(1)) * 100 + Sp.f(C.c(1)) * 10 + viaDict(C.c(1))",
            ),
            "w885d.drive",
        ),
        Ok(222),
    );
}

/// WHICH MECHANISM ANSWERS WHICH ROUTE (§5.3): the dictionary holds the BODY (3), and the
/// call that names the member is rewritten by the EQUATION (2). An equation that disagrees
/// with its body is a false law, the author's to keep true; this pins the mechanism, which
/// `Float.recip`'s agreeing pair cannot show.
#[test]
fn the_dictionary_runs_the_body_and_the_named_call_the_equation() {
    assert_eq!(
        run_int64(
            &program(
                "w885m",
                &format!("{SPEC_WITH_DEFAULT}{}{VIA_DICT}", carrier(" = 3")),
                "C.f(C.c(1)) * 100 + Sp.f(C.c(1)) * 10 + viaDict(C.c(1))",
            ),
            "w885m.drive",
        ),
        Ok(233),
    );
}

/// A carrier `eq` defined by CLAUSES, with a `@[simp]` equation beside them: the eq bridge
/// proves the clauses, so the member is runnable and the provision loads. The clauses are
/// INVERTED against structural equality (WI-1092's reason) so the dictionary route's answer
/// can only come from them. `Color` has constructors, so the declaration judges this `eq`;
/// the provision check's own clause leg is driven by the witness row below.
#[test]
fn a_clause_defined_eq_with_a_simp_equation_beside_it_still_runs() {
    assert_eq!(
        run_int64(
            &program(
                "w885k",
                "  sort Color\n    entity red\n    entity blue\n    \
                 operation ceq(a: Color, b: Color) -> Bool\n    \
                 rule ceq(red, blue) :- true\n    rule ceq(blue, red) :- true\n    \
                 rule ceq(red, blue) <=> true @[simp]\n    \
                 provides PartialEq[T = Color, eq = ceq]\n  end\n  \
                 operation same[A](a: A, b: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(a, b)\n",
                "if same(Color.red, Color.blue) then 1 else 0",
            ),
            "w885k.drive",
        ),
        Ok(1),
    );
}

/// The same through a WITNESS — a sort that may be provided, whose `eq` the declaration does
/// not judge, so `defined_by_simp_alone`'s clause leg is what keeps the provision loading.
/// Inverted clauses again: `same(red, blue)` is 1 only if the witness's clauses answered.
#[test]
fn a_witness_eq_defined_by_clauses_with_a_simp_equation_beside_them_still_runs() {
    assert_eq!(
        run_int64(
            &program(
                "w885w",
                "  sort C\n    entity red\n    entity blue\n  end\n  \
                 sort CEq\n    provides PartialEq[T = C]\n    \
                 operation eq(a: C, b: C) -> Bool\n    \
                 rule eq(red, blue) :- true\n    rule eq(blue, red) :- true\n    \
                 rule eq(red, blue) <=> true @[simp]\n  end\n  \
                 operation same[A](a: A, b: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(a, b)\n",
                "if same(C.red, C.blue) then 1 else 0",
            ),
            "w885w.drive",
        ),
        Ok(1),
    );
}
