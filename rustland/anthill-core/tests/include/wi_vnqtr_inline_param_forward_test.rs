//! WI-20260911-VNQTR — A VARIABLE WRITTEN INLINE IN A SIGNATURE IS A TYPE PARAMETER OF THE
//! CALLER'S, AND A FORWARD OF IT IS REFUSED AS A FORWARD OF A BRACKET'S IS.
//!
//! `midInline(y: ?t) -> Type = tyOf(y)`, over `tyOf[B](x: B) requires TypeValue[T = B]`,
//! hands its own `?t` to an operation that demands evidence about it, holding none and
//! having declared none. §5.4 quantifies a variable named in a parameter type as it does an
//! `[A]` binder, so this is `mid[U](y: U) = tyOf(y)` spelled the other way, which §5.2
//! refuses at the call naming the clause to add. The inline spelling LOADED CLEAN: the
//! refusal names a parameter of the caller's, and its list of them held the brackets and the
//! sort's parameters only. Called with a value that carries its type the program answered,
//! the slot being filled from the argument at entry; called with `nil` typed `List[T =
//! Int64]` it died `UnpinnedRequirement` — a clean load that fails at run time
//! ([`the_printed_repair_loads_and_answers_where_the_forward_died`]).
//!
//! BACK-OUTS, each a temporary switch in one build, over the whole `wi_tests` binary (7552
//! rows, all green without a switch):
//!
//! * **the record without the inline family** — the loader minting the variables and not
//!   listing them: **11 red** here, every row but three (30 across the binary — the other
//!   VNQTR files', `wi1078 the_tie_survives_the_opening`, five of `wi9pgcm` and one of
//!   `value_holding_type_readers`, which read an inline variable through the record). Off
//!   the record, the variable is read in the body as an alias's slot is, by its path, so the
//!   two rows whose clause names `?t` fail too.
//! * **the name off** — an inline variable minted under the plain name it is written with, as
//!   a bracket is: **10 red** here (20 across the binary). The refusal names `t`, which names
//!   nothing in the caller's scope, and a bracket `[U]` and a variable `?U` share one key, so
//!   a clause list keyed by it drops one of them.
//! * **the slot reading off**: [`an_anonymous_variable_in_the_carrier_is_the_slot_it_stands_in`],
//!   whose switches are `wi_vnqtr_unwritten_slot_forward_test`'s; **the member advice off**:
//!   [`a_provider_members_forward_is_declared_on_the_spec_operation`].
//!
//! PASSES UNDER EVERY SWITCH, by design: [`the_bracketed_twins_are_refused_as_they_were`].

use crate::common::{
    assert_refused_naming, interp_for, load_errors_of, replace_in_fixture, show_value,
};
use crate::wi_xsvcs_op_requires_forward_test::printed_repair;

/// Each of `ops` called on one load of `src`, its answer shown.
pub(crate) fn answers(src: &str, ops: &[&str]) -> Vec<String> {
    let mut interp = interp_for(src);
    ops.iter()
        .map(|op| match interp.call(op, &[]) {
            Ok(v) => show_value(interp.kb(), &v),
            Err(e) => panic!("{op}: {e:?}"),
        })
        .collect()
}

/// The one refusal `src` gets, which names every `want`.
pub(crate) fn the_one_refusal(src: &str, want: &[&str]) -> String {
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    assert_refused_naming(&errs, want, "a forward of the caller's parameter");
    errs.into_iter().next().unwrap()
}

/// `src` with the clause its one refusal prints written where the refusal says: on the
/// declaration whose signature is `sig` — written so in the fixture, followed by ` = ` —
/// whose qualified name is `declaration`.
pub(crate) fn with_printed_repair(src: &str, sig: &str, declaration: &str) -> String {
    let (clause, on) = printed_repair(&the_one_refusal(src, &[]));
    assert_eq!(on, declaration, "the clause belongs on the declaration that lacks it");
    replace_in_fixture(src, &format!("{sig} = "), &format!("{sig} {clause} = "))
}

const HEAD: &str = r#"
  import anthill.prelude.{Cell, Int64, String, Type, List, Option, Bool, cons, nil, some, none}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
"#;

/// A program in `test.vnqtr.<ns>` over `tyOf[B](x: B) requires TypeValue[T = B]`.
pub(crate) fn program(ns: &str, body: &str) -> String {
    format!("namespace test.vnqtr.{ns}\n{HEAD}\n{body}\nend\n")
}

/// The ticket's program in the present language. The variable is named as written, `?t`,
/// in the requirement, in the account of the carrier and in the clause to add — printed
/// bare, `requires TypeValue[T = t]` names nothing in `midInline`'s scope.
#[test]
fn a_forward_of_an_inline_variable_is_refused_at_the_call() {
    let src = program("bare", "  operation midInline(y: ?t) -> Type = tyOf(y)");
    let e = the_one_refusal(
        &src,
        &[
            "cannot be supplied for call to `test.vnqtr.bare.tyOf`",
            "`anthill.reflect.TypeValue[T = ?t]`",
            "its carrier is `?t`, a type parameter of the CALLING operation `test.vnqtr.bare.midInline`",
            "Declare `requires anthill.reflect.TypeValue[T = ?t]` on `test.vnqtr.bare.midInline`",
        ],
    );
    // At the call in `midInline`'s body: the program's eighth line, where `tyOf(y)` starts.
    assert!(e.starts_with("8:40:"), "the refusal belongs at the forwarding call; got {e:?}");
}

/// A variable inside a sort application is the same forward: `List[T = ?t]`'s instance holds
/// only where `?t`'s does, and the evidence the caller lacks is `TypeValue[T = ?t]`.
#[test]
fn an_inline_variable_inside_an_application_is_refused() {
    let src = program("nested", "  operation midNested(y: List[T = ?t]) -> Type = tyOf(y)");
    the_one_refusal(
        &src,
        &[
            "`anthill.reflect.TypeValue[T = anthill.prelude.List[T = ?t]]`",
            "its carrier `anthill.prelude.List[T = ?t]` holds `?t`",
            "Declare `requires anthill.reflect.TypeValue[T = ?t]` on `test.vnqtr.nested.midNested`",
        ],
    );
}

/// THE PRINTED REPAIR IS A REPAIR, pasted and driven — and the row that pins what the
/// refusal replaces: without the clause, `empty()` loaded and died `UnpinnedRequirement`,
/// `nil` carrying no element type for the slot to be read from. With it, the caller's own
/// call supplies `TypeValue[T = Int64]`, and both calls answer.
#[test]
fn the_printed_repair_loads_and_answers_where_the_forward_died() {
    let src = program(
        "repair",
        r#"  operation midNested(y: List[T = ?t]) -> Type = tyOf(y)
  operation full() -> Type = midNested(cons(1, nil))
  operation empty() -> Type =
    let xs: List[T = Int64] = nil
    midNested(xs)"#,
    );
    let repaired = with_printed_repair(
        &src,
        "operation midNested(y: List[T = ?t]) -> Type",
        "test.vnqtr.repair.midNested",
    );
    assert_eq!(
        answers(&repaired, &["test.vnqtr.repair.full", "test.vnqtr.repair.empty"]),
        ["Cell[V = List[T = Int64]]", "Cell[V = List[T = Int64]]"]
    );
}

/// A bracket and a variable of one name are two parameters: `[U]` and `?U` share the key
/// `U`, and the refusal asks for evidence about each. Keyed by name, the second clause was
/// dropped and the pasted repair was refused again, naming `?U`.
#[test]
fn a_bracket_and_a_variable_of_one_name_are_two_parameters() {
    let src = program(
        "twokeys",
        r#"  sort Two[A, C]
    entity two(a: A, c: C)
  end
  operation m[U](a: U, b: ?U) -> Type = tyOf(two(a: a, c: b))
  operation go() -> Type = m(1, "s")
  operation stated() -> Type = Cell[V = Two[A = Int64, C = String]]"#,
    );
    let (clause, _) = printed_repair(&the_one_refusal(&src, &[]));
    for each in ["anthill.reflect.TypeValue[T = U]", "anthill.reflect.TypeValue[T = ?U]"] {
        assert!(clause.contains(each), "the repair must ask for `{each}`; got {clause:?}");
    }
    let repaired = with_printed_repair(&src, "operation m[U](a: U, b: ?U) -> Type", "test.vnqtr.twokeys.m");
    // Compared with the type written out, printed alike: each parameter took its argument's.
    let [got, stated] = <[String; 2]>::try_from(answers(
        &repaired,
        &["test.vnqtr.twokeys.go", "test.vnqtr.twokeys.stated"],
    ))
    .unwrap();
    assert_eq!(got, stated);
}

/// CONTROL, passes either way: the bracketed twins were refused before, in the same words.
/// What the change adds is that the two spellings of one signature agree.
#[test]
fn the_bracketed_twins_are_refused_as_they_were() {
    for sig in ["mid[U](y: U)", "mid[U](y: List[T = U])"] {
        let src = program("twin", &format!("  operation {sig} -> Type = tyOf(y)"));
        the_one_refusal(
            &src,
            &["Declare `requires anthill.reflect.TypeValue[T = U]` on `test.vnqtr.twin.mid`"],
        );
    }
}

/// CONTROL, passes either way: the description's acceptance, in the present language. The
/// type-argument channel it was written against is gone; a type parameter's run-time value
/// is read through a `TypeValue` requirement, and with the clause written a forward of the
/// inline variable is handed the evidence as a forward of the bracket's is.
#[test]
fn the_tickets_acceptance_holds_with_the_clause_written() {
    let src = program(
        "accept",
        r#"  operation viaInline(b: List[T = ?t]) -> Type requires TypeValue[T = ?t] = tyOf(b)
  operation viaBracket[U](b: List[T = U]) -> Type requires TypeValue[T = U] = tyOf(b)
  operation i() -> Type = viaInline(cons(1, nil))
  operation b() -> Type = viaBracket(cons(1, nil))"#,
    );
    assert_eq!(
        answers(&src, &["test.vnqtr.accept.i", "test.vnqtr.accept.b"]),
        ["Cell[V = List[T = Int64]]", "Cell[V = List[T = Int64]]"]
    );
}

/// The verdict is the carrier's, not `TypeValue`'s: a spec of the program's own is refused
/// the same way, and the clause the refusal prints makes the call answer.
#[test]
fn a_spec_of_the_programs_own_is_refused_and_repaired_the_same_way() {
    let src = program(
        "own",
        r#"  sort Stamp
    sort T = ?
    operation stamp() -> Int64
  end

  sort Leaf
    entity leaf(n: Int64)
    provides Stamp[T = Leaf]
    operation stamp() -> Int64 = 7
  end

  operation stampOf[B](x: B) -> Int64 requires Stamp[T = B] = Stamp.stamp[T = B]()
  operation relay(x: ?t) -> Int64 = stampOf(x)
  operation go() -> Int64 = relay(leaf(n: 1))"#,
    );
    the_one_refusal(
        &src,
        &[
            "`test.vnqtr.own.Stamp[T = ?t]`",
            "a type parameter of the CALLING operation `test.vnqtr.own.relay`",
            "Declare `requires test.vnqtr.own.Stamp[T = ?t]` on `test.vnqtr.own.relay`",
        ],
    );
    let repaired = with_printed_repair(&src, "operation relay(x: ?t) -> Int64", "test.vnqtr.own.relay");
    assert_eq!(answers(&repaired, &["test.vnqtr.own.go"]), ["7"]);
}

/// A member of a parametric sort: the variable is the OPERATION's, so the clause goes on the
/// operation — the sort declares no `?t` and could not name it.
#[test]
fn a_members_inline_variable_is_declared_on_the_member() {
    let src = program(
        "member",
        r#"  sort Box[V]
    entity box(v: V)
    operation m(b: Self, y: ?t) -> Type = tyOf(y)
  end
  operation go() -> Type = Box.m(box(v: "s"), 5)"#,
    );
    the_one_refusal(&src, &["`anthill.reflect.TypeValue[T = ?t]`"]);
    let repaired =
        with_printed_repair(&src, "operation m(b: Self, y: ?t) -> Type", "test.vnqtr.member.Box.m");
    assert_eq!(answers(&repaired, &["test.vnqtr.member.go"]), ["Cell[V = Int64]"]);
}

/// A variable spelled like the sort's parameter is its own: `?T` in `sort Box[T]` is not
/// `T`. Evidence about the sort's `T` does not cover it, the refusal names `?T`, and the
/// clause it prints is the one that covers it.
#[test]
fn an_inline_variable_spelled_like_the_sorts_parameter_is_its_own() {
    let src = program(
        "coll",
        r#"  sort Box[T]
    entity box(v: T)
    operation m(b: Self, y: ?T) -> Type requires TypeValue[T = T] = tyOf(y)
  end
  operation go() -> Type = Box.m(box(v: "s"), 5)"#,
    );
    let e = the_one_refusal(&src, &["`anthill.reflect.TypeValue[T = ?T]`", "its carrier is `?T`"]);
    let (clause, declaration) = printed_repair(&e);
    assert_eq!(clause, "requires anthill.reflect.TypeValue[T = ?T]");
    assert_eq!(declaration, "test.vnqtr.coll.Box.m");
    let repaired = replace_in_fixture(&src, "requires TypeValue[T = T] = tyOf(y)", &format!("{clause} = tyOf(y)"));
    assert_eq!(answers(&repaired, &["test.vnqtr.coll.go"]), ["Cell[V = Int64]"]);
}

/// Two variables, one covered: the refusal names the one the caller holds nothing for, and
/// its clause beside the written one makes the call answer.
#[test]
fn of_two_inline_variables_the_uncovered_one_is_named() {
    let src = program(
        "two",
        r#"  operation two[A, C](a: A, c: C) -> Type requires TypeValue[T = A], TypeValue[T = C] = Cell[V = A]
  operation m(a: ?s, c: ?t) -> Type requires TypeValue[T = ?s] = two(a, c)
  operation go() -> Type = m(1, "s")"#,
    );
    let e = the_one_refusal(&src, &["its carrier is `?t`"]);
    let (clause, _) = printed_repair(&e);
    assert_eq!(clause, "requires anthill.reflect.TypeValue[T = ?t]");
    let repaired = replace_in_fixture(
        &src,
        "requires TypeValue[T = ?s] = two(a, c)",
        "requires TypeValue[T = ?s], TypeValue[T = ?t] = two(a, c)",
    );
    assert_eq!(answers(&repaired, &["test.vnqtr.two.go"]), ["Cell[V = Int64]"]);
}

/// EVERY PLACE A CALL IS WRITTEN IN A BODY gives the two spellings one verdict: a `let`, an
/// `if` condition, a match arm, a lambda's body, a dot on a receiver typed with the variable,
/// and a signature whose callback slot names the variable too. Each inline twin LOADED. The
/// bracketed twin is the inline one with `?t` written as a bracket's `U`.
#[test]
fn every_site_of_the_forward_refuses_both_spellings_alike() {
    let sites: &[(&str, &str)] = &[
        ("let", "m(y: ?t) -> Type =\n    let z = tyOf(y)\n    z"),
        ("if", "m(y: ?t, c: Bool) -> Bool = if tyOf(y) = Int64 then c else c"),
        (
            "match",
            "m(y: ?t, o: Option[T = Int64]) -> Type =\n    match o\n      case some(v) -> tyOf(y)\n      case none() -> Int64",
        ),
        ("lambda", "m(y: ?t) -> Type = app(lambda () -> tyOf(y))"),
        ("callback", "m(f: (x: ?t) -> Int64, y: ?t) -> Type = tyOf(y)"),
        ("dot", "m(b: Box[V = ?t]) -> Type = b.elem()"),
    ];
    let support = r#"  operation app(f: () -> Type) -> Type = f()
  sort Box[V]
    entity box(v: V)
    operation elem(b: Self) -> Type requires TypeValue[T = V] = V
  end
"#;
    for (site, inline) in sites {
        let bracket = inline.replacen("m(", "m[U](", 1).replace("?t", "U");
        assert_ne!(bracket, *inline, "{site}: the twin must differ from the inline spelling");
        for (sig, param) in [(*inline, "?t"), (bracket.as_str(), "U")] {
            the_one_refusal(
                &program(site, &format!("{support}  operation {sig}")),
                &[
                    &format!("Declare `requires anthill.reflect.TypeValue[T = {param}]` on `test.vnqtr.{site}.m`"),
                    "a type parameter of the CALLING operation",
                ],
            );
        }
    }
}

/// CONTROL, passes either way: a clause whose spec's contract holds `TypeValue` at the
/// variable covers it, as it covers a bracket's parameter — and the evidence it holds is
/// the one `tyOf` reads, a `nil` carrying no element type included.
#[test]
fn a_clause_whose_contract_holds_the_evidence_covers_an_inline_variable() {
    let src = program(
        "desc",
        r#"  sort Desc
    sort T = ?
    requires TypeValue[T = T]
    operation d() -> Int64
  end
  sort Leaf
    entity leaf(n: Int64)
    provides Desc[T = Leaf]
    operation d() -> Int64 = 7
  end
  operation m(y: ?t) -> Type requires Desc[T = ?t] = tyOf(y)
  operation mList(y: List[T = ?t]) -> Type requires Desc[T = ?t] = tyOf(y)
  operation one() -> Type = m(leaf(n: 1))
  operation empty() -> Type =
    let xs: List[T = Leaf] = nil
    mList(xs)"#,
    );
    assert_eq!(
        answers(&src, &["test.vnqtr.desc.one", "test.vnqtr.desc.empty"]),
        ["Cell[V = Leaf]", "Cell[V = List[T = Leaf]]"]
    );
}

/// An anonymous `?` in the carrier names nothing and ties nothing, so it is the slot of
/// `y`'s type it stands in, unwritten: the forward is refused naming the slot by its path,
/// `y.T`, as a slot left out is, inside the application the call passes, and no clause is
/// printed over the `?`. Written where the refusal says, the clause answers. It was refused
/// as a call at a type no row of `TypeValue` may be written for — the slot is a projection,
/// which counts as ground — while that clause repairs it.
#[test]
fn an_anonymous_variable_in_the_carrier_is_the_slot_it_stands_in() {
    let src = program(
        "anon",
        "  operation m(y: List[T = ?]) -> Type = tyOf(y)\n  operation empty() -> Type =\n    let ys: List[T = Int64] = nil\n    m(ys)",
    );
    let e = the_one_refusal(
        &src,
        &[
            "its carrier `anthill.prelude.List[T = y.T]` holds `y.T`",
            "Declare `requires anthill.reflect.TypeValue[T = y.T]`",
        ],
    );
    assert!(!e.contains("TypeValue[T = ?]"), "no clause names a `?`: {e}");
    let repaired = with_printed_repair(&src, "operation m(y: List[T = ?]) -> Type", "test.vnqtr.anon.m");
    assert_eq!(answers(&repaired, &["test.vnqtr.anon.empty"]), ["Cell[V = List[T = Int64]]"]);
}

/// A member that backs a spec operation for its provider restates the spec operation's
/// `requires` and adds none, so the clause its forward lacks goes on the spec operation and
/// is restated on the member: on the member alone it is refused as a strengthening, which is
/// where the refusal used to send it. The refusal says so, and the clause written on both
/// answers — the bracket spelling as the inline one.
#[test]
fn a_provider_members_forward_is_declared_on_the_spec_operation() {
    for (ns, param) in [("provin", "?u"), ("provbr", "U")] {
        let (spec_sig, member_sig) = if param == "U" {
            ("operation r[U](x: T, y: U) -> Type", "operation r[U](x: Leaf, y: U) -> Type")
        } else {
            ("operation r(x: T, y: ?u) -> Type", "operation r(x: Leaf, y: ?u) -> Type")
        };
        let src = program(
            ns,
            &format!(
                "  sort Rel\n    sort T = ?\n    {spec_sig}\n  end\n  sort Leaf\n    entity leaf(n: Int64)\n    provides Rel[T = Leaf]\n    {member_sig} = tyOf(y)\n  end\n  operation go() -> Type = Rel.r(leaf(n: 1), \"s\")"
            ),
        );
        let e = the_one_refusal(
            &src,
            &[
                &format!("Declare `requires anthill.reflect.TypeValue[T = {param}]` on `test.vnqtr.{ns}.Rel.r`, the spec operation `test.vnqtr.{ns}.Leaf.r` backs"),
                &format!("restate it on `test.vnqtr.{ns}.Leaf.r`"),
            ],
        );
        let clause = format!("requires TypeValue[T = {param}]");
        let on_member = replace_in_fixture(&src, &format!("{member_sig} = "), &format!("{member_sig} {clause} = "));
        assert_refused_naming(&load_errors_of(&on_member), &["strengthens the precondition"], "on the member alone");
        let on_both = replace_in_fixture(&on_member, &format!("{spec_sig}\n"), &format!("{spec_sig} {clause}\n"));
        assert_eq!(answers(&on_both, &[&format!("test.vnqtr.{ns}.go")]), ["Cell[V = String]"], "{ns}: {e}");
    }
}
