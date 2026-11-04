//! WI-20261005-SGXYH — a slot nothing at the call fixes is answered only by a provision that
//! holds at every value of it (kernel-language §5.2).
//!
//! Three spellings leave a slot of a carrier unfixed: an argument whose own type leaves a
//! parameter undetermined (`buf(v: 1)`, `N` named by no field), a result typed at the sort
//! with parameters left out (`Bag.empty()`, `-> Self` with nothing fixing `T`), and a partial
//! one (`Buf.of(1)`, `T` fixed and `N` not). MEASURED on the parent commit, the three were
//! read three ways, and a call through a requirement and a direct call of the spec's
//! operation read them differently again:
//!
//! * THE BARE SPELLING RAN ANOTHER PROVISION. Beside `PBag provides Store[State = Bag[T = E]]`
//!   and `Gen provides Store[State = X]`, `User.go1(Bag.empty())` and `Store.peek(Bag.empty())`
//!   answered 55, Gen's, where `User[S = Bag[T = ?]].go1(…)`, a `let`-annotated `Bag[T =
//!   Int64]` and `mk() -> Bag` all answered 7. And `User.go1[Store = PBag](Bag.empty())`
//!   was refused beside `Gen` ("PBag provides Store, but not at the bindings this call
//!   needs") while it ran alone.
//! * A PROVISION AT ONE INSTANCE CHOSE THE SLOT, for one spelling of three. Beside
//!   `QB provides Store[State = Buf[T = Int64, N = Bool]]` alone, `User.go1(buf(v: 1))`
//!   answered 41, a second such provision made it a tie, and beside a provision generic in
//!   `N` the instance won (41 over 60). `Buf.of(1)` and `Bag.empty()` were refused there.
//! * A DIRECT CALL LOADED AND DIED. `Store.peek(Bag.empty())` beside two provisions at
//!   instances of `Bag` loaded clean and raised `AmbiguousSpecOpDispatch` at run time, and
//!   with one it answered through the run time's dispatch, which the typer had found
//!   nothing for.
//!
//! Each is one reading now. The provision matcher reads a sort written with slots left out
//! as that sort at an open slot in each, wherever it is asked — a requirement's
//! construction, the named-slot inference, a selection's check, a direct call's dispatch —
//! and meets an open slot with a provision's own parameter only. Where only provisions at
//! instances would answer, the call is refused at load naming the slot and them.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ───────────────────────────────
//!
//! EACH PART backed out present-but-wrong, APPLIED AND RUN over `wi_tests` (8 708 rows).
//!
//! 1. THE MATCHER'S OPENING — a bare or partial sort matched as written
//!    (`unwritten_slots_opened_at` answering `None`). 18 FAIL. Here 7:
//!    [`the_bare_spelling_reaches_the_provision_at_its_sort`] (55),
//!    [`a_direct_call_at_the_bare_spelling_reaches_it_too`] (55),
//!    [`a_selection_at_the_bare_spelling_is_judged_alike`] (refused beside `Gen`),
//!    [`a_provision_generic_in_the_slot_answers_it`],
//!    [`one_provision_at_an_instance_does_not_answer_an_unfixed_slot`],
//!    [`two_provisions_at_instances_are_one_refusal_not_a_tie`] and
//!    [`a_direct_call_is_held_to_the_same_rule`], each at its bare or partial spelling;
//!    elsewhere 8 of `wi_2kv4y_unfixed_carrier_test`, 2 of `wi_jn09w_holder_gate_test` and
//!    `wi_zy11j_alias_typed_value_test …a_clause_binding_at_an_alias_with_an_open_slot_is_
//!    asked_at_its_type`.
//! 2. AN UNFIXED SLOT MET BY ANY TYPE, as the subtype relation reads the placeholder. 13 FAIL.
//!    Here 5: [`one_provision_at_an_instance_does_not_answer_an_unfixed_slot`],
//!    [`two_provisions_at_instances_are_one_refusal_not_a_tie`] (a tie),
//!    [`a_provision_generic_in_the_slot_answers_it`] (41),
//!    [`a_direct_call_is_held_to_the_same_rule`] and
//!    [`a_provision_at_a_structured_instance_is_named_too`]; elsewhere 6 of
//!    `wi_2kv4y_unfixed_carrier_test` and 2 of `wi_f3fyj_value_in_type_binding_test`.
//! 3. THE ACCOUNT — the resolver's "no impl provides" where the slot is the reason. 9 FAIL,
//!    each at its message: here [`one_provision_at_an_instance_does_not_answer_an_unfixed_slot`],
//!    [`two_provisions_at_instances_are_one_refusal_not_a_tie`] and
//!    [`a_provision_at_a_structured_instance_is_named_too`]; elsewhere 6 of
//!    `wi_2kv4y_unfixed_carrier_test`.
//! 4. THE DIRECT CALL PASSED THROUGH to the run time's dispatch. 4 FAIL, each a clean load:
//!    here [`a_direct_call_is_held_to_the_same_rule`] and
//!    [`a_provision_at_a_structured_instance_is_named_too`]; elsewhere 2 of
//!    `wi_f3fyj_value_in_type_binding_test`.
//! 5. A CONSTRUCTION'S PLACEHOLDER READ AS A TYPE (`element_at`). 2 FAIL, neither here, each
//!    refused at the construction where the call it is passed to fixes `N`:
//!    `wi_kssa4_spec_typed_value_test …a_slot_the_construction_leaves_open_is_left_to_the_call`
//!    and `wi_wbhtm_value_in_type_call_test …a_self_parameter_binds_the_value_in_type`.
//! 6. A SELECTED WITNESS REFUSED TOO. 1 FAILS, at its message: `wi_0rp29_review9_regressions_test
//!    …a_bracket_naming_a_witness_dispatches_to_it_over_an_undecided_slot_control`.
//!
//! PASS UNDER EVERY ONE, by design: [`a_generic_provision_alone_still_answers_the_bare_spelling`],
//! [`writing_the_slot_lets_the_provision_at_it_answer`],
//! [`a_selected_witness_answers_an_unfixed_slot`],
//! [`an_opened_existential_is_not_named_as_unfixed`] and
//! [`a_provision_leaving_the_slot_out_answers_it`].
//!
//! ADDED BY THE REVIEW, each measured on the tree before its repair and on the parent commit:
//! [`the_empty_literal_is_answered_at_an_instance`] (refused, naming `T` of `List`, where
//! the parent answers 3), [`an_applied_head_still_outranks_a_bare_one`] (refused as a tie,
//! the parent answers 2) and [`a_rule_body_call_is_refused_between_two_instances`] (with the
//! refusal kept to operation bodies the two-provision clauses loaded clean, where the parent
//! refused them as a tie; with it fired at one provision the clause that declared its
//! `requires(…)` was refused, where the parent loads it — measured while a rule body could
//! write `requires(…)`, which proposal 060.1 §5 removed). The six parts above were measured
//! before the review gathered the unfixed rule into one check after the matcher's arm (1).
//!
//! GONE, MEASURED REDUNDANT: 2KV4Y's second asking of a goal at its open slots (restored, it
//! moves one row's text — the tie names `Bag[T = ?]` for `Bag`) and a selection's check asked
//! at the open slots too (restored, nothing moves).

use crate::common::{assert_refused_naming, load_errors_of, replace_in_fixture, run_int64};

/// `Bag[T]`, whose `empty()` fixes no `T`; `Buf[T, N]`, whose `buf(v: T)` names no `N` and
/// whose `of(v: T)` returns the sort with `N` left out; the spec `Store`; `User`, which
/// requires `Store` at its `S`; and `mk() -> Bag`, an existential return. `providers`
/// follow, then `go() = {call}`.
fn program(ns: &str, providers: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, Option, List}}

  sort Bag
    sort T = ?
    entity bag(n: Int64)
    operation empty() -> Self = bag(n: 1)
  end

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
    operation of(v: T) -> Self = buf(v: v)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end

  sort User
    sort S = ?
    requires Store[State = S]
    operation go1(s: S) -> Int64 = Store.peek(s)
  end

  operation mk() -> Bag = bag(n: 2)
{providers}
  operation go() -> Int64 = {call}
end
"#
    )
}

/// A provider `name` of `Store` at `at`, whose `peek` answers `n`.
fn at(name: &str, at: &str, n: i64) -> String {
    format!(
        "\n  sort {name}\n    provides Store[State = {at}]\n    \
         operation peek(s: {at}) -> Int64 = {n}\n  end\n"
    )
}

/// A provider of `Store` at every `Bag` (7), and one at every type (55).
fn pbag() -> String {
    "\n  sort PBag\n    sort E = ?\n    provides Store[State = Bag[T = E]]\n    \
     operation peek(s: Bag[T = E]) -> Int64 = 7\n  end\n"
        .to_owned()
}
fn gen() -> String {
    "\n  sort Gen\n    sort X = ?\n    provides Store[State = X]\n    \
     operation peek(s: X) -> Int64 = 55\n  end\n"
        .to_owned()
}

/// A provider of `Store` at every `N` of a `Buf[T = Int64]` (60).
fn qg() -> String {
    "\n  sort QG\n    sort F = ?\n    provides Store[State = Buf[T = Int64, N = F]]\n    \
     operation peek(s: Buf[T = Int64, N = F]) -> Int64 = 60\n  end\n"
        .to_owned()
}

const BUF_BOOL: &str = "Buf[T = Int64, N = Bool]";
const BUF_STRING: &str = "Buf[T = Int64, N = String]";

/// `ns.go` run.
fn go(ns: &str, providers: &str, call: &str) -> Result<i64, String> {
    run_int64(&program(ns, providers, call), &format!("{ns}.go"))
}

/// The refusal naming `slot` (as `` `N` of `Buf` ``) unfixed and `providers` as the ones at
/// an instance of it — and no tie.
fn assert_unfixed(ns: &str, providers: &str, call: &str, slot: &str, named: &[&str], why: &str) {
    let errs = load_errors_of(&program(ns, providers, call));
    let named: Vec<String> = named.iter().map(|p| format!("`{ns}.{p}`")).collect();
    let provide = if named.len() == 1 { "provides" } else { "provide" };
    assert_refused_naming(
        &errs,
        &[
            &format!("nothing here fixes {slot}"),
            &format!(
                "{} {provide} `{ns}.Store` only at an instance of it: write it in the type of \
                 the value",
                named.join(" and ")
            ),
        ],
        why,
    );
    assert!(
        !errs.join(" | ").contains("ambiguous"),
        "{why}: provisions at instances are no rivals for a slot nothing fixes, got {errs:#?}"
    );
}

// ── one answer for the bare spelling ──────────────────────────────────────────────────

/// THE TICKET'S PROGRAM: beside a provision at every `Bag` and one at every type, the bare
/// spelling reaches the one at `Bag`, as the open-slot and the annotated spellings do.
#[test]
fn the_bare_spelling_reaches_the_provision_at_its_sort() {
    let ns = "wisgxyh.bare";
    let providers = format!("{}{}", pbag(), gen());
    for call in [
        "User.go1(Bag.empty())",
        "User[S = Bag[T = ?]].go1(Bag.empty())",
        "\n    let b: Bag[T = Int64] = Bag.empty()\n    User.go1(b)",
        "User.go1(mk())",
    ] {
        assert_eq!(go(ns, &providers, call), Ok(7), "{call}");
    }
}

/// A DIRECT CALL OF THE SPEC'S OPERATION reads the bare spelling the same way.
#[test]
fn a_direct_call_at_the_bare_spelling_reaches_it_too() {
    let ns = "wisgxyh.bare_direct";
    let providers = format!("{}{}", pbag(), gen());
    for call in [
        "Store.peek(Bag.empty())",
        "\n    let b: Bag[T = Int64] = Bag.empty()\n    Store.peek(b)",
        "Store.peek(mk())",
    ] {
        assert_eq!(go(ns, &providers, call), Ok(7), "{call}");
    }
}

/// A SELECTED WITNESS IS JUDGED AT THE SAME READING: `[Store = PBag]` at the bare spelling is
/// among the providers beside `Gen` as it is alone.
#[test]
fn a_selection_at_the_bare_spelling_is_judged_alike() {
    let ns = "wisgxyh.bare_sel";
    let call = "User.go1[Store = PBag](Bag.empty())";
    assert_eq!(go(ns, &pbag(), call), Ok(7));
    assert_eq!(go(ns, &format!("{}{}", pbag(), gen()), call), Ok(7));
}

/// CONTROL: a provision at every type still answers the bare spelling alone. Passes with or
/// without the change.
#[test]
fn a_generic_provision_alone_still_answers_the_bare_spelling() {
    let ns = "wisgxyh.bare_gen";
    assert_eq!(go(ns, &gen(), "User.go1(Bag.empty())"), Ok(55));
    assert_eq!(go(ns, &gen(), "Store.peek(Bag.empty())"), Ok(55));
}

// ── a slot nothing at the call fixes ──────────────────────────────────────────────────

/// ONE PROVISION AT AN INSTANCE DOES NOT ANSWER A SLOT NOTHING FIXES, in any of the three
/// spellings that leave one.
#[test]
fn one_provision_at_an_instance_does_not_answer_an_unfixed_slot() {
    let qb = at("QB", BUF_BOOL, 41);
    let pint = at("PInt", "Bag[T = Int64]", 9);
    for (ns, providers, call, slot, named) in [
        ("wisgxyh.one_arg", &qb, "User.go1(buf(v: 1))", "`N` of `Buf`", "QB"),
        ("wisgxyh.one_part", &qb, "User.go1(Buf.of(1))", "`N` of `Buf`", "QB"),
        ("wisgxyh.one_bare", &pint, "User.go1(Bag.empty())", "`T` of `Bag`", "PInt"),
        ("wisgxyh.one_hole", &pint, "User[S = Bag[T = ?]].go1(Bag.empty())", "`T` of `Bag`", "PInt"),
    ] {
        assert_unfixed(ns, providers, call, slot, &[named], call);
    }
}

/// TWO SUCH PROVISIONS ARE ONE REFUSAL NAMING BOTH, not a tie: neither answers the call.
#[test]
fn two_provisions_at_instances_are_one_refusal_not_a_tie() {
    let qs = format!("{}{}", at("QB", BUF_BOOL, 41), at("QS", BUF_STRING, 42));
    let ps = format!(
        "{}{}",
        at("PInt", "Bag[T = Int64]", 9),
        at("PStr", "Bag[T = String]", 5)
    );
    for (ns, providers, call, slot, named) in [
        ("wisgxyh.two_arg", &qs, "User.go1(buf(v: 1))", "`N` of `Buf`", ["QB", "QS"]),
        ("wisgxyh.two_part", &qs, "User.go1(Buf.of(1))", "`N` of `Buf`", ["QB", "QS"]),
        ("wisgxyh.two_bare", &ps, "User.go1(Bag.empty())", "`T` of `Bag`", ["PInt", "PStr"]),
    ] {
        assert_unfixed(ns, providers, call, slot, &named, call);
    }
}

/// A PROVISION GENERIC IN THE SLOT ANSWERS IT, beside one at an instance: the instance does
/// not choose the slot for the call.
#[test]
fn a_provision_generic_in_the_slot_answers_it() {
    let buf = format!("{}{}", at("QB", BUF_BOOL, 41), qg());
    assert_eq!(go("wisgxyh.gen_arg", &buf, "User.go1(buf(v: 1))"), Ok(60));
    assert_eq!(go("wisgxyh.gen_part", &buf, "User.go1(Buf.of(1))"), Ok(60));
    let bag = format!("{}{}", at("PInt", "Bag[T = Int64]", 9), pbag());
    assert_eq!(go("wisgxyh.gen_bare", &bag, "User.go1(Bag.empty())"), Ok(7));
}

/// THE REPAIR THE REFUSAL NAMES: the slot written in the type of the value, and the
/// provision at it answers. Passes with or without the change.
#[test]
fn writing_the_slot_lets_the_provision_at_it_answer() {
    let qs = format!("{}{}", at("QB", BUF_BOOL, 41), at("QS", BUF_STRING, 42));
    let call = format!("\n    let b: {BUF_BOOL} = buf(v: 1)\n    User.go1(b)");
    assert_eq!(go("wisgxyh.written_arg", &qs, &call), Ok(41));
    let ps = format!(
        "{}{}",
        at("PInt", "Bag[T = Int64]", 9),
        at("PStr", "Bag[T = String]", 5)
    );
    let call = "\n    let b: Bag[T = String] = Bag.empty()\n    User.go1(b)";
    assert_eq!(go("wisgxyh.written_bare", &ps, call), Ok(5));
}

/// A DIRECT CALL OF THE SPEC'S OPERATION IS HELD TO THE SAME RULE, at load: with one
/// provision at an instance it ran through the run time's dispatch, and with two it loaded
/// and raised `AmbiguousSpecOpDispatch`.
#[test]
fn a_direct_call_is_held_to_the_same_rule() {
    let qb = at("QB", BUF_BOOL, 41);
    let qs = format!("{qb}{}", at("QS", BUF_STRING, 42));
    let pint = at("PInt", "Bag[T = Int64]", 9);
    let ps = format!("{pint}{}", at("PStr", "Bag[T = String]", 5));
    assert_unfixed("wisgxyh.d_one_arg", &qb, "Store.peek(buf(v: 1))", "`N` of `Buf`", &["QB"], "one, arg");
    assert_unfixed("wisgxyh.d_two_arg", &qs, "Store.peek(buf(v: 1))", "`N` of `Buf`", &["QB", "QS"], "two, arg");
    assert_unfixed("wisgxyh.d_one_bare", &pint, "Store.peek(Bag.empty())", "`T` of `Bag`", &["PInt"], "one, bare");
    assert_unfixed("wisgxyh.d_two_bare", &ps, "Store.peek(Bag.empty())", "`T` of `Bag`", &["PInt", "PStr"], "two, bare");
    let generic = format!("{qb}{}", qg());
    assert_eq!(go("wisgxyh.d_gen", &generic, "Store.peek(buf(v: 1))"), Ok(60));
}

/// A SLOT A PROVISION WRITES AT A STRUCTURED TYPE is an instance of it too: `N = Option[T =
/// Int64]` answers no call that leaves `N` unfixed. With a second at `Option[T = String]` the
/// direct call loaded and raised `AmbiguousSpecOpDispatch` at run time.
#[test]
fn a_provision_at_a_structured_instance_is_named_too() {
    let ns = "wisgxyh.structured";
    let opt = at("QO", "Buf[T = Int64, N = Option[T = Int64]]", 43);
    assert_unfixed(ns, &opt, "Store.peek(buf(v: 1))", "`N` of `Buf`", &["QO"], "direct");
    assert_unfixed(ns, &opt, "User.go1(buf(v: 1))", "`N` of `Buf`", &["QO"], "requirement");
    let two = format!("{opt}{}", at("QO2", "Buf[T = Int64, N = Option[T = String]]", 44));
    assert_unfixed(ns, &two, "Store.peek(buf(v: 1))", "`N` of `Buf`", &["QO", "QO2"], "two");
    let call = "\n    let b: Buf[T = Int64, N = Option[T = Int64]] = buf(v: 1)\n    Store.peek(b)";
    assert_eq!(go(ns, &two, call), Ok(43));
}

/// A WITNESS THE CALL SELECTS is the author's choice of dictionary, and answers the slot as it
/// stands. Passes with or without the change.
#[test]
fn a_selected_witness_answers_an_unfixed_slot() {
    let qs = format!("{}{}", at("QB", BUF_BOOL, 41), at("QS", BUF_STRING, 42));
    assert_eq!(
        go("wisgxyh.sel_direct", &qs, "Store.peek[Store = QS](buf(v: 1))"),
        Ok(42)
    );
}

/// CONTROL: AN OPENED EXISTENTIAL IS NO UNFIXED SLOT. `mk() -> Bag`'s `T` is fixed — by
/// `mk`'s body, unknown here — so a provision at one instance does not answer it, and the
/// refusal does not tell the author to write a slot no type they write could fix.
#[test]
fn an_opened_existential_is_not_named_as_unfixed() {
    let ns = "wisgxyh.skolem";
    let errs = load_errors_of(&program(ns, &at("PInt", "Bag[T = Int64]", 9), "User.go1(mk())"));
    assert_refused_naming(
        &errs,
        &[&format!("cannot be supplied for call to `{ns}.User.go1`")],
        "a skolem element",
    );
    assert!(
        !errs.join(" | ").contains("nothing here fixes"),
        "an opened existential is fixed, got {errs:#?}"
    );
}

/// THE SPELLINGS LEFT ALONE: a provision that leaves the slot out of its own head is generic
/// in it, and answers. Passes with or without the change.
#[test]
fn a_provision_leaving_the_slot_out_answers_it() {
    let ns = "wisgxyh.left_out";
    let ground = at("QT", "Buf[T = Int64]", 44);
    assert_eq!(go(ns, &ground, "Store.peek(buf(v: 1))"), Ok(44));
    let src = replace_in_fixture(
        &program(ns, &ground, "Store.peek(buf(v: 1))"),
        "Store.peek(buf(v: 1))",
        "User.go1(buf(v: 1))",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(44));
}

// ── what the rule leaves alone ────────────────────────────────────────────────────────

/// THE EMPTY LITERAL'S ELEMENT IS NO UNFIXED SLOT: it stands for a type no value has, below
/// every instance, so `[]` is answered by a provision at `List[T = Int64]` as a named `[]`
/// is. Read as unfixed it was refused, naming `T` of `List`, where `let xs = []` ran.
#[test]
fn the_empty_literal_is_answered_at_an_instance() {
    let ns = "wisgxyh.empty";
    let pl = at("PL", "List[T = Int64]", 3);
    for call in [
        "Store.peek([])",
        "User.go1([])",
        "\n    let xs = []\n    Store.peek(xs)",
    ] {
        assert_eq!(go(ns, &pl, call), Ok(3), "{call}");
    }
}

/// A PROVISION'S HEAD IS COMPARED AS WRITTEN WHERE PROVISIONS ARE RANKED: an applied head
/// (`Box[V = W]`) is more specific than a bare one (`Box`), and answers. Opened there, the
/// two answered each other and the call was refused as a tie.
#[test]
fn an_applied_head_still_outranks_a_bare_one() {
    let ns = "wisgxyh.rank";
    let heads = "\n  sort Box\n    sort V = ?\n    entity box(n: Int64)\n  end\n  \
                 sort PBare\n    provides Store[State = Box]\n    \
                 operation peek(s: Box) -> Int64 = 1\n  end\n  \
                 sort PApp\n    sort W = ?\n    provides Store[State = Box[V = W]]\n    \
                 operation peek(s: Box[V = W]) -> Int64 = 2\n  end\n";
    for call in ["Store.peek(b)", "User.go1(b)"] {
        let call = format!("\n    let b: Box[V = Int64] = box(n: 1)\n    {call}");
        assert_eq!(go(ns, heads, &call), Ok(2), "{call}");
    }
}

/// IN A RULE BODY THE CALL IS REFUSED BETWEEN TWO PROVISIONS AT INSTANCES, as the tie was,
/// and one is left to the rule body's own check. The instance written on the call's
/// receiver, `Store[State = Buf[T = Int64, N = Bool]].peek(…)`, fixes the slot — the
/// refusal's repair — and answers `QB`'s 41 beside one provision and beside two. (The
/// declared variant was the check-only `requires(Store[State = …])` before the call, which
/// proposal 060.1 §5 removed; it named no dictionary, and beside two provisions it was
/// refused as the bare call is.)
#[test]
fn a_rule_body_call_is_refused_between_two_instances() {
    let qb = at("QB", BUF_BOOL, 41);
    let qs = format!("{qb}{}", at("QS", BUF_STRING, 42));
    let body = "?x <=> Store.peek(buf(v: 1))".to_owned();
    let written = format!("?x <=> Store[State = {BUF_BOOL}].peek(buf(v: 1))");
    for (ns, providers, goals, refused) in [
        ("wisgxyh.rule_one", &qb, &body, false),
        ("wisgxyh.rule_one_written", &qb, &written, false),
        ("wisgxyh.rule_two", &qs, &body, true),
        ("wisgxyh.rule_two_written", &qs, &written, false),
    ] {
        let rules = format!("{providers}\n  rule r(?x) :- {goals}\n");
        let src = program(ns, &rules, "0");
        if refused {
            assert_refused_naming(
                &load_errors_of(&src),
                &[
                    "nothing here fixes `N` of `Buf`",
                    &format!("`{ns}.QB` and `{ns}.QS` provide `{ns}.Store` only at an instance"),
                ],
                ns,
            );
        } else {
            let mut kb = crate::common::load_kb_with(&src);
            assert_eq!(crate::common::one_definite_int(&mut kb, &format!("{ns}.r")), Some(41), "{ns}");
        }
    }
}
