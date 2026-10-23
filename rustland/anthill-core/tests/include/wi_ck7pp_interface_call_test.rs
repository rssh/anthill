//! WI-20261017-CK7PP — A CALL OF A SORT'S MEMBER IS REFUSED WHERE ITS CARRIER CANNOT
//! ANSWER IT (kernel-language.md §5.4, *At the call*).
//!
//! A call of a body-less member of a sort `S` that may be provided is answered by the member
//! of its carrier (§5.3). In an operation body or a const's value it is refused at load
//! when:
//!
//!   * the carrier is `S` itself and `S`'s own member runs nothing. Here: a member that
//!     names `S` in its result alone (`Set.empty() -> Self`, `LogicalStream.guard(cond:
//!     Bool) -> LogicalStream[…]`, a user `Mon.unit(x: Int64) -> Self`) — `Self` in a sort
//!     is that sort, so the result names no provider, while the type expected of it still
//!     binds `S`'s parameters, and a provision at that binding answers; a call in a member
//!     of a sort WITH constructors that provides `S`, which runs at its own sort; a body run
//!     at `S` itself that calls such a member, or a member of a sort `S` provides; and the
//!     bare zero-arg reading, which is not dispatched. Sites: `unselectable_spec_operation_
//!     call` (kb/typing/call_class.rs, before the dispatch) and the result-only check after
//!     the dispatch in kb/typing/apply.rs;
//!   * the carrier is a sort, known at load, that supplies no such member by any route and
//!     `S`'s own runs nothing — `LogicalStream.mplus(r, r)` over a `Relation`
//!     (`CarrierSuppliesNoMember`, kb/typing/apply.rs). In a user program a sort with
//!     constructors that lacks a member is refused at its provision already; the forwarding
//!     row on a host carrier is the one way left to reach it.
//!
//! And ONE PROVIDER NO LONGER FIXES A CARRIER the call leaves open
//! (`resolve_nullary_result_carrier`, kb/typing/candidates.rs).
//!
//! On the tree before, every refused row loaded clean and died `OperationBodyMissing` when
//! it ran, except: the lone-provider row, which ran `Box`'s member; and the case-4 row and
//! `g() -> Box = Mon.unit(7)`, which were refused for their return type — they pin which
//! refusal stands, not that one exists.
//!
//! NOT REFUSED, by the user's decision (2026-10-23): a call on an argument typed `S`. The
//! value exists, so its own sort answers when the call runs, whether or not a provider of
//! `S` is loaded, and at whatever type arguments.
//!
//! BACKED OUT, MEASURED (2026-10-23), one switch at a time in one build, every other row
//! green each time:
//!   * the result-only check after the dispatch — the `Set.empty`, `LogicalStream`, const
//!     and case-4 rows;
//!   * the result-only leg before the dispatch — `result_only_sibling_in_a_default_body_…`
//!     (a body-less ground member is caught after the dispatch too; a member with a default
//!     body never reaches it);
//!   * result-only siblings in the default-body walk — the same row;
//!   * a provided sort's member in that walk — `a_provided_sorts_member_in_a_body_run_…`;
//!   * the bare reading asked like a dispatched call — `result_only_bare_name_…`;
//!   * the exemption for any providing sort restored — `a_call_in_a_member_of_a_providing_…`;
//!   * the bracket repair for a sort with no parameter restored — the same row;
//!   * the carrier check — `supplies_no_member_relation_mplus_…`;
//!   * the lone-provider pick restored — `one_provider_does_not_fix_an_open_carrier` and
//!     `wi508_nullary_carrier_dispatch_test::wi508_one_provider_does_not_pin_the_carrier`;
//!   * the result-only check asked before the dispatch for every signature (the first
//!     version of this change) — `result_only_member_is_answered_by_a_provision_at_its_…`.
//! PASS EITHER WAY, BY DESIGN: the rows named `control_…`, each a program that loads and,
//! where it has an entry, runs.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

#[track_caller]
fn assert_loads(src: &str, why: &str) {
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "{why}: expected a clean load, got {errs:#?}");
}

const MON_SELF: &str = r#"
  sort Mon
    operation unit(x: Int64) -> Self
  end
  sort Box
    entity box(v: Int64)
    provides Mon
    operation unit(x: Int64) -> Box = box(v: x)
    operation get(b: Box) -> Int64 =
      match b
        case box(v: n) -> n
  end
"#;

const MON_C: &str = r#"
  sort Mon
    sort C = ?
    operation unit(x: Int64) -> C
    operation make() -> C
    operation get(m: C) -> Int64
  end
  sort Box
    entity box(v: Int64)
    provides Mon[C = Box]
    operation unit(x: Int64) -> Box = box(v: x)
    operation make() -> Box = box(v: 9)
    operation get(m: Box) -> Int64 =
      match m
        case box(v: n) -> n
  end
"#;

const MY_SET: &str = r#"
  sort MySet
    sort T = ?
    operation contains(s: Self, x: T) -> Bool
  end
"#;

// ── the carrier is the sort itself ───────────────────────────────────────────────────

/// `LogicalStream`'s construction members name the sort in their result alone, and nothing
/// provides one with a member: each call reaches the sort's own, which runs nothing.
#[test]
fn result_only_logical_stream_members_are_refused() {
    for (call, short) in [
        ("LogicalStream.guard(true)", "guard"),
        ("LogicalStream.pure(())", "pure"),
        ("LogicalStream.empty()", "empty"),
    ] {
        let errs = load_errors_of(&format!(
            "namespace ck1a\n  import anthill.prelude.{{Unit, LogicalStream}}\n  \
             operation g() -> LogicalStream[T = Unit, E = {{}}] = {call}\nend\n"
        ));
        assert_refused_naming(
            &errs,
            &[
                &format!("a call of `anthill.prelude.LogicalStream.{short}` that nothing can run"),
                &format!("`{short}` names `anthill.prelude.LogicalStream` in its result alone"),
            ],
            call,
        );
    }
}

/// `Set.empty()` is refused; the `Set.insert` around it, whose argument stands at `Set`, is
/// not what the refusal names.
#[test]
fn result_only_set_empty_is_refused() {
    let errs = load_errors_of(
        "namespace ck1b\n  import anthill.prelude.{Int64, Set}\n  \
         operation s() -> Set[T = Int64] = Set.insert(Set.empty(), 1)\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["a call of `anthill.prelude.Set.empty` that nothing can run"],
        "Set.empty()",
    );
    assert!(!errs.join(" ").contains("Set.insert"), "{errs:#?}");
}

/// A sort of the user's own with a provider: `Mon.unit(7)` names no provider, whatever the
/// result is expected at. The provider's own member is the repair, and runs.
#[test]
fn result_only_user_member_is_refused_and_the_providers_member_runs() {
    for body in ["k() -> Mon = Mon.unit(7)", "g() -> Box = Mon.unit(7)"] {
        let errs = load_errors_of(&format!(
            "namespace ck1c\n  import anthill.prelude.{{Int64}}\n{MON_SELF}  operation {body}\nend\n"
        ));
        assert_refused_naming(
            &errs,
            &[
                "a call of `ck1c.Mon.unit` that nothing can run",
                "`unit` names `ck1c.Mon` in its result alone",
                "`Provider.unit(…)`",
            ],
            body,
        );
    }
    assert_eq!(
        run_int64(
            &format!(
                "namespace ck1cok\n  import anthill.prelude.{{Int64}}\n{MON_SELF}  \
                 operation drive() -> Int64 = Box.get(Box.unit(7))\nend\n"
            ),
            "ck1cok.drive",
        ),
        Ok(7),
    );
}

/// A default body that calls a result-only sibling, run at the sort itself, reaches the
/// sibling there.
#[test]
fn result_only_sibling_in_a_default_body_is_refused() {
    let errs = load_errors_of(&format!(
        "namespace ck1d\n  import anthill.prelude.{{Int64}}\n  \
         sort Mon\n    operation unit(x: Int64) -> Self\n    \
         operation two() -> Self = unit(2)\n  end\n  \
         sort Box\n    entity box(v: Int64)\n    provides Mon\n    \
         operation unit(x: Int64) -> Box = box(v: x)\n  end\n  \
         operation k() -> Mon = Mon.two()\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["a call of `ck1d.Mon.two` that nothing can run", "its body calls `ck1d.Mon.unit`"],
        "Mon.two()",
    );
}

const BAG: &str = r#"
  sort Bag
    sort T = ?
    operation empty() -> Self
    operation size(b: Self) -> Int64
  end
  sort IntBag
    entity ib
    provides Bag[T = Int64]
    operation empty() -> IntBag = ib()
    operation size(b: IntBag) -> Int64 = 5
  end
"#;

/// The type expected of a result-only member's result binds the sort's parameters, and a
/// provision at that binding answers: `Bag.empty()` at `Bag[T = Int64]` runs `IntBag`'s.
/// Refused when the result-only check was asked before the dispatch.
#[test]
fn result_only_member_is_answered_by_a_provision_at_its_binding() {
    assert_eq!(
        run_int64(
            &format!(
                "namespace ck1e\n  import anthill.prelude.{{Int64}}\n{BAG}  \
                 operation g() -> Bag[T = Int64] = Bag.empty()\n  \
                 operation drive() -> Int64 = Bag.size(g())\nend\n"
            ),
            "ck1e.drive",
        ),
        Ok(5),
    );
}

/// The bare zero-arg reading `empty` is not dispatched, so no provision answers it through
/// the type expected of it: refused beside the `IntBag` that answers `Bag.empty()`.
#[test]
fn result_only_bare_name_is_refused_beside_a_provision_at_its_binding() {
    let errs = load_errors_of(&format!(
        "namespace ck1f\n  import anthill.prelude.{{Int64}}\n  import ck1f.Bag.{{empty}}\n{BAG}  \
         operation g() -> Bag[T = Int64] = empty\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["a call of `ck1f.Bag.empty` that nothing can run"],
        "bare empty",
    );
}

/// A const's value is run as an operation body is.
#[test]
fn result_only_call_in_a_const_value_is_refused() {
    let errs = load_errors_of(
        "namespace ck1g\n  import anthill.prelude.{Int64, Set}\n  \
         const e: Set[T = Int64] = Set.empty()\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["a call of `anthill.prelude.Set.empty` that nothing can run"],
        "Set.empty() in a const",
    );
}

/// The ticket's case (4): a result expected at a provider. It reported a return mismatch
/// and `missing requires LogicalStream[E = …]`, a repair that does not repair; the call's
/// own refusal stands instead.
#[test]
fn result_only_call_expected_at_a_provider_is_refused_without_a_missing_requires() {
    let errs = load_errors_of(
        "namespace ck4\n  import anthill.prelude.{Unit, LogicalStream, Relation}\n  \
         operation g() -> Relation[T = Unit, E = {}] = LogicalStream.guard(true)\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["a call of `anthill.prelude.LogicalStream.guard` that nothing can run"],
        "guard expected at a Relation",
    );
    assert!(!errs.join(" ").contains("missing `requires"), "{errs:#?}");
}

/// A call in a member of a sort WITH constructors that provides the called sort runs at
/// that sort, which is no instance of the called one: `Sp.name()` in `W` reached `Sp.name`
/// though `W` declares `name`, and `Mon.unit(x)` in `Box` reached `Mon.unit`. Both are
/// refused; the member of the sort itself is the repair.
#[test]
fn a_call_in_a_member_of_a_providing_sort_with_constructors_is_refused() {
    let errs = load_errors_of(
        "namespace ck3a\n  import anthill.prelude.{Int64}\n  \
         sort Sp\n    operation name() -> Int64\n  end\n  \
         sort W\n    entity w\n    provides Sp\n    operation name() -> Int64 = 42\n    \
         operation other() -> Int64 = Sp.name()\n  end\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["a call of `ck3a.Sp.name` that nothing can run", "`Provider.name(…)`"],
        "Sp.name() in a member of W",
    );
    assert!(!errs.join(" ").contains("name[]("), "no bracket names an instance of a sort with no parameter: {errs:#?}");
    let errs = load_errors_of(&format!(
        "namespace ck3b\n  import anthill.prelude.{{Int64}}\n{MON_SELF}  \
         sort Twice\n    entity tw\n    provides Mon\n    \
         operation unit(x: Int64) -> Twice = tw()\n    \
         operation again(x: Int64) -> Mon = Mon.unit(x)\n  end\nend\n"
    ));
    assert_refused_naming(
        &errs,
        &["a call of `ck3b.Mon.unit` that nothing can run"],
        "Mon.unit(x) in a member of Twice",
    );
}

/// A body of a sort without constructors, run at that sort itself, reaches a provided
/// sort's member there: `Mid.other()` has no instance for `Sp.name()` to be answered at.
#[test]
fn a_provided_sorts_member_in_a_body_run_at_the_sort_itself_is_refused() {
    let errs = load_errors_of(
        "namespace ck3d\n  import anthill.prelude.{Int64}\n  \
         sort Sp\n    operation name() -> Int64\n  end\n  \
         sort Mid\n    provides Sp\n    operation other() -> Int64 = Sp.name()\n  end\n  \
         sort W\n    entity w\n    provides Mid\n    operation name() -> Int64 = 42\n  end\n  \
         operation drive() -> Int64 = Mid.other()\nend\n",
    );
    assert_refused_naming(
        &errs,
        &["a call of `ck3d.Mid.other` that nothing can run", "its body calls `ck3d.Sp.name`"],
        "Mid.other() run at Mid",
    );
}

/// CONTROL: a member of a sort WITHOUT constructors that provides the called sort is
/// entered at the instance of the value it was dispatched on, and the call reaches that
/// instance's member.
#[test]
fn control_a_sub_interface_body_reaches_the_values_member() {
    assert_eq!(
        run_int64(
            "namespace ck3c\n  import anthill.prelude.{Int64}\n  \
             sort Sp\n    operation name() -> Int64\n  end\n  \
             sort Mid\n    provides Sp\n    operation other(m: Self) -> Int64 = Sp.name()\n  end\n  \
             sort W\n    entity w\n    provides Mid\n    operation name() -> Int64 = 42\n  end\n  \
             operation drive() -> Int64 = Mid.other(w())\nend\n",
            "ck3c.drive",
        ),
        Ok(42),
    );
}

// ── the carrier supplies no member ───────────────────────────────────────────────────

/// `Relation` provides `LogicalStream` and supplies none of its construction members:
/// `mplus` and `interleave` at a `Relation` reach `LogicalStream`'s own, which run nothing.
/// Both spellings are one call.
#[test]
fn supplies_no_member_relation_mplus_is_refused_in_both_spellings() {
    for (call, short) in [
        ("LogicalStream.mplus(r, r)", "mplus"),
        ("r.mplus(r)", "mplus"),
        ("LogicalStream.interleave(r, r)", "interleave"),
    ] {
        let errs = load_errors_of(&format!(
            "namespace ck2\n  import anthill.prelude.{{Int64, LogicalStream, Relation}}\n  \
             operation h(r: Relation[T = Int64, E = {{}}]) -> LogicalStream[T = Int64, E = {{}}] \
             = {call}\nend\n"
        ));
        assert_refused_naming(
            &errs,
            &[
                &format!(
                    "a call of `anthill.prelude.LogicalStream.{short}` at \
                     `anthill.prelude.Relation` that nothing can run"
                ),
                &format!("supplies no `{short}`"),
            ],
            call,
        );
    }
}

/// CONTROL: the same call on an argument typed `LogicalStream` is answered by the value's
/// own sort when it runs.
#[test]
fn control_mplus_on_an_abstract_argument_loads() {
    assert_loads(
        "namespace ck2c\n  import anthill.prelude.{Int64, LogicalStream}\n  \
         operation h(r: LogicalStream[T = Int64, E = {}]) -> LogicalStream[T = Int64, E = {}] \
         = LogicalStream.mplus(r, r)\nend\n",
        "mplus over an abstract LogicalStream",
    );
}

// ── one provider ─────────────────────────────────────────────────────────────────────

/// `Mon.make()` with its carrier left open ran `Box`'s member because `Box` was the one
/// provider. It is refused; the bracket and the expected type each name the carrier.
#[test]
fn one_provider_does_not_fix_an_open_carrier() {
    let errs = load_errors_of(&format!(
        "namespace ck5\n  import anthill.prelude.{{Int64}}\n{MON_C}  \
         operation g() -> Int64 = {{ let _ = Mon.make()  1 }}\nend\n"
    ));
    assert_refused_naming(&errs, &["ck5.Mon.make", "Mon[C = …]"], "Mon.make() left open");
    for (body, want) in [
        ("Mon.get(Mon.make[C = Box]())", 9),
        ("{ let b: Box = Mon.make()  Mon.get(b) }", 9),
    ] {
        assert_eq!(
            run_int64(
                &format!(
                    "namespace ck5ok\n  import anthill.prelude.{{Int64}}\n{MON_C}  \
                     operation drive() -> Int64 = {body}\nend\n"
                ),
                "ck5ok.drive",
            ),
            Ok(want),
            "{body}",
        );
    }
}

// ── controls ─────────────────────────────────────────────────────────────────────────

/// CONTROL: a result at the sort's carrier parameter names the carrier, through the type
/// expected of it or the call's bracket.
#[test]
fn control_a_result_at_the_carrier_parameter_names_the_carrier() {
    for body in ["Mon.get(g())", "Mon.get(Mon.unit[C = Box](7))"] {
        assert_eq!(
            run_int64(
                &format!(
                    "namespace ck6\n  import anthill.prelude.{{Int64}}\n{MON_C}  \
                     operation g() -> Box = Mon.unit(7)\n  \
                     operation drive() -> Int64 = {body}\nend\n"
                ),
                "ck6.drive",
            ),
            Ok(7),
            "{body}",
        );
    }
}

/// CONTROL: a call on an argument typed `S` runs the member of the value's sort, in both
/// spellings.
#[test]
fn control_an_abstract_argument_is_answered_by_its_value() {
    let src = format!(
        "namespace ck7\n  import anthill.prelude.{{Int64, Bool}}\n{MY_SET}  \
         sort OneSet\n    entity one(v: Int64)\n    provides MySet[T = Int64]\n    \
         operation contains(s: OneSet, x: Int64) -> Bool = true\n  end\n  \
         operation byDot(s: MySet[T = Int64]) -> Int64 = if s.contains(1) then 11 else 10\n  \
         operation byName(s: MySet[T = Int64]) -> Int64 = if MySet.contains(s, 2) then 21 else 20\n  \
         operation drive() -> Int64 = byDot(one(v: 1)) + byName(one(v: 1))\nend\n"
    );
    assert_eq!(run_int64(&src, "ck7.drive"), Ok(32));
}

/// CONTROL: with nothing providing the sort, or a provider at another type argument only,
/// a call on an argument typed `S` still loads — the user's decision, 2026-10-23. So does
/// one over the stdlib's `Set`.
#[test]
fn control_an_abstract_argument_loads_with_no_provider() {
    for (extra, call) in [
        ("", "MySet.contains(s, 1)"),
        ("", "s.contains(1)"),
        (
            "  sort StrSet\n    entity str(v: String)\n    provides MySet[T = String]\n    \
             operation contains(s: StrSet, x: String) -> Bool = true\n  end\n",
            "s.contains(1)",
        ),
    ] {
        assert_loads(
            &format!(
                "namespace ck8\n  import anthill.prelude.{{Int64, Bool, String}}\n{MY_SET}{extra}  \
                 operation c(s: MySet[T = Int64]) -> Bool = {call}\nend\n"
            ),
            call,
        );
    }
    assert_loads(
        "namespace ck8s\n  import anthill.prelude.{Int64, Bool, Set}\n  \
         operation c(s: Set[T = Int64]) -> Bool = s.contains(1)\nend\n",
        "Set.contains on an argument",
    );
}
