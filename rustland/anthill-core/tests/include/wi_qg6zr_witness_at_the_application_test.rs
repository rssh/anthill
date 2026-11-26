//! WI-20261126-QG6ZR — A WITNESS PROVISION IS JUDGED AT THE APPLICATION IT IS, NOT AT THE SORT
//! DISPATCH FILES IT UNDER.
//!
//! Dispatch files each provision under ONE sort: its binding of the spec's single dispatch
//! parameter, by its head (`typing::spec_carrier_param`, `typing::witness_dispatch_carrier`). Over
//! `Sp { sort A = ?  sort B = ?  operation count(xs: List[T = A], b: B) -> Int64 = 0 }` that is
//! `B`, so `W provides Sp[A = Other, B = Int64]` and `W provides Sp[A = W, B = Int64]` are both
//! filed under `Int64`; over `Show { sort T = ?  operation show(x: T) -> Int64 = 0 }`, `Show[T =
//! Box[E = Int64]]` and `Show[T = Box[E = String]]` are both filed under `Box`. Two readers decided
//! by that sort alone (MEASURED on 246f3c962, each row's program):
//!
//! * THE WITNESS MEMBER'S VERDICT (WI-20261126-Q1WE9) was one per `(witness, operation, sort)`, so
//!   a member that fits one application and not the other supplied nothing at either: beside
//!   `W`'s own `Sp[A = W, B = Int64]`, `Sp.count([o(n: 1)], 1)` answered the default's 0 where
//!   `W.count` fits and answers 7. It is per provision now (`KnowledgeBase::
//!   witness_member_supplies_nothing`, keyed by the row).
//! * THE CALL took the supplier found at that sort whatever else it fixed: `Sp.count([w(n: 1)],
//!   1)` ran `W.count`, written for `Other`'s lists, on a list of `W`s, and `Show.show(box(v:
//!   "s"))` ran `WB.show(x: Box[E = Int64])` on a `Box[E = String]`, each answering 7 where
//!   nothing provides the spec at what the call fixes. A witness's member or a provision's
//!   binding now answers only where a provision answering the call's goal supplies it
//!   (`typing::supplier_answers_goal`, decision 1 of `docs/design/spec-carrier-set.md`).
//!
//! Two more of the kind, folded in: a call in a generic body, at a carrier an argument pins and
//! open at the caller's type parameter, is deferred to the caller's requirement where no provision
//! answers it (`requirement_alone_answers_call` in the typer's defaulted arm); and a call of a
//! spec with no dispatch parameter whose fixed type-vars no provision answers is refused, as a call
//! at a carrier none answers is.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * the witness verdict keyed by the sort again: [`beside_its_own_provision_the_witness_member_answers_only_where_it_fits`],
//!   [`through_a_requirement_each_application_answers_its_own`],
//!   [`two_applications_at_one_sort_each_answer_their_own`].
//! * the call's filter left off: [`a_call_at_an_application_no_provision_is_at_is_refused`],
//!   [`a_call_at_another_application_of_the_same_sort_is_refused`], and the second half of the
//!   first and third rows above (the requirement row passes: its call is deferred).
//! * the deferral to the requirement left off: [`through_a_requirement_each_application_answers_its_own`].
//! * the refusal of a call no provision answers left off:
//!   [`a_call_no_provision_answers_with_no_dispatch_parameter_is_refused`].
//! * the answering provisions read by row instead of by provider and application:
//!   `wi1012_static_supplier_tie_test` and twelve more rows of the supplier-tie refusals — a
//!   carrier's provision in its body and a binding in a `namespace` entry are one candidate to the
//!   resolver, read off the first row.
//!
//! PASS EITHER WAY, BY DESIGN: [`the_controls_answer_as_before`].

use anthill_core::eval::value::Value;
use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::KnowledgeBase;

use crate::common::{assert_refused_naming, load_errors_of, try_load_kb_with_files};

fn int_of(kb: KnowledgeBase, op: &str) -> i64 {
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp);
    match interp.call(op, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{op}` did not run to an Int64: {other:?}"),
    }
}

fn loads(src: &str) -> KnowledgeBase {
    try_load_kb_with_files(&[src]).unwrap_or_else(|e| panic!("must load: {e:#?}"))
}

/// `Sp[A, B]` with `count(xs: List[T = A], b: B) -> Int64 = 0`, `Other`, and `W` with values
/// writing `w_provisions` and a `count` for `Other`'s lists; `rest` is the probes.
fn two_vars(ns: &str, w_provisions: &str, rest: &str) -> String {
    format!(
        "namespace test.qg6zr.{ns}\n  import anthill.prelude.{{Int64, List}}\n  \
         sort Sp\n    sort A = ?\n    sort B = ?\n    \
         operation count(xs: List[T = A], b: B) -> Int64 = 0\n  end\n  \
         sort Other\n    entity o(n: Int64)\n  end\n  \
         sort W\n    entity w(n: Int64)\n{w_provisions}    \
         operation count(xs: List[T = Other], b: Int64) -> Int64 = 7\n  end\n{rest}end\n"
    )
}

const AT_OTHER: &str = "  operation atOther() -> Int64 = Sp.count([Other.o(n: 1)], 1)\n";
const AT_W: &str = "  operation atW() -> Int64 = Sp.count([W.w(n: 1)], 1)\n";
const WITNESS: &str = "    provides Sp[A = Other, B = Int64]\n";
const BOTH: &str = "    provides Sp[A = Other, B = Int64]\n    provides Sp[A = W, B = Int64]\n";

/// `Show[T]`, `Box[E]`, and `WB` writing `wb_provisions` and a `show` for `Box[E = Int64]`.
fn one_var(ns: &str, wb_provisions: &str, rest: &str) -> String {
    format!(
        "namespace test.qg6zr.{ns}\n  import anthill.prelude.{{Int64, String}}\n  \
         sort Show\n    sort T = ?\n    operation show(x: T) -> Int64 = 0\n  end\n  \
         sort Box[E]\n    entity box(v: E)\n  end\n  \
         sort WB\n{wb_provisions}    operation show(x: Box[E = Int64]) -> Int64 = 7\n  end\n{rest}end\n"
    )
}

const BOX_INT: &str = "  operation atInt() -> Int64 = Show.show(Box.box(v: 1))\n";
const BOX_STR: &str = "  operation atStr() -> Int64 = Show.show(Box.box(v: \"s\"))\n";

/// THE TICKET'S PROGRAM (t1): nothing provides `Sp` at `A = W` — `W`'s provision is at `A =
/// Other` — so the call at a list of `W`s is refused. It answered 7.
#[test]
fn a_call_at_an_application_no_provision_is_at_is_refused() {
    let errors = load_errors_of(&two_vars("t1", WITNESS, &format!("{AT_OTHER}{AT_W}")));
    assert_refused_naming(
        &errors,
        &["Sp.count.dispatch", "no impl matches", "unresolved: test.qg6zr.t1.Sp[A = test.qg6zr.t1.W, B = anthill.prelude.Int64]"],
        "`W` provides `Sp` at `A = Other`, not at `A = W`",
    );
    assert_eq!(errors.len(), 1, "`atOther` is right: {errors:#?}");
}

/// t2: beside `W`'s own `Sp[A = W, B = Int64]` the call at `Other`'s values runs `W.count`, which
/// fits there, and the call at `W`'s the default, `W.count` not fitting `A = W`. It answered 0
/// and 0: one misfit made the member supply nothing at both provisions filed under `Int64`.
#[test]
fn beside_its_own_provision_the_witness_member_answers_only_where_it_fits() {
    let kb = loads(&two_vars("t2", BOTH, &format!("{AT_OTHER}{AT_W}")));
    assert_eq!(int_of(kb.deep_clone().expect("copy"), "test.qg6zr.t2.atOther"), 7, "`W.count` at `A = Other`");
    assert_eq!(int_of(kb, "test.qg6zr.t2.atW"), 0, "the default at `A = W`");
}

/// t4: the same through a generic `g` requiring `Sp[A = X, B = Int64]`. Inside `g` the call is at
/// the caller's `X`, and the requirement's dictionary is its instance: `W.count` at `A = Other`,
/// the default at `A = W`. It answered 0 and 0, and with the verdict alone 7 and 7 — `W.count`
/// pinned at the carrier `1` fixes, for every `X`.
#[test]
fn through_a_requirement_each_application_answers_its_own() {
    let g = "  sort G\n    sort X = ?\n    requires Sp[A = X, B = Int64]\n    \
             operation g(xs: List[T = X]) -> Int64 = Sp.count(xs, 1)\n  end\n  \
             operation viaOther() -> Int64 = G.g([Other.o(n: 1)])\n  \
             operation viaW() -> Int64 = G.g([W.w(n: 1)])\n";
    let kb = loads(&two_vars("t4", BOTH, g));
    assert_eq!(int_of(kb.deep_clone().expect("copy"), "test.qg6zr.t4.viaOther"), 7, "`W.count` at `A = Other`");
    assert_eq!(int_of(kb, "test.qg6zr.t4.viaW"), 0, "the default at `A = W`");
}

/// t5: a spec with NO dispatch parameter — `A` only inside a list, `B` only in a result — whose
/// call fixes `A = W` beside a provision at `A = Other` alone is refused, naming what it fixes. It
/// ran the default, 0. The call at `Other` reads `B` off the one provision there and runs `W.cnt`.
#[test]
fn a_call_no_provision_answers_with_no_dispatch_parameter_is_refused() {
    let src = |calls: &str| {
        format!(
            "namespace test.qg6zr.t5\n  import anthill.prelude.{{Int64, List}}\n  \
             sort Sp\n    sort A = ?\n    sort B = ?\n    \
             operation count(xs: List[T = A]) -> B\n    \
             operation cnt(xs: List[T = A]) -> Int64 = 0\n  end\n  \
             sort Other\n    entity o(n: Int64)\n  end\n  \
             sort W\n    entity w(n: Int64)\n    provides Sp[A = Other, B = Int64]\n    \
             operation count(xs: List[T = Other]) -> Int64 = 7\n    \
             operation cnt(xs: List[T = Other]) -> Int64 = 7\n  end\n{calls}end\n"
        )
    };
    let kb = loads(&src("  operation atOther() -> Int64 = Sp.cnt([Other.o(n: 1)])\n"));
    assert_eq!(int_of(kb, "test.qg6zr.t5.atOther"), 7, "`W.cnt` at `A = Other`");
    let errors = load_errors_of(&src("  operation atW() -> Int64 = Sp.cnt([W.w(n: 1)])\n"));
    assert_refused_naming(
        &errors,
        &["Sp.cnt", "no provision of `test.qg6zr.t5.Sp` binds `A = test.qg6zr.t5.W`"],
        "nothing provides `Sp` at `A = W`",
    );
    // The rule-body spelling is held to the same rule: it answered 0.
    let errors = load_errors_of(&src("  rule r(?n) :- ?n <=> Sp.cnt([W.w(n: 1)])\n"));
    assert_refused_naming(
        &errors,
        &["Sp.cnt", "no provision of `test.qg6zr.t5.Sp` binds `A = test.qg6zr.t5.W`", "this clause declares"],
        "nothing provides `Sp` at `A = W`, in a rule body",
    );
}

/// u1, A SPEC OF ONE TYPE-VAR: a witness at two applications of one parameterized sort, filed
/// under `Box` both. Its member written for `Box[E = Int64]` answers that one, and the default the
/// other. It answered 0 and 0.
#[test]
fn two_applications_at_one_sort_each_answer_their_own() {
    let provisions = "    provides Show[T = Box[E = Int64]]\n    provides Show[T = Box[E = String]]\n";
    let kb = loads(&one_var("u1", provisions, &format!("{BOX_INT}{BOX_STR}")));
    assert_eq!(int_of(kb.deep_clone().expect("copy"), "test.qg6zr.u1.atInt"), 7, "`WB.show` at `Box[E = Int64]`");
    assert_eq!(int_of(kb, "test.qg6zr.u1.atStr"), 0, "the default at `Box[E = String]`");
}

/// u3: with the `Box[E = Int64]` provision alone, a call at a `Box[E = String]` is refused. It
/// answered 7, `WB.show` run on a box of a string.
#[test]
fn a_call_at_another_application_of_the_same_sort_is_refused() {
    let errors = load_errors_of(&one_var("u3", "    provides Show[T = Box[E = Int64]]\n", BOX_STR));
    assert_refused_naming(
        &errors,
        &["Show.show.dispatch", "no impl matches", "unresolved: test.qg6zr.u3.Show[T = test.qg6zr.u3.Box[E = anthill.prelude.String]]"],
        "`WB` provides `Show` at `Box[E = Int64]` alone",
    );
}

/// CONTROLS, passing either way by design: `W`'s own provision alone answers no call at `Other`
/// (t3); the body-less `count` at `A = W` is refused (t6); the witness's member answers the
/// application it is at (t1's `atOther`, u2).
#[test]
fn the_controls_answer_as_before() {
    let errors = load_errors_of(&two_vars("t3", "    provides Sp[A = W, B = Int64]\n", AT_OTHER));
    assert_refused_naming(
        &errors,
        &["no impl matches", "unresolved: test.qg6zr.t3.Sp[A = test.qg6zr.t3.Other, B = anthill.prelude.Int64]"],
        "nothing provides `Sp` at `A = Other`",
    );
    let bodyless = "namespace test.qg6zr.t6\n  import anthill.prelude.{Int64, List}\n  \
                    sort Sp\n    sort A = ?\n    sort B = ?\n    \
                    operation count(xs: List[T = A], b: B) -> Int64\n  end\n  \
                    sort Other\n    entity o(n: Int64)\n  end\n  \
                    sort W\n    entity w(n: Int64)\n    provides Sp[A = Other, B = Int64]\n    \
                    operation count(xs: List[T = Other], b: Int64) -> Int64 = 7\n  end\n  \
                    operation atW() -> Int64 = Sp.count([W.w(n: 1)], 1)\nend\n";
    assert!(!load_errors_of(bodyless).is_empty(), "the body-less call at `A = W` is refused");
    let kb = loads(&two_vars("t1c", WITNESS, AT_OTHER));
    assert_eq!(int_of(kb, "test.qg6zr.t1c.atOther"), 7);
    let kb = loads(&one_var("u2", "    provides Show[T = Box[E = Int64]]\n", BOX_INT));
    assert_eq!(int_of(kb, "test.qg6zr.u2.atInt"), 7);
}
