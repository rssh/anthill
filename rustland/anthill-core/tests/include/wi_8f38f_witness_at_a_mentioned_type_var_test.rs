//! WI-20261126-8F38F — A WITNESS PROVISION OF A SPEC WHOSE OPERATIONS TAKE THE TYPE PARAMETER ONLY
//! INSIDE ANOTHER TYPE IS ABOUT THE SORT IT BINDS, NOT ABOUT ITS PROVIDER.
//!
//! `sort Sp { sort T = ?  operation count(xs: List[T = T]) -> Int64 = 0 }`: no operation of `Sp`
//! takes a `T` (the list is `List`'s), so the parameter dispatch reads (`typing::spec_carrier_param`)
//! was none, no provision of `Sp` was a witness's (`typing::witness_dispatch_carrier`), and each was
//! filed at its provider. `W provides Sp[T = Other]` then answered `Sp` at `W`: `W`'s
//! `count(xs: List[T = Other])` was `W`'s own supplier, handed a list of `W`s — `Sp.count([w(n:
//! 1)])` answered 7 where nothing provides `Sp` at `W`, and 7 beside `provides Sp[T = W]`, where
//! `W.count` does not fit and the default's 0 runs (MEASURED on 88a94552d, the first two rows).
//!
//! Now the dispatch parameter of a spec of ONE type-var that no operation takes is that type-var
//! where a parameter's type mentions it — inside an application, an arrow, an option — so `W
//! provides Sp[T = Other]` is a witness at `Other`, as decision 6 of
//! `docs/design/spec-carrier-set.md` (`typing::provision_is_own`) already read it.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * the second rung of `spec_carrier_param` taken out: [`a_call_at_the_witness_is_refused`],
//!   [`beside_its_own_provision_the_witness_member_does_not_answer_its_own_values`],
//!   [`through_a_requirement_the_witness_answers_only_the_sort_it_binds`],
//!   [`a_mention_at_any_depth_is_read`].
//! * the rung asked of a spec of several type-vars (the one-type-var gate dropped):
//!   `wi_me8wr_receiver_less_default_test::a_bracket_no_provision_answers_is_refused` — `Pc2[C,
//!   Element]` with `both2(xs: List[T = Element])` made `Element` the parameter, and `Bag provides
//!   Pc2[C = Bag, Element = Int64]`, `Bag`'s own, a witness at `Int64`.
//! * the rung asked of a self-representing spec: the standard library's `Stream`, `FiniteStream`,
//!   `LogicalStream` and `Option` are filed at their element (WI-1076's defect), and 13 rows of
//!   eight files fail, among them
//!   `wi1102_unsatisfiable_requirement_test::a_self_representing_spec_does_not_file_its_element_as_the_carrier`
//!   and `wi1076_self_representing_spec_carrier_test::a_supplier_tie_on_a_self_representing_spec_is_now_refused`.
//!
//! PASS EITHER WAY, BY DESIGN: [`the_witness_answers_the_sort_it_binds`] (the ticket's `atOther`),
//! [`the_own_provision_alone_answers_no_other_sort`] (the ticket's third measurement), and
//! [`an_own_provider_a_valueless_witness_and_a_bracket_still_answer`].

use anthill_core::eval::value::Value;
use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::KnowledgeBase;

use crate::common::{assert_refused_naming, load_errors_of, try_load_kb_with_files};

/// `Sp` over one type-var that `count` takes inside a `List`, beside `Other`, and `W`, with values,
/// writing `w_provisions` and a `count` for `Other`'s lists. `calls` are the probes.
fn program(ns: &str, w_provisions: &str, calls: &str) -> String {
    format!(
        "namespace test.f38f.{ns}\n  import anthill.prelude.{{Int64, Bool, List}}\n  \
         sort Sp\n    sort T = ?\n    operation count(xs: List[T = T]) -> Int64 = 0\n  end\n  \
         sort Other\n    entity o(n: Int64)\n  end\n  \
         sort W\n    entity w(n: Int64)\n{w_provisions}    \
         operation count(xs: List[T = Other]) -> Int64 = 7\n  end\n\
         {calls}end\n"
    )
}

const AT_OTHER: &str = "  operation atOther() -> Int64 = Sp.count([Other.o(n: 1)])\n";
const AT_W: &str = "  operation atW() -> Int64 = Sp.count([W.w(n: 1)])\n";

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

/// THE TICKET'S PROGRAM: nothing provides `Sp` at `W` — `W`'s provision is about `Other` — so the
/// call at a list of `W`s is refused. It loaded, and answered 7: `W.count`, written for `Other`'s
/// lists, handed `W`'s.
#[test]
fn a_call_at_the_witness_is_refused() {
    let errors = load_errors_of(&program("ticket", "    provides Sp[T = Other]\n", &format!("{AT_OTHER}{AT_W}")));
    assert_refused_naming(
        &errors,
        &["test.f38f.ticket.Sp.count.dispatch", "no impl matches", "unresolved: test.f38f.ticket.Sp[T = test.f38f.ticket.W]"],
        "`W` provides `Sp` at `Other`, not at `W`",
    );
    assert_eq!(errors.len(), 1, "refused at `atW` alone, `atOther` is right: {errors:#?}");
}

/// THE TICKET'S SECOND MEASUREMENT: beside `provides Sp[T = W]`, a call at `W`'s values runs the
/// default — `W.count` takes `Other`'s lists, so it does not fit `Sp.count` at `T = W` and is no
/// supplier there (kernel-language §8.7, *A member that does not fit is no supplier*) — and the call
/// at `Other`'s runs `W.count`. Both answered 7.
#[test]
fn beside_its_own_provision_the_witness_member_does_not_answer_its_own_values() {
    let src = program(
        "both",
        "    provides Sp[T = Other]\n    provides Sp[T = W]\n",
        &format!("{AT_OTHER}{AT_W}"),
    );
    let kb = loads(&src);
    assert_eq!(int_of(kb.deep_clone().expect("copy"), "test.f38f.both.atOther"), 7, "`W.count` answers `Other`");
    assert_eq!(int_of(kb, "test.f38f.both.atW"), 0, "the default answers `W`, at `W`'s own provision");
}

/// THE CONTROL: the call at `Other`'s values runs the witness's member, as it did. Passes either
/// way by design.
#[test]
fn the_witness_answers_the_sort_it_binds() {
    let kb = loads(&program("other", "    provides Sp[T = Other]\n", AT_OTHER));
    assert_eq!(int_of(kb, "test.f38f.other.atOther"), 7);
}

/// THE TICKET'S THIRD MEASUREMENT, a control: `W`'s own provision alone answers no call at `Other`.
/// Passes either way by design.
#[test]
fn the_own_provision_alone_answers_no_other_sort() {
    let errors = load_errors_of(&program("own", "    provides Sp[T = W]\n", AT_OTHER));
    assert_refused_naming(
        &errors,
        &["no impl matches", "unresolved: test.f38f.own.Sp[T = test.f38f.own.Other]"],
        "nothing provides `Sp` at `Other`",
    );
}

/// THE SAME DEFECT THROUGH A DICTIONARY: a generic `g` requiring `Sp[T = X]`, called at a list of
/// `W`s, runs at `W`'s own provision (the default, 0) and at a list of `Other`s at `W`'s witness
/// provision (`W.count`, 7). The call at `W`'s answered 7: the dictionary of `Sp[T = W]` named
/// `W`, whose `count` was read as its own supplier.
#[test]
fn through_a_requirement_the_witness_answers_only_the_sort_it_binds() {
    let calls = "  sort G\n    sort X = ?\n    requires Sp[T = X]\n    \
                 operation g(xs: List[T = X]) -> Int64 = Sp.count(xs)\n  end\n  \
                 operation viaOther() -> Int64 = G.g([Other.o(n: 1)])\n  \
                 operation viaW() -> Int64 = G.g([W.w(n: 1)])\n";
    let kb = loads(&program("dict", "    provides Sp[T = Other]\n    provides Sp[T = W]\n", calls));
    assert_eq!(int_of(kb.deep_clone().expect("copy"), "test.f38f.dict.viaOther"), 7, "`W.count` answers `Other`");
    assert_eq!(int_of(kb, "test.f38f.dict.viaW"), 0, "the default answers `W`");
}

/// THE MENTION IS READ AT ANY DEPTH: a spec whose one operation takes a function of `T`, or an
/// option of one, is the same shape. The call at `W` is refused, and the call at `Other` runs the
/// witness's member. Each call at `W` loaded and answered 7.
#[test]
fn a_mention_at_any_depth_is_read() {
    let shapes = [
        ("arrow", "f: (x: T) -> Int64", "f: (x: Other) -> Int64", "lambda (x: Other) -> 1", "lambda (x: W) -> 1"),
        ("option", "x: Option[T = T]", "x: Option[T = Other]", "Option.some(Other.o(n: 1))", "Option.some(W.w(n: 1))"),
    ];
    for (ns, spec_param, member_param, at_other, at_w) in shapes {
        let src = |calls: &str| {
            format!(
                "namespace test.f38f.{ns}\n  import anthill.prelude.{{Int64, Bool, List, Option}}\n  \
                 sort Sp\n    sort T = ?\n    operation apply({spec_param}) -> Int64 = 0\n  end\n  \
                 sort Other\n    entity o(n: Int64)\n  end\n  \
                 sort W\n    entity w(n: Int64)\n    provides Sp[T = Other]\n    \
                 operation apply({member_param}) -> Int64 = 7\n  end\n{calls}end\n"
            )
        };
        let kb = loads(&src(&format!("  operation atOther() -> Int64 = Sp.apply({at_other})\n")));
        assert_eq!(int_of(kb, &format!("test.f38f.{ns}.atOther")), 7, "{ns}: `W.apply` answers `Other`");
        let errors = load_errors_of(&src(&format!("  operation atW() -> Int64 = Sp.apply({at_w})\n")));
        assert_refused_naming(
            &errors,
            &["no impl matches", &format!("unresolved: test.f38f.{ns}.Sp[T = test.f38f.{ns}.W]")],
            &format!("{ns}: `W` provides `Sp` at `Other`, not at `W`"),
        );
    }
}

/// CONTROLS, passing either way by design: a sort's own provision (`Other2 provides Sp[T = Self]`)
/// answers with its own member; a witness with no values answers `Other`; a bracket naming the
/// witness selects it.
#[test]
fn an_own_provider_a_valueless_witness_and_a_bracket_still_answer() {
    let src = "namespace test.f38f.ctl\n  import anthill.prelude.{Int64, Bool, List}\n  \
               sort Sp\n    sort T = ?\n    operation count(xs: List[T = T]) -> Int64 = 0\n  end\n  \
               sort Other\n    entity o(n: Int64)\n  end\n  \
               sort Other2\n    entity o2(n: Int64)\n    provides Sp[T = Self]\n    \
               operation count(xs: List[T = Other2]) -> Int64 = 5\n  end\n  \
               sort WV\n    provides Sp[T = Other]\n    \
               operation count(xs: List[T = Other]) -> Int64 = 7\n  end\n  \
               operation own() -> Int64 = Sp.count([Other2.o2(n: 1)])\n  \
               operation valueless() -> Int64 = Sp.count([Other.o(n: 1)])\n  \
               operation bracket() -> Int64 = Sp.count[Sp = WV]([Other.o(n: 1)])\nend\n";
    let kb = loads(src);
    assert_eq!(int_of(kb.deep_clone().expect("copy"), "test.f38f.ctl.own"), 5);
    assert_eq!(int_of(kb.deep_clone().expect("copy"), "test.f38f.ctl.valueless"), 7);
    assert_eq!(int_of(kb, "test.f38f.ctl.bracket"), 7);
}
