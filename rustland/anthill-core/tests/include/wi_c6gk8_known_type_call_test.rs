//! WI-20261105-C6GK8 — proposal 073 stage 1: A CALL AT A TYPE THE PROGRAM KNOWS IS DECIDED
//! AT LOAD, through any chain of provisions (073 §1).
//!
//! `add(1, length(xs))` in `List.length` is `Int64.add`, reached through `Int64 provides
//! Numeric[T = Int64]` and `Numeric provides Additive[T = T]`; a program's own `Box` reaches
//! `Top` through `Box provides Mid` and `Mid provides Top[C = Self]`. Each such call is
//! decided by the typer and stamped on the call, where it used to be left as the spec
//! operation and dispatched by the interpreter on the argument's value at every call. Three
//! sites in kb/typing/apply.rs left it so:
//!
//!   * the `Unique` arm pinned a member only for a body, so a member the host implements
//!     (`Int64.add`, an `operation_map` entry) stayed the spec operation — the commonest
//!     value-directed dispatch of the workspace, `List.length` included. It now pins a member
//!     this runtime can run; one only another language implements stays the spec operation.
//!     The higher-kinded arm and the nullary path (WI-508) asked the same of a body, and a
//!     host member there loaded clean and died at run time, "operation has no body";
//!   * a carrier reaching the spec through a chain of provisions was deferred outright, by
//!     the arm WI-496 added for a dispatch failure the dispatch no longer gives — kept now
//!     only where the dispatch finds no candidate, WI-20261025-053QV's provision row;
//!   * a provision by an intermediate spec answers with that spec's member, which the carrier
//!     answers in its turn by its own member or the intermediate's default (`Box.get` for
//!     `Mid.get`): the dispatch stopped there. `Top.get(box(n: 7))` over a body-less `Mid.get`
//!     loaded and answered nothing; over a bodied one an operation body answered the carrier's
//!     member by eval's carrier override and a rule body the default. The member is now
//!     dispatched as a call of it is, under its own name, and its refusals are the call's.
//!
//! WHAT IT TOUCHED IN A RULE BODY. A clause's declared guard covers the calls at its
//! parameter (060.1 §1), and the weave skipped a call the typer had pinned — so a pin at the
//! value's own type outran the dictionary the citation passed. `atGoal[A = Money, WeakOrd =
//! DescMoney]()` over a bodied `Money.compare` answered `Money`'s `-4` on the tree before,
//! where 060.1 §8.9 has the passed dictionary decide (`4`); the same shape over `Int64`
//! answered `4` only because `Int64.compare` was not pinned, and pinning it gave `-1`
//! (`wi_j9ssg_rule_citation_bracket_test::a_bracket_on_a_paren_less_reference_is_refused`).
//! A carrier-bearing call at the guard's carrier is now woven whatever the typer pinned —
//! except one that writes its own bracket (`collect_covered_calls`,
//! kb/typing/rule_requirements.rs) — and the resolver hands a woven labelled call to the
//! member its dictionary selects by position (`woven_args_at_member`, kb/resolve.rs).
//!
//! BACKED OUT, MEASURED one part at a time in one build, every other row green each time:
//! see each row's own doc.

use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::kb::node_occurrence::{for_each_child, ApplyDispatch, Expr, NodeOccurrence};
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

use crate::common::{interp_for, load_errors_of, one_definite_int, query_unary};

/// What the typer decided for each call of `spec_op` under `roots`: the operation it runs,
/// or `None` for a call left to run time. Walked by hand rather than with
/// `visit_classifications`, which skips an unstamped call — the very answer a row asserts.
fn decided_at_load(
    kb: &KnowledgeBase,
    roots: &[Rc<NodeOccurrence>],
    spec_op: &str,
) -> Vec<Option<String>> {
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = roots.to_vec();
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        if let Expr::Apply { functor, .. } = expr {
            if kb.qualified_name_of(*functor) == spec_op {
                out.push(match o.apply_dispatch() {
                    ApplyDispatch::Pin(t) | ApplyDispatch::NeedsDict(t) => {
                        Some(kb.qualified_name_of(t).to_string())
                    }
                    ApplyDispatch::Unclassified => None,
                });
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    out
}

/// [`decided_at_load`] over the body of the operation `op`.
fn decided_in_op(kb: &KnowledgeBase, op: &str, spec_op: &str) -> Vec<Option<String>> {
    let sym = kb
        .try_resolve_symbol(op)
        .unwrap_or_else(|| panic!("`{op}` resolves"));
    let body = kb
        .op_body_node(sym)
        .unwrap_or_else(|| panic!("`{op}` has a body"));
    decided_at_load(kb, &[Rc::clone(body)], spec_op)
}

/// [`decided_at_load`] over every clause body of the relation `qn`.
fn decided_in_rule(kb: &KnowledgeBase, qn: &str, spec_op: &str) -> Vec<Option<String>> {
    let roots: Vec<Rc<NodeOccurrence>> = kb
        .rule_ids_by_qn(qn)
        .into_iter()
        .flat_map(|rid| kb.rule_body_nodes(rid).to_vec())
        .collect();
    decided_at_load(kb, &roots, spec_op)
}

/// The `Int64` the nullary operation `op` answers.
fn int(interp: &mut Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{op}`: expected an Int64, got {other:?}"),
    }
}

/// The one definite `Int64` the unary relation `qn` answers.
fn rule_int(interp: &mut Interpreter, qn: &str) -> Option<i64> {
    one_definite_int(interp.kb_mut(), qn)
}

fn some(qn: &str) -> Vec<Option<String>> {
    vec![Some(qn.to_string())]
}

/// An interpreter over `src` with the embedder's host function `f` registered under `key`
/// BEFORE the load, as `kb/host_fns.rs` orders it: a fresh load, off the shared base
/// (`wi_rah0z_one_recipe_test`'s `PINNED`).
fn interp_with_host_fn(
    src: &str,
    key: &'static str,
    arity: usize,
    f: fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>,
) -> Interpreter {
    let kb = crate::common::try_load_kb_prepared(src, |kb| {
        kb.register_host_fn(key, arity, f)
            .expect("the registration succeeds");
    })
    .unwrap_or_else(|errs| panic!("expected a clean load; got: {errs:?}"));
    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp);
    interp
}

const ADD: &str = "anthill.prelude.Additive.add";
const MUL: &str = "anthill.prelude.Multiplicative.mul";

/// `List.length`'s `add(1, length(xs))` is `Int64.add`, decided where the standard library is
/// typed, and every list length in the language runs it — called from an operation body and
/// from a rule. FAILS with the member pinned for a body alone (the stamp `None`); the two
/// values pass either way, value-direction computed them before.
#[test]
fn list_length_is_decided_at_load() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.len
  import anthill.prelude.{Int64, List}
  operation len3() -> Int64 = List.length([1, 2, 3])
  rule len(?n) :- List.length([1, 2, 3], ?n)
end
"#,
    );
    assert_eq!(
        decided_in_op(interp.kb(), "anthill.prelude.List.length", ADD),
        some("anthill.prelude.Int64.add"),
    );
    assert_eq!(int(&mut interp, "c6gk8.len.len3"), 3);
    assert_eq!(rule_int(&mut interp, "c6gk8.len.len"), Some(3));
}

/// A `Multiplicative.mul` at `Int64`, written in the program's own operation body and rule
/// body: `Int64.mul`, through `Numeric provides Multiplicative[T = T]`. FAILS with the member
/// pinned for a body alone; the values pass either way.
#[test]
fn multiplicative_mul_at_int64_is_decided_at_load() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.mul
  import anthill.prelude.{Int64, Multiplicative}
  operation dbl(n: Int64) -> Int64 = Multiplicative.mul(2, n)
  operation eight() -> Int64 = dbl(4)
  rule twelve(?r) :- Multiplicative.mul(3, 4, ?r)
end
"#,
    );
    let int64_mul = some("anthill.prelude.Int64.mul");
    assert_eq!(decided_in_op(interp.kb(), "c6gk8.mul.dbl", MUL), int64_mul);
    assert_eq!(
        decided_in_rule(interp.kb(), "c6gk8.mul.twelve", MUL),
        int64_mul
    );
    assert_eq!(rule_int(&mut interp, "c6gk8.mul.twelve"), Some(12));
    assert_eq!(int(&mut interp, "c6gk8.mul.eight"), 8);
}

/// A provision whose other column names the carrier bare is decided at load: behind `Car
/// provides Rel[A = Car, B = Car]`, `Rel[A = Self, B = MyCar]` (`sort MyCar = Car`) and `Rel[A
/// = Self, B = Car[V = ?]]` — each `B` any `Car` (proposal 070) — `Rel.mix(x, y)` over an
/// `Int64` car and a `String` car runs `Car.mix`, 7 (6 + 1), from an operation body and from
/// a rule. FAILS with the provider's own parameters grounded at every column (arm (2.5) of
/// `match_candidate_against_goal`): `A`'s instance binds `V` to `Int64`, `B`'s is refused at
/// `String`, and the dispatch finds no candidate (the stamp `None`); the values pass either
/// way, the run time's value route computing them.
#[test]
fn a_bare_carrier_at_another_column_is_any_instance_at_load() {
    const PROGRAM: &str = r#"
namespace @NS@
  import anthill.prelude.{Int64, String}
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides Rel[A = @A@, B = @B@]
    operation mix[W](a: Self, b: Car[V = W]) -> Int64 = b.n + 1
  end
  sort MyCar = Car
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1, n: 1)
    let y: Car[V = String] = car(v: "s", n: 6)
    Rel.mix(x, y)
  rule viaRule(?r) :- Rel.mix(car(v: 1, n: 1), car(v: "s", n: 6), ?r)
end
"#;
    for (n, a, b) in [
        ("bare", "Car", "Car"),
        ("alias", "Self", "MyCar"),
        ("open", "Self", "Car[V = ?]"),
    ] {
        let ns = format!("c6gk8.rel.{n}");
        let mut interp = interp_for(
            &PROGRAM
                .replace("@NS@", &ns)
                .replace("@A@", a)
                .replace("@B@", b),
        );
        let mix = format!("{ns}.Rel.mix");
        let car_mix = some(&format!("{ns}.Car.mix"));
        assert_eq!(
            decided_in_op(interp.kb(), &format!("{ns}.go"), &mix),
            car_mix,
            "{n}"
        );
        assert_eq!(
            decided_in_rule(interp.kb(), &format!("{ns}.viaRule"), &mix),
            car_mix,
            "{n}"
        );
        assert_eq!(int(&mut interp, &format!("{ns}.go")), 7, "{n}");
        assert_eq!(
            rule_int(&mut interp, &format!("{ns}.viaRule")),
            Some(7),
            "{n}"
        );
    }
}

/// The provider's own parameter is the receiver's slot, so a condition on it reads the receiver's
/// instance: behind `Car provides Rel[A = Car, B = Car] :- Tag[T = V]` with only `Tag[T = Int64]`
/// provided, `Rel.mix(x, y)` at an `Int64` receiver is `Car.mix`, 7, decided at load, and at a
/// `String` receiver it is refused, "unresolved: `Tag[T = String]`"; providing `Tag[T = String]`
/// is the repair (7). FAILS with the provider's parameters grounded at every column (at `Int64`
/// the stamp is `None`); on the tree before, the `String` receiver loaded and answered 7 by
/// value, its condition never asked. CONTROL, passing either way by design: a more specific
/// witness, `Wit provides Rel[A = Car[V = Int64], B = Car[V = String]]`, still answers (500).
#[test]
fn a_condition_on_the_providers_parameter_reads_the_receivers_instance() {
    const PROGRAM: &str = r#"
namespace @NS@
  import anthill.prelude.{Int64, String}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort IntTag
    import @NS@.Tag
    provides Tag[T = Int64]
    operation tag(x: Int64) -> Int64 = x
  end
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    import @NS@.{Rel, Tag}
    sort V = ?
    entity car(v: V, n: Int64)
    provides Rel[A = Car, B = Car] :- Tag[T = V]
    operation mix[W](a: Self, b: Car[V = W]) -> Int64 = b.n + 1
  end
  @EXTRA@
  operation go() -> Int64 =
    let x: Car[V = @X@] = car(v: @XV@, n: 1)
    let y: Car[V = @Y@] = car(v: @YV@, n: 6)
    Rel.mix(x, y)
end
"#;
    let program = |ns: &str, extra: &str, (x, xv): (&str, &str), (y, yv): (&str, &str)| {
        PROGRAM
            .replace("@NS@", ns)
            .replace("@EXTRA@", extra)
            .replace("@X@", x)
            .replace("@XV@", xv)
            .replace("@Y@", y)
            .replace("@YV@", yv)
    };
    let int64 = ("Int64", "1");
    let string = ("String", "\"s\"");
    let mut at_int = interp_for(&program("c6gk8.cond.int", "", int64, string));
    assert_eq!(
        decided_in_op(at_int.kb(), "c6gk8.cond.int.go", "c6gk8.cond.int.Rel.mix"),
        some("c6gk8.cond.int.Car.mix"),
    );
    assert_eq!(int(&mut at_int, "c6gk8.cond.int.go"), 7);
    crate::common::assert_refused_naming(
        &load_errors_of(&program("c6gk8.cond.str", "", string, int64)),
        &[
            "c6gk8.cond.str.Rel.mix",
            "unresolved: c6gk8.cond.str.Tag[T = anthill.prelude.String]",
        ],
        "a condition at the receiver's instance",
    );
    let str_tag = "sort StrTag\n    import c6gk8.cond.rep.Tag\n    provides Tag[T = String]\n    \
                   operation tag(x: String) -> Int64 = 0\n  end";
    let mut repaired = interp_for(&program("c6gk8.cond.rep", str_tag, string, int64));
    assert_eq!(int(&mut repaired, "c6gk8.cond.rep.go"), 7);

    let witness = "sort Wit\n    import c6gk8.cond.wit.{Rel, Car}\n    \
                   provides Rel[A = Car[V = Int64], B = Car[V = String]]\n    \
                   operation mix(a: Car[V = Int64], b: Car[V = String]) -> Int64 = 500\n  end";
    let mut with_witness = interp_for(&program("c6gk8.cond.wit", witness, int64, string));
    assert_eq!(int(&mut with_witness, "c6gk8.cond.wit.go"), 500);
}

/// A program's own two-step chain: `Box provides Mid`, `Mid provides Top[C = Self]`, and
/// `Top.get(box(n: 7))` runs `Mid.get` within `Box`'s `Mid` instance — `midGet(m) * 10`, `70`
/// — in an operation body and in a rule body; `Box` writes no `get`, so `Mid`'s is its answer.
/// `Mid.get`'s own `midGet(m)` is a call at `Self`, an abstract type, and stays the
/// interpreter's until 073 stage 3. FAILS with WI-496's deferral restored (the stamp `None`);
/// the values pass either way. Passes with the rest of the chain not dispatched, by design: the
/// first dispatch's `Mid.get` is the answer here.
#[test]
fn a_call_through_a_two_step_chain_of_own_sorts_is_decided_at_load() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.chain
  import anthill.prelude.{Int64}
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.chain.Top
    provides Top[C = Self]
    operation midGet(m: Self) -> Int64
    operation get(m: Self) -> Int64 = midGet(m) * 10
  end
  sort Box
    import c6gk8.chain.Mid
    entity box(n: Int64)
    provides Mid
    operation midGet(b: Self) -> Int64 = match b case box(n) -> n
  end
  operation probe() -> Int64 = Top.get(box(n: 7))
  rule viaRule(?r) :- Top.get(box(n: 7), ?r)
end
"#,
    );
    let get = "c6gk8.chain.Top.get";
    let mid_get = some("c6gk8.chain.Mid.get");
    assert_eq!(
        decided_in_op(interp.kb(), "c6gk8.chain.probe", get),
        mid_get
    );
    assert_eq!(
        decided_in_rule(interp.kb(), "c6gk8.chain.viaRule", get),
        mid_get
    );
    assert_eq!(rule_int(&mut interp, "c6gk8.chain.viaRule"), Some(70));
    assert_eq!(int(&mut interp, "c6gk8.chain.probe"), 70);
}

/// The same chain where the intermediate spec's member implements nothing: `Mid.get` is
/// body-less, and `Box` answers it with its own `Box.get`, as `Mid.get(box(n: 7))` reaches it.
/// On the tree before, `Top.get(box(n: 7))` loaded and answered nothing in every position: the
/// run time's value route landed on `Mid.get` as well. FAILS with WI-496's deferral restored
/// and with the rest of the chain not dispatched (stamp `None`, then no answer).
#[test]
fn a_chain_whose_intermediate_member_implements_nothing_is_decided_at_load() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.chain2
  import anthill.prelude.{Int64}
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.chain2.Top
    provides Top[C = Self]
    operation get(m: Self) -> Int64
  end
  sort Box
    import c6gk8.chain2.Mid
    entity box(n: Int64)
    provides Mid
    operation get(b: Self) -> Int64 = match b case box(n) -> n
  end
  operation probe() -> Int64 = Top.get(box(n: 7))
  rule viaRule(?r) :- Top.get(box(n: 7), ?r)
end
"#,
    );
    let get = "c6gk8.chain2.Top.get";
    let box_get = some("c6gk8.chain2.Box.get");
    assert_eq!(
        decided_in_op(interp.kb(), "c6gk8.chain2.probe", get),
        box_get
    );
    assert_eq!(
        decided_in_rule(interp.kb(), "c6gk8.chain2.viaRule", get),
        box_get
    );
    assert_eq!(rule_int(&mut interp, "c6gk8.chain2.viaRule"), Some(7));
    assert_eq!(int(&mut interp, "c6gk8.chain2.probe"), 7);
}

/// A chain whose intermediate member has a default the carrier overrides: `Mid.get = 55`,
/// `Box.get = n`. `Top.get(box(n: 7))` is `Box.get`, 7, wherever it is written, as
/// `Mid.get(box(n: 7))` is. FAILS with the chain stopping at a member that has a body, and with
/// the rest of the chain not dispatched: the stamp is `Mid.get`, the operation body answers 7
/// only by eval's carrier override and the rule body 55 (on the tree before, 55 everywhere);
/// and with WI-496's deferral restored (the stamp `None`).
#[test]
fn a_chain_answers_the_carriers_override_of_a_defaulted_member_everywhere() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.dflt
  import anthill.prelude.{Int64}
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.dflt.Top
    provides Top[C = Self]
    operation get(m: Self) -> Int64 = 55
  end
  sort Box
    import c6gk8.dflt.Mid
    entity box(n: Int64)
    provides Mid
    operation get(b: Self) -> Int64 = match b case box(n) -> n
  end
  operation probe() -> Int64 = Top.get(box(n: 7))
  rule viaGoal(?r) :- Top.get(box(n: 7), ?r)
  rule viaValue(?r) :- ?r <=> Top.get(box(n: 7))
end
"#,
    );
    let get = "c6gk8.dflt.Top.get";
    let box_get = some("c6gk8.dflt.Box.get");
    assert_eq!(decided_in_op(interp.kb(), "c6gk8.dflt.probe", get), box_get);
    assert_eq!(
        decided_in_rule(interp.kb(), "c6gk8.dflt.viaGoal", get),
        box_get
    );
    assert_eq!(int(&mut interp, "c6gk8.dflt.probe"), 7);
    assert_eq!(rule_int(&mut interp, "c6gk8.dflt.viaGoal"), Some(7));
    assert_eq!(rule_int(&mut interp, "c6gk8.dflt.viaValue"), Some(7));
}

/// A chain through a provision that binds the operation under another name: `Mid provides
/// Top[C = Self, get = fetch]`, `Box` writing `fetch` and an unrelated `get`. `Top.get(box(n:
/// 7))` is `Box.fetch`, 7, as `Mid.fetch(box(n: 7))` is. FAILS with the member dispatched under
/// the call's own name: `Box.get`'s 1000, where the tree before answered nothing; and with the
/// rest of the chain not dispatched or WI-496's deferral restored (the stamp `None`).
#[test]
fn a_chain_through_a_renamed_binding_reaches_the_renamed_member() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.ren
  import anthill.prelude.{Int64}
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.ren.Top
    provides Top[C = Self, get = fetch]
    operation fetch(m: Self) -> Int64
  end
  sort Box
    import c6gk8.ren.Mid
    entity box(n: Int64)
    provides Mid
    operation fetch(b: Self) -> Int64 = match b case box(n) -> n
    operation get(b: Self) -> Int64 = 1000
  end
  operation probe() -> Int64 = Top.get(box(n: 7))
  rule viaRule(?r) :- Top.get(box(n: 7), ?r)
end
"#,
    );
    let get = "c6gk8.ren.Top.get";
    assert_eq!(
        decided_in_op(interp.kb(), "c6gk8.ren.probe", get),
        some("c6gk8.ren.Box.fetch")
    );
    assert_eq!(int(&mut interp, "c6gk8.ren.probe"), 7);
    assert_eq!(rule_int(&mut interp, "c6gk8.ren.viaRule"), Some(7));
}

/// A chain whose final member reads its sort's requirement slots gets the dictionary laid out
/// for the spec it was dispatched at: `Box requires Tag[T = Int64]` and `provides Mid :-
/// Tag[T = Bool]`, `Top requires Tag[T = Int64]` — `Top.get(box(n: 7))` is `IntTag`'s 107, as
/// `Mid.get(box(n: 7))` is. FAILS with the call classified as `Top.get` over `Mid`'s tree: one
/// arity, another split, and `Box.get` reads `BoolTag`'s 9000 (with two arities, an internal
/// error at the frame push); and with the rest of the chain not dispatched or WI-496's deferral
/// restored: "operation has no body: `Top.get`".
#[test]
fn a_chain_member_reading_its_sorts_requirements_gets_its_own_dictionary() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.req
  import anthill.prelude.{Int64, Bool}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort IntTag
    import c6gk8.req.Tag
    provides Tag[T = Int64]
    operation tag(x: Int64) -> Int64 = x + 100
  end
  sort BoolTag
    import c6gk8.req.Tag
    provides Tag[T = Bool]
    operation tag(x: Bool) -> Int64 = 9000
  end
  sort Top
    import c6gk8.req.Tag
    sort C = ?
    requires Tag[T = Int64]
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.req.Top
    provides Top[C = Self]
    operation get(m: Self) -> Int64
  end
  sort Box
    import c6gk8.req.{Mid, Tag}
    entity box(n: Int64)
    requires Tag[T = Int64]
    provides Mid :- Tag[T = Bool]
    operation get(b: Self) -> Int64 = match b case box(n) -> Tag.tag(n)
  end
  operation probe() -> Int64 = Top.get(box(n: 7))
  rule viaRule(?r) :- Top.get(box(n: 7), ?r)
end
"#,
    );
    assert_eq!(int(&mut interp, "c6gk8.req.probe"), 107);
    assert_eq!(rule_int(&mut interp, "c6gk8.req.viaRule"), Some(107));
}

/// A self-receiver operation through the same kind of chain: `Strm.next(s: Self)`, `Mid
/// provides Strm` declaring its own body-less `next`, and `Cell provides Mid` writing it.
/// `Strm.next(cell(5))` is `Cell.next`; on the tree before it was left at `Mid.next` and found
/// by the argument's value at every call. FAILS with the rest of the chain not dispatched (the
/// stamp `None`); the value passes either way. WI-496's deferral never read a self-receiver
/// call, so restoring it moves nothing here.
#[test]
fn a_self_receiver_call_through_a_chain_is_decided_at_load() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.selfchain
  import anthill.prelude.{Int64}
  sort Strm
    operation next(s: Self) -> Int64
  end
  sort Mid
    import c6gk8.selfchain.Strm
    sort K = ?
    provides Strm
    operation next(m: Self) -> Int64
  end
  sort Cell
    import c6gk8.selfchain.Mid
    entity cell(v: Int64)
    provides Mid[K = Int64]
    operation next(c: Self) -> Int64 = match c case cell(v) -> v + 1
  end
  operation probe() -> Int64 = Strm.next(cell(5))
end
"#,
    );
    assert_eq!(
        decided_in_op(
            interp.kb(),
            "c6gk8.selfchain.probe",
            "c6gk8.selfchain.Strm.next"
        ),
        some("c6gk8.selfchain.Cell.next"),
    );
    assert_eq!(int(&mut interp, "c6gk8.selfchain.probe"), 6);
}

/// What the member's dispatch refuses, the call through the chain is refused for, naming the
/// member, whose bracket repair answers: `Box` provides `Mid` through two specs, `SideA` and
/// `SideB`. FAILS with the member dispatch's verdict dropped, the rest of the chain not
/// dispatched, or WI-496's deferral restored: the program loads and `Top.get(box(n: 7))` answers
/// nothing, as on the tree before; and with the refusal naming the written call, `Top.get`,
/// whose bracket cannot select a provider of `Mid`.
#[test]
fn a_tie_in_the_chain_is_refused_naming_the_member() {
    const PROGRAM: &str = r#"
namespace c6gk8.tie
  import anthill.prelude.{Int64}
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.tie.Top
    provides Top[C = Self]
    operation get(m: Self) -> Int64
  end
  sort SideA
    import c6gk8.tie.Mid
    provides Mid
    operation get(s: Self) -> Int64 = 1
  end
  sort SideB
    import c6gk8.tie.Mid
    provides Mid
    operation get(s: Self) -> Int64 = 2
  end
  sort Box
    import c6gk8.tie.{SideA, SideB}
    entity box(n: Int64)
    provides SideA
    provides SideB
  end
  operation probe() -> Int64 = CALL
end
"#;
    crate::common::assert_refused_naming(
        &load_errors_of(&PROGRAM.replace("CALL", "Top.get(box(n: 7))")),
        &[
            "ambiguous dispatch of `c6gk8.tie.Mid.get`",
            "SideA",
            "SideB",
        ],
        "a tie at the chain's member",
    );
    let mut interp = interp_for(&PROGRAM.replace("CALL", "Mid.get[Mid = SideA](box(n: 7))"));
    assert_eq!(int(&mut interp, "c6gk8.tie.probe"), 1);
}

/// The member dispatch's double supply is the call's, naming the member: `Box` supplies `get`
/// twice, its own and the instance binding `get = alt`. The advised repair, "keep exactly one",
/// with its own deleted: `alt` answers 2 (a bound operation takes the spec at a `Self` receiver,
/// `alt(b: Mid)`). FAILS with the member dispatch's verdict dropped, the rest of the chain not
/// dispatched, or WI-496's deferral restored (a clean load, the call answering nothing); and with
/// the refusal naming the written call.
#[test]
fn a_double_supply_at_the_member_is_refused_naming_it() {
    const DUP: &str = r#"
namespace c6gk8.dup
  import anthill.prelude.{Int64}
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.dup.Top
    provides Top[C = Self]
    operation get(m: Self) -> Int64
  end
  sort Box
    import c6gk8.dup.Mid
    entity box(n: Int64)
    provides Mid[get = alt]
    OWN
    operation alt(b: Mid) -> Int64 = 2
  end
  operation probe() -> Int64 = Top.get(box(n: 7))
end
"#;
    crate::common::assert_refused_naming(
        &load_errors_of(&DUP.replace("OWN", "operation get(b: Self) -> Int64 = 1")),
        &[
            "ambiguous dispatch of `c6gk8.dup.Mid.get`",
            "2 implementations are supplied",
        ],
        "a double supply at the chain's member",
    );
    let mut interp = interp_for(&DUP.replace("OWN", ""));
    assert_eq!(int(&mut interp, "c6gk8.dup.probe"), 2);
}

/// An unmet condition on the carrier's provision of the chain's member is the call's, naming the
/// member: `Box provides Mid :- Tag[T = T]` at `box(n: "s")`, where `box(n: 3)` meets it through
/// `IntTag` (99). FAILS with the member dispatch's verdict dropped, the rest of the chain not
/// dispatched, WI-496's deferral restored, or that deferral taking a dispatch that matched nothing
/// (a clean load); and with the refusal naming the written call.
#[test]
fn an_unmet_condition_at_the_member_is_refused_naming_it() {
    const COND: &str = r#"
namespace c6gk8.mcond
  import anthill.prelude.{Int64, String}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort IntTag
    import c6gk8.mcond.Tag
    provides Tag[T = Int64]
    operation tag(x: Int64) -> Int64 = x
  end
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.mcond.Top
    provides Top[C = Self]
    operation get(m: Self) -> Int64
  end
  sort Box
    import c6gk8.mcond.{Mid, Tag}
    sort T = ?
    entity box(n: T)
    provides Mid :- Tag[T = T]
    operation get(b: Self) -> Int64 = 99
  end
  operation probe() -> Int64 = Top.get(box(n: ARG))
end
"#;
    crate::common::assert_refused_naming(
        &load_errors_of(&COND.replace("ARG", "\"s\"")),
        &[
            "c6gk8.mcond.Mid.get.dispatch",
            "unresolved: c6gk8.mcond.Tag[T = anthill.prelude.String]",
        ],
        "an unmet condition on the carrier's provision of the chain's member",
    );
    let mut interp = interp_for(&COND.replace("ARG", "3"));
    assert_eq!(int(&mut interp, "c6gk8.mcond.probe"), 99);
}

/// An unmet condition on the provision a chain goes through is refused at load, as on a direct
/// provision: `Mid provides Top[C = Self] :- Tag[T = T]` and `Box provides Mid[T = String]`, with
/// nothing providing `Tag[T = String]`; provided by `StrTag`, `Top.get(box(n: 7))` answers
/// `Mid.get`'s 1. FAILS with WI-496's deferral restored, or taking a dispatch that matched nothing
/// as well as one that found no candidate: the program loads, and the call is left to the run
/// time. Passes with the rest of the chain not dispatched, by design: the refusal is the first
/// dispatch's.
#[test]
fn an_unmet_condition_on_a_chain_provision_is_refused_at_load() {
    const PROGRAM: &str = r#"
namespace c6gk8.cond
  import anthill.prelude.{Int64, String}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Top
    sort C = ?
    operation get(c: C) -> Int64
  end
  sort Mid
    import c6gk8.cond.{Top, Tag}
    sort T = ?
    provides Top[C = Self] :- Tag[T = T]
    operation get(m: Self) -> Int64 = 1
  end
  sort Box
    import c6gk8.cond.Mid
    entity box(n: Int64)
    provides Mid[T = String]
  end
  STRTAG
  operation probe() -> Int64 = Top.get(box(n: 7))
end
"#;
    crate::common::assert_refused_naming(
        &load_errors_of(&PROGRAM.replace("STRTAG", "")),
        &[
            "c6gk8.cond.Top.get.dispatch",
            "unresolved: c6gk8.cond.Tag[T = anthill.prelude.String]",
        ],
        "an unmet condition on the chain's provision",
    );
    let str_tag = "sort StrTag\n    import c6gk8.cond.Tag\n    provides Tag[T = String]\n    \
                   operation tag(x: String) -> Int64 = 0\n  end";
    let mut interp = interp_for(&PROGRAM.replace("STRTAG", str_tag));
    assert_eq!(int(&mut interp, "c6gk8.cond.probe"), 1);
}

/// WI-496's deferral, kept where the dispatch finds no candidate at a carrier the chain
/// reaches: a provision at `Tagger`, a spec over a parameter, answers a `Bk` that provides
/// `Tagger[C = Bk]` (WI-20261025-053QV) — left to the run time, which walks the same chain, and
/// answering `W.d`'s 100. FAILS with the deferral removed: refused at load, "requirement
/// `Desc[T = Bk]` cannot be supplied". The call stays unstamped by design until 053QV's rule
/// reaches the dispatch.
#[test]
fn a_provision_at_a_spec_over_a_parameter_still_answers_its_providers_value() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.desc
  import anthill.prelude.{Int64}
  sort Tagger
    sort C = ?
    operation tag(c: C) -> Int64
  end
  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort W
    import c6gk8.desc.{Desc, Tagger}
    provides Desc[T = Tagger]
    operation d(x: Tagger) -> Int64 = 100
  end
  sort Bk
    import c6gk8.desc.Tagger
    entity bk(k: Int64)
    provides Tagger[C = Bk]
    operation tag(c: Bk) -> Int64 = match c case bk(k) -> k
  end
  operation probe() -> Int64 = Desc.d(bk(k: 0))
end
"#,
    );
    assert_eq!(
        decided_in_op(interp.kb(), "c6gk8.desc.probe", "c6gk8.desc.Desc.d"),
        vec![None]
    );
    assert_eq!(int(&mut interp, "c6gk8.desc.probe"), 100);
}

/// A member only another language implements is not pinned: `Sq.area` has a cpp
/// `operation_map` entry and nothing this runtime runs, so a rule-body goal over
/// `Shape.area(sq(n: 2), 4)` stays undecided, and so does its negation. FAILS with the pin
/// asked of every language's implementation (`op_is_executable`): the goal answers nothing and
/// its negation succeeds definitely, for a call that never ran.
#[test]
fn a_member_only_another_language_implements_is_not_pinned() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace c6gk8.cpp
  import anthill.prelude.{Int64}
  sort Shape
    sort C = ?
    operation area(c: C) -> Int64
  end
  sort Sq
    import c6gk8.cpp.Shape
    entity sq(n: Int64)
    provides Shape[C = Sq]
    operation area(s: Sq) -> Int64 @[host_implemented]
  end
  fact item(1)
  rule noArea(?x) :- item(?x), not(Shape.area(sq(n: 2), 4))
  rule hasArea(?x) :- item(?x), Shape.area(sq(n: 2), 4)
end
namespace c6gk8.cpp
  provides Sq language cpp
    operation_map {
      area: "($1.n * $1.n)"
    }
  end
end
"#,
    );
    for qn in ["c6gk8.cpp.hasArea", "c6gk8.cpp.noArea"] {
        let answers = query_unary(&mut kb, qn);
        assert_eq!(answers.len(), 1, "{qn}: {answers:?}");
        assert!(!answers[0].1, "{qn}: undecided, not definite: {answers:?}");
    }
}

/// A higher-kinded spec's member the host implements is pinned as a bodied one is:
/// `Sized.size(bag(v: 5))` over `Bag.size`, an `operation_map` entry naming an embedder's
/// function, is `Bag.size`, 77, from an operation body and from a rule. FAILS with the pin asked
/// for a body alone (the stamp `None`): the program loads and dies at run time, "operation has
/// no body: `Sized.size`".
#[test]
fn a_higher_kinded_members_host_implementation_is_pinned() {
    fn size_77(_: &mut Interpreter, _: &[Value]) -> Result<Value, EvalError> {
        Ok(Value::Int(77))
    }
    let mut interp = interp_with_host_fn(
        r#"
namespace c6gk8.hk
  import anthill.prelude.{Int64}
  sort Sized[F[T]]
    operation size[A](x: F[A]) -> Int64
  end
  sort Bag
    import c6gk8.hk.Sized
    sort T = ?
    entity bag(v: T)
    provides Sized[F = Self]
    operation size[A](x: Bag[T = A]) -> Int64 @[host_implemented]
  end
  provides Bag language rust
    artifact "nowhere.rs"
    operation_map { size: "c6gk8_size" }
  end
  operation probe() -> Int64 = Sized.size(bag(v: 5))
  rule viaRule(?r) :- Sized.size(bag(v: 5), ?r)
end
"#,
        "c6gk8_size",
        1,
        size_77,
    );
    assert_eq!(
        decided_in_op(interp.kb(), "c6gk8.hk.probe", "c6gk8.hk.Sized.size"),
        some("c6gk8.hk.Bag.size")
    );
    assert_eq!(int(&mut interp, "c6gk8.hk.probe"), 77);
    assert_eq!(rule_int(&mut interp, "c6gk8.hk.viaRule"), Some(77));
}

/// A nullary member the host implements, its carrier read off the type expected of the result,
/// is pinned too: `let b: Box = Mk.make()` over `Box.make`, `Mk`'s `Element` left open so the
/// dispatch finds no candidate and the expected type decides (WI-508). FAILS with the pin asked
/// for a body alone, by that path or by the `Unique` arm it hands the member to: the stamp
/// `None`, and "operation has no body: `Mk.make`" at run time.
#[test]
fn a_nullary_members_host_implementation_is_pinned() {
    fn make_unit0(interp: &mut Interpreter, _: &[Value]) -> Result<Value, EvalError> {
        let functor = interp
            .kb()
            .try_resolve_symbol("c6gk8.hn.Box.unit0")
            .expect("`unit0` resolves");
        Ok(Value::Entity {
            functor,
            pos: Rc::from(Vec::new()),
            named: Rc::from(Vec::new()),
        })
    }
    let mut interp = interp_with_host_fn(
        r#"
namespace c6gk8.hn
  import anthill.prelude.{Int64}
  sort Mk
    sort C = ?
    sort Element = ?
    operation make() -> C
  end
  sort Box
    import c6gk8.hn.Mk
    entity unit0
    provides Mk[C = Box, Element = Int64]
    operation make() -> Box @[host_implemented]
  end
  provides Box language rust
    artifact "nowhere.rs"
    operation_map { make: "c6gk8_make" }
  end
  operation probe() -> Int64 = (let b: Box = Mk.make()  match b case unit0 -> 42)
end
"#,
        "c6gk8_make",
        0,
        make_unit0,
    );
    assert_eq!(
        decided_in_op(interp.kb(), "c6gk8.hn.probe", "c6gk8.hn.Mk.make"),
        some("c6gk8.hn.Box.make")
    );
    assert_eq!(int(&mut interp, "c6gk8.hn.probe"), 42);
}

/// The rule-body guard over a member the typer pins (060.1 §1, §8.9). `Money` provides
/// `WeakOrd` with a bodied `compare`, and `DescMoney` is a witness at `Money` that compares the
/// other way. A clause declaring `WeakOrd[T = A]` reads its calls at `A` through the dictionary
/// its citation passes, wherever the call is written — though the `srcPair` fact types `?a` at
/// `Money`, where the typer pins `Money.compare`; uncited, `Money`'s own answers. A call that
/// writes its own bracket keeps what it selects, cited or not. FAILS with the weave skipping
/// the pinned call (the cited rows `-4`) and, for the bracket rows, with the weave taking a
/// bracketed call too (`Money`'s -4 uncited, the citation's when cited).
#[test]
fn a_guard_decides_a_call_the_typer_pins_at_the_values_type() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.guard
  import anthill.prelude.{Int64, Bool, Error, EmptyStream, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
  sort Money
    import anthill.prelude.Numeric.{sub}
    entity m(n: Int64)
    provides PartialEq[T = Money]
    provides Eq[T = Money]
    provides PartialOrd[T = Money]
    provides WeakOrd[T = Money]
    provides Ord[T = Money]
    operation eq(a: Money, b: Money) -> Bool = match a case m(x) -> (match b case m(y) -> PartialEq.eq(x, y))
    operation compare(a: Money, b: Money) -> Int64 = match a case m(x) -> (match b case m(y) -> sub(x, y))
  end
  sort DescMoney
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Money]
    operation compare(a: Money, b: Money) -> Int64 = match a case m(x) -> (match b case m(y) -> sub(y, x))
  end
  sort BigMoney
    provides Ord[T = Money]
    operation compare(a: Money, b: Money) -> Int64 = 100
  end
  fact srcPair(m(n: 1), m(n: 5))
  rule atGoal[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], srcPair(?a, ?b), WeakOrd.compare(?a, ?b, ?c)
  rule atValue[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], srcPair(?a, ?b), ?c <=> WeakOrd.compare(?a, ?b)
  rule inIf[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], srcPair(?a, ?b), ?c <=> (if true then WeakOrd.compare(?a, ?b) else 0)
  rule inLet[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], srcPair(?a, ?b), ?c <=> (let d = WeakOrd.compare(?a, ?b)  d)
  rule bracketed[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], srcPair(?a, ?b), ?c <=> (let d = WeakOrd.compare[WeakOrd = DescMoney](?a, ?b)  d)
  operation goalDesc() -> Int64 effects {Error, Error[EmptyStream]} = atGoal[A = Money, WeakOrd = DescMoney]().head.c
  operation valueDesc() -> Int64 effects {Error, Error[EmptyStream]} = atValue[A = Money, WeakOrd = DescMoney]().head.c
  operation ifDesc() -> Int64 effects {Error, Error[EmptyStream]} = inIf[A = Money, WeakOrd = DescMoney]().head.c
  operation letDesc() -> Int64 effects {Error, Error[EmptyStream]} = inLet[A = Money, WeakOrd = DescMoney]().head.c
  operation goalOwn() -> Int64 effects {Error, Error[EmptyStream]} = atGoal[A = Money]().head.c
  operation valueOwn() -> Int64 effects {Error, Error[EmptyStream]} = atValue[A = Money]().head.c
  operation bracketOwn() -> Int64 effects {Error, Error[EmptyStream]} = bracketed[A = Money]().head.c
  operation bracketBig() -> Int64 effects {Error, Error[EmptyStream]} = bracketed[A = Money, WeakOrd = BigMoney]().head.c
end
"#,
    );
    let ops = [
        "goalDesc",
        "valueDesc",
        "ifDesc",
        "letDesc",
        "goalOwn",
        "valueOwn",
        "bracketOwn",
        "bracketBig",
    ];
    let got: Vec<(&str, i64)> = ops
        .into_iter()
        .map(|op| (op, int(&mut interp, &format!("c6gk8.guard.{op}"))))
        .collect();
    assert_eq!(
        got,
        vec![
            ("goalDesc", 4),
            ("valueDesc", 4),
            ("ifDesc", 4),
            ("letDesc", 4),
            ("goalOwn", -4),
            ("valueOwn", -4),
            ("bracketOwn", 4),
            ("bracketBig", 4),
        ],
    );
}

/// A woven labelled call reaches a member that spells its parameters otherwise: `Desc.describe(x:
/// T, k: Int64)` behind `Leaf.describe(item: Leaf, n: Int64)`, called `Desc.describe(k: 1, x:
/// ?x)` in a guarded clause — `31`, and the cited `AltDesc`'s `501`. FAILS with the woven call
/// rebuilt on the member with its labels: no definite row, and `.head` raises (on the tree
/// before, the uncited row answered 31 by its pin and the cited one 31 as well); and with the
/// weave skipping the pinned call, the cited row `31`.
#[test]
fn a_woven_labelled_call_reaches_a_member_that_renames_its_parameters() {
    let mut interp = interp_for(
        r#"
namespace c6gk8.lab
  import anthill.prelude.{Int64, Error, EmptyStream}
  sort Desc
    sort T = ?
    operation describe(x: T, k: Int64) -> Int64
  end
  sort Leaf
    import c6gk8.lab.Desc
    entity leaf(v: Int64)
    provides Desc[T = Leaf]
    operation describe(item: Leaf, n: Int64) -> Int64 = match item case leaf(v) -> v * 10 + n
  end
  sort AltDesc
    import c6gk8.lab.{Desc, Leaf}
    provides Desc[T = Leaf]
    operation describe(item: Leaf, n: Int64) -> Int64 = 500 + n
  end
  fact src(leaf(v: 3))
  rule labelled[A](?x: A, ?r) :- Desc[T = A], src(?x), ?r <=> Desc.describe(k: 1, x: ?x)
  operation own() -> Int64 effects {Error, Error[EmptyStream]} = labelled[A = Leaf]().head.r
  operation alt() -> Int64 effects {Error, Error[EmptyStream]} = labelled[A = Leaf, Desc = AltDesc]().head.r
end
"#,
    );
    assert_eq!(int(&mut interp, "c6gk8.lab.own"), 31);
    assert_eq!(int(&mut interp, "c6gk8.lab.alt"), 501);
}
