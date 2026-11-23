//! WI-20261121-XS9YD — one lambda annotation that reads a sibling both off itself and through a
//! field loads, and runs. Over `sort WrapH { sort L = ?; entity wraph(f: Box[T = List[T = ?]], l:
//! L) }`, `let g = lambda (a: WrapH[L = State], k: Pair2[A = a.L, B = a.f.T]) -> 42` was refused
//! "type mismatch in <binder>.k (binder-annotation): expected Pair2[A = State, B = List[T = ?T]],
//! got Pair2[A = State[P = ?P], B = List[T = ?T]]" (MEASURED on 338cce4e8; WI-20261121-204T6
//! pinned it as refused and not crashed).
//!
//! The two `?T` were two unknowns. `a`'s closing mints a rigid for `State`'s `P`, a slot nested in
//! a written binding, so the member `a.L` is read off `a` as written (204T6: read off the closed
//! `a` it is that rigid, which has no `requires` bound). The lambda's own tuple read the whole
//! annotation so, in a record of its own, and the binder check read it with `a` closed, in the
//! body's record, so the field's nested slot (`List`'s `T`) was opened once in each. The `A`
//! halves were never the difference: `State` conforms to `State[P = ?P]` (MEASURED: with `f:
//! Box[T = List[T = Int64]]` the lambda loaded).
//!
//! Now, in two parts (`read_list_in_order`):
//!  * THE BODY'S READING: only the MEMBER is read off the sibling as written
//!    (`read_minted_siblings_as_written`), and the rest of the annotation as every other is, with
//!    the sibling closed, in the body's record, as the binder check reads it. Two binders (`b:
//!    a.L`, `k: a.f.T`) already split it that way; now one annotation does too, and no reading of
//!    the list keeps a record of its own. The sibling "as written" is its own reading (its
//!    annotation read, not closed), so a member read off a sibling whose annotation projects (`j:
//!    Pair2[A = k.A]`) is read.
//!  * THE LAMBDA'S OWN TUPLE keeps each projection off a binder of the list the lambda's own, read
//!    where the lambda is applied at the arguments, as an operation's parameter is read where the
//!    operation is called (`SiblingReading::Own`). The body's reading in the own tuple made `k`'s
//!    `A` a `State` and lost the `a` it projects: any `State` passed, where `h(a: WrapH[L = State],
//!    b: a.L)` refuses one of another `P` (MEASURED, the review of the first part; the two-binder
//!    form alike since 204T6). The binders are typed at the body's readings, the arrow at the own
//!    tuple.
//!
//! BACK-OUTS, MEASURED — each part alone, with a temporary switch, over a temporary binary of the
//! 14 files whose lambdas' binders carry annotations (315 tests: this one, 204T6's, DNDZF's,
//! SG16K's, 794's, …); every failure is named:
//!  * all of it (the source of 338cce4e8) — 6: each test here but the three controls, the
//!    ticket's refusal quoted above, and the two rows of 204T6 that moved with it
//!    (`a_chain_of_projections_reads_each_at_its_type`, `a_nested_slot_is_closed_once_and_read_at_that_type`);
//!  * the own tuple at the body's reading (the first part alone) — 5: those two of 204T6's,
//!    `each_half_of_the_annotation_is_read_at_the_application` and
//!    `a_chain_reads_the_sibling_as_its_own_reading` (the expected types print as the body's
//!    reading, `Pair2[A = State, …]`, and a `State` of another `P` runs), and
//!    `over_two_binders_the_member_is_read_at_the_argument`;
//!  * the sibling as written being its annotation, not its own reading — 1:
//!    `a_chain_reads_the_sibling_as_its_own_reading`, refused at `j` as its doc quotes;
//!  * no member read as written, every member read off the sibling closed — 1: 204T6's
//!    `a_chain_of_projections_reads_each_at_its_type`, "no `requires` bound on '…State' whose
//!    carrier is this abstract type parameter declares a member 'K'". With the own tuple dependent,
//!    the closing's rigid no longer reaches what an application is checked at; 204T6's exception is
//!    still needed for a `requires` read through the member.
//!
//! PASS WITH ALL OF IT BACKED OUT, BY DESIGN: `split_over_two_binders_runs`,
//! `a_field_with_no_nested_slot_read_both_ways_runs`, the two shapes the ticket names as having no
//! need of the change, and `an_operation_reads_its_parameter_at_the_argument`.
//!
//! NOT HERE: an argument for `B` other than `[]`. `k`'s `B` is `a.f.T` read at `a0`, whose field
//! leaves its element open (`List[T = ?]`), so `[1]` is refused, and so is `a0.f.v`, read off the
//! holder itself, which an operation's parameter takes (WI-20261121-ZPZDY): `NESTED_SLOT_APPLIED`.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// The ticket's sorts.
const SORTS: &str = "  import anthill.prelude.{Int64, List, String}
  sort State
    sort P = ?
    entity state(provider: P)
  end
  sort Pair2
    sort A = ?
    sort B = ?
    entity pair2(a: A, b: B)
  end
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort WrapH
    sort L = ?
    entity wraph(f: Box[T = List[T = ?]], l: L)
  end";

/// The ticket's lambda, in order and written forward.
const IN_ORDER: &str = "a: WrapH[L = State], k: Pair2[A = a.L, B = a.f.T]";
const FORWARD: &str = "k: Pair2[A = a.L, B = a.f.T], a: WrapH[L = State]";

/// The refusal at `B` of an argument that is a list of a known element: `a0`'s field leaves its
/// element open, so `k`'s `B` read there is a list of the unknown it opens to (WI-20261121-ZPZDY).
const NESTED_SLOT_APPLIED: &str = "type mismatch in g.k (op-arg): expected Pair2[A = State[P = Int64], B = List[T = ?T]], got Pair2[A = State[P = Int64], B = List[T = Int64]]";

/// `go`, which binds `g` to `lambda ({params}) -> 42`, a `State` `u` and a holder `a0` of it, and
/// ends with `tail`.
fn program(ns: &str, params: &str, tail: &str) -> String {
    format!(
        "namespace {ns}
{SORTS}
  operation go() -> Int64 =
    let u = state(provider: 1)
    let a0 = wraph(f: box(v: [1]), l: u)
    let g = lambda ({params}) -> 42
    {tail}
end
"
    )
}

#[track_caller]
fn assert_runs(src: &str, ns: &str, why: &str) {
    assert_eq!(run_int64(src, &format!("{ns}.go")), Ok(42), "{why}");
}

/// `src` is refused once, naming `refusal`.
#[track_caller]
fn assert_refused(src: &str, refusal: &str, why: &str) {
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 1, "{why}: one refusal: {errs:#?}");
    assert_refused_naming(&errs, &[refusal], why);
}

/// The ticket's acceptance: the lambda loads, in order and written forward, and applied where its
/// arguments allow — `k`'s `A` the `State` `a0` holds, its `B` the empty list — it runs.
/// FAILS backed out: each refused, "type mismatch in <binder>.k (binder-annotation)".
#[test]
fn the_tickets_lambda_loads_and_runs() {
    for (tag, params, tail) in [
        ("unapplied", IN_ORDER, "42"),
        ("applied", IN_ORDER, "g(a0, pair2(a: u, b: []))"),
        ("forward_unapplied", FORWARD, "42"),
        ("forward_applied", FORWARD, "g(pair2(a: u, b: []), a0)"),
    ] {
        let ns = format!("wi_xs9yd.ticket.{tag}");
        assert_runs(&program(&ns, params, tail), &ns, tag);
    }
}

/// `k`'s annotation is read at the arguments of the application, each half at the `a` given:
/// `A` is `a0`'s `L`, `State[P = Int64]`, so an `A` that is no `State`, and a `State` of another
/// `P`, are refused; `B` is `a0.f.T`, and a list of a known element meets the nested slot's
/// refusal ([`NESTED_SLOT_APPLIED`]). In either order.
/// FAILS backed out: each refused at the lambda instead, "(binder-annotation)". FAILS with the own
/// tuple at the body's reading: the expected type prints as that reading, `Pair2[A = State, …]`,
/// and `other_p` and `forward_other_p` run (any `State` passes).
#[test]
fn each_half_of_the_annotation_is_read_at_the_application() {
    let no_state = "type mismatch in g.k (op-arg): expected Pair2[A = State[P = Int64], B = List[T = ?T]], got Pair2[A = Int64, B = List[T = ??T]]";
    let other_p = "type mismatch in g.k (op-arg): expected Pair2[A = State[P = Int64], B = List[T = ?T]], got Pair2[A = State[P = String], B = List[T = ??T]]";
    let s = "state(provider: \"s\")";
    for (tag, params, apply, refusal) in [
        ("no_state", IN_ORDER, "g(a0, pair2(a: 1, b: []))".to_owned(), no_state),
        ("forward_no_state", FORWARD, "g(pair2(a: 1, b: []), a0)".to_owned(), no_state),
        ("other_p", IN_ORDER, format!("g(a0, pair2(a: {s}, b: []))"), other_p),
        ("forward_other_p", FORWARD, format!("g(pair2(a: {s}, b: []), a0)"), other_p),
        ("element", IN_ORDER, "g(a0, pair2(a: u, b: [1]))".to_owned(), NESTED_SLOT_APPLIED),
        ("forward_element", FORWARD, "g(pair2(a: u, b: [1]), a0)".to_owned(), NESTED_SLOT_APPLIED),
    ] {
        assert_refused(&program(&format!("wi_xs9yd.halves.{tag}"), params, &apply), refusal, tag);
    }
}

/// A member read off a sibling whose own annotation reads both ways (`j: Pair2[A = k.A, B = a.L]`
/// beside the ticket's `k`): `k`'s closing mints a rigid for the `State` its `A` is, so the body
/// reads `k.A` off `k` as written — its own reading, `Pair2[A = State, B = List[T = ?T]]` — a
/// `State`. Applied, it runs; a `B` of `j` that is no `State` is refused.
/// FAILS backed out: refused at `k`, as the ticket's lambda was; with only the own reading backed
/// out, refused at `j`, "expected Pair2[A = a.L, B = State], got Pair2[A = State[P = ?P], B =
/// State[P = ?P]]" — `k.A` read off `k`'s annotation as written is the projection `a.L`, unread;
/// with the own tuple at the body's reading, the refusal of `j` prints `Pair2[A = State, B =
/// State]`.
#[test]
fn a_chain_reads_the_sibling_as_its_own_reading() {
    let params = "a: WrapH[L = State], k: Pair2[A = a.L, B = a.f.T], j: Pair2[A = k.A, B = a.L]";
    for (tag, tail) in [
        ("unapplied", "42"),
        ("applied", "g(a0, pair2(a: u, b: []), pair2(a: u, b: u))"),
    ] {
        let ns = format!("wi_xs9yd.chain.{tag}");
        assert_runs(&program(&ns, params, tail), &ns, tag);
    }
    assert_refused(
        &program(
            "wi_xs9yd.chain.no_state",
            params,
            "g(a0, pair2(a: u, b: []), pair2(a: u, b: 1))",
        ),
        "type mismatch in g.j (op-arg): expected Pair2[A = State[P = Int64], B = State[P = Int64]], got Pair2[A = State[P = Int64], B = Int64]",
        "a `B` of `j` that is no `State`",
    );
}

/// CONTROL — the ticket's two readings over two binders (`b: a.L`, `k: a.f.T`): each annotation
/// reads `a` one way, and the lambda loaded and ran before this change. PASSES WITH ALL OF IT
/// BACKED OUT, BY DESIGN.
#[test]
fn split_over_two_binders_runs() {
    for (tag, params, tail) in [
        ("in_order", "a: WrapH[L = State], b: a.L, k: a.f.T", "g(a0, u, [])"),
        ("forward", "k: a.f.T, b: a.L, a: WrapH[L = State]", "g([], u, a0)"),
    ] {
        let ns = format!("wi_xs9yd.split.{tag}");
        assert_runs(&program(&ns, params, tail), &ns, tag);
    }
}

/// Over two binders, `b: a.L` is read at the `a` given too: a `State` of another `P` is refused
/// at the application, as an operation's parameter refuses it, in either order. It passed since
/// 204T6, `b` being `State` in the lambda's own tuple.
/// FAILS backed out, and with the own tuple at the body's reading: each runs.
#[test]
fn over_two_binders_the_member_is_read_at_the_argument() {
    let other_p = "type mismatch in g.b (op-arg): expected State[P = Int64], got State[P = String]";
    let s = "state(provider: \"s\")";
    for (tag, params, apply) in [
        ("in_order", "a: WrapH[L = State], b: a.L, k: a.f.T", format!("g(a0, {s}, [])")),
        ("forward", "k: a.f.T, b: a.L, a: WrapH[L = State]", format!("g([], {s}, a0)")),
    ] {
        assert_refused(&program(&format!("wi_xs9yd.two.{tag}"), params, &apply), other_p, tag);
    }
}

/// CONTROL — what the lambda's parameters now read as: an operation's `b: a.L` is read at the
/// argument given for `a`, so a `State` of another `P` is refused, and the `State` `a0` holds
/// runs. PASSES EITHER WAY BY DESIGN.
#[test]
fn an_operation_reads_its_parameter_at_the_argument() {
    let program = |ns: &str, b: &str| {
        format!(
            "namespace {ns}
{SORTS}
  operation h(a: WrapH[L = State], b: a.L) -> Int64 = 42
  operation go() -> Int64 =
    let u = state(provider: 1)
    let a0 = wraph(f: box(v: [1]), l: u)
    h(a0, {b})
end
"
        )
    };
    let ns = "wi_xs9yd.operation.same";
    assert_runs(&program(ns, "u"), ns, "the `State` `a0` holds");
    assert_refused(
        &program("wi_xs9yd.operation.other_p", "state(provider: \"s\")"),
        "type mismatch in h.b (op-arg): expected State[P = Int64], got State[P = String]",
        "a `State` of another `P`",
    );
}

/// CONTROL — one annotation reading the sibling both ways through a field that leaves no slot
/// open (`a.st.provider.K` over `st: State[P = MemStore]`, a `State` with a `requires`): the field
/// reads one type in either record, so the two readings agree, and the lambda ran before this
/// change. PASSES WITH ALL OF IT BACKED OUT, BY DESIGN.
#[test]
fn a_field_with_no_nested_slot_read_both_ways_runs() {
    let ns = "wi_xs9yd.no_nested_slot";
    let src = format!(
        "namespace {ns}
  import anthill.prelude.{{Int64, List}}
  sort DataProvider
    sort P = ?
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P = P]
    entity state(provider: P)
  end
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
  end
  sort Pair2
    sort A = ?
    sort B = ?
    entity pair2(a: A, b: B)
  end
  sort WrapMN
    sort L = ?
    entity wrapmn(st: State[P = MemStore], l: L)
  end
  operation go() -> Int64 =
    let u: State[P = MemStore] = state(provider: mem(n: 1))
    let g = lambda (a: WrapMN[L = State], k: Pair2[A = a.L, B = a.st.provider.K]) -> k.b + 1
    g(wrapmn(st: u, l: u), pair2(a: u, b: 41))
end
"
    );
    assert_runs(&src, ns, "a field with no nested slot, read both ways");
}
