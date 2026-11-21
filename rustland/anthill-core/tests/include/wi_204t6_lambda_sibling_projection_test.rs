//! WI-20261121-204T6 — a lambda whose parameter projects a sibling parameter is typed, and runs.
//! Over `sort State { sort P = ?; requires DataProvider[P = P]; entity state(provider: P) }`,
//! `let h = lambda (s2: State, k: s2.provider.K) -> check(s2, k)` stopped a build with debug
//! assertions at load, "the holder `s2` was opened at `State` and is read at `State[P = s2.P]`: a
//! re-key gave a path another value", applied or not (MEASURED on d75028d1 with the debug CLI);
//! so did the forward `lambda (k: s2.provider.K, s2: State)`, and the forward one checked against a
//! slot. A release build opened the path afresh, unrecorded.
//!
//! A path names one value for its body, and the body's record holds each holder at the one type it
//! is read at (`PathOpenings`). The lambda arm read the list's annotations — to type the lambda's
//! own tuple — with each sibling bound at its annotation AS WRITTEN (`s2: State`), in the body's
//! record, and the binder check then bound `s2` at its type closed where named (`State[P =
//! s2.P]`) and read `s2.provider` again. Now (`read_list_in_order`, `closed_binder_types`):
//!  * each annotation is read once, in the order the annotations project one another, with each
//!    sibling at its type closed where named, in the body's record; the lambda's own tuple takes
//!    those readings, and each binder's type is that reading closed ONCE — a slot nested in a
//!    written binding takes a fresh rigid at each closing;
//!  * each binder is bound at its closed type in the body's environment before any of the list's
//!    annotations is read there, and takes it at its turn;
//!  * except a sibling an annotation reads off itself (`b: a.L`) whose closing minted a rigid for a
//!    nested slot: that annotation reads it as written, the slot left open, and one that reads it
//!    through a field as well is read in a record of its own.
//!
//! BACK-OUTS, MEASURED — each part alone, with a temporary switch, over the whole `wi_tests` (9689);
//! every failure is in this file but two, named:
//!  * all of it (the list read with its siblings as written, in the body's record, as before) — 7:
//!    each test but the two controls; the ticket's rows panic as quoted above;
//!  * every sibling read as written, not at its closed type — 6: each of those but
//!    `one_annotation_reading_a_sibling_both_ways_is_refused_not_crashed`;
//!  * a sibling read off itself read at its closed type even where that minted a rigid — 3:
//!    `a_chain_of_projections_reads_each_at_its_type` (`k: b.provider.K` reads nothing off the
//!    rigid), `a_sibling_read_off_itself_and_through_a_field` (`apart`) and
//!    `one_annotation_reading_a_sibling_both_ways_is_refused_not_crashed`;
//!  * the annotation reading a sibling both ways read in the body's record — 1:
//!    `one_annotation_reading_a_sibling_both_ways_is_refused_not_crashed`, a panic;
//!  * every annotation read in a record of its own — 3:
//!    `a_slot_nested_in_a_field_is_one_unknown_for_both_readings`,
//!    `a_chain_of_projections_reads_each_at_its_type` (`field`) and
//!    `a_sibling_read_off_itself_and_through_a_field` (`nested_field`), each refused against its own
//!    annotation, "two different unknowns";
//!  * the lambda's own tuple reading its annotations again rather than taking those readings — 5:
//!    `a_chain_of_projections_reads_each_at_its_type`,
//!    `a_nested_slot_is_closed_once_and_read_at_that_type`,
//!    `a_sibling_read_off_itself_and_through_a_field`,
//!    `a_slot_nested_in_a_field_is_one_unknown_for_both_readings` and
//!    `one_annotation_reading_a_sibling_both_ways_is_refused_not_crashed`;
//!  * no binder bound in the body before the list is — 7: five here,
//!    `a_key_of_another_state_is_refused`, `a_forward_projection_reads_the_sibling_at_its_type`,
//!    `a_chain_of_projections_reads_each_at_its_type`,
//!    `a_nested_slot_is_closed_once_and_read_at_that_type` and
//!    `a_sibling_read_off_itself_and_through_a_field`, and two rows of
//!    `wi_dndzf_arrow_parameter_projects_another_test` (`a_lambda_parameter_projects_another_in_either_order`,
//!    `a_written_arrow_parameter_projects_another_in_either_order`): that binding is the only one the
//!    body has of a sibling before the list is bound, so a forward annotation finds none;
//!  * each binder closed again at its turn rather than taking its closed type — 2:
//!    `a_nested_slot_is_closed_once_and_read_at_that_type` and
//!    `a_sibling_read_off_itself_and_through_a_field`, each forward row a panic.
//!
//! PASS WITH ALL OF IT BACKED OUT, BY DESIGN: `against_a_slot_whose_types_are_written_the_list_is_read_as_before`
//! (a slot's components type the binders and nothing is read before their turn) and
//! `a_slot_nested_in_a_field_is_one_unknown_for_both_readings` (no projected binder is closed to
//! another type, so nothing changes — it is the control of the reading kept apart, above).
//!
//! NOT HERE, measured beside it and out of this ticket: `takes(lambda (s2: State[P = MemStore], k:
//! s2.provider.K) -> …)` against `f: (s: State[P = MemStore], j: s.provider.K) -> Int64` is refused
//! "type mismatch in <binder>.k (binder-annotation): expected s2.provider.K, got Int64", with or
//! without this change (WI-20261121-59S43); and a field read two hops off a sibling whose argument
//! is a constructed value (`k: a.st.provider.K` given `wrap0(st: u)`) is refused at the call, "no
//! `requires` bound on 'State' …", an operation's parameter alike (WI-20261121-YKW7E).

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// The ticket's sorts, `Pair` beside them, and `check`, which takes a key of the `State` it is
/// given.
const SORTS: &str = "  import anthill.prelude.{Int64, String, List}
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
  sort Pair
    sort L = ?
    entity pair(l: L)
  end
  operation check(s: State, k: s.provider.K) -> Int64 = 42";

/// The ticket's program: `fwd(u, ju)` whose body is `body`, run by `go` at a `State[P =
/// MemStore]`; `decls` beside it.
fn ticket_program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}
{SORTS}
{decls}
  operation fwd(u: State, ju: u.provider.K) -> Int64 =
    {body}
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41)
end
"
    )
}

/// [`ticket_program`] with a second `State`, `w`, and a key `jw` of its own.
fn two_state_program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}
{SORTS}
{decls}
  operation fwd(u: State, w: State, ju: u.provider.K, jw: w.provider.K) -> Int64 =
    {body}
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, st, 41, 41)
end
"
    )
}

/// `takes`, which applies a function of a `State` and its key, and `takes_forward`, whose
/// function names the key first.
const TAKES: &str = "  operation takes(f: (s: State, k: s.provider.K) -> Int64, x: State, j: x.provider.K) -> Int64 = f(x, j)
  operation takes_forward(f: (j: s.provider.K, s: State) -> Int64, x: State, j: x.provider.K) -> Int64 = f(j, x)";

/// `Hold`, whose field leaves a slot nested in its written binding open (`List`'s `T`), and
/// `HoldL`, which has a type member `L` beside such a field, over `Box`.
const HOLDS: &str = "  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort Hold
    entity hold(f: Box[T = List[T = ?]])
  end
  sort HoldL
    sort L = ?
    entity holdl(f: Box[T = List[T = ?]], l: L)
  end";

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

/// The refusal an application meets where a lambda's parameter reads a slot nested in a field's
/// written binding (`k: h.f.T` over `f: Box[T = List[T = ?]]`): the lambda's `k` is a list of the
/// rigid that slot opens to, which no argument is. Of `[1]` it is right where the field writes `?`
/// (`Hold`, `HoldL`, `WrapH`: an element no argument is known to be), and wrong over `Hold2[X =
/// List]`, whose holder's type fixes it, and for the argument read off the holder itself
/// (`h0.f.v`), which an operation's parameter `k: h.f.T` takes (MEASURED): WI-20261121-ZPZDY. No
/// change of this ticket's: a lambda over a plain `Hold` meets it as before
/// (`a_slot_nested_in_a_field_is_one_unknown_for_both_readings`).
const NESTED_SLOT_APPLIED: &str =
    "type mismatch in g.k (op-arg): expected List[T = ?T], got List[T = Int64]";

/// `body` (a `let g = lambda …` line) runs `go` to 42 left unapplied, and its application
/// `apply` is refused at the argument ([`NESTED_SLOT_APPLIED`]).
#[track_caller]
fn assert_loads_and_applied_refused(ns: &str, decls: &str, body: &str, apply: &str, why: &str) {
    assert_runs(&ticket_program(ns, decls, &format!("{body}\n    42")), ns, why);
    assert_refused(
        &ticket_program(&format!("{ns}.applied"), decls, &format!("{body}\n    {apply}")),
        NESTED_SLOT_APPLIED,
        why,
    );
}

/// The ticket's acceptance: the program runs to 42, and the lambda written and never applied
/// loads (and `go` runs) — the ticket's second program, which panicked at load as the first did.
/// FAILS backed out: both panic at load.
#[test]
fn the_tickets_program_runs() {
    for (tag, body) in [
        ("applied", "let h = lambda (s2: State, k: s2.provider.K) -> check(s2, k)\n    h(u, ju)"),
        ("unapplied", "let h = lambda (s2: State, k: s2.provider.K) -> check(s2, k)\n    42"),
    ] {
        let ns = format!("wi_204t6.ticket.{tag}");
        assert_runs(&ticket_program(&ns, "", body), &ns, tag);
    }
}

/// The ticket's control: `k` is the key of the `State` the lambda is given, so a key of another
/// is refused at the application, and the body handing `k` to `check(u, …)` is refused there.
/// FAILS backed out: each panics at load.
#[test]
fn a_key_of_another_state_is_refused() {
    let other = "type mismatch in h.k (op-arg): expected w.provider.K, got u.provider.K";
    for (tag, body, refusal) in [
        (
            "applied",
            "let h = lambda (s2: State, k: s2.provider.K) -> check(s2, k)\n    h(w, ju)",
            other,
        ),
        (
            "forward",
            "let h = lambda (k: s2.provider.K, s2: State) -> check(s2, k)\n    h(ju, w)",
            other,
        ),
        (
            "body",
            "let h = lambda (s2: State, k: s2.provider.K) -> check(u, k)\n    42",
            "type mismatch in check.k (op-arg): expected u.provider.K, got s2.provider.K",
        ),
    ] {
        assert_refused(
            &two_state_program(&format!("wi_204t6.other.{tag}"), "", body),
            refusal,
            tag,
        );
    }
}

/// A binder may project one written after it (kernel-language §4.4): `k: s2.provider.K` before
/// `s2: State` reads `s2` at the type it is bound at from its turn on — on its own and checked
/// against a slot that names the key first.
/// FAILS backed out: both panic at load.
#[test]
fn a_forward_projection_reads_the_sibling_at_its_type() {
    for (tag, body) in [
        ("own", "let h = lambda (k: s2.provider.K, s2: State) -> check(s2, k)\n    h(ju, u)"),
        ("slot", "takes_forward(lambda (k: s2.provider.K, s2: State) -> check(s2, k), u, ju)"),
    ] {
        let ns = format!("wi_204t6.forward.{tag}");
        assert_runs(&ticket_program(&ns, TAKES, body), &ns, tag);
    }
}

/// CONTROL — against a slot that names each binder's type in order, the binders are typed at its
/// components, annotated or not, and nothing is read before their turn: each runs, and a key of
/// another `State` is refused at the call. PASSES EITHER WAY BY DESIGN.
#[test]
fn against_a_slot_whose_types_are_written_the_list_is_read_as_before() {
    for (tag, body) in [
        ("annotated", "takes(lambda (s2: State, k: s2.provider.K) -> check(s2, k), u, ju)"),
        ("unannotated", "takes(lambda (s2, k) -> check(s2, k), u, ju)"),
    ] {
        let ns = format!("wi_204t6.slot.{tag}");
        assert_runs(&ticket_program(&ns, TAKES, body), &ns, tag);
    }
    assert_refused(
        &two_state_program(
            "wi_204t6.slot.other",
            TAKES,
            "takes(lambda (s2: State, k: s2.provider.K) -> check(s2, k), w, ju)",
        ),
        "type mismatch in takes.j (op-arg): expected w.provider.K, got u.provider.K",
        "a key of another `State` handed to `takes`",
    );
}

/// A chain: `b: a.L` over `a: Pair[L = State]` is a `State`, and `k: b.provider.K` its key. In
/// order it runs, as it did; written backwards it runs too — `b` is read at its turn's type, where
/// before it was read as `a.L` and refused, "cannot access field 'provider' on a receiver with no
/// concrete sort"; and a key of another `State` is refused at the application.
/// FAILS backed out: `backward` (refused as before). `in_order`, `field` and `other` pass with all
/// of it backed out; `field` and `in_order` fail with the parts the module doc lists.
#[test]
fn a_chain_of_projections_reads_each_at_its_type() {
    for (tag, body) in [
        (
            "in_order",
            "let h = lambda (a: Pair[L = State], b: a.L, k: b.provider.K) -> check(b, k)\n    h(pair(l: u), u, ju)",
        ),
        (
            "backward",
            "let h = lambda (k: b.provider.K, b: a.L, a: Pair[L = State]) -> check(b, k)\n    h(ju, u, pair(l: u))",
        ),
    ] {
        let ns = format!("wi_204t6.chain.{tag}");
        assert_runs(&ticket_program(&ns, "", body), &ns, tag);
    }
    // A field read off the middle binder, whose own type is read (`b: a.L` is a `Hold`): bound at
    // that type where the lambda's own types are read, it loads (refused before this review,
    // "expected b.f.T, got List[T = ?T]", the reading as written kept apart, MEASURED).
    // Applied, it meets the refusal of a slot nested in a field (`NESTED_SLOT_APPLIED`).
    assert_loads_and_applied_refused(
        "wi_204t6.chain.field",
        HOLDS,
        "let h0 = hold(f: box(v: [1]))\n    let g = lambda (a: Pair[L = Hold], b: a.L, k: b.f.T) -> 42",
        "g(pair(l: h0), h0, [1])",
        "a field read off the middle binder",
    );
    assert_refused(
        &two_state_program(
            "wi_204t6.chain.other",
            "",
            "let h = lambda (a: Pair[L = State], b: a.L, k: b.provider.K) -> check(b, k)\n    h(pair(l: u), w, ju)",
        ),
        "type mismatch in h.k (op-arg): expected w.provider.K, got u.provider.K",
        "a key of another `State` in the chain",
    );
}

/// A sibling whose type leaves a slot NESTED in a binding open (`h: Hold2[X = List]`, `List`'s `T`)
/// is closed once, and read through a field (`k: h.f.T`) at that closed type by the lambda's own
/// tuple and the binder check alike, in one record: the lambda loads, in either order. Closed again
/// at its turn, `h` took another rigid for that slot and "was opened at `Hold2[X = List[T = ?T]]`
/// and is read at `Hold2[X = List[T = ?T]]`" (MEASURED); read as written by the lambda's own tuple
/// in a record of its own, `k` was refused against its own annotation, "two different unknowns"
/// (MEASURED on this change's first review). Both orders panicked before.
#[test]
fn a_nested_slot_is_closed_once_and_read_at_that_type() {
    let program = |ns: &str, params: &str| {
        format!(
            "namespace {ns}
  import anthill.prelude.{{Int64, List}}
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort Hold2
    sort X = ?
    entity hold2(f: Box[T = X])
  end
  operation size(b: Box[T = List]) -> Int64 = 42
  operation go() -> Int64 =
    let g = lambda ({params}) -> size(h.f)
    42
end
"
        )
    };
    for (tag, params) in [
        ("forward", "k: h.f.T, h: Hold2[X = List]"),
        ("in_order", "h: Hold2[X = List], k: h.f.T"),
    ] {
        let ns = format!("wi_204t6.nested_binding.{tag}");
        assert_runs(&program(&ns, params), &ns, tag);
    }
    // Applied, it is refused at the argument, as a lambda reading a nested slot through a field
    // was before this change (`a_slot_nested_in_a_field_is_one_unknown_for_both_readings`): its
    // `k` is a list of the unknown that slot opens to, which no argument is.
    for (tag, params, apply) in [
        ("forward", "k: h.f.T, h: Hold2[X = List]", "g([1], h0)"),
        ("in_order", "h: Hold2[X = List], k: h.f.T", "g(h0, [1])"),
    ] {
        let applied = program(&format!("wi_204t6.nested_binding.applied.{tag}"), params)
            .replace("    42\n", &format!("    let h0 = hold2(f: box(v: [1]))\n    {apply}\n"));
        assert_refused(&applied, NESTED_SLOT_APPLIED, tag);
    }
}

/// A sibling read both off itself (`b: a.L`) and through a field (`k: a.st.provider.K`). Where its
/// closing names what it leaves open by projections alone (`WrapM`'s `L` is `a.L`), it is bound at
/// that closed type where the lambda's own types are read, as one read through a field only is:
/// applied, it runs. So is `HoldL`, whose field `f` leaves a nested slot open (`k: h.f.T`), in
/// either order — refused before this review against its own annotation, "two different unknowns",
/// the reading kept apart (MEASURED).
///
/// Where its closing fills a slot nested in a written binding with a fresh rigid (`WrapMN[L =
/// State]`, `State`'s `P`), `b: a.L` reads it as written, the `P` left open, and names it `b.P`;
/// `k: a.st.provider.K` reads it at its closed type, as the binder check does — applied, it runs,
/// in either order — and so does `k: a.f.T`, a field leaving a nested slot open: read off `a` as
/// written in a record of its own (this change's third cut), the two readings opened that slot to
/// two rigids, "two different unknowns" (MEASURED, its review).
/// FAILS backed out: each panics at load.
#[test]
fn a_sibling_read_off_itself_and_through_a_field() {
    let decls = "  sort WrapM
    sort L = ?
    entity wrapm(st: State[P = MemStore], l: L)
  end
  sort WrapMN
    sort L = ?
    entity wrapmn(st: State[P = MemStore], l: L)
  end
  sort WrapH
    sort L = ?
    entity wraph(f: Box[T = List[T = ?]], l: L)
  end";
    let decls = format!("{decls}\n{HOLDS}");
    for (tag, body) in [
        (
            "closed",
            "let h = lambda (a: WrapM, b: a.L, k: a.st.provider.K) -> k + 1\n    h(wrapm(st: state(provider: mem(n: 1)), l: 1), 1, 41)",
        ),
        (
            "apart",
            "let h = lambda (a: WrapMN[L = State], b: a.L, k: a.st.provider.K) -> k + 1\n    h(wrapmn(st: state(provider: mem(n: 1)), l: u), u, 41)",
        ),
        (
            "apart_forward",
            "let h = lambda (k: a.st.provider.K, b: a.L, a: WrapMN[L = State]) -> k + 1\n    h(41, u, wrapmn(st: state(provider: mem(n: 1)), l: u))",
        ),
    ] {
        let ns = format!("wi_204t6.both_ways.{tag}");
        assert_runs(&ticket_program(&ns, &decls, body), &ns, tag);
    }
    // Through a field leaving a nested slot open, applied, each meets that slot's refusal
    // (`NESTED_SLOT_APPLIED`).
    for (tag, body, apply) in [
        (
            "nested_field",
            "let h0 = holdl(f: box(v: [1]), l: 1)\n    let g = lambda (h: HoldL, b: h.L, k: h.f.T) -> 42",
            "g(h0, 1, [1])",
        ),
        (
            "nested_field_forward",
            "let h0 = holdl(f: box(v: [1]), l: 1)\n    let g = lambda (k: h.f.T, b: h.L, h: HoldL) -> 42",
            "g([1], 1, h0)",
        ),
        (
            "minted_nested_field",
            "let a0 = wraph(f: box(v: [1]), l: u)\n    let g = lambda (a: WrapH[L = State], b: a.L, k: a.f.T) -> 42",
            "g(a0, u, [1])",
        ),
        (
            "minted_nested_field_forward",
            "let a0 = wraph(f: box(v: [1]), l: u)\n    let g = lambda (k: a.f.T, b: a.L, a: WrapH[L = State]) -> 42",
            "g([1], u, a0)",
        ),
    ] {
        assert_loads_and_applied_refused(
            &format!("wi_204t6.both_ways.{tag}"),
            &decls,
            body,
            apply,
            tag,
        );
    }
}

/// ONE annotation reading a sibling both off itself and through a field, where the sibling's
/// closing minted a rigid for a nested slot (`k: Pair2[A = a.L, B = a.f.T]` beside `a: WrapH[L =
/// State]`): the member wants `a` as written and the field read `a` closed, so it is read with `a`
/// as written, in a record of its own — kept in the body's, `a` would be opened at `WrapH[L =
/// State]` there and read at its closing in the body, a build with debug assertions' stop. STILL
/// REFUSED, an over-rejection: the binder check reads it with `a` closed, and the two readings
/// differ, "type mismatch in <binder>.k (binder-annotation)" (WI-20261121-XS9YD).
/// FAILS with that reading kept in the body's record: a panic at load.
#[test]
fn one_annotation_reading_a_sibling_both_ways_is_refused_not_crashed() {
    let src = format!(
        "namespace wi_204t6.one_annotation
  import anthill.prelude.{{Int64, List}}
  sort State
    sort P = ?
    entity state(provider: P)
  end
  sort Pair2
    sort A = ?
    sort B = ?
    entity pair2(a: A, b: B)
  end
{HOLDS}
  sort WrapH
    sort L = ?
    entity wraph(f: Box[T = List[T = ?]], l: L)
  end
  operation go() -> Int64 =
    let g = lambda (a: WrapH[L = State], k: Pair2[A = a.L, B = a.f.T]) -> 42
    42
end
"
    );
    assert_refused(
        &src,
        "type mismatch in <binder>.k (binder-annotation)",
        "`a.L` and `a.f.T` in one annotation",
    );
}

/// CONTROL — a slot nested in a field's written binding (`k: h.f.T` over `f: Box[T = List[T =
/// ?]]`) is one unknown for the two readings of `k`'s annotation, the lambda's own tuple's and the
/// binder check's, which share the body's record where no projected binder is closed to another
/// type: written and not applied, the lambda loads. Applied, it is refused at the argument, as it
/// was: the lambda's `k` is a list of that unknown. PASSES EITHER WAY BY DESIGN — read in a record
/// of its own, the definition was refused against its own annotation, "two different unknowns"
/// (MEASURED on the first cut of this change, which kept every such reading apart).
#[test]
fn a_slot_nested_in_a_field_is_one_unknown_for_both_readings() {
    let program = |ns: &str, use_it: &str| {
        format!(
            "namespace {ns}
  import anthill.prelude.{{Int64, List}}
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort Hold
    entity hold(f: Box[T = List[T = ?]])
  end
  operation len(b: Box[T = List[T = ?]]) -> Int64 = 42
  operation go() -> Int64 =
    let h0 = hold(f: box(v: [1]))
    let g = lambda (h: Hold, k: h.f.T) -> len(h.f)
    {use_it}
end
"
        )
    };
    let ns = "wi_204t6.nested.unapplied";
    assert_runs(&program(ns, "42"), ns, "the lambda written and not applied");
    assert_refused(
        &program("wi_204t6.nested.applied", "g(h0, [1])"),
        "type mismatch in g.k (op-arg): expected List[T = ?T], got List[T = Int64]",
        "the lambda applied",
    );
}
