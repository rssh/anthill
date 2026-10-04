//! WI-20261001-80ZV8, stage (c), part 3 — A SIBLING CALL IS A CALL: the same-sort fill is
//! gone, and a call inside a sort is placed as any call is.
//!
//! Inside a sort, a call to one of the sort's own operations used to have the callee's sort
//! parameters seeded with the enclosing instance BEFORE its arguments were read (WI-424) —
//! the call-side half of the self tie. Proposal 070 §1.1 makes a sort's parameters ordinary
//! type parameters of each of its operations, fixed per call by the bracket, the arguments or
//! the expected type; §3 deletes the fill. Four things follow, and each has rows here:
//!
//!  * a sibling call AT ANOTHER INSTANCE loads — with the fill a receiver written `Self`
//!    refused it, which is why the fill goes with the migration to `Self`;
//!  * a sibling call NOTHING PLACES ELSEWHERE is still at this instance. That is the rule
//!    `kernel-language.md` §8.1 already states for a bare sibling call, and the evaluator
//!    already hands such a call its caller's frame; the typer now decides it AFTER the
//!    arguments instead of before them, so the two agree;
//!  * a sibling call at another instance RUNS AT THAT INSTANCE. The callee's frame of
//!    requirement dictionaries was inherited from the caller whenever the two were one
//!    sort, which cannot tell an instance from its sort: it is inherited only at the
//!    caller's instance now, and otherwise built for the call's own — or refused where
//!    nothing in scope supplies it, as a call from another sort is;
//!  * a member that needs ITS OWN instance to read an argument against says so. A spec
//!    writes its result in the carrier's terms — `iterator(c: C) -> Strm[c.Element, c.E]`
//!    (user, 2026-10-03) — and the projection is read off the receiver in each of the
//!    three places a receiver can stand.
//!
//! Every row that can RUNS and names its value.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-03), each part present but disabled, over this file's 16 rows:
//!
//! 1. THE FILL RESTORED (typing/apply.rs, the block after `seed_receiver_type_args`, put
//!    back). 7 FAIL: [`a_sibling_call_at_another_instance_loads`] and
//!    [`a_sibling_call_on_a_let_bound_value_at_another_instance_loads`] (both refused
//!    `rev.xs (op-arg): expected MyList[T = ?T], got MyList[T = ?Dst]`),
//!    [`a_sibling_call_at_another_instance_runs_that_instances_provider`],
//!    [`a_sibling_call_at_another_instance_owes_that_instances_requirement`] and
//!    [`a_call_at_another_instance_is_never_handed_the_callers_frame`] (the argument is
//!    refused before any requirement is asked for),
//!    [`the_expected_type_places_a_receiverless_sibling_call`], and
//!    [`a_sibling_call_stands_at_one_instance`], whose second call is then refused at its
//!    FIRST argument.
//! 2. THE PLACEMENT (typing/slots.rs `place_sibling_call_at_callers_instance`, a no-op). 2
//!    FAIL: [`a_sibling_call_nothing_places_elsewhere_is_at_this_instance`] — refused `got
//!    Option[T = Pair[A = ?Out, B = List[T = ?_]]]` — and
//!    [`an_unplaced_sibling_call_is_not_placed_later`], which then loads. The stdlib and
//!    the rest of the suite are the larger witness: the same back-out fails four rows of
//!    `wi_ekwdc_carrier_requires_instantiation_test` and three of
//!    `wi_wbhtm_value_in_type_call_test`, whose fixtures call a parameterless sibling under
//!    `some(pair(…))`.
//! 3. THE INSTANCE TEST (`call_is_at_callers_instance`, answering "here" always — the
//!    inherit as it was). 5 FAIL: [`a_sibling_call_at_another_instance_runs_that_instances_
//!    provider`] (1 for 2), [`a_sibling_call_at_another_instance_owes_that_instances_
//!    requirement`] (loads), [`the_expected_type_places_a_receiverless_sibling_call`],
//!    [`a_sibling_passed_as_a_function_value_is_placed_by_its_arrow`] and
//!    [`a_call_at_another_instance_is_never_handed_the_callers_frame`].
//! 4. THE CALLER'S CLAUSES READ AT THE CALLER'S INSTANCE (typing/requires.rs
//!    `chain_at_callers_instance`, returning the chain as stored). 3 FAIL: the first, the
//!    second and the fourth of part 3's — a dictionary is built, and it is the caller's.
//! 5. THE FRAME STATED BY THE TYPER (typing/apply.rs: `CalleeFrame::Inherited` chosen by
//!    "same sort", as eval used to infer it, instead of by the instance). 1 FAILS:
//!    [`a_call_at_another_instance_is_never_handed_the_callers_frame`] — answers 1.
//! 6. A PROJECTION OFF THE SPEC'S OWN CARRIER IS THIS INSTANCE'S MEMBER
//!    (typing/projection.rs `this_instance_member`). 12 FAIL, and not row by row: the
//!    STDLIB stops loading — `Iterable`'s six members calling `iterator(c)` are each
//!    refused `cannot project 'Element' off an abstract receiver with no concrete sort` —
//!    so every row that must load fails with it. The row that is about this part is
//!    [`a_specs_member_reads_its_own_carrier`]; it cannot be isolated from the stdlib it
//!    loads.
//! 7. A PROJECTION OFF A REQUIRED CARRIER IS WHAT THE CLAUSE BINDS
//!    (`required_instance_member`). 1 FAILS: [`a_requiring_sort_reads_what_its_clause_binds`]
//!    — the same refusal, at its `Iter.iterator(src)`.
//! 8. A PROJECTION OFF A CARRIER REACHED THROUGH A CHAIN IS READ THROUGH THE CHAIN
//!    (`project_via_provided_spec`'s composed view, put back to the direct one). 1 FAILS:
//!    [`a_carrier_reached_through_a_chain_is_read_through_it`] — `type '…Deep' has no member
//!    'Element'`.
//! 9. ONLY A SPEC WITH A CARRIER PARAMETER (`this_instance_member`'s
//!    `spec_is_self_representing` gate, removed). 1 FAILS:
//!    [`an_element_typed_receiver_has_no_instance_to_read`] — `x.T` off an element loads.
//! 10. A RIGID IS NAMED IN A REQUIREMENT REFUSAL (typing/synth.rs `format_term_for_goal`).
//!    1 FAILS: [`a_sibling_call_at_another_instance_owes_that_instances_requirement`] —
//!    the caller's own clause reads `requires Tag[T = ?]`.
//!
//! 11. TWO PARAMETERS THE CALL MADE ONE ARE ANOTHER INSTANCE (`open_params_at_callers_
//!    instance`'s alias test, removed). No row of THIS file fails; the row that does is
//!    `wi383_hk_application_test::rigid_functor_application_rejects_wrong_functor`, which
//!    panics on the placement's own assertion — `G`'s variable, left bound to `F`'s by a
//!    failed expected-type unification, is placed at `F`'s rigid and then refused at
//!    `G`'s. In a release build nothing panics and that row still passes (its refusal
//!    comes from the functor symbols), so the assertion is what drives this part.
//!
//! The stdlib is the larger witness of parts 7 and 8 too: with `Iterable.iterator` declared
//! in the carrier's terms they fail `wi590_enclosing_requires_test` and three rows of
//! `wi_bh1jz_carrier_arg_projection_test`.
//!
//! Every row fails under at least one part. Two are controls and say so at their sites —
//! they pass under every part but 6, which takes the stdlib with it:
//! [`a_sibling_call_at_this_instance_still_runs`] and
//! [`a_sibling_call_at_this_instance_reads_the_callers_frame`].

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

// ── A sibling call at another instance ──────────────────────────────────────

/// `MyList` with `rev(xs: Self) -> Self`, and a member that builds a list at ANOTHER element
/// type and reverses it — `body` is that member's body.
fn list_program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort MyList
    sort T = ?
    entity mnil
    entity mcons(head: T, tail: Self)
    operation len(xs: Self) -> Int64 =
      match xs
        case mnil() -> 0
        case mcons(_, rest) -> 1 + len(rest)
    operation rev(xs: Self) -> Self = revOnto(xs, mnil)
    operation revOnto(xs: Self, acc: Self) -> Self =
      match xs
        case mnil() -> acc
        case mcons(h, rest) -> revOnto(rest, mcons(head: h, tail: acc))
    operation mapOnto[Dst](xs: Self, f: (x: T) -> Dst, acc: MyList[T = Dst]) -> MyList[T = Dst] =
      match xs
        case mnil() -> acc
        case mcons(h, rest) -> mapOnto(rest, f, mcons(head: f(h), tail: acc))
    operation mapped[Dst](xs: Self, f: (x: T) -> Dst) -> MyList[T = Dst] =
{body}
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation go() -> Int64 =
    MyList.len(MyList.mapped(mcons(head: 1, tail: mcons(head: 2, tail: mnil)), inc))
end
"#
    )
}

/// A SIBLING CALL AT ANOTHER INSTANCE LOADS AND RUNS: `rev` is called on a `MyList[T = Dst]`
/// from inside a member of `MyList[T = T]`. This is the stdlib's `List.mapElems`, and with
/// the receiver written `Self` it was refused while the fill pinned the callee's `T` to the
/// enclosing instance — `rev.xs (op-arg): expected MyList[T = ?T], got MyList[T = ?Dst]`
/// (MEASURED on the stdlib migrated to `Self`).
#[test]
fn a_sibling_call_at_another_instance_loads() {
    let src = list_program(
        "wi80zv8s.a1",
        "      rev(mapOnto(xs, f, mnil))",
    );
    assert_eq!(run_src(&src, "wi80zv8s.a1.go"), Ok(2));
}

/// …AND WITH A LET-BOUND ARGUMENT. `let seed = mapOnto(xs, f, mnil)` is a `MyList[T = Dst]`
/// in hand, and `rev(seed)` reverses it. The fill refused this one in EITHER spelling of
/// `rev`'s receiver — the callee's `T` was pinned before the argument was read, whatever the
/// receiver said — while the same call from outside the sort loaded (070 §3, measured).
#[test]
fn a_sibling_call_on_a_let_bound_value_at_another_instance_loads() {
    let src = list_program(
        "wi80zv8s.a3",
        "      let seed = mapOnto(xs, f, mnil)\n      rev(seed)",
    );
    assert_eq!(run_src(&src, "wi80zv8s.a3.go"), Ok(2));
}

/// …BUT AT ONE INSTANCE PER CALL. `both(a: Self, b: Self)` takes two values of one
/// instance, and a sibling call handing it one of this instance and one of another is
/// refused at the SECOND argument, whichever comes first — the first places the call, as it
/// would from outside the sort. The fill refused both calls too, the second one at its
/// FIRST argument (it had placed the call before looking — MEASURED): the row is here so
/// that removing the pin is not read as removing the `Self` both parameters share.
#[test]
fn a_sibling_call_stands_at_one_instance() {
    let program = |ns: &str, call: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort MyList
    sort T = ?
    entity mnil
    entity mcons(head: T, tail: Self)
    operation both(a: Self, b: Self) -> Int64 = 0
    operation mixed[Dst](xs: Self, ys: MyList[T = Dst]) -> Int64 = {call}
  end
end
"#
        )
    };
    assert_refused_naming(
        &load_errors(&program("wi80zv8s.a4", "both(xs, ys)")),
        &["both.b (op-arg): expected MyList[T = ?T], got MyList[T = ?Dst]"],
        "this instance, then another",
    );
    assert_refused_naming(
        &load_errors(&program("wi80zv8s.a5", "both(ys, xs)")),
        &["both.b (op-arg): expected MyList[T = ?Dst], got MyList[T = ?T]"],
        "another instance, then this one",
    );
}

/// CONTROL — a sibling call at THIS instance: `rev(xs)` inside a member, its argument typed
/// by the instance itself. Ran with the fill and runs without it (MEASURED, part 1), the
/// argument fixing the parameter either way.
#[test]
fn a_sibling_call_at_this_instance_still_runs() {
    let src = list_program(
        "wi80zv8s.a2",
        "      mapOnto(rev(xs), f, mnil)",
    );
    assert_eq!(run_src(&src, "wi80zv8s.a2.go"), Ok(2));
}

/// A SIBLING CALL NOTHING PLACES ELSEWHERE IS AT THIS INSTANCE. `rest()` takes no argument,
/// and under a constructor — across the upcast of `List` to the `Stream` it provides — the
/// expected type does not reach it either. It is this instance's `rest`, as it was while the
/// fill said so before looking, and the program runs.
///
/// With the placement backed out the call keeps its parameter open and the program is
/// refused, `got Option[T = Pair[A = ?Out, B = List[T = ?_]]]` (MEASURED) — which is what a
/// generic `empty[X]() -> List[T = X]` in the same position gets, in other words
/// (`expected a type for 'X', got unconstrained`).
#[test]
fn a_sibling_call_nothing_places_elsewhere_is_at_this_instance() {
    let src = r#"
namespace wi80zv8s.b1
  import anthill.prelude.{Int64, List, Stream, Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  sort Holder
    sort Out = ?
    entity holder(v: Out)
    operation rest() -> List[T = Out] = []
    operation tailOf(h: Self) -> Option[Pair[A = Out, B = Stream[T = Out, E = {}]]] =
      match h
        case holder(o) -> some(pair(o, rest()))
  end
  operation go() -> Int64 =
    match Holder.tailOf(holder(v: 7))
      case some(pair(a, _)) -> a
      case _ -> 0
end
"#;
    assert_eq!(run_src(src, "wi80zv8s.b1.go"), Ok(7));
}

// ── The callee's frame: at the caller's instance it is the caller's ──────────

/// `Tag` with two providers that answer 1 and 2, and `Box requires Tag[T = T]` whose `tagIn`
/// asks its element's tag — so the answer names the instance `tagIn` ran at. `member` is one
/// more operation of `Box`; `go` is the entry's body.
fn box_program(ns: &str, member: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List}}
  sort Tag
    sort T = ?
    operation tagOf(x: T) -> Int64
  end
  sort A
    entity a(k: Int64)
    provides Tag[T = A]
    operation tagOf(x: A) -> Int64 = 1
  end
  sort B
    entity b(k: Int64)
    provides Tag[T = B]
    operation tagOf(x: B) -> Int64 = 2
  end
  sort Box
    sort T = ?
    requires Tag[T = T]
    entity box(v: T)
    operation tagIn(bx: Self) -> Int64 =
      match bx
        case box(v) -> Tag.tagOf(v)
{member}
  end
  operation sum(xs: List[T = Int64]) -> Int64 = List.foldLeft(xs, 0, lambda (acc, x) -> acc + x)
  operation go() -> Int64 = {go}
end
"#
    )
}

/// `Box.swap` over an `A` box and a `B` box.
const SWAP: &str = "Box.swap(box(v: a(k: 0)), box(v: b(k: 0)))";

/// A SIBLING CALL AT ANOTHER INSTANCE RUNS THAT INSTANCE'S PROVIDER. `swap` runs at `Box[T =
/// A]` and calls `tagIn` on a box of another element; the answer is the OTHER element's tag,
/// 2. Four ways a call is placed, one answer:
///
///  * by its ARGUMENT, abstractly — `other: Box[T = D]`, with `swap` requiring `Tag[T = D]`,
///    whose dictionary is forwarded;
///  * by its argument, concretely — `other: Box[T = B]`, whose dictionary is constructed;
///  * by the callee's BRACKET, `tagIn[T = D](other)`;
///  * by the RECEIVER's, `Box[T = D].tagIn(other)`.
///
/// The two bracket forms loaded BEFORE this change and answered 1 — the caller's provider,
/// applied to a value of another sort (MEASURED on the parent commit). The two argument
/// forms were refused there by the fill, and with the fill alone deleted answered 1 as well.
#[test]
fn a_sibling_call_at_another_instance_runs_that_instances_provider() {
    for (ns, member) in [
        (
            "wi80zv8s.f1",
            "    operation swap[D](bx: Self, other: Box[T = D]) -> Int64 requires Tag[T = D] = \
             tagIn(other)",
        ),
        (
            "wi80zv8s.f2",
            "    operation swap(bx: Self, other: Box[T = B]) -> Int64 = tagIn(other)",
        ),
        (
            "wi80zv8s.f3",
            "    operation swap[D](bx: Self, other: Box[T = D]) -> Int64 requires Tag[T = D] = \
             tagIn[T = D](other)",
        ),
        (
            "wi80zv8s.f4",
            "    operation swap[D](bx: Self, other: Box[T = D]) -> Int64 requires Tag[T = D] = \
             Box[T = D].tagIn(other)",
        ),
    ] {
        assert_eq!(
            run_src(&box_program(ns, member, SWAP), &format!("{ns}.go")),
            Ok(2),
            "{member}"
        );
    }
}

/// CONTROL — the same call AT THIS INSTANCE answers this instance's tag, 1: `tagIn(bx)`
/// reads the caller's frame, as it always did. Passes with or without the change by design.
#[test]
fn a_sibling_call_at_this_instance_reads_the_callers_frame() {
    let src = box_program(
        "wi80zv8s.f5",
        "    operation swap[D](bx: Self, other: Box[T = D]) -> Int64 = tagIn(bx)",
        SWAP,
    );
    assert_eq!(run_src(&src, "wi80zv8s.f5.go"), Ok(1));
}

/// …AND WHERE NOTHING SUPPLIES THE OTHER INSTANCE'S REQUIREMENT, IT IS REFUSED AT LOAD — as
/// the same call from OUTSIDE the sort is (`operation outside[D](other: Box[T = D]) =
/// Box.tagIn(other)`: the same refusal, MEASURED). `swap` holds a `Tag[T = T]` and is asked
/// for a `Tag[T = D]`; its own clause is named as what does not cover it.
#[test]
fn a_sibling_call_at_another_instance_owes_that_instances_requirement() {
    let src = box_program(
        "wi80zv8s.f6",
        "    operation swap[D](bx: Self, other: Box[T = D]) -> Int64 = tagIn(other)",
        SWAP,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "of `wi80zv8s.f6.Box` cannot be supplied for call to `wi80zv8s.f6.Box.tagIn`",
            "the enclosing scope's `requires wi80zv8s.f6.Tag[T = ?T]` covers only as a wildcard",
        ],
        "a sibling call at `T = D` with no `Tag[T = D]` in scope",
    );
}

/// NEVER THE CALLER'S FRAME FOR ANOTHER INSTANCE — the third state. `swap(bx: Self, w:
/// Tagger) = tagIn(box(v: w))` builds a box of `w`'s carrier, another instance, and `w`'s
/// type discharges the callee's `Tag` requirement without a dictionary being built (§8.7's
/// route 4: a spec-typed value in scope holds it). So the callee is handed NOTHING, exactly
/// as it is when the same call is made from outside the sort.
///
/// WHAT THAT DOES TODAY IS A KNOWN GAP, AND THE ROW PINS IT ON PURPOSE: `tagIn`'s read of
/// its `Tag` slot finds none and raises — from inside the sort and from outside it alike
/// (the second program). That is a defect of route 4 (it discharges at load what eval
/// cannot reach where the callee's body defers to its frame), and it is LOUD. What this
/// row is here for is what the sort-side call did before the typer stated the frame: eval
/// inferred an inherit from "same sort, no dictionary" and the call answered 1 — a `B`
/// tagged by `A`'s provider — in silence (MEASURED, the inference put back). When route 4
/// is repaired both programs answer 2 and this row is rewritten to say so.
#[test]
fn a_call_at_another_instance_is_never_handed_the_callers_frame() {
    let program = |ns: &str, member: &str, free: &str, go: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Tag
    sort T = ?
    operation tagOf(x: T) -> Int64
  end
  sort Tagger
    sort C = ?
    requires Tag[T = C]
    operation probe(x: C) -> Int64
  end
  sort A
    entity a(k: Int64)
    provides Tag[T = A]
    operation tagOf(x: A) -> Int64 = 1
  end
  sort B
    entity b(k: Int64)
    provides Tag[T = B]
    operation tagOf(x: B) -> Int64 = 2
    provides Tagger[C = B]
    operation probe(x: B) -> Int64 = 7
  end
  sort Box
    sort T = ?
    requires Tag[T = T]
    entity box(v: T)
    operation tagIn(bx: Self) -> Int64 =
      match bx
        case box(v) -> Tag.tagOf(v)
{member}
  end
{free}
  operation go() -> Int64 = {go}
end
"#
        )
    };
    const UNBOUND: &str = "requirement param `__req_tag` not bound in caller frame";

    let inside = program(
        "wi80zv8s.r1",
        "    operation swap(bx: Self, w: Tagger) -> Int64 = tagIn(box(v: w))",
        "",
        "Box.swap(box(v: a(k: 0)), b(k: 0))",
    );
    let from_inside = run_src(&inside, "wi80zv8s.r1.go");
    assert!(
        matches!(&from_inside, Err(e) if e.contains(UNBOUND)),
        "a sibling call at another instance must not run on its caller's dictionaries, got \
         {from_inside:?}"
    );

    let outside = program(
        "wi80zv8s.r2",
        "",
        "  operation outside(w: Tagger) -> Int64 = Box.tagIn(box(v: w))",
        "outside(b(k: 0))",
    );
    let from_outside = run_src(&outside, "wi80zv8s.r2.go");
    assert!(
        matches!(&from_outside, Err(e) if e.contains(UNBOUND)),
        "the call from outside the sort is the reference, got {from_outside:?}"
    );
}

/// `Dflt.dflt() -> T` has no receiver, so only a dictionary can say which provider answers;
/// `Box.fresh()` builds a box of it. `body` is `Box.swap`'s.
fn dflt_program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Dflt
    sort T = ?
    operation dflt() -> T
  end
  sort A
    entity a(k: Int64)
    provides Dflt[T = A]
    operation dflt() -> A = a(k: 1)
  end
  sort B
    entity b(k: Int64)
    provides Dflt[T = B]
    operation dflt() -> B = b(k: 2)
  end
  sort Box
    sort T = ?
    requires Dflt[T = T]
    entity box(v: T)
    operation fresh() -> Box[T = T] = box(v: Dflt[T = T].dflt())
    operation swap(bx: Self) -> Int64 =
{body}
  end
  operation go() -> Int64 = Box.swap(box(v: a(k: 0)))
end
"#
    )
}

/// THE EXPECTED TYPE PLACES A CALL THAT TAKES NO ARGUMENT, and the call runs where it was
/// placed: `let other: Box[T = B] = fresh()` inside `Box[T = A]` builds `B`'s default, 2.
/// The same `fresh()` with nothing said is this instance's, 1.
#[test]
fn the_expected_type_places_a_receiverless_sibling_call() {
    let placed = dflt_program(
        "wi80zv8s.g1",
        "      let other: Box[T = B] = fresh()\n      match other\n        case box(b(k)) -> k",
    );
    assert_eq!(run_src(&placed, "wi80zv8s.g1.go"), Ok(2));

    let unplaced = dflt_program(
        "wi80zv8s.g2",
        "      match fresh()\n        case box(a(k)) -> k\n        case _ -> 0",
    );
    assert_eq!(run_src(&unplaced, "wi80zv8s.g2.go"), Ok(1));
}

/// ONCE PLACED, A CALL STAYS WHERE IT IS. `let made = fresh()` says nothing, so `made` is a
/// box of this instance; annotating it at another instance afterwards is a mismatch, not a
/// second chance to place the call. Without the placement `made` kept an open element, the
/// annotation bound it to `B`, and the call had already run with this instance's dictionary.
#[test]
fn an_unplaced_sibling_call_is_not_placed_later() {
    let src = dflt_program(
        "wi80zv8s.g3",
        "      let made = fresh()\n      let other: Box[T = B] = made\n      match other\n        \
         case box(b(k)) -> k",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["other.annotation (let-binding): expected Box[T = B], got Box[T = ?T]"],
        "a box of this instance annotated as a box of `B`",
    );
}

/// A SIBLING PASSED AS A FUNCTION VALUE is placed by the arrow it is passed at, and carries
/// the dictionary of that instance: `List.mapElems(others, tagIn)` over boxes of `B` tags
/// each as a `B`, 2, and over boxes of this instance as an `A`, 1. Before this change the
/// reference captured its minting frame whatever the arrow said — 1 for the `B` boxes
/// (MEASURED, instance test backed out).
///
/// At an ABSTRACT other instance it is refused, with or without a `requires Tag[T = D]` on
/// the operation: a function value's dictionary is built from the enclosing SORT's clauses
/// alone (`TypingEnv::enclosing_dict_chain`), and those hold a `Tag[T = T]`. So the direct
/// call's `requires Tag[T = D]` repair does not carry over to the reference — a limit of
/// the function-value route, and a loud one. The refusal is the one the direct call gets
/// where nothing supplies the requirement.
#[test]
fn a_sibling_passed_as_a_function_value_is_placed_by_its_arrow() {
    let elsewhere = box_program(
        "wi80zv8s.h1",
        "    operation tags(bx: Self, others: List[T = Box[T = B]]) -> List[T = Int64] = \
         List.mapElems(others, tagIn)",
        "sum(Box.tags(box(v: a(k: 0)), [box(v: b(k: 0))]))",
    );
    assert_eq!(run_src(&elsewhere, "wi80zv8s.h1.go"), Ok(2));

    let here = box_program(
        "wi80zv8s.h2",
        "    operation tags(bx: Self, others: List[T = Self]) -> List[T = Int64] = \
         List.mapElems(others, tagIn)",
        "sum(Box.tags(box(v: a(k: 0)), [box(v: a(k: 0))]))",
    );
    assert_eq!(run_src(&here, "wi80zv8s.h2.go"), Ok(1));

    for (ns, requires) in [("wi80zv8s.h3", " requires Tag[T = D]"), ("wi80zv8s.h4", "")] {
        let abstractly = box_program(
            ns,
            &format!(
                "    operation tags[D](bx: Self, others: List[T = Box[T = D]]) -> List[T = \
                 Int64]{requires} = List.mapElems(others, tagIn)"
            ),
            "sum(Box.tags(box(v: a(k: 0)), [box(v: b(k: 0))]))",
        );
        assert_refused_naming(
            &load_errors(&abstractly),
            &[&format!("cannot be supplied for `{ns}.Box.tagIn` used as a function value")],
            "a sibling passed as a function value at `T = D`",
        );
    }
}

// ── A projection off a carrier, in the three places a receiver stands ────────

/// `Iter` writes `iterator`'s result in the carrier's terms; `rest` is what follows the
/// spec — a carrier, a sort that requires the spec, and `go`.
fn projection_program(ns: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Strm
    sort T = ?
    operation head(s: Self) -> s.T
    provides Iter[C = Self, Element = T]
    operation iterator(s: Self) -> Strm[T = s.T] = s
  end

  sort Iter
    sort C = ?
    sort Element = ?
    operation iterator(c: C) -> Strm[T = c.Element]
    operation first(c: C) -> Element = Strm.head(iterator(c))
  end

  sort One
    sort T = ?
    entity one(v: T)
    provides Strm[T = T]
    operation head(o: Self) -> T = o.v
  end

{rest}
end
"#
    )
}

/// INSIDE THE SPEC, the receiver is the spec's own carrier and the projection is THIS
/// instance's member: `first(c: C) -> Element = Strm.head(iterator(c))`, where `iterator(c)`
/// is a `Strm[T = c.Element]` and `c.Element` is `Element`.
#[test]
fn a_specs_member_reads_its_own_carrier() {
    let src = projection_program(
        "wi80zv8s.p1",
        "  operation go() -> Int64 = Iter.first(one(v: 7))",
    );
    assert_eq!(run_src(&src, "wi80zv8s.p1.go"), Ok(7));
}

/// IN A SORT THAT REQUIRES THE SPEC, the receiver is a parameter the clause is about and the
/// projection is what the clause binds: `Peek requires Iter[C = Source, Element = T]`, so
/// `Iter.iterator(src)` over `src: Source` is a `Strm[T = T]`.
#[test]
fn a_requiring_sort_reads_what_its_clause_binds() {
    let src = projection_program(
        "wi80zv8s.p2",
        r#"  sort Peek
    sort Source = ?
    sort T = ?
    requires Iter[C = Source, Element = T]
    entity peek(source: Source)
    operation top(p: Self) -> T =
      match p
        case peek(src) -> Strm.head(Iter.iterator(src))
  end
  operation go() -> Int64 = Peek.top(peek(source: one(v: 9)))"#,
    );
    assert_eq!(run_src(&src, "wi80zv8s.p2.go"), Ok(9));
}

/// AT A CONCRETE CARRIER THAT REACHES THE SPEC THROUGH A CHAIN, the projection is read
/// through the chain: `Deep` provides only `Strm`, and `Strm` provides `Iter[…, Element =
/// T]`, so `Iter.iterator(d)` over a `Deep` is a `Strm[T = Int64]`.
#[test]
fn a_carrier_reached_through_a_chain_is_read_through_it() {
    let src = projection_program(
        "wi80zv8s.p3",
        r#"  sort Deep
    entity deep(v: Int64)
    provides Strm[T = Int64]
    operation head(d: Deep) -> Int64 = d.v
  end
  operation go() -> Int64 =
    let d = deep(v: 11)
    Strm.head(Iter.iterator(d))"#,
    );
    assert_eq!(run_src(&src, "wi80zv8s.p3.go"), Ok(11));
}

/// ONLY A CARRIER. A sort that receives on ITSELF has no carrier parameter, and a receiver
/// typed by its element has no instance to be read at: `x.T` off `x: T` stays refused. The
/// reading asks for a spec whose operations receive on a parameter and declines this one —
/// without that gate `x.T` is read as `T` and the program loads (MEASURED, part 5).
#[test]
fn an_element_typed_receiver_has_no_instance_to_read() {
    let src = r#"
namespace wi80zv8s.c1
  import anthill.prelude.{Int64}
  sort Stack
    sort T = ?
    entity stack(top: T)
    operation push(s: Self, x: T) -> Self = stack(top: x)
    operation odd(x: T) -> x.T
    operation use(s: Self, x: T) -> T = odd(x)
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["cannot project 'T' off an abstract receiver with no concrete sort"],
        "`x.T` off an element",
    );
}
