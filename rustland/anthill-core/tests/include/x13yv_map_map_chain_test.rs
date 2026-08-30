//! WI-20260829-X13YV — `xs.map(f).map(g)` and `xs.filter(p).filter(q)`.
//!
//! THE DEFECT WAS A ROUTE, NOT A CALLBACK. Dot dispatch resolves a member on the
//! receiver's OWN sort before the specs it provides (`own_op.or_else(
//! find_spec_op_for_provided_sort)`, `kb/typing.rs`). `MappedStream` declares a member
//! named `map`, so the second hop of `xs.map(f).map(g)` landed there; `FilteredStream`
//! declares `filter`, likewise. Neither sort declares the OTHER name, so `xs.map(f)
//! .filter(p)` and `xs.filter(p).map(g)` fell through to `FiniteCollection` and worked.
//! THE MIXED CHAINS ARE WHAT LOCALIZED IT — same chain, same callbacks, different member
//! name, different route — and they are rows here for that reason.
//!
//! WHAT THE DECLARATION IT LANDED ON WAS. A static constructor over a bare Stream:
//!
//!     map[S, Dst, EffS, EffP](s: Stream[S, EffS], f: …) -> Stream[Dst, {EffS, EffP}]
//!
//! Two things wrong with reaching it, and the second is why grounding `EffS` would not
//! have been a fix. (1) `EffS` did not ground from `MappedStream provides Stream[T = T,
//! E = {ES, EF}]` — WI-594's gap 2 — so the chain did not load: "expected a type for
//! 'EffS', got unconstrained". (2) The return ERASED the source to a bare `Stream`, the
//! erasure WI-590 deleted the finite twin carriers to be rid of, so even grounded the
//! result would carry no `Source` for `MappedStreamFinite` to read and
//! `xs.map(f).map(g).size()` would still have been refused — exactly as
//! `total(Iterable.map(xs, f))` is, and must stay.
//!
//! THE REPAIR REUSES THE INPUT TYPE: the result names its input as its own `Source`, so the
//! witness recurses and a two-hop chain is finite exactly when the ORIGINAL carrier is.
//! `combinators.anthill` carries the signature.
//!
//! WHAT X13YV ALSO COST HAS SINCE BEEN REPAID: the input was narrowed to THIS carrier, which
//! is what made the two operations stop accepting a bare `List`. WI-20260829-70XVH ground
//! the element from an op-level `requires` on a free operation and the input is `Sc` again
//! — general over any `Iterable` source, with the `Source` reuse and therefore every row
//! below unchanged. Driven in `wi599_carrier_arg_provision_test::
//! the_stdlib_combinators_are_general_over_any_iterable_source`.
//!
//! WHICH ROWS MEASURE THE CHANGE, by restoring the two old static-constructor signatures:
//!   * `map_map_chain_evaluates` / `filter_filter_chain_evaluates` — RED (they do not
//!     load: "expected a type for 'EffS', got unconstrained").
//!   * `a_chain_crossing_both_carriers_collects` — RED. It was drafted as a control and
//!     the back-out said otherwise: its second same-name hop is the repaired member. It
//!     lives apart from `the_mixed_chains_are_unchanged` for that reason.
//!   * `each_hop_resolves_to_the_receivers_own_member` — PASSES EITHER WAY, and the
//!     back-out is what established that; this note first claimed it went red at the hop-2
//!     rows and that was wrong. It reads the ROUTE, and the route is deliberately
//!     unchanged: hop 2 resolved to `MappedStream.map` before the repair and resolves
//!     there after it. That is the whole design choice recorded as a measurement — the
//!     repair re-typed the DECLARATION the ladder finds, it did not re-point the ladder.
//!   * `a_two_hop_chain_is_finite_exactly_when_its_source_is` — RED, but for a DIFFERENT
//!     reason (the `.map` hop itself stops loading), so it is not a witness for the
//!     repair; it is the SOUNDNESS control, and it is stated here rather than credited.
//!   * `the_mixed_chains_are_unchanged` and `an_erasing_iterable_map_is_still_not
//!     _consumable` — PASS EITHER WAY BY DESIGN too. They are the controls: the first says
//!     the callbacks and the chaining were never implicated, the second that the repair
//!     did not buy the chain by weakening the finiteness boundary.

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The digit-fold `acc * 10 + x` over the collected chain. NOT a sum: a sum is
/// commutative and idempotent-ish enough that a chain which dropped a hop, reordered the
/// elements or applied a transform twice can still hit the expected number. The fold
/// pins COUNT, ORDER and VALUE at once — `[3,5,7,9]` is 3579 and nothing else is.
const EVAL_SRC: &str = r#"
namespace x13yv.eval
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.FiniteCollection.{size, collect}

  operation digits(xs: List[T = Int64]) -> Int64 =
    List.foldLeft(xs, 0, lambda (acc, x) -> acc * 10 + x)

  -- THE CHAIN. [1,2,3,4] -> *2 -> [2,4,6,8] -> +1 -> [3,5,7,9].
  operation map_map() -> Int64 =
    digits([1, 2, 3, 4].map(lambda n -> n * 2).map(lambda n -> n + 1).collect())
  -- ONE HOP, the value that separates "the chain ran" from "a hop was dropped": 2468.
  operation map_one() -> Int64 =
    digits([1, 2, 3, 4].map(lambda n -> n * 2).collect())

  -- [1,2,3,4] -> >1 -> [2,3,4] -> <4 -> [2,3].
  operation filter_filter() -> Int64 =
    digits([1, 2, 3, 4].filter(lambda n -> n > 1).filter(lambda n -> n < 4).collect())
  operation filter_one() -> Int64 =
    digits([1, 2, 3, 4].filter(lambda n -> n > 1).collect())

  -- THREE hops, so the recursion is driven past the depth two reaches.
  operation map_map_map() -> Int64 =
    digits([1, 2, 3, 4].map(lambda n -> n * 2).map(lambda n -> n + 1).map(lambda n -> n - 3).collect())

  operation map_map_size() -> Int64 = [1, 2, 3, 4].map(lambda n -> n * 2).map(lambda n -> n + 1).size()
  operation filter_filter_size() -> Int64 = [1, 2, 3, 4].filter(lambda n -> n > 1).filter(lambda n -> n < 4).size()
end
"#;

/// `xs.map(f).map(g)` runs, and the value says the chain ran ONCE per hop in order.
#[test]
fn map_map_chain_evaluates() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    assert_eq!(
        run_int(&mut interp, "x13yv.eval.map_one"),
        2468,
        "one hop: [1,2,3,4] * 2"
    );
    assert_eq!(
        run_int(&mut interp, "x13yv.eval.map_map"),
        3579,
        "two hops: [1,2,3,4] * 2 then + 1"
    );
    assert_eq!(
        run_int(&mut interp, "x13yv.eval.map_map_map"),
        246,
        "three hops: … then - 3 gives [0,2,4,6]; the leading 0 is why this is 246"
    );
    assert_eq!(run_int(&mut interp, "x13yv.eval.map_map_size"), 4);
}

/// The filter twin. A kept element is returned VERBATIM, so this also says the element
/// type threads unchanged across the hop where `map`'s becomes `Dst`.
#[test]
fn filter_filter_chain_evaluates() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    assert_eq!(
        run_int(&mut interp, "x13yv.eval.filter_one"),
        234,
        "one hop: keep > 1"
    );
    assert_eq!(
        run_int(&mut interp, "x13yv.eval.filter_filter"),
        23,
        "two hops: keep > 1 then keep < 4"
    );
    assert_eq!(run_int(&mut interp, "x13yv.eval.filter_filter_size"), 2);
}

const FIXTURE: &str = r#"
namespace x13yv.route
  import anthill.prelude.{List, Int64, Bool, Stream, Iterable, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size, collect}
  sort Row
    import anthill.prelude.{Int64, Bool}
    entity row(a: Int64, flag: Bool)
  end
  import x13yv.route.Row.{row}
  operation total(c: FiniteCollection) -> Int64 effects c.E = size(c)
  operation cell(xs: List[T = Row]) -> Int64 =
    let s = {BODY}
    42
end
"#;

fn load_errors(body: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(&FIXTURE.replace("{BODY}", body)) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// WHICH DECLARATION each hop reaches, read off the arity error — the same instrument
/// `each_spelling_resolves_to_a_named_declaration` uses, and the reason this file can say
/// the defect was a ROUTE rather than assert it.
///
/// IT PASSES WITH THE REPAIR BACKED OUT, measured, and that is the point rather than a
/// weakness: the shadowing is still there BY DESIGN. Hop 2 resolved to the receiver's own
/// `MappedStream.map` before the repair and resolves there after it; what changed is that
/// the member it lands on now keeps the source in its type. Re-pointing the ladder was the
/// alternative and was rejected — it would change a shared dispatch decision, used by every
/// dot in the tree, for a reason two operations had. So this test pins the route the repair
/// chose NOT to touch, and it reds only if some later change moves it.
#[test]
fn each_hop_resolves_to_the_receivers_own_member() {
    let rows: &[(&str, &str, &str)] = &[
        ("hop 1 — .map on a List", "xs.map()", "anthill.prelude.FiniteCollection.map"),
        ("hop 2 — .map on a MappedStream", "xs.map(lambda r -> r.a).map()", "anthill.prelude.MappedStream.map"),
        ("hop 2 — .filter on a FilteredStream", "xs.filter(lambda r -> r.flag).filter()", "anthill.prelude.FilteredStream.filter"),
        // The two members neither sort declares — the fall-through that always worked.
        ("mixed — .filter on a MappedStream", "xs.map(lambda r -> r.a).filter()", "anthill.prelude.FiniteCollection.filter"),
        ("mixed — .map on a FilteredStream", "xs.filter(lambda r -> r.flag).map()", "anthill.prelude.FiniteCollection.map"),
    ];
    let mut wrong = Vec::new();
    for (label, body, want) in rows {
        let errs = load_errors(body);
        if !errs.iter().any(|e| e.contains("arity")) {
            wrong.push(format!(
                "{label} — no arity error, so this test can no longer read the resolved \
                 declaration and is measuring nothing:\n    {}",
                errs.join("\n    ")
            ));
            continue;
        }
        if !errs.iter().any(|e| e.contains(want)) {
            wrong.push(format!(
                "{label} — expected the call to resolve to `{want}`, got:\n    {}",
                errs.join("\n    ")
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n\n"));
}

/// THE SOUNDNESS GATE, after the second hop. The repair keeps the source carrier in the
/// result type, so `MappedStreamFinite` RECURSES: a two-hop chain is collectable exactly
/// when the ORIGINAL carrier is.
///
/// `collect` AND NOT `size`, deliberately, and the difference is measured rather than
/// assumed: on the untouched tree `FiniteCollection.size` over a `MappedStream[Source =
/// Nats]` LOADS while `FiniteCollection.collect` over the identical value is REFUSED.
/// `size` is the DEFAULTED member (`List.length(collect(c))`) and does not re-ask the
/// witness. That is a pre-existing hole, filed as WI-20260829-H0YCE; here it means only
/// that a `size` row could not witness this gate, so this test does not use one.
///
/// The `Nats` row is also what says the repair did not simply make everything finite:
/// the `.map` hop over it still LOADS — chaining a lazy stream is always sound — and only
/// the CONSUMPTION is refused, naming `FiniteCollection[C = Nats]`.
#[test]
fn a_two_hop_chain_is_finite_exactly_when_its_source_is() {
    const PROBE: &str = r#"
namespace x13yv.gate
  import anthill.prelude.{List, Int64, Bool, Stream, Option, Pair, MappedStream, FilteredStream, FiniteCollection}
  import anthill.prelude.Option.{some}
  import anthill.prelude.Pair.{pair}

  -- An INFINITE source: provides Stream (so it is a fine combinator source) and never
  -- FiniteCollection, because counting it does not terminate.
  sort Nats
    import anthill.prelude.{Int64, Stream, Option, Pair}
    import anthill.prelude.Option.{some}
    import anthill.prelude.Pair.{pair}
    entity nats(from: Int64)
    provides Stream[T = Int64, E = {}]
    operation splitFirst(n: Nats)
      -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =
      match n
        case nats(k) -> some(pair(k, nats(from: k + 1)))
  end

  operation twoHopMap(
      m: MappedStream[Source = {SOURCE}, Src = Int64, T = Int64, ES = {}, EF = {}])
    -> List[T = Int64] =
    FiniteCollection.collect(m.map(lambda n -> n))

  operation twoHopFilter(
      f: FilteredStream[Source = {SOURCE}, T = Int64, ES = {}, EF = {}])
    -> List[T = Int64] =
    FiniteCollection.collect(f.filter(lambda n -> true))
end
"#;
    let over = |source: &str| match crate::common::try_load_kb_with(&PROBE.replace("{SOURCE}", source)) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };

    let finite = over("List[T = Int64]");
    assert!(
        finite.is_empty(),
        "a two-hop chain over a FINITE source must stay collectable; got: {finite:#?}"
    );

    let infinite = over("Nats");
    assert_eq!(
        infinite.len(),
        2,
        "both hops (map and filter) over an INFINITE source must be refused; got: {infinite:#?}"
    );
    assert!(
        infinite
            .iter()
            .all(|e| e.contains("FiniteCollection.collect.dispatch")
                && e.contains("C = x13yv.gate.Nats")),
        "the refusal must land on the CONSUMPTION and name the ORIGINAL carrier — that is \
         what says the witness recursed through the second hop rather than stopping at it; \
         got: {infinite:#?}"
    );
}

/// THE CONTROL, and it passes either way BY DESIGN. `MappedStream` declares no `filter`
/// and `FilteredStream` no `map`, so these two chains always fell through to
/// `FiniteCollection` and always worked. Without them the file would be consistent with
/// "chaining lazy combinators was broken", which is what the shape looked like.
#[test]
fn the_mixed_chains_are_unchanged() {
    for body in [
        "xs.map(lambda r -> r.a).filter(lambda n -> true)",
        "xs.filter(lambda r -> r.flag).map(lambda r -> r.a)",
        "xs.map(lambda r -> r.a).filter(lambda n -> true).size()",
        "xs.filter(lambda r -> r.flag).map(lambda r -> r.a).size()",
    ] {
        let errs = load_errors(body);
        assert!(errs.is_empty(), "`{body}` must still load; got: {errs:#?}");
    }
}

/// THE BOUNDARY, also passing either way by design: `Iterable.map` DECLARES a bare
/// `Stream` return, erasing the source and with it the finiteness gate, so its result
/// must stay un-consumable. This is the row that says the chain was not bought by
/// weakening the boundary — the repair added a NON-erasing hop, it did not make the
/// erasing one consumable.
#[test]
fn an_erasing_iterable_map_is_still_not_consumable() {
    let errs = load_errors("total(Iterable.map(xs, lambda r -> r.a))");
    assert!(
        errs.iter().any(|e| e.contains("expected FiniteCollection")),
        "`Iterable.map`'s erased Stream must not feed an eager consumer; got: {errs:#?}"
    );
}

/// THREE hops CROSSING BOTH carriers, then consumed. The two-hop rows cannot ask this: each
/// stays inside ONE carrier's own witness, while here `MappedStreamFinite` must discharge a
/// `requires FiniteCollection[C = FilteredStream[…]]` that only `FilteredStreamFinite` can
/// answer, and vice versa — the witnesses have to chain through each other.
///
/// NOT A CONTROL, and it was written as one before being measured: the SECOND same-name hop
/// in each row is the repaired member, so both rows go red on the back-out. It is kept apart
/// from `the_mixed_chains_are_unchanged` for exactly that reason — a row that moves with the
/// change does not belong in the table whose contract is that nothing in it does.
#[test]
fn a_chain_crossing_both_carriers_collects() {
    for body in [
        "xs.map(lambda r -> r.a).filter(lambda n -> true).filter(lambda n -> true).collect()",
        "xs.filter(lambda r -> r.flag).map(lambda r -> r.a).map(lambda n -> n).collect()",
    ] {
        let errs = load_errors(body);
        assert!(errs.is_empty(), "`{body}` must load; got: {errs:#?}");
    }
}
