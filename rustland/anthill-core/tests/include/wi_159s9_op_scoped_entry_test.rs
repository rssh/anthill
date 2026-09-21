//! WI-20260921-159S9 — **A SLOT DECLARED ON THE OPERATION IS AS GOOD AS ONE DECLARED
//! ON ITS SORT.**
//!
//! Two programs differing only in WHERE the requirement clause is written. Before this
//! ticket, one ran and the other was refused at load:
//!
//! ```text
//! (A)  sort OnSort                            (B)  sort OnSort
//!        sort E = ?   sort OE = ?                    operation ins[E, OE](
//!        requires OE: WeakOrd[E]                       s: SortedSet[T = E, O = OE], x: E)
//!        operation ins(s: SortedSet[…], x: E)          requires OE: WeakOrd[E] =
//!          = SortedSet.insert(s, x)                    SortedSet.insert(s, x)
//!      end                                     end
//! ```
//!
//! (A) printed `zz`; (B) was refused by WI-456's `no_scope_route` arm — *"a slot
//! declared on the OPERATION does not reach this call"*. The same shape WI-822 LEG 1
//! closed for receiverless dispatch and did not close here.
//!
//! # THE TWO HALVES, AND WHY THEY LAND TOGETHER
//!
//! **The typer half.** `build_concrete_dispatch_dict`'s caller chain is now
//! `TypingEnv::enclosing_frame_chain()` — the sort's slots *then the operation's own* —
//! where it was the sort half alone.
//!
//! **The eval half.** That channel is read STRICTLY at eval: a `var_ref(__req_*)` in a
//! forwarded dictionary must resolve or the dispatch has no target. So the widening is
//! sound only if EVERY route into an operation fills its op-scoped slots.
//! `Interpreter::fill_missing_op_scoped_slots` is the gate that makes that true, at
//! `enter_operation` — the last point every body-entry route passes through.
//!
//! # BACK-OUT MATRIX — MEASURED on this tree (`wi_tests`, 4847 rows), not reasoned
//!
//!  * **the eval gate alone** (drop the `fill_missing_op_scoped_slots` call from
//!    `enter_operation`, keep the widened chain) → **1 failure**,
//!    [`a_deferred_dispatch_fills_the_targets_op_scoped_slot`] ALONE, as
//!    `Internal(var_ref(__req_desc) unbound in requirement position (running
//!    `…SpLeaf.m`; frame binds ["__req_self"]))`. That row is the whole reason the two
//!    halves are ONE change: with the typer half and without the gate, that program
//!    LOADS CLEAN and dies at eval — strictly worse than the load refusal it had before.
//!
//!  * **the typer half alone** (restore `env.enclosing_dict_chain()`) → **20 failures**,
//!    in three groups. The first five are this ticket's:
//!    [`the_op_scoped_spelling_runs`], [`the_op_half_reaches_a_cross_sort_call`],
//!    [`a_deferred_dispatch_fills_the_targets_op_scoped_slot`],
//!    `wi456_no_scope_route_test::an_op_scoped_slot_is_a_working_spelling` and
//!    `wi822_op_scoped_supply_test::the_instance_dictionary_channel_forwards_an_op_slot`.
//!    The other fifteen are the two SPECIAL CASES the unconditional widening SUBSUMED,
//!    and they are why the two conditions could be deleted rather than kept beside it:
//!    `wi_1z3e7_provision_where_blocks_test::a_helper_calling_a_member_directly_builds_-
//!    its_dictionary` (the old `!serves` arm) and all fourteen
//!    `wi_r541x_body_read_of_type_param_test` rows (WI-20260919-N31XX's `TypeValue`
//!    arm, whose gate `callee_chain_reads_type_value` this ticket removed as unread).
//!    Those fifteen pass on the GENERAL rule, which is the evidence that it is general.
//!
//!  * [`the_sort_scoped_spelling_still_runs`] PASSES EITHER WAY BY DESIGN. It is the
//!    working spelling (A), here as the control that says the two spellings now agree
//!    rather than that (B) merely stopped erroring.
//!
//! Related pins elsewhere, both of which this ticket INVERTED rather than deleted:
//! `wi456_no_scope_route_test::an_op_scoped_slot_is_a_working_spelling` and
//! `wi822_op_scoped_supply_test::the_instance_dictionary_channel_forwards_an_op_slot`.
//! `wi817_polyrec_requirement_test::op_scoped_relay_chain_correct_via_value_direction`
//! still computes 551 — value-direction remains the channel for a call with no
//! dictionary, and this ticket adds a channel rather than replacing one.

use anthill_core::eval::Value;

/// Two rival `WeakOrd[String]`, so no assertion below can be explained by there being
/// only one ordering to find. Same fixture as `wi456_no_scope_route_test`.
const ORDERINGS: &str = r#"
  sort ByLength
    import anthill.prelude.{String, Int64, WeakOrd}
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
  sort Alphabetical
    import anthill.prelude.{String, Int64, Ord}
    import anthill.prelude.PartialOrd.{lt, gt}
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 =
      if lt(a, b) then -1 else if gt(a, b) then 1 else 0
  end
  sort Head
    import anthill.prelude.{String, List}
    import anthill.prelude.List.{cons, nil}
    operation head(l: List[T = String]) -> String =
      match l
        case nil() -> "<empty>"
        case cons(h, t) -> h
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool, SortedSet}}\n\
         {ORDERINGS}{body}\nend\n"
    )
}

/// The two drivers both call the SAME polymorphic body over the SAME two strings,
/// differing only in the ordering the caller's set was built with. One answer twice
/// would mean the slot decided nothing.
const DRIVERS: &str = "  sort Driver\n    \
     operation byLength() -> String =\n      \
     let s = SortedSet.empty[T = String, O = ByLength]()\n      \
     Head.head(SortedSet.toList(Poly.ins(Poly.ins(s, \"zz\"), \"aaa\")))\n    \
     operation alphabetical() -> String =\n      \
     let s = SortedSet.empty[T = String, O = Alphabetical]()\n      \
     Head.head(SortedSet.toList(Poly.ins(Poly.ins(s, \"zz\"), \"aaa\")))\n  end";

/// `entry()` on a FRESH interpreter — `interp_for` panics on a dirty load, so a value
/// assertion is also a clean-load assertion.
fn eval_str(src: &str, entry: &str, why: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[]) {
        Ok(Value::Str(s)) => s,
        other => panic!("{why}; got {other:?}\n{src}"),
    }
}

/// Drive BOTH orderings through one body and assert they disagree.
fn assert_both_orderings(src: &str, ns: &str) {
    assert_eq!(
        eval_str(src, &format!("{ns}.Driver.byLength"), "the length ordering travels"),
        "zz",
    );
    assert_eq!(
        eval_str(
            src,
            &format!("{ns}.Driver.alphabetical"),
            "the alphabetic ordering travels"
        ),
        "aaa",
        "ONE polymorphic body over the SAME two strings, differing only in the ordering \
         its caller's set carries — so one answer twice would mean the slot decided \
         nothing and the comparator was re-searched at the callee",
    );
}

// ── (A) the control: the slot on the SORT ────────────────────────────

/// PASSES EITHER WAY BY DESIGN. The working spelling, here so the change is visibly
/// about making (B) join it rather than about (A) moving.
#[test]
fn the_sort_scoped_spelling_still_runs() {
    let src = program(
        "wi159s9.onsort",
        &format!(
            "  sort Poly\n    \
             sort E = ?\n    \
             sort OE = ?\n    \
             requires OE: WeakOrd[E]\n    \
             operation ins(s: SortedSet[T = E, O = OE], x: E) \
             -> SortedSet[T = E, O = OE] =\n      \
             SortedSet.insert(s, x)\n  end\n\
             {DRIVERS}"
        ),
    );
    assert_both_orderings(&src, "wi159s9.onsort");
}

// ── (B) THE ACCEPTANCE: the identical clause on the OPERATION ────────

/// **THE TICKET.** The same clause, moved onto the operation. Refused at load before
/// this change by WI-456's `no_scope_route` arm; now it runs, and answers the two
/// orderings differently — which is what proves the op slot CARRIED the comparator
/// rather than the callee re-finding one.
#[test]
fn the_op_scoped_spelling_runs() {
    let src = program(
        "wi159s9.onop",
        &format!(
            "  sort Poly\n    \
             operation ins[E, OE](s: SortedSet[T = E, O = OE], x: E) \
             -> SortedSet[T = E, O = OE]\n        \
             requires OE: WeakOrd[E] =\n      \
             SortedSet.insert(s, x)\n  end\n\
             {DRIVERS}"
        ),
    );
    assert_both_orderings(&src, "wi159s9.onop");
}

// ── the op half reaching a cross-sort callee's SORT-level requires ───

/// The `wi822 instchan` shape, driven to VALUES rather than to a load verdict.
///
/// `Holder.probe requires Desc[HT]` (OP-scoped) cross-sort-calls `Coll.size`, whose
/// SORT declares `requires Desc[CT]`. The caller's sort chain is empty, so the only
/// thing that can answer the callee's dep is the caller's own OP slot. Two answers from
/// one body — 1 for a `Leaf`, 12 for a `Wrap[Leaf]` — show the dictionary travelled and
/// descended: 12 is `WrapDesc.describe` reading the ELEMENT's `Desc` out of its own
/// chain (`10·1 + 2`), which a wrong or missing slot cannot produce.
///
/// This is the program `wi822_op_scoped_supply_test` asserted was REFUSED. Its arm
/// there now asserts the opposite, re-derived rather than re-pointed.
#[test]
fn the_op_half_reaches_a_cross_sort_call() {
    let src = format!(
        r#"
namespace wi159s9.instchan
  import anthill.prelude.{{Int64, Bool}}
{}
  sort Coll
    sort CT = ?
    requires Desc[CT]
    operation size(x: CT) -> Int64 = Desc.describe(x)
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Coll.size(x)
  end
  sort Driver
    operation shallow(n: Int64) -> Int64 = Holder.probe(leaf())
    operation deep(n: Int64) -> Int64 = Holder.probe(wrap(leaf()))
  end
end
"#,
        crate::common::DESC_INSTANCES
    );
    let mut interp = crate::common::interp_for(&src);
    let shallow = interp.call("wi159s9.instchan.Driver.shallow", &[Value::Int(0)]);
    assert!(
        matches!(shallow, Ok(Value::Int(1))),
        "`Leaf.describe` through the caller's OP slot; got {shallow:?}"
    );
    let deep = interp.call("wi159s9.instchan.Driver.deep", &[Value::Int(0)]);
    assert!(
        matches!(deep, Ok(Value::Int(12))),
        "expected 12 = `WrapDesc.describe` (10·`Leaf.describe` + 2), which needs the \
         op slot's dictionary AND one descent into its own chain — 1 would mean the \
         projection landed on the element's dictionary, a refusal that the op half \
         never reached the builder; got {deep:?}"
    );
}

// ── THE EVAL GATE: the route that fills nothing at the call site ─────

/// **THE DEFERRED ROUTE, and the row that makes the eval half a separate measurable
/// change.**
///
/// `User.go` defers `Sp.m` to its `requires Sp[T = UT]` frame slot, so the target is
/// chosen AT RUN TIME by `start_apply_deferred` — which resolves a dictionary out of
/// the caller's frame and expands its SORT half alone. Nothing at that call site can
/// fill the target's own op-scoped slots: the stamp a call site would carry is built
/// against the SPEC's chain, and the impl chosen at run time lays out its own
/// (WI-20260921-28TAT measured exactly that and `push_op_scoped_slots`' `built_for !=
/// target` guard is what refuses it). So the fill has to happen at ENTRY, from the
/// argument values, which is [`fill_missing_op_scoped_slots`].
///
/// THE SHAPE IS THE ONLY ONE §8.7 ADMITS. An override may not STRENGTHEN a
/// precondition, so `SpLeaf.m` cannot declare an op-scoped clause `Sp.m` lacks — both
/// declare the structurally identical `requires Desc[T = U]` over their own op type
/// param. (Measured: the spelling where only the impl declares it is refused at load,
/// "it strengthens the precondition"; so is the one where the two range over different
/// sorts' params. This is the reachable configuration.)
///
/// FAILS WITHOUT THE GATE with `Internal(var_ref(__req_desc) unbound in requirement
/// position (running `…SpLeaf.m`; frame binds ["__req_self"]))` — loading clean and
/// dying at eval, which is the regression the typer half would otherwise introduce.
#[test]
fn a_deferred_dispatch_fills_the_targets_op_scoped_slot() {
    let src = format!(
        r#"
namespace wi159s9.defer
  import anthill.prelude.{{Int64, Bool}}
{}
  sort Coll
    sort CT = ?
    requires Desc[CT]
    operation size(x: CT) -> Int64 = Desc.describe(x)
  end
  sort Sp
    sort T = ?
    operation m[U](x: T, y: U) -> Int64 requires Desc[T = U]
  end
  sort SpLeaf
    provides Sp[T = Leaf]
    operation m[U](x: Leaf, y: U) -> Int64 requires Desc[T = U] =
      add(100, Coll.size(y))
  end
  sort User
    sort UT = ?
    requires Sp[T = UT]
    operation go(x: UT) -> Int64 = Sp.m(x, leaf())
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = User.go(leaf())
  end
end
"#,
        crate::common::DESC_INSTANCES
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi159s9.defer.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(101))),
        "expected Ok(Int(101)) = 100 + `Coll.size(leaf())` 1, where `Coll`'s SORT-level \
         `requires Desc[CT]` is answered from `SpLeaf.m`'s OWN op-scoped slot — filled \
         at entry, because the deferred route supplies nothing at the call site; \
         got {got:?}"
    );
}
