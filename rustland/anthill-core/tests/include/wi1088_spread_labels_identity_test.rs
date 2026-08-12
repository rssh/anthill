//! WI-1088 — the two edges of `Value::OpRef::spread_labels`, the eta-site mapping WI-1087
//! added. Both were found by review of that ticket and left standing there with a stated
//! reason; this file is where each is decided and driven.
//!
//! ## (2) THE MAPPING IS PINNED AT THE MINT AND SURVIVES RE-TYPING
//!
//! A `Function[A, B, E]` slot admits TWO readings of `A` (WI-801) and the VALUE at it may be
//! applied under either, at a call site the pairing cannot see: the WHOLE-`A` reading, where
//! `A` is one argument's DATA type related BY NAME and order-free since WI-803; and the
//! SPREAD reading, where `A` IS the callback's parameter list, applied POSITIONALLY, and
//! order is identity (WI-782, §4.5). `Function`/`Function` conformance took the first
//! reading's answer alone, so a value could be re-typed at a second slot whose `A` orders the
//! same labels differently — and the runtime keeps the FIRST slot's mapping, because that is
//! where it was pinned (`Value::OpRef::spread_labels` for the operation spelling,
//! `Pattern::Tuple.labels` for the lambda one). MEASURED on the WI-1087 tree, loading clean
//! and running:
//!
//! ```text
//! operation inner(g: Function[A = (x: Int64, acc: Int64), B = Int64]) -> Int64 = g((acc: 3, x: 10))
//! operation outer(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64 = inner(f)
//! inner(sub2) =>  7     -- `inner`'s own `A` says parameter 1 <- `x`
//! outer(sub2) => -7     -- the MINT site's `A` won
//! ```
//!
//! The two spellings AGREE — the lambda half answered 7/-7 identically, and did so BEFORE
//! WI-1087 existed — so WI-784 holds and this is not a WI-1087 regression. What WI-1087
//! changed is that the operation spelling now reaches the same shape. The defect is that
//! `inner`'s DECLARED `A` is silently not the mapping used.
//!
//! THE RULE: `A` at a `Function` slot must satisfy BOTH readings, so the admissible relation
//! is their INTERSECTION, which on the ORDER axis is [`TupleOrder::Preserved`]. A
//! `Function`/`Function` pairing whose two `A`s are PERMUTATIONS of each other is refused —
//! `function_pairing_permutes_a` (kb/typing.rs), guarding both routes that decompose the
//! pairing.
//!
//! WHAT IT REFUSES THAT USED TO LOAD, driven rather than left to be discovered: a pairing
//! whose value would only ever be applied at arity ONE, where the whole-`A` reading is the
//! only live one and a permutation is harmless. That case is not separable here — a
//! `Function` slot states NO arity, which is the whole reason it admits two readings, so the
//! pairing cannot know which one its value will meet.
//! [`the_refusal_reaches_a_pairing_only_arity_one_could_use`] is that program, refused, so
//! the price is a row and not a sentence. The corpus contains none (all seven tiers, zero
//! errors and unchanged rule totals) and neither does the crate.
//!
//! ## (1) THE FIELD IS PART OF THE VALUE'S STRUCTURAL IDENTITY
//!
//! `opref_shape` (kb/term_view.rs) states the rule for this value: a payload two `OpRef`s can
//! differ in while answering differently is IDENTITY, because the shape feeds fact dedup and
//! merging DROPS A FACT (WI-815). WI-1087 added `spread_labels` and did not list it, which by
//! that rule is a known false-equality rather than a considered exemption. It is now the
//! FOURTH key.
//!
//! THE ALTERNATIVE — "establish that the two values cannot both exist and be compared" — is
//! refuted, not declined: [`two_slots_ordering_a_differently_mint_two_readings`] is a program
//! that mints both under one KB, and hazard (2)'s refusal does not touch it (that guard
//! relates a declared slot to a value flowing INTO it, and two independent slots are never so
//! related). `views_structurally_equal` compares whatever it is handed.
//!
//! WHAT IT COST, deliberately, since `opref_shape`'s keys ARE declared accessors: a fourth
//! operation on the reflect `OpRef` sort, `spreadLabels(r) -> Option[List[Symbol]]`. Every
//! seven-tier corpus load moved by exactly **+2 facts**, ZERO rules and zero errors — one
//! declared operation's own load facts, uniform because the declaration is in the stdlib
//! every tier loads. Tier by tier, before → after: 2595→2597, 2594→2596, 3669→3671,
//! 2674→2676, 3077→3079, 5019→5021, 2706→2708.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each, whole crate
//!
//! | revert | cost |
//! |---|---|
//! | the `parameterized_compatible_view` guard (the GROUND route) | **2** — [`a_permuted_function_to_function_pairing_is_refused`] and [`a_permuted_pairing_is_refused_in_the_lambda_spelling_too`], both back to loading clean and answering 7 through one route and -7 through the other |
//! | the `validate_arrow_param_result` guard (the σ-PINNED route) | **1** — [`a_permutation_is_refused_through_a_sigma_pinned_slot_too`], back to loading clean. Nothing else notices: the two routes are reached by different programs, not by one program twice |
//! | `"spread"` dropped from `opref_shape` | **1** — [`two_oprefs_differing_only_in_their_spread_mapping_are_distinct`], the same narrow shape `wi1019…`'s `dict` and `named` rows have |
//! | the `spreadLabels` BUILTIN unregistered (the accessor still declared) | **1** — [`the_spread_labels_accessor_answers_for_both_mints`], which is what makes the declaration a surface rather than a name |
//!
//! NOT A ROW, and the omission is the finding: backing out the stdlib DECLARATION alone is
//! not a coherent tree to measure. `opref_shape`'s keys are resolved through
//! `accessor_key`/`reflect_ctor_sym`, which PANICS on an unresolved qualified name — that is
//! the invariant making a declared accessor the right thing to key on (`accessor_key`'s own
//! doc). So the declaration and the shape key are ONE piece: without the declaration the
//! first eta'd `OpRef` to reach the view aborts rather than answering wrongly.
//!
//! Rows that pass BOTH ways, by design, and say so at their sites:
//! [`an_agreeing_function_to_function_pairing_still_runs`],
//! [`two_slots_ordering_a_differently_mint_two_readings`].
//!
//! ## What review changed after the first cut
//!
//! Three low-severity findings, all taken:
//!
//!  * `opref_shape`'s inherited doc justified the conditional key by "the arity difference
//!    keeps the two shapes distinct". True of TWO optional payloads and false of three —
//!    `{op, dict}`, `{op, named}` and `{op, spread}` all have `named_arity: 2`. What keeps
//!    them apart is the KEY SET, which is what `views_structurally_equal` and
//!    `goal_fingerprint` actually read. Restated there; a fifth payload added on the arity
//!    reading would have shipped the WI-815 false-equality that doc exists to prevent;
//!  * the two call sites both claimed to consult "the SAME predicate" while handing it
//!    operands of different provenance — σ-walked at `validate_arrow_param_result`, raw
//!    bindings at `parameterized_compatible_view`. `named_tuple_fields` answers EMPTY for a
//!    variable, so a σ-bound `A` would have made the guard answer `false` SILENTLY. The
//!    predicate now σ-resolves its own operands, which makes the claim true instead of
//!    nearly true. Not separately drivable today (`validate_arg_against_param` withholds its
//!    deep walk whenever a callable appears, so the ground route sees callables already
//!    ground) — kept because the alternative is a silent under-refusal in exactly the class
//!    this ticket closes, not because a program needs it;
//!  * the arity-1 cost above was described and is now driven.
//!
//! REFERENCE: WI-1087 (where the field was added and both hazards recorded at their sites),
//! WI-815 (fingerprint vs allocation — why a shape omission drops a fact), WI-814 (the
//! four-site shape discipline), WI-803 (order-free `<:` on a data tuple), WI-782 (order is
//! identity for a parameter list), WI-784 (operation/lambda interchangeability), WI-857 (why
//! `named` is identity), WI-1019 (the shape IS the equality).

use std::rc::Rc;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term_view::{goal_fingerprint, views_structurally_equal};

fn drive_int(src: &str, op: &str) -> i64 {
    // A FRESH interpreter per call — a reused one poisons later calls after a trap.
    match crate::common::interp_for(src)
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// The ticket's program: `outer` hands its callback on to `inner`, whose `A` names the same
/// two components. `callee` is the function value; `outer_a` is `outer`'s own `A`.
fn retype_case(ns: &str, outer_a: &str, callee: &str) -> String {
    format!(
        "namespace {ns}\n\
         \x20 import anthill.prelude.{{Int64, Function}}\n\
         \x20 operation sub2(a: Int64, b: Int64) -> Int64 = a - b\n\
         \x20 operation inner(g: Function[A = (x: Int64, acc: Int64), B = Int64]) -> Int64 \
            = g((acc: 3, x: 10))\n\
         \x20 operation outer(f: Function[A = {outer_a}, B = Int64]) -> Int64 = inner(f)\n\
         \x20 operation drive_inner() -> Int64 = inner({callee})\n\
         \x20 operation drive_outer() -> Int64 = outer({callee})\n\
         end\n"
    )
}

/// The load errors, or a panic naming the program that was supposed to be refused.
fn refusal_of(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!("expected a load refusal; the program loaded clean:\n{src}"),
    }
}

/// THE HEADLINE (2). `outer`'s `A` is `(acc, x)` and `inner`'s is `(x, acc)` — the same two
/// components, permuted. The by-name relation admitted it; the mapping the value carries is
/// the one its MINT site pinned, so `inner`'s declared `A` was silently not the mapping used
/// and one program answered 7 through one route and -7 through the other.
///
/// CONTROL: with the `parameterized_compatible_view` guard removed, this program loads clean
/// and `drive_inner` / `drive_outer` return 7 and -7 — measured on the WI-1087 tree, which is
/// where the hazard was found.
#[test]
fn a_permuted_function_to_function_pairing_is_refused() {
    let errs = refusal_of(&retype_case(
        "test.wi1088.perm",
        "(acc: Int64, x: Int64)",
        "sub2",
    ));
    let joined = errs.join("\n");
    assert!(
        joined.contains("inner.g") && joined.contains("(x: Int64, acc: Int64)"),
        "the refusal names the slot and the two orders: {joined}",
    );
}

/// THE LAMBDA SPELLING of the same pairing, refused identically. WI-784's rule is that an
/// operation and a lambda are interchangeable as function values, and the hazard is one they
/// SHARE: the lambda half answered 7/-7 before WI-1087 existed, because an unannotated lambda
/// adopts its mint site's `A` as `Pattern::Tuple.labels` exactly as an eta'd operation adopts
/// it as `spread_labels`. A fix on the relation covers both; a fix on `OpRef` alone would
/// have left this row loading.
///
/// CONTROL: same revert as the row above — this one loads clean and disagrees with itself.
#[test]
fn a_permuted_pairing_is_refused_in_the_lambda_spelling_too() {
    let errs = refusal_of(&retype_case(
        "test.wi1088.permlam",
        "(acc: Int64, x: Int64)",
        "lambda (p, q) -> p - q",
    ));
    assert!(errs.join("\n").contains("inner.g"), "{errs:?}");
}

/// THE BOUND. Re-typing a function value through a second `Function` slot is not what is
/// refused — DISAGREEING about the order is. With `outer`'s `A` written in `inner`'s order
/// the program still loads, still runs, and the two routes return the SAME answer, which is
/// what the ticket asked to be driven.
///
/// Passes BOTH ways, by design: it is the control that keeps the refusal narrow, and a guard
/// that banned re-typing outright would fail here while the two rows above stayed green.
#[test]
fn an_agreeing_function_to_function_pairing_still_runs() {
    for (ns, callee) in [
        ("test.wi1088.agree", "sub2"),
        ("test.wi1088.agreelam", "lambda (p, q) -> p - q"),
    ] {
        let src = retype_case(ns, "(x: Int64, acc: Int64)", callee);
        let direct = drive_int(&src, &format!("{ns}.drive_inner"));
        let through = drive_int(&src, &format!("{ns}.drive_outer"));
        assert_eq!(
            direct, 7,
            "parameter `a` takes `A`'s first component `x` = 10"
        );
        assert_eq!(
            through, direct,
            "one value, two slots that agree on `A`'s order, one answer ({callee})",
        );
    }
}

/// THE COST, PINNED RATHER THAN DESCRIBED. `one` is a genuine ONE-parameter callback that
/// reads its argument BY LABEL, so `A`'s order is semantically irrelevant to it and the
/// whole-`A` reading — the order-free one — is the only one this value can ever meet. The
/// pairing is refused anyway.
///
/// It is not separable, and that is the claim this row exists to keep honest. A `Function`
/// slot states NO arity — that is exactly why it admits two readings (WI-801) — so nothing
/// at the pairing can know that the value behind it is one-parameter. Refusing here is the
/// price of a slot that will not say, and there is no spelling that opts out.
///
/// Found by review, which drove it; recorded as a test so a later ticket that thinks it can
/// narrow the guard to "only when a spread is reachable" fails HERE and reads why.
#[test]
fn the_refusal_reaches_a_pairing_only_arity_one_could_use() {
    let errs = refusal_of(
        "namespace test.wi1088.arity1cost\n\
         \x20 import anthill.prelude.{Int64, Function}\n\
         \x20 operation one(t: (x: Int64, acc: Int64)) -> Int64 = t.x\n\
         \x20 operation inner(g: Function[A = (x: Int64, acc: Int64), B = Int64]) -> Int64 \
            = g((acc: 3, x: 10))\n\
         \x20 operation outer(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64 \
            = inner(f)\n\
         \x20 operation drive() -> Int64 = inner(one)\n\
         end\n",
    );
    assert!(
        errs.join("\n").contains("inner.g"),
        "the pairing is refused on `A`'s order even where only the order-free reading is \
         reachable — a `Function` slot states no arity, so it cannot tell: {errs:?}",
    );
}

/// THE σ-PINNED ROUTE. The pair above is GROUND, so it is decided by `types_compatible` and
/// decomposed at `parameterized_compatible_view`. A slot whose `A` carries a type variable is
/// not ground and is routed to `validate_arrow_param_result` instead — a different function
/// with its own relation, which is why WI-1087 had to state the rule at both and why the
/// guard is asked at both, through one predicate.
///
/// `T` is pinned by the SIBLING argument `w`, which is what makes the comparison reachable at
/// all (WI-1085: the groundness gate reads the component AFTER σ).
///
/// CONTROL: with the `validate_arrow_param_result` guard removed this loads clean, while both
/// rows above stay refused — the two routes are reached by different programs.
#[test]
fn a_permutation_is_refused_through_a_sigma_pinned_slot_too() {
    let case = |ns: &str, inner_a: &str| {
        format!(
            "namespace {ns}\n\
             \x20 import anthill.prelude.{{Int64, Function}}\n\
             \x20 operation inner[T](g: Function[A = {inner_a}, B = Int64], w: T) -> Int64 = 0\n\
             \x20 operation outer(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64 \
                = inner(f, 1)\n\
             end\n"
        )
    };
    let errs = refusal_of(&case("test.wi1088.ng", "(x: T, acc: Int64)"));
    assert!(
        errs.join("\n").contains("inner.g"),
        "the σ-pinned slot refuses the permutation too: {errs:?}",
    );

    // The agreeing twin, through the SAME route — without it this row would pass on a
    // guard that refused every non-ground `Function`/`Function` pairing.
    crate::common::load_kb_with(&case("test.wi1088.ngok", "(acc: T, x: Int64)"));
}

// ── (1) the mapping is part of the value's structural identity ───────────────

/// THE HEADLINE (1). Two `OpRef`s to ONE operation, agreeing on `op`, `dict` and `named`
/// and differing ONLY in which of `A`'s components fills which parameter. They answer
/// differently from the same argument, so they are different values — and before this
/// ticket they compared EQUAL and shared a `goal_fingerprint`.
///
/// The pair is REACHABLE, which is what refuted the alternative reading ("establish that
/// the two values cannot both exist and be compared"): one operation eta'd at two
/// independent `Function` slots that order `A`'s labels differently mints exactly this
/// pair, and hazard (2)'s refusal does not touch it — that guard relates two slots to
/// each other, and two independent slots are never so related.
/// [`two_slots_ordering_a_differently_mint_two_readings`] drives that program.
///
/// Asked of BOTH questions at once, following `wi1019…`'s discipline: equality and the
/// KEY answered differently once before (WI-1014's stopgap fixed the first and could not
/// reach the second), and a shape is what makes them one read.
///
/// CONTROL: with `"spread"` dropped from `opref_shape` this test fails and only this test
/// — the same shape the `dict` and `named` rows have in `wi1019…`.
#[test]
fn two_oprefs_differing_only_in_their_spread_mapping_are_distinct() {
    let interp = crate::common::interp_for("namespace test.wi1088.empty\nend\n");
    let kb = interp.kb();
    let sym = |qn: &str| {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("symbol {qn} not found in KB"))
    };
    let op = sym("anthill.prelude.Option");
    let (acc, x) = (sym("anthill.prelude.Int64"), sym("anthill.prelude.Bool"));
    let with = |labels: Option<Vec<Symbol>>| Value::OpRef {
        op,
        dict: None,
        named: None,
        spread_labels: labels.map(|l| Rc::from(l.as_slice())),
    };
    let eq_and_key = |a: &Value, b: &Value| {
        let s = Substitution::new();
        (
            views_structurally_equal(kb, a, b),
            goal_fingerprint(kb, a, &s) == goal_fingerprint(kb, b, &s),
        )
    };

    let (eq, same_key) = eq_and_key(&with(Some(vec![acc, x])), &with(Some(vec![x, acc])));
    assert!(
        !eq,
        "ORDER is the whole content of this field — a permuted mapping is a different value"
    );
    assert!(
        !same_key,
        "and the difference reaches the key, which is what feeds fact dedup"
    );

    // Equal to ITSELF — `assert!(!…)` alone is also satisfied by a shape that makes every
    // `OpRef` distinct from every other, including from its own twin (the WI-1014 defect,
    // one direction over).
    let (eq, same_key) = eq_and_key(&with(Some(vec![acc, x])), &with(Some(vec![acc, x])));
    assert!(
        eq && same_key,
        "one mapping, separately built, is one value"
    );

    // A present mapping and an ABSENT one differ by the conditional key's ARITY — the
    // `Expr::Proof` precedent the other two optional halves follow, so no `Option` wrapper
    // is synthesized on the child read.
    let (eq, same_key) = eq_and_key(&with(Some(vec![acc, x])), &with(None));
    assert!(
        !eq && !same_key,
        "an eta'd reference is not the same value as a dictionary-minted one"
    );
}

/// THE PAIR ABOVE, MINTED BY A PROGRAM rather than by hand — which is what makes the
/// identity claim about the language and not about a struct literal. `sub2` is eta'd at
/// two INDEPENDENT slots whose `A`s order the same labels differently; each spread reads
/// its own slot's mapping, so one operation and one argument produce two answers.
///
/// This is also the refutation of "the two values cannot co-exist": here they do, under
/// one KB, and neither is refused — hazard (2)'s guard relates a declared slot to a value
/// flowing INTO it, and these two slots are never compared with each other.
#[test]
fn two_slots_ordering_a_differently_mint_two_readings() {
    let src = "namespace test.wi1088.twoslots\n\
         \x20 import anthill.prelude.{Int64, Function}\n\
         \x20 operation sub2(a: Int64, b: Int64) -> Int64 = a - b\n\
         \x20 operation ap1(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64 \
            = f((acc: 3, x: 10))\n\
         \x20 operation ap2(f: Function[A = (x: Int64, acc: Int64), B = Int64]) -> Int64 \
            = f((acc: 3, x: 10))\n\
         \x20 operation drive1() -> Int64 = ap1(sub2)\n\
         \x20 operation drive2() -> Int64 = ap2(sub2)\n\
         end\n";
    assert_eq!(
        drive_int(src, "test.wi1088.twoslots.drive1"),
        -7,
        "`acc` - `x`"
    );
    assert_eq!(
        drive_int(src, "test.wi1088.twoslots.drive2"),
        7,
        "`x` - `acc`"
    );
}

/// THE ACCESSOR RUNS. `opref_shape`'s keys are DECLARED accessors, so listing a fourth
/// means declaring `OpRef.spreadLabels` on the reflect `OpRef` sort — and a declared
/// accessor a caller cannot call is a surface that only looks complete. Driven to the
/// VALUE: the labels come back through the anthill signature, in DECLARED ORDER, as the
/// `List[Symbol]` it promises.
///
/// The non-eta half is asserted beside it because `none()` is the answer for every mint
/// that is not a `Function`-slot eta (`Dictionary.resolveOp` / `ops` mint from a
/// dictionary, with no slot to read a mapping off), and a reader answering `some([])`
/// there would pass a positive-only test.
#[test]
fn the_spread_labels_accessor_answers_for_both_mints() {
    let mut interp = crate::common::interp_for("namespace test.wi1088.acc\nend\n");
    let sym = |i: &Interpreter, qn: &str| {
        i.kb()
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("symbol {qn} not found in KB"))
    };
    let (op, acc, x) = (
        sym(&interp, "anthill.prelude.Option"),
        sym(&interp, "anthill.prelude.Int64"),
        sym(&interp, "anthill.prelude.Bool"),
    );
    let (some_s, none_s, cons_s, nil_s) = (
        sym(&interp, "anthill.prelude.Option.some"),
        sym(&interp, "anthill.prelude.Option.none"),
        sym(&interp, "anthill.prelude.List.cons"),
        sym(&interp, "anthill.prelude.List.nil"),
    );
    let child = |v: &Value, name: &str, kb: &anthill_core::kb::KnowledgeBase| -> Value {
        match v {
            Value::Entity { named, .. } => named
                .iter()
                .find(|(s, _)| kb.local_name_of(*s) == name)
                .map(|(_, c)| c.clone())
                .unwrap_or_else(|| panic!("no `{name}` child on {v:?}")),
            other => panic!("expected an entity, got {other:?}"),
        }
    };
    let functor = |v: &Value| match v {
        Value::Entity { functor, .. } => *functor,
        other => panic!("expected an entity, got {other:?}"),
    };
    let call = |i: &mut Interpreter, labels: Option<Vec<Symbol>>| {
        i.call(
            "anthill.realization.runtime.OpRef.spreadLabels",
            &[Value::OpRef {
                op,
                dict: None,
                named: None,
                spread_labels: labels.map(|l| Rc::from(l.as_slice())),
            }],
        )
        .expect("OpRef.spreadLabels")
    };

    let answer = call(&mut interp, Some(vec![acc, x]));
    assert_eq!(
        functor(&answer),
        some_s,
        "an eta'd reference answers some(...)"
    );
    // Walk the cons chain and read the symbols back — the ORDER is the content.
    let mut node = child(&answer, "value", interp.kb());
    let mut read: Vec<Symbol> = Vec::new();
    while functor(&node) == cons_s {
        match child(&node, "head", interp.kb()) {
            Value::SymbolRef(s) => read.push(s),
            other => panic!("a list element is not a Symbol: {other:?}"),
        }
        node = child(&node, "tail", interp.kb());
    }
    assert_eq!(functor(&node), nil_s, "the chain ends in nil");
    assert_eq!(
        read,
        vec![acc, x],
        "`A`'s labels, in the order the slot declares them"
    );

    let answer = call(&mut interp, None);
    assert_eq!(
        functor(&answer),
        none_s,
        "a non-eta mint answers none(), not an empty list",
    );
}
