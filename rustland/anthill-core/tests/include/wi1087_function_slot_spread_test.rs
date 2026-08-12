//! WI-1087 — a `Function[A = …]` slot reads `A` as the callback's PARAMETER LIST when the
//! callback spreads it, so the two spellings of `A` stop disagreeing.
//!
//! Two settled rules were in outright conflict, and the kernel applied each where the other
//! could not see. WI-775: a `Function[A = …]`'s `A` is the ARGUMENT's data type, aligned BY
//! NAME. WI-801: the same slot admits exactly TWO call counts — ONE whole `A`, or `A`'s
//! components SPREAD. For a 2-parameter OPERATION they cannot both hold, because its eta
//! arrow always spells its parameter list with the synthetic `_1, _2` (an arrow drops its
//! binder names, WI-783), so the by-name comparison refuses every spread WI-801 admits.
//!
//! WHAT MADE IT A DEFECT rather than a strict rule: the verdict turned on a property the
//! runtime never reads. Written `Function[A = (Int64, Int64)]` the program loaded and ran;
//! written `Function[A = (acc: Int64, x: Int64)]` it was refused — byte-identical otherwise,
//! and the positional spelling passed only because ITS labels are `_1, _2` and coincide with
//! the synthetic escape. `spread_eta_args` consults no label at all. Both spellings now take
//! the positional reading, and [`both_spellings_of_a_take_a_two_parameter_operation`] drives
//! them side by side.
//!
//! ## THE RELATION ALONE WOULD HAVE BEEN A SILENT WRONG ANSWER
//!
//! Under the rule the callee's parameter `i` is `A`'s component `i`, positionally — while
//! the VALUE at the slot conforms to `A` BY NAME and may present its components in another
//! order, since WI-803 made `<:` on a data tuple order-free. `spread_eta_args` read
//! `TupleComponents::iter()` — `pos ++ named`, which drops the labels — so a permuted value
//! handed parameter `i` the `i`-th WRITTEN component. Its own site comment had called it
//! "THE LATENT TWIN of the destructuring reader", "currently UNREACHABLE, and only
//! incidentally": what blocked it was exactly the by-name refusal this ticket removes.
//!
//! MEASURED WITH THE RELATION WIDENED AND THE READER UNTOUCHED: `f((x: 10, acc: 3))` at
//! `A = (acc, x)` with `sub2(a, b) = a - b` answered **7**, where the labels say `3 - 10`.
//! A program that loads, runs, and is wrong. The operation now spreads BY LABEL, through the
//! mapping the typer attaches at the eta site (`Value::OpRef::spread_labels`) — the channel
//! `dict` already rides, and for the same reason: the apply site cannot re-derive it. Its
//! lambda twin has read by label since WI-803, and WI-784's rule is that the two are
//! interchangeable; [`an_operation_and_a_lambda_agree_on_a_permuted_argument`] is that pair.
//!
//! ## NARROW BY DECISION (user, 2026-08-12)
//!
//! The general rule "labels absent → align positionally, labels present → reorder" was
//! considered and rejected: it requires overturning proposal 004 rule 4 and §4.5 ("no
//! subtyping between named and positional"), and two readers that are NOT local — `._N` on a
//! name-keyed value and `.name` on a POSITIONAL one, the latter resolvable only from the
//! declared type's component index at EVERY access site. §4.5 states why such a widening
//! cannot be gated on the reader: "a value flows through a `Function[A, B]` parameter to a
//! consumer chosen at a DIFFERENT call site than the one relating it to `A`." Data-tuple
//! identity is untouched, and [`data_tuple_identity_is_untouched`] pins both directions.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each, whole crate
//!
//! | revert | cost |
//! |---|---|
//! | `function_slot_reads_a_as_param_list` forced `false` (the by-name rule restored) | **9** (measured before the review correction below; the arm it names is unchanged) — [`both_spellings_of_a_take_a_two_parameter_operation`] and [`an_operation_and_a_lambda_agree_on_a_permuted_argument`] here; `wi775…::function_sort_argument_type_takes_a_two_parameter_operation`, the pin this inverts; THREE `wi787_eta_spread_named_tuple_test` rows and `wi1083…::a_requires_carrying_member_runs_as_a_function_value`, all of which reach a `Function` slot through a σ-pinned `A` and were previously carried by the WI-1085 groundness skip that this ticket's σ-resolution removes; and both `wi1085…` `Function`-arm rows. Every one a program that EVALUATES |
//! | the READER — `spread_eta_args` back on `TupleComponents::iter()` | **1** — [`an_operation_and_a_lambda_agree_on_a_permuted_argument`], which answers **7** on the operation half and **-7** on the lambda half. Nothing else in the crate notices, and that is the shape of the hazard rather than evidence against it: it is reachable only where a value is PERMUTED relative to a written-out `A`, which no corpus program does and which the relation refused outright until this ticket. A load-clean, run-clean wrong answer |
//! | the arity check's σ-resolution (`function_slot_arity_error` reads `declared` as written) | **2** — `wi784…::a_callback_arity_pinned_by_a_sibling_argument_is_refused_at_load` and `wi787…::arity_mismatch_is_refused_at_load`, both back to a run-time trap on a load-clean program. This is the piece that moves WI-801's decider from "the slot states no component count" to "σ has pinned one" |
//!
//! ONE DIRECTION, NOT TWO — a correction found by review, and the reason the table above
//! has no mirror row. The first cut let the positional relation run in EITHER arrangement,
//! which gave it to a `Function`-typed VALUE at an `arrow` SLOT. That is unsound: an arrow
//! slot states a hard arity and applies its value with exactly that many arguments, while a
//! `Function` value states none and may be either reading, so `n == |A|` proves nothing
//! about the callable inside. Measured, load-clean and trapping `ArityMismatch { expected:
//! 1, got: 2 }` at eval. `wi1085…::a_function_typed_argument_at_an_arrow_slot_is_refused_-
//! whatever_the_labels` is that pairing, refused in both label shapes.
//!
//! Rows that pass BOTH ways, by design, and say so at their sites:
//! [`a_positional_argument_still_spreads_in_slot_order`], [`data_tuple_identity_is_untouched`],
//! [`arity_one_keeps_the_by_name_reading`].
//!
//! REFERENCE: WI-1085 (where the conflict was measured), WI-775 (what it ACTUALLY filed —
//! one defect in one direction — and the `Function`-surface extension this inverts), WI-801
//! (the two admitted arities), WI-782/WI-442 (`PARAM_LIST` and the synthetic escape), WI-803
//! (resolve from the expected type; the lambda half of the reader), WI-787/WI-784 (the
//! spread that runs; operation/lambda interchangeability), WI-790 (what makes a label
//! synthetic), proposal 004 rule 4 and `docs/kernel-language.md` §4.5.

use crate::wi1012_static_supplier_tie_test::refusal;

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

/// `apply2(f: Function[A = {a_ty}, B = Int64]) = f({lit})` driven with `{callee}`.
fn slot_case(ns: &str, a_ty: &str, lit: &str, callee: &str) -> String {
    format!(
        "namespace {ns}\n\
         \x20 import anthill.prelude.{{Int64, Function}}\n\
         \x20 operation sub2(a: Int64, b: Int64) -> Int64 = a - b\n\
         \x20 operation apply2(f: Function[A = {a_ty}, B = Int64]) -> Int64 = f({lit})\n\
         \x20 operation drive() -> Int64 = apply2({callee})\n\
         end\n"
    )
}

/// THE HEADLINE. The same program written two ways — `A`'s components labelled, and `A`
/// written positionally — must reach the same verdict, because the runtime treats them
/// identically. Before this ticket the labelled one was REFUSED and the positional one ran.
///
/// Driven to VALUES on both sides: "both load" would pass on a fix that accepted the pairing
/// without spreading it, which is the shape WI-775 originally refused for a real reason.
///
/// CONTROL: with `function_slot_reads_a_as_param_list` forced to `false` (the by-name rule
/// restored), the labelled row is refused at load with `expected Function[A = (acc: Int64,
/// x: Int64), B = Int64], got (_1: Int64, _2: Int64) -> Int64` while the positional row is
/// untouched — which is the asymmetry this ticket exists to remove.
#[test]
fn both_spellings_of_a_take_a_two_parameter_operation() {
    assert_eq!(
        drive_int(
            &slot_case("test.wi1087.named", "(acc: Int64, x: Int64)", "(acc: 3, x: 10)", "sub2"),
            "test.wi1087.named.drive",
        ),
        -7,
    );
    assert_eq!(
        drive_int(
            &slot_case("test.wi1087.pos", "(Int64, Int64)", "(3, 10)", "sub2"),
            "test.wi1087.pos.drive",
        ),
        -7,
        "the positional spelling ran throughout — it is the CONTROL, not the change",
    );
}

/// THE READER. `A` declares `(acc, x)` and the argument is written `(x: 10, acc: 3)` — a
/// permutation, which `<:` on a data tuple admits by name (WI-803). Parameter `a` wants
/// `A`'s FIRST component, `acc` = 3, so the answer is `3 - 10`. Reading the value in source
/// order gives `10 - 3` instead, and that is what the relation change alone produced.
///
/// The LAMBDA spelling is asserted beside it because WI-784's rule is that an operation and
/// a lambda are interchangeable as function values, and until this ticket they were not:
/// `match_tuple_pattern` has read by label since WI-803 while `spread_eta_args` read by
/// slot. The pair is the claim; either row alone would pass on a one-sided fix.
///
/// CONTROL: with `spread_eta_args` back on `TupleComponents::iter()`, the operation row
/// answers 7 and the lambda row still answers -7 — a load-clean, run-clean disagreement
/// between two spellings of one program.
#[test]
fn an_operation_and_a_lambda_agree_on_a_permuted_argument() {
    let by_op = drive_int(
        &slot_case("test.wi1087.perm", "(acc: Int64, x: Int64)", "(x: 10, acc: 3)", "sub2"),
        "test.wi1087.perm.drive",
    );
    let by_lambda = drive_int(
        &slot_case(
            "test.wi1087.permlam",
            "(acc: Int64, x: Int64)",
            "(x: 10, acc: 3)",
            "lambda (p, q) -> p - q",
        ),
        "test.wi1087.permlam.drive",
    );
    assert_eq!(by_op, -7, "parameter `a` takes `A`'s first component `acc` = 3");
    assert_eq!(by_lambda, -7, "the lambda half, unchanged since WI-803");
}

/// A POSITIONAL carrier still spreads in SLOT order — the by-label read must not turn into
/// a requirement that the value carry names. `A` is written positionally here, so its labels
/// are the synthetic `_1, _2` and the argument is a positional tuple; `by_label` resolves
/// `_N` through its own arm and lands on `pos[N-1]`.
///
/// This is also where the reader's ONE gate went: a `TupleComponents::is_name_keyed` early
/// return, modelled on `match_tuple_pattern`'s, could not be driven — a positional carrier
/// reaches a LABELLED `A` only by conforming to it, and proposal 004 rule 4 refuses that at
/// load (see [`data_tuple_identity_is_untouched`]). So the labels are `_1.._n` whenever the
/// carrier is positional, and the gate guarded nothing. Removed rather than kept unmeasured.
///
/// Passes both ways, by design: it bounds the row above, which a reader keying on names
/// unconditionally would satisfy while raising here.
#[test]
fn a_positional_argument_still_spreads_in_slot_order() {
    assert_eq!(
        drive_int(
            &slot_case("test.wi1087.posarg", "(Int64, Int64)", "(3, 10)", "sub2"),
            "test.wi1087.posarg.drive",
        ),
        -7,
    );
}

/// An element-TYPE disagreement inside a spread `A` is REFUSED — the positional reading
/// relates the components, it does not wave them through. `A`'s second component is a
/// `String` and the callback's second parameter an `Int64`.
///
/// Its agreeing twin is [`both_spellings_of_a_take_a_two_parameter_operation`] above, which
/// is what makes this row a claim about the COMPONENTS rather than about the pairing.
#[test]
fn an_element_type_disagreement_inside_a_spread_a_is_refused() {
    let msg = refusal(
        "namespace test.wi1087.badty\n\
         \x20 import anthill.prelude.{Int64, String, Function}\n\
         \x20 operation sub2(a: Int64, b: Int64) -> Int64 = a - b\n\
         \x20 operation apply2(f: Function[A = (acc: Int64, x: String), B = Int64]) -> Int64 \
            = f((acc: 3, x: \"s\"))\n\
         \x20 operation drive() -> Int64 = apply2(sub2)\n\
         end\n",
    );
    assert!(
        msg.contains("apply2.f") && msg.contains("String"),
        "the component types are still related, positionally: {msg}",
    );
}

/// ARITY ONE KEEPS THE BY-NAME READING, which is WI-775's rule and is not touched. At one
/// parameter the two call counts coincide, `A` is the sole parameter's TYPE, and a tuple
/// there is DATA — so a callback declaring `(t: (x: Int64, y: Int64))` against
/// `A = (a: Int64, b: Int64)` is refused on the names, exactly as it was.
#[test]
fn arity_one_keeps_the_by_name_reading() {
    let msg = refusal(
        "namespace test.wi1087.arity1\n\
         \x20 import anthill.prelude.{Int64, Function}\n\
         \x20 operation get_x(t: (x: Int64, y: Int64)) -> Int64 = t.x\n\
         \x20 operation apply1(f: Function[A = (a: Int64, b: Int64), B = Int64]) -> Int64 \
            = f((a: 3, b: 10))\n\
         \x20 operation drive() -> Int64 = apply1(get_x)\n\
         end\n",
    );
    assert!(msg.contains("apply1.f"), "{msg}");
}

/// DATA-TUPLE IDENTITY IS UNTOUCHED, in both directions — the half the narrow decision
/// deliberately left alone. Proposal 004 rule 4 and §4.5 stand: `(a: Int64, b: Int64)` and
/// `(Int64, Int64)` are different types, no subtyping either way.
///
/// Pinned HERE, not only at wi775, because this ticket is where the temptation to widen it
/// arises: the spread reading relates a labelled `A` to a synthetic `_1.._n` parameter list,
/// and it would be an easy over-generalization to conclude that named and positional tuples
/// relate everywhere. They do not. `A` in the spread reading is not a data tuple at all.
#[test]
fn data_tuple_identity_is_untouched() {
    let case = |ns: &str, slot: &str, ret: &str, lit: &str, read: &str| {
        format!(
            "namespace {ns}\n\
             \x20 import anthill.prelude.{{Int64}}\n\
             \x20 operation get(t: {slot}) -> Int64 = {read}\n\
             \x20 operation mk() -> {ret} = {lit}\n\
             \x20 operation drive() -> Int64 = get(mk())\n\
             end\n"
        )
    };
    let named_at_positional = case(
        "test.wi1087.d1",
        "(Int64, Int64)",
        "(a: Int64, b: Int64)",
        "(a: 3, b: 10)",
        "t._1",
    );
    let positional_at_named = case(
        "test.wi1087.d2",
        "(a: Int64, b: Int64)",
        "(Int64, Int64)",
        "(3, 10)",
        "t.a",
    );
    for src in [&named_at_positional, &positional_at_named] {
        assert!(
            crate::common::try_load_kb_with(src).is_err(),
            "named and positional tuples do not relate as DATA (004 rule 4):\n{src}",
        );
    }
}
