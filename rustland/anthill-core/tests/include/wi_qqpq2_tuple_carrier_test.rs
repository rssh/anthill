//! WI-20260904-QQPQ2 — A TUPLE DESTRUCTURES ON EVERY CARRIER, NOT ONLY `Value::Tuple`.
//!
//! The ticket's own row is a MULTI-BINDER LAMBDA in a rule body: it loads and is never
//! applied. Its operation-body twin answers, and so does `sum2((a: 1, b: 2))` written in
//! the same rule-body position, so the gap was an APPLICATION one and not a typing one
//! (measured on WI-20260904-50B2K, whose
//! `the_tuple_binders_operation_body_twin_drives_and_is_unmoved` pinned that reading).
//!
//! THE MECHANISM. `bridge_op_to_eval` (kb/resolve.rs) hands a bridged operation each
//! operand ON THE CARRIER THE RESOLVER PROVED IT ON, so a written `(a: 1, b: 2)` arrives
//! as a `Value::Node` occurrence rather than a `Value::Tuple`. Every tuple read in eval
//! went through `Value::tuple_components`, which matched `Value::Tuple` and answered
//! `None` for everything else — and `None` here is not "not a tuple", it is
//! `match_tuple_pattern` declining, which `enter_closure` turns into a raised
//! `Error[MatchFailed]`, which the bridge residualizes. The rule FLOUNDERS: one solution,
//! not definite, `?r` unbound.
//!
//! FOUR SPELLINGS, ONE ROOT — censused before the fix, all four red, all four green
//! after, and each is a separate row below because they reach the reader by different
//! routes (a closure's parameter pattern, a `match` arm, a `let` binder) and because a
//! POSITIONAL tuple takes the other side of the `is_name_keyed` gate:
//!
//! ```text
//!   apply2(lambda (a: Int64, b: Int64) -> a + b, (a: 1, b: 2))   the ticket's row
//!   match p case (x, y) -> x + y                                  over a named tuple
//!   let (x, y) = p                                                over a named tuple
//!   match p case (x, y) -> x + y                                  over a POSITIONAL one
//! ```
//!
//! `tuple_components` HAS A SECOND CONSUMER and it is covered too: `spread_eta_args`,
//! where an `OpRef` applied to one tuple argument spreads it across the operation's
//! parameters. Its fixture had to route around a SECOND defect the census turned up —
//! `apply2(sum2op, (a: 1, b: 2))` written in a rule body never reaches this reader,
//! because an operation NAME in a rule-body function slot is not callable and dies
//! `UnknownOperation { name: "…apply2.f" }` before any tuple is looked at. That is a
//! DIFFERENT root, not a scope call: it reproduces at ONE parameter (`apply1(inc1, 2)`),
//! where no tuple exists anywhere. Filed as WI-20260904-833DK and pinned by
//! `an_eta_d_operation_name_is_a_known_gap`; the reader itself is driven by
//! `an_op_ref_spreads_a_bridged_tuple_and_keeps_its_labels`, which mints the `OpRef` in
//! an OPERATION body and threads the bridged tuple in as a parameter.
//!
//! TWO BACK-OUTS, MEASURED SEPARATELY, because the repair has two parts and the second
//! is invisible to the first's rows:
//!
//!  * **A — `tuple_components`' non-native arm restored to `_ => None`.** EIGHT of the
//!    eleven rows fall. The three that stand are the two operation-body CONTROLS, which
//!    never leave `Value::Tuple`, and the eta known-gap row, whose failure is raised
//!    before any tuple is read. The controls pass either way BY DESIGN: they are here to
//!    say the repair did not simply widen what a tuple pattern accepts, and that the
//!    rule-body and operation-body spellings now AGREE where they disagreed.
//!  * **B — the view's halves forwarded unchanged, without putting the synthetic `_N`
//!    components back in `pos`.** EXACTLY ONE row falls,
//!    `a_positional_tuple_meeting_a_name_keyed_pattern_reads_by_slot`, and finding it
//!    took writing a second fixture: the obvious positional row is green under B, because
//!    its own pattern labels are synthetic too and gate the by-label arm off from the
//!    other side.

use anthill_core::kb::term_view::TermView;
use anthill_core::kb::KnowledgeBase;

const PREAMBLE: &str = r#"  import anthill.prelude.{Int64, Function}
  operation apply2(f: Function[A = (a: Int64, b: Int64), B = Int64], p: (a: Int64, b: Int64)) -> Int64 = f(p)
  operation named_match(p: (a: Int64, b: Int64)) -> Int64 =
    match p
      case (x, y) -> x + y
  operation named_let(p: (a: Int64, b: Int64)) -> Int64 =
    let (x, y) = p
    x + y
  operation positional_match(p: (Int64, Int64)) -> Int64 =
    match p
      case (x, y) -> x + y
  operation named_sub(p: (a: Int64, b: Int64)) -> Int64 =
    match p
      case (x, y) -> x - y
  operation sub2op(a: Int64, b: Int64) -> Int64 = a - b
  operation apply_oparg(f: Function[A = (a: Int64, b: Int64), B = Int64], p: (a: Int64, b: Int64)) -> Int64 = f(p)
  operation spread_outer(p: (a: Int64, b: Int64)) -> Int64 = apply_oparg(sub2op, p)
"#;

fn load(ns: &str, body: &str) -> KnowledgeBase {
    let src = format!("namespace {ns}\n{PREAMBLE}{body}end\n");
    crate::common::try_load_kb_with(&src).unwrap_or_else(|errs| {
        panic!(
            "must load; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n")
        )
    })
}

/// The one definite `Int64` answer — the VALUE, not "something answered".
///
/// `definite_unary` rather than a solution count, and that distinction is the whole
/// measurement here: every red row below answered ONE solution before the fix, a
/// FLOUNDERED one carrying an unbound `?r`. A `query_unary(..).len()` assertion would
/// have been green throughout (WI-20260822-WZX6B).
fn only_int(kb: &mut KnowledgeBase, qn: &str) -> i64 {
    let mut vs = crate::common::definite_unary(kb, qn);
    assert_eq!(vs.len(), 1, "{qn}: expected exactly one answer, got {vs:?}");
    let v = vs.pop().unwrap();
    v.literal_int64(kb)
        .unwrap_or_else(|| panic!("{qn}: expected an Int64 answer, got {v:?}"))
}

/// **THE ROW THIS TICKET EXISTS FOR.** A two-binder lambda handed to a higher-order
/// operation from a RULE body. The binder list destructures the tuple the caller built,
/// which is `gather_closure_arg`'s documented "arity n" hand-off — and the tuple it is
/// handed is a `Value::Node`.
///
/// ANNOTATED deliberately. The un-annotated twin does not load at all: its binder
/// components still take their type from the sub-pattern ladder's inert `type_var`
/// (WI-20260904-50B2K's `?pat` census item, which measured that flipping it fails four
/// rows), so it is refused with an `Additive` ambiguity long before application. That is
/// a TYPING gap on a different mint; this row is the APPLICATION one, and the annotation
/// is what isolates it.
///
/// FAILS ON THE BACK-OUT: one FLOUNDERED solution, `?r` unbound.
#[test]
fn a_multi_binder_lambda_in_a_rule_body_is_applied() {
    let mut kb = load(
        "zzqqpq2.lambda",
        "  rule value(?r) :- ?r <=> apply2(lambda (a: Int64, b: Int64) -> a + b, (a: 1, b: 2))\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.lambda.value"), 3);
}

/// A `match` arm's tuple pattern over a NAME-KEYED tuple — `match_tuple_pattern`'s
/// by-label arm, reached with the value on the occurrence carrier.
///
/// FAILS ON THE BACK-OUT.
#[test]
fn a_match_arms_tuple_pattern_destructures_a_rule_body_tuple() {
    let mut kb = load(
        "zzqqpq2.matchnamed",
        "  rule value(?r) :- ?r <=> named_match((a: 1, b: 2))\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.matchnamed.value"), 3);
}

/// A `let` binder's tuple pattern — the same reader through a third route.
///
/// FAILS ON THE BACK-OUT.
#[test]
fn a_let_binders_tuple_pattern_destructures_a_rule_body_tuple() {
    let mut kb = load(
        "zzqqpq2.letnamed",
        "  rule value(?r) :- ?r <=> named_let((a: 1, b: 2))\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.letnamed.value"), 3);
}

/// **THE POSITIONAL TUPLE, AND IT IS NOT A DUPLICATE OF THE TWO ABOVE.** It takes the
/// OTHER side of the `is_name_keyed` gate, and it is the row that made the repair
/// NORMALIZE the carrier rather than forward it: `(1, 2)` is
/// `Tuple { pos: [1, 2], named: [] }` natively, while its occurrence twin is ALL-NAMED
/// with the synthetic `_1` / `_2` labels (`convert.rs`'s `TupleLiteral` build). Handing
/// those through as `named` would leave the two carriers disagreeing about
/// `is_name_keyed`, which is what selects the by-label arm — so the `_N` half is put back
/// where the native carrier holds it.
///
/// FAILS ON THE BACK-OUT, and it is the LOUDER of the two back-outs this row sits over.
/// It is GREEN under the narrower one — forwarding the view's halves unchanged — because
/// its own pattern labels are the synthetic `_1` / `_2`, which gate by-label off either
/// way. The row that drives the normalization is
/// `a_positional_tuple_meeting_a_name_keyed_pattern_reads_by_slot` below; both are kept,
/// because this one is the shape a user writes and that one is the shape that decides.
#[test]
fn a_positional_tuple_destructures_on_a_rule_body_carrier() {
    let mut kb = load(
        "zzqqpq2.matchpos",
        "  rule value(?r) :- ?r <=> positional_match((1, 2))\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.matchpos.value"), 3);
}

/// CONTROL — the operation-body twin of the two named-tuple rows. The literal is
/// evaluated by the interpreter before the call, so the callee sees a `Value::Tuple` and
/// never reaches the non-native arm. GREEN EITHER WAY BY DESIGN.
#[test]
fn the_operation_body_twins_are_unmoved() {
    let mut kb = load(
        "zzqqpq2.viaop",
        "  operation v() -> Int64 = named_match((a: 1, b: 2))\n  \
           rule value(?r) :- ?r <=> v()\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.viaop.value"), 3);
}

/// CONTROL — the operation-body twin of the POSITIONAL row, for the same reason.
/// GREEN EITHER WAY BY DESIGN.
#[test]
fn the_positional_operation_body_twin_is_unmoved() {
    let mut kb = load(
        "zzqqpq2.viapos",
        "  operation v() -> Int64 = positional_match((1, 2))\n  \
           rule value(?r) :- ?r <=> v()\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.viapos.value"), 3);
}

/// **THE ROW THAT DRIVES THE `_N` NORMALIZATION**, and it took a second back-out to
/// find — the row above is green without it.
///
/// A POSITIONAL literal reaching a NAME-KEYED declared parameter, destructured by a
/// `match` arm whose labels therefore come from that declared type and are REAL names.
/// The repair's two candidate readings part company exactly here:
///
/// ```text
///   forward the view's halves     named = [(_1, 1), (_2, 2)]   is_name_keyed() = TRUE
///     -> by-label arm ON (the labels `a`,`b` are not synthetic)
///     -> no component is called `a`, and `positional_label_index("a")` is None
///     -> NO MATCH -> MatchFailed -> the rule FLOUNDERS
///   normalize `_N` back to `pos`  pos = [1, 2]                 is_name_keyed() = FALSE
///     -> source-order zip, which is what the NATIVE carrier does for the same program
/// ```
///
/// So the normalization is not tidiness: `is_name_keyed` is a QUESTION the accessor
/// answers, the two carriers answered it differently, and the reader it gates picks a
/// different arm on the answer. MEASURED both ways — 3 with the normalization, one
/// FLOUNDERED solution without it.
#[test]
fn a_positional_tuple_meeting_a_name_keyed_pattern_reads_by_slot() {
    let mut kb = load(
        "zzqqpq2.poscross",
        "  rule value(?r) :- ?r <=> named_match((1, 2))\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.poscross.value"), 3);
}

/// **A PERMUTED NAMED TUPLE BINDS BY NAME THROUGH A `match` / `let` PATTERN** — the row
/// that says the carrier repair did not cost the by-label correspondence.
///
/// `a - b` over `(b: 2, a: 1)` is `-1` read BY NAME and `1` read BY SLOT, so the witness
/// is order-sensitive; a `+` fixture would have summed to 3 either way and measured
/// nothing. The pattern's labels come from the operation's DECLARED parameter type, which
/// a rule-body carrier does not change — and the operation-body twin is the control that
/// says so.
///
/// FAILS ON BACK-OUT A (no answer at all). It cannot distinguish back-out B: both
/// readings leave this value name-keyed.
#[test]
fn a_permuted_named_tuple_binds_by_name_not_by_slot() {
    let mut kb = load(
        "zzqqpq2.permuted",
        "  rule value(?r) :- ?r <=> named_sub((b: 2, a: 1))\n",
    );
    assert_eq!(only_int(&mut kb, "zzqqpq2.permuted.value"), -1);
    let mut ctl = load(
        "zzqqpq2.permutedop",
        "  operation v() -> Int64 = named_sub((b: 2, a: 1))\n  \
           rule value(?r) :- ?r <=> v()\n",
    );
    assert_eq!(only_int(&mut ctl, "zzqqpq2.permutedop.value"), -1);
}

/// **THE SECOND READER — `spread_eta_args`, THE OPERATION SPELLING OF A DESTRUCTURE.**
/// `tuple_components` has two consumers and this is the one `match_tuple_pattern` is not.
///
/// GETTING IT DRIVEN TOOK ROUTING AROUND WI-20260904-833DK. The obvious fixture —
/// `apply2(sub2op, (a: 1, b: 2))` written in a rule body — never reaches this reader: an
/// operation name in a rule-body function slot is not callable and dies first. So the
/// `OpRef` is minted in an OPERATION body (`spread_outer`, where `reduce_var` eta-expands
/// it) while the TUPLE is the bridged rule-body operand threaded through as a parameter.
/// One value on each side of the carrier boundary, which is what this reader needs.
///
/// BOTH ORDERINGS, because `a - b` is order-sensitive and `a + b` would have summed to
/// the same answer under either correspondence. The permuted row answers by NAME (-1, not
/// 1): `spread_labels` carries `A`'s components in declared order (WI-1087) and the
/// spread resolves through them — which was exactly the channel a rule-body LAMBDA did
/// not get until WI-20260904-50B2K part (b) reached it with the callee's declared
/// parameter type (see the note where that gap's row stood, below).
///
/// FAILS ON BACK-OUT A — both orderings, one FLOUNDERED solution each. Green under
/// back-out B: the value is name-keyed, so the `_N` question does not arise.
#[test]
fn an_op_ref_spreads_a_bridged_tuple_and_keeps_its_labels() {
    for (ns, written) in [
        ("zzqqpq2.spread", "(a: 1, b: 2)"),
        ("zzqqpq2.spreadperm", "(b: 2, a: 1)"),
    ] {
        let mut kb = load(
            ns,
            &format!("  rule value(?r) :- ?r <=> spread_outer({written})\n"),
        );
        assert_eq!(
            only_int(&mut kb, &format!("{ns}.value")),
            -1,
            "{written}: the spread must resolve `a` and `b` BY LABEL, not by written slot",
        );
    }
}

// THE GAP THAT STOOD HERE IS CLOSED, and the row is gone rather than flipped. Written as
// a plain comment, not a doc one, so it attaches to nothing: a `///` block with no item
// under it is read as the NEXT item's documentation.
//
// `known_gap_a_rule_body_lambdas_binders_zip_by_slot` asserted that a rule-body lambda's
// binder list destructured a permuted named tuple BY SLOT — `apply2(lambda (a: Int64,
// b: Int64) -> a - b, (b: 2, a: 1))` answered 1, where every other spelling of the same
// program answered -1. Its cause was on the PATTERN side: a tuple pattern takes its
// labels from the EXPECTED type (`bind_and_label_pattern`, WI-803) and a lambda written
// in a rule-body DATA slot received no expectation at all.
//
// CLOSED BY WI-20260904-50B2K PART (b) — `data_slot_arg_hints`, which carries the
// callee's declared parameter type one level down into the children of a `DataTerm`. The
// row now lives with the change that closed it, as `wi_50b2k_binder_inference_test::
// part_b_a_permuted_named_tuple_binds_a_rule_body_lambdas_binders_by_name`, which asserts
// -1 and fails on that change's own back-out.

/// **A KNOWN GAP, PINNED RATHER THAN LEFT TO BE REDISCOVERED.** An operation NAME in a
/// rule-body function slot is not callable: it arrives as a `Value::Node(Ref(op))` and
/// the apply path, which knows `Value::Closure` and `Value::OpRef`, dies
/// `UnknownOperation { name: "<caller>.f" }` — the callee's own PARAMETER read as an
/// operation name.
///
/// FOUND BY THIS TICKET'S CENSUS AND EXCLUDED FROM IT ON MEASUREMENT, not on scope:
/// the failure is raised BEFORE any argument is destructured, `spread_eta_args` (the
/// other `tuple_components` reader) is never entered, and the row below is at ONE
/// parameter — no tuple exists anywhere in it. WI-784's rule that a lambda and an
/// operation are interchangeable as function values is what makes it a defect rather
/// than a missing feature; its repair is in the apply path's callee classification and
/// carries its own controls. WI-20260904-833DK owns it.
///
/// The row asserts the CURRENT behaviour: ZERO definite answers, one floundered
/// solution. When it starts answering 3, the gap is closed — delete this row and say
/// which change closed it.
#[test]
fn an_eta_d_operation_name_is_a_known_gap() {
    let src = "\
namespace zzqqpq2.etagap
  import anthill.prelude.{Int64, Function}
  operation inc1(n: Int64) -> Int64 = n + 1
  operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)
  rule value(?r) :- ?r <=> apply1(inc1, 2)
end
";
    let mut kb = crate::common::try_load_kb_with(src).expect("the KNOWN GAP still LOADS");
    let all = crate::common::query_unary(&mut kb, "zzqqpq2.etagap.value");
    assert_eq!(
        all.len(),
        1,
        "expected the single residual solution, got {all:?}"
    );
    assert!(
        !all[0].1,
        "KNOWN GAP: an operation name in a rule-body function slot answers a RESIDUAL. \
         If it is now DEFINITE the gap is closed: delete this row and say which change \
         closed it. Got {all:?}",
    );
}

/// **A USER-WRITTEN `_1` LABEL IS NOT A SYNTHETIC ONE, AND THE TWO CARRIERS MUST STILL
/// AGREE.** Found by `/code-review` (high) on this ticket's shipped code, and DRIVEN —
/// against a comment at the site that called the shape undrivable.
///
/// `tuple_components_from_view` puts the synthetic `_N` components back in `pos` so the
/// occurrence carrier answers `is_name_keyed` the way the native one does. It asked
/// WI-790's owner about the FILTERED subsequence of `_N` labels, which RENUMBERS them: a
/// `_1` written at slot 1 becomes index 0 of that subsequence, passes the owner's test,
/// and is promoted — so `iter()` yields it FIRST and the components are silently
/// REORDERED. The owner's whole contract is that `_N` is synthetic only at ITS OWN index
/// (CLAUDE.md: `_0`, `_01`, a `_2` written first are USER labels).
///
/// `a - b` over `(x: 1, _1: 2)` is the order-sensitive witness: `-1` in source order and
/// `1` reordered. FAILS ON THE BACK-OUT (the run restored to a filtered subsequence) with
/// the RULE side answering 1 while the OPERATION side answers -1 — one program, two
/// answers, which is the disagreement this whole function exists to remove.
///
/// THE CONTROL IS THE SAME PROGRAM WITH THE LABEL RENAMED to `y`: both sides answer -1
/// under the back-out too, so the `_N` spelling is the cause and not the fixture.
///
/// THE ROUTE MATTERS: the lambda sits in an ENTITY FIELD, the one slot shape
/// WI-20260904-50B2K part (b) deliberately does not hint, so the binder list gets no
/// expected type, `labels` is empty and `match_tuple_pattern` takes its SOURCE-ORDER arm
/// — which is the arm this promotion feeds. If that gap is ever closed
/// (`wi_50b2k_binder_inference_test::known_gap_an_entity_field_lambda_is_unhinted_in_both_bodies`),
/// this row needs another way to reach the source-order arm.
#[test]
fn a_user_written_underscore_label_is_not_promoted_and_both_carriers_agree() {
    for (tag, label) in [("u1", "_1"), ("ctl", "y")] {
        let ns = format!("zzqqpq2.{tag}");
        let src = format!(
            "\
namespace {ns}
  import anthill.prelude.{{Int64, Function}}
  sort Holder
    entity holder(f: Function[A = (x: Int64, {label}: Int64), B = Int64])
  end
  operation runit(h: Holder, p: (x: Int64, {label}: Int64)) -> Int64 =
    match h
      case holder(f) -> f(p)
  operation w() -> Int64 =
    runit(holder(f: lambda (u: Int64, v: Int64) -> u - v), (x: 1, {label}: 2))
  rule rule_side(?r) :- ?r <=> runit(holder(f: lambda (u: Int64, v: Int64) -> u - v), \
(x: 1, {label}: 2))
  rule op_side(?r)   :- ?r <=> w()
end
"
        );
        let mut kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("{ns}: must load; got {errs:?}"));
        let rule_side = only_int(&mut kb, &format!("{ns}.rule_side"));
        let op_side = only_int(&mut kb, &format!("{ns}.op_side"));
        assert_eq!(
            (rule_side, op_side),
            (-1, -1),
            "{ns}: a `{label}` component must keep its written position on BOTH carriers",
        );
    }
}

/// **AN ALL-SYNTHETIC NAMED LIST, INCLUDING OUT OF ORDER** — the gap /code-review found in
/// the control beside it.
///
/// `a_user_written_underscore_label_is_not_promoted_and_both_carriers_agree` covers a
/// MIXED list (`(x: 1, _1: 2)`), where the leading-run rule declines. The reviewer noted
/// that an ENTIRELY `_N`-spelled list is the other side: the occurrence carrier promotes
/// it into `pos` (so `is_name_keyed()` answers false) while a native `Value::Tuple` keeps
/// it in `named` (answering true) — and `match_tuple_pattern` gates its by-label arm on
/// exactly that predicate, so the two carriers could destructure differently.
///
/// DRIVEN AND NOT REPRODUCED, which is why this is a control rather than a fix. All three
/// shapes answer -1 on both carriers, the out-of-order declared `(_2, _1)` included: the
/// declared labels are not `labels_are_positional`, so both carriers take the POSITIONAL
/// path and agree. Stated as measured rather than as proof — this drives the ANSWER, not
/// `is_name_keyed` itself, so a divergence reachable another way is not excluded.
#[test]
fn an_all_synthetic_named_tuple_destructures_alike_on_both_carriers() {
    for (tag, decl, arg) in [
        ("out of order", "(_2: Int64, _1: Int64)", "(_1: 1, _2: 2)"),
        ("in order", "(_1: Int64, _2: Int64)", "(_1: 1, _2: 2)"),
        (
            "user-labelled control",
            "(a: Int64, b: Int64)",
            "(a: 1, b: 2)",
        ),
    ] {
        let src = format!(
            "namespace zzqqpq2.allsyn\n  import anthill.prelude.{{Int64}}\n  \
             operation sub2(p: {decl}) -> Int64 =\n    match p\n      case (x, y) -> x - y\n  \
             operation viaop() -> Int64 = sub2({arg})\n  \
             rule value(?r) :- ?r <=> sub2({arg})\n  \
             rule opval(?r) :- ?r <=> viaop()\nend\n"
        );
        let mut kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("{tag} must load; got:\n{}", errs.join("\n")));
        let bridged = crate::common::definite_unary(&mut kb, "zzqqpq2.allsyn.value");
        let native = crate::common::definite_unary(&mut kb, "zzqqpq2.allsyn.opval");
        assert_eq!(
            format!("{bridged:?}"),
            format!("{native:?}"),
            "{tag}: one program, two carriers, two answers",
        );
    }
}

/// **A SYNTHETIC `_N` PREFIX BESIDE A USER LABEL — the third shape, and it cannot
/// diverge.** `/code-review` (high) raised it against the `context` slice: a user writing
/// `_1:` AT INDEX 0 spells the synthetic name for that slot (CLAUDE.md: `_N` at its own
/// index IS the synthetic one), so the occurrence carrier promotes it into `pos` while a
/// native `Value::Tuple` might keep it in `named` — the `is_name_keyed` disagreement the
/// sibling rows exist to catch.
///
/// DRIVEN, NOT REPRODUCED, and here the reason is STRUCTURAL rather than a measured
/// coincidence. With a user label still in the list, all three things a consumer can ask
/// agree after the promotion:
///  * `iter()` — the run is a PREFIX, so moving it from `named` to `pos` leaves the
///    `pos ++ named` sequence byte-for-byte where it was;
///  * `is_name_keyed()` — it is `!named.is_empty()`, and the user label is still there,
///    so BOTH carriers answer true and both take the by-label arm;
///  * `by_label("_1")` — the native carrier finds it by name in `named` (step 1), the
///    promoted one by `positional_label_index` in `pos` (step 2), and the two steps
///    return the SAME `iter()`-order index.
/// The one shape where `named` does empty out — an ALL-synthetic list — is the row above.
///
/// THE FIXTURE PUTS THE DECLARED ORDER AND THE WRITTEN ORDER IN CONFLICT (`(b, _1)`
/// declared, `(_1: 1, b: 2)` written), which is what makes the two arms answer
/// differently at all: by-label gives `b - _1 = 1`, source order would give `1 - 2 = -1`.
/// A fixture whose two orders agreed could not tell the arms apart.
///
/// IT PASSES ON THE BACK-OUT (promotion disabled entirely) AND THAT IS THE POINT — it is a
/// negative control for a hypothesis, not a driver. What DOES fail when the promotion
/// changes: `a_user_written_underscore_label_is_not_promoted_and_both_carriers_agree`
/// (the prefix rule) and `an_op_ref_spreads_a_bridged_tuple_and_keeps_its_labels`.
#[test]
fn a_synthetic_prefix_beside_a_user_label_agrees_on_both_carriers() {
    for (tag, decl, arg) in [
        ("synthetic prefix", "(b: Int64, _1: Int64)", "(_1: 1, b: 2)"),
        (
            "user-labelled control",
            "(b: Int64, c: Int64)",
            "(c: 1, b: 2)",
        ),
    ] {
        let src = format!(
            "namespace zzqqpq2.mixsyn\n  import anthill.prelude.{{Int64}}\n  \
             operation sub2(p: {decl}) -> Int64 =\n    match p\n      case (x, y) -> x - y\n  \
             operation viaop() -> Int64 = sub2({arg})\n  \
             rule value(?r) :- ?r <=> sub2({arg})\n  \
             rule opval(?r) :- ?r <=> viaop()\nend\n"
        );
        let mut kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("{tag} must load; got:\n{}", errs.join("\n")));
        let bridged = crate::common::definite_unary(&mut kb, "zzqqpq2.mixsyn.value");
        let native = crate::common::definite_unary(&mut kb, "zzqqpq2.mixsyn.opval");
        assert_eq!(
            format!("{bridged:?}"),
            format!("{native:?}"),
            "{tag}: one program, two carriers, two answers",
        );
        // The VALUE too, not only the agreement: two carriers that both stopped
        // computing would agree on nothing happening. `b - _1` is the by-label read,
        // which is the arm both must take.
        assert_eq!(
            format!("{bridged:?}"),
            "[Int(1)]",
            "{tag}: expected the by-label read `b - first = 1`",
        );
    }
}
