//! WI-20260909-QMFC5 — proposal 060 §3's SECOND ANCHOR: a TYPED HEAD BINDING grounds a
//! clause's `require[Spec]`, where before only a covered body call (the witness) could.
//!
//! Design and every measurement: `docs/design/060-implementation.md` §8.1–§8.9.
//!
//! ## The fixture is the point, and it was built deliberately
//!
//! `Desc.tag()` is NULLARY. It has no argument to value-dispatch on, so the carrier's `7`
//! is reachable ONLY through a dictionary — [`the_control_a_nullary_call_folds_the_spec_
//! default`] measures that it answers `1` with no `require` at all. And because
//! `op_has_spec_carrier_param` is false for it, it can never be a WITNESS, so no witness
//! scan can ground the requirement either.
//!
//! That combination is what makes every `7` below evidence. The obvious fixture — a
//! bodied `Desc.describe(?x, ?r)` — is SIMULTANEOUSLY the witness and the covered call
//! (measured: it answers `7` on the witness path alone, and
//! [`a_typed_head_beside_a_witness_call_is_unchanged`] pins that), so a test built on it
//! would pass entirely without the anchor and never exercise a line of it.
//!
//! `Other` supplies `9` against `Leaf`'s `7`, and [`the_other_carrier_anchors_to_its_own_
//! supplier`] drives it: neither number can be produced by accident.
//!
//! ## What fails when each half is backed out — MEASURED, not predicted
//!
//! Every count below is written from a run, after restoring the tree between each. An
//! earlier version of this header said "8 of 11" while the file held 14 tests and 11
//! failed — a count written from a prediction and never re-run. `/code-review` caught it.
//!
//!  * **The anchor scan** (`anchor_grounding` returning `None` unconditionally — the
//!    pre-ticket code). **19 rows**, 18 here and
//!    [`wi_51w18…::a_head_introduced_type_variable_resolves_inside_the_bracket`], which
//!    lives in S1's file and fails under S2's back-out because S2 is what lifted its
//!    second half.
//!  * **The check tier emitting its goal** (returning `goal: None` again, as an earlier
//!    draft of this ticket did). **4 rows**:
//!    [`the_check_tier_emits_the_same_goal_the_bind_tier_does`],
//!    [`a_refining_carrier_answers_the_same_in_both_tiers`],
//!    [`a_conditional_provision_is_decided_at_run_time_not_at_load`] and
//!    [`equation_headed_anchor_keeps_its_body`] — the last of which PANICS rather than
//!    failing, which is what that arm cost.
//!  * **The `>1` refusal's collapse** (restoring the data-sort collapse that was built
//!    and then removed). **2 rows**:
//!    [`two_head_variables_of_one_data_sort_are_still_two_dictionaries`] and
//!    [`a_parameterized_data_sort_at_two_instantiations_is_refused`].
//!  * **The second gate** (presence test only, no agreement check). **1**:
//!    [`a_spec_that_receives_on_a_non_carrier_parameter_is_refused`].
//!  * **The written-binding disagreement refusal**. **1**:
//!    [`a_written_binding_that_disagrees_with_the_bound_is_refused`].
//!  * **`carrier_provides_spec` at both ends** (back to a bare `sort_provides`). **1**:
//!    [`a_witness_supplied_provision_anchors_too`]. Backing out only ONE end was measured
//!    to move the failure rather than remove it — a loud refusal becomes a silent
//!    no-answer — which is why the two are written as a pair.
//!
//! [`the_untyped_twin_stays_refused`] and [`a_typed_head_beside_a_witness_call_is_
//! unchanged`] pass under ALL of them BY DESIGN — the first has no bound to anchor with,
//! the second is grounded by its witness before the anchor is ever reached. They are the
//! yardsticks the rows above are read against.
//!
//! ## Two boundaries, stated rather than discovered
//!
//!  * A SELF-REPRESENTING spec whose provider pins a sibling CONCRETELY still delays —
//!    [`a_self_representing_spec_whose_provider_pins_a_sibling_concretely_delays`]. The
//!    written bracket would decide it and S1 retains it, but slot 0 does not reach
//!    `fetch_dictionary`, so closing it is a resolver signature change.
//!  * TWO anchors are refused rather than threaded. WI-20260909-96ZTM owns the lift, and
//!    the two rows above say what the interim refusal costs.

use anthill_core::eval::Value;
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;

/// A spec with TWO operations that differ in what they can do:
///   * `describe(x: T)` — a carrier parameter, so it can be a witness AND value-dispatch;
///   * `tag()` — nullary, so it can be NEITHER. It is the one the anchored rows call.
/// Two providers, `7` and `9`, so no answer below can be produced by accident.
fn program(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation describe(x: Other) -> Int64 = 9
    operation tag() -> Int64 = 9
  end

  sort Plain
    entity plain
  end

  fact seed(leaf())
  fact seedo(other())
  fact seedp(plain())
{tail}end
"#
    )
}

/// `Sub` REFINES `Leaf` (the `requires` chain) and provides nothing. `sort_refines` is
/// an edge `bare_sort_compatible` walks and `sort_provides` does not, which is what made
/// the deleted load-time verdict discharge a requirement no carrier met.
fn refining(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5r
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  sort Sub
    requires Leaf
    entity sub
  end

  fact seed(sub())
{tail}end
"#
    )
}

/// A CONDITIONAL provision — `Wrap provides Sh[T = Wrap] :- Sh[A]` — whose guard depends
/// on a type argument no BOUND records. `Bad` provides nothing, so `wrap(bad())` does not
/// satisfy `Sh` however the bound reads.
fn conditional(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5c
  import anthill.prelude.Int64

  sort Sh
    sort T = ?
    operation tag() -> Int64 = 1
  end

  sort Good
    import anthill.prelude.Int64
    entity good
    provides Sh[T = Good]
    operation tag() -> Int64 = 3
  end

  sort Bad
    entity bad
  end

  sort Wrap
    import anthill.prelude.Int64
    sort A = ?
    entity wrap(v: A)
    provides Sh[T = Wrap] :- Sh[A]
    operation tag() -> Int64 = 7
  end

  fact seedg(wrap(v: good()))
  fact seedb(wrap(v: bad()))
{tail}end
"#
    )
}

/// `Leaf` declares NO provision of its own; `Rival` declares one FOR it. That is
/// WI-1043's second supply channel, which `carrier_provides_spec` owns and a bare
/// `sort_provides` cannot see. `9` is reachable only through the dictionary.
fn rival_answer(tail: &str) -> i64 {
    let src = format!(
        r#"namespace test.qmfc5v
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    entity leaf
  end

  sort Rival
    import anthill.prelude.Int64
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
    operation tag() -> Int64 = 9
  end

  fact seed(leaf())
{tail}end
"#
    );
    let mut kb = crate::common::load_kb_with(&src);
    match crate::common::query_unary(&mut kb, "test.qmfc5v.answer").as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`answer` must yield one DEFINITE Int, got {other:?}\n{src}"),
    }
}

/// A PARAMETERIZED data sort with a conditional provision — the shape the removed
/// collapse could not see, and the one that ships (`pair`, `list`, `option`).
fn boxed(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5b
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation describe(x: Other) -> Int64 = 9
    operation tag() -> Int64 = 9
  end

  sort Box
    import anthill.prelude.Int64
    sort E = ?
    entity box(v: E)
    provides Desc[T = Box] :- Desc[E]
    operation tag() -> Int64 = 5
  end

  fact seedbl(box(v: leaf()))
  fact seedbo(box(v: other()))
{tail}end
"#
    )
}

/// A spec that RECEIVES on a parameter its providers do not bind to themselves:
/// `touch(x: P)` makes `spec_carrier_param` answer `P`, while every provision carries the
/// carrier in `C`. [`spec_carrier_param_or_sole`]'s own doc warns a new consumer about
/// exactly this shape.
fn mismatched(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5m
  import anthill.prelude.Int64

  sort Sp
    import anthill.prelude.Int64
    sort C = ?
    sort P = ?
    operation touch(x: P) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Sp[C = Leaf, P = Int64]
    operation touch(x: Int64) -> Int64 = 5
    operation tag() -> Int64 = 7
  end

  fact seed(leaf())
{tail}end
"#
    )
}

/// The single definite Int `test.qmfc5.answer` yields. Panics on anything else including
/// `[]` — "returned nothing" must never read as a pass — and on an INDEFINITE solution,
/// which is how a requirement that delayed would otherwise slip through as success.
fn answer(src: &str) -> i64 {
    let mut kb = crate::common::load_kb_with(src);
    match crate::common::query_unary(&mut kb, "test.qmfc5.answer").as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`answer` must yield one DEFINITE Int, got {other:?}\n{src}"),
    }
}

fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a refusal; the program loaded clean:\n{src}"))
        .join("\n")
}

/// Does the clause defining `qn` still carry a `find_dictionary` goal? The check tier's
/// whole claim is that it does NOT — the requirement was decided at load.
fn has_find_dictionary_goal(kb: &KnowledgeBase, qn: &str) -> bool {
    let Some(head_sym) = kb.try_resolve_symbol(qn) else {
        panic!("`{qn}` does not resolve — the clause under test is not there at all");
    };
    for rid in kb.live_rule_ids() {
        let Value::Term { id: head, .. } = *kb.rule_head_value(rid) else {
            continue;
        };
        if !matches!(kb.get_term(head), Term::Fn { functor, .. } if *functor == head_sym) {
            continue;
        }
        if kb.rule_body_nodes(rid).iter().any(|n| {
            matches!(n.as_expr(), Some(Expr::Apply { functor, .. })
                if kb.qualified_name_of(*functor).ends_with("find_dictionary"))
        }) {
            return true;
        }
    }
    false
}

// ── the anchor grounds, and the dictionary threads ───────────────────────────

#[test]
fn a_concrete_typed_head_grounds_the_requirement() {
    // THE TICKET'S DRIVING SURFACE. `?x: Leaf` is the only thing in the clause that says
    // which carrier the requirement is at — there is no call to a `Desc` operation that
    // could witness it, and `tag()` cannot value-dispatch. `7` is therefore reachable
    // only through the dictionary the ANNOTATION grounded.
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored(?x: Leaf, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), Desc.tag(?r)\n"
        )),
        7,
    );
}

#[test]
fn an_introducer_bound_grounds_it_too() {
    // THE OTHER BOUND SHAPE, and it is not a spelling variant: after WI-582's
    // substitution the recorded bound is the SPEC (`Desc`), not a carrier, so the anchor
    // test is `bound == spec` where the row above needs `sort_provides`. Two
    // non-overlapping tests over one channel — backing either out leaves the other row
    // passing, which is what says they are separate.
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored[A](?x: A, ?r) :- Desc[A], ?d = require[Desc[T = A]], seed(?x), Desc.tag(?r)\n"
        )),
        7,
    );
}

#[test]
fn the_other_carrier_anchors_to_its_own_supplier() {
    // THE CONTROL THAT MAKES `7` MEAN SOMETHING. The same clause shape at the other
    // carrier answers `9`. Without this row, a `7` could be the spec default read
    // through some other path, or a constant nothing selected.
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?y, ?r)\n  \
             rule anchored(?y: Other, ?r) :- ?d = require[Desc[T = Other]], seedo(?y), Desc.tag(?r)\n"
        )),
        9,
    );
}

#[test]
fn the_control_a_nullary_call_folds_the_spec_default() {
    // WHY THE FIXTURE IS BUILT THIS WAY, asserted rather than asserted-about. With no
    // `require` anywhere the nullary call folds the spec's own default. So every `7` and
    // `9` above is a dictionary doing work; none of them can be value-dispatch.
    assert_eq!(answer(&program("  rule answer(?r) :- Desc.tag(?r)\n")), 1);
}

// ── the yardsticks ───────────────────────────────────────────────────────────

#[test]
fn the_untyped_twin_stays_refused() {
    // WHAT SAYS THE ANNOTATION IS WHAT GROUNDS IT. The same clause with the bound removed
    // has nothing to anchor from, and keeps the WITNESS refusal word for word — the
    // anchor scan is skipped entirely for a clause with no bound, which is why this row
    // passes under every back-out BY DESIGN.
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored(?x, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("no such call in the rule body"),
        "the untyped twin must keep the witness refusal; got:\n{errs}",
    );
}

#[test]
fn a_typed_head_beside_a_witness_call_is_unchanged() {
    // THE WITNESS PATH IS NOT DISPLACED. The anchor runs only after every witness scan
    // misses, so a clause with both is grounded by its witness exactly as before this
    // ticket. Passes either way BY DESIGN; it is here so that a future change which
    // REORDERS the two is caught rather than absorbed.
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored(?x: Leaf, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), Desc.describe(?x, ?r)\n"
        )),
        7,
    );
}

// ── the refusals the anchor owns ─────────────────────────────────────────────

#[test]
fn a_bound_that_does_not_provide_is_refused_by_its_own_message() {
    // BEFORE THIS TICKET THIS ROW WAS REFUSED BY THE WITNESS ERROR — the right verdict
    // for the wrong reason, which is why the umbrella ticket's own acceptance control
    // ("a typed head whose bound does NOT provide stays refused") did not discriminate:
    // it passed identically with and without any anchor at all. The message must name the
    // BOUND, because the repair is to fix the annotation, not to add a call.
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored(?x: Plain, ?r) :- ?d = require[Desc[T = Plain]], seedp(?x), Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("head bound(s) — Plain — provide no `Desc`"),
        "the refusal must name the bound and the spec; got:\n{errs}",
    );
    assert!(
        !errs.contains("no such call in the rule body"),
        "and must NOT be the witness error, which sends the author to fix the wrong \
         thing; got:\n{errs}",
    );
}

#[test]
fn two_anchors_for_one_spec_are_refused() {
    // TWO ANCHORS ARE TWO DICTIONARIES (§8.5), not a tie to break. Picking one would
    // silently thread `Leaf`'s dictionary into a call whose carrier is `Other`, or the
    // reverse — a clean load and a wrong answer. Refused loudly until the carrier-directed
    // weave exists; the message names its owner so the next reader is not left guessing.
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
         rule anchored(?x: Leaf, ?y: Other, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), seedo(?y), Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("2 of them do — Leaf, Other") && errs.contains("96ZTM"),
        "the refusal must name both anchors and its owner; got:\n{errs}",
    );
}

// ── the check tier ───────────────────────────────────────────────────────────

#[test]
fn the_check_tier_emits_the_same_goal_the_bind_tier_does() {
    // `requires(X)` IS the no-`out` case of one relation (WI-1040), so it gets ONE
    // producer and ONE consumer — the same goal the bind tier emits, minus `out:`.
    //
    // AN EARLIER DRAFT RESOLVED THIS TIER AT LOAD and left no goal, on the argument that
    // the anchor selection had already established the requirement. `/code-review`
    // falsified that three ways; the three rows below are those three, each a program
    // where the load-time verdict said SATISFIED and the bind twin left a residual.
    //
    // TWO ASSERTIONS, because either alone is satisfiable the wrong way: the clause LOADS
    // (a refusal would also leave a goal-free rule), and it answers the DEFAULT `1` —
    // `requires` checks and does not thread, so a `7` here would mean the check tier had
    // quietly become the bind tier.
    let src = program(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored(?x: Leaf, ?r) :- requires(Desc[T = Leaf]), seed(?x), Desc.tag(?r)\n",
    );
    assert_eq!(answer(&src), 1);
    let kb = crate::common::load_kb_with(&src);
    assert!(
        has_find_dictionary_goal(&kb, "test.qmfc5.anchored"),
        "the check tier must emit the goal, not decide the requirement at load",
    );
}

#[test]
fn a_refining_carrier_answers_the_same_in_both_tiers() {
    // HOLE 1 of 3 in the deleted load-time verdict. `sort_refines` — the `requires`
    // chain — admits a carrier through `bare_sort_compatible` that `sort_provides` never
    // walks, so a `Sub` that refines `Leaf` and provides NOTHING satisfied the bound.
    //
    // MEASURED BEFORE THE FIX: the check tier answered `1` with one solution while the
    // bind tier answered nothing — one relation, two opposite answers, which is exactly
    // what "`requires(X)` IS the no-`out` case" forbids. Both now answer nothing.
    //
    // BACKING OUT the goal emission (returning `goal: None` for the no-`out` case again)
    // fails this row on the CHECK line only; the BIND line passes either way, and that is
    // what makes the pair evidence rather than a coincidence.
    let src = |tier: &str| {
        refining(&format!(
            "  rule answer(?r) :- checked(?x, ?r)\n  \
             rule checked(?x: Leaf, ?r) :- {tier}, seed(?x), Desc.tag(?r)\n"
        ))
    };
    let run = |t: &str| {
        let mut kb = crate::common::load_kb_with(&src(t));
        crate::common::query_unary(&mut kb, "test.qmfc5r.answer").len()
    };
    assert_eq!(run("requires(Desc[T = Leaf])"), 0, "check tier");
    assert_eq!(run("?d = require[Desc[T = Leaf]]"), 0, "bind tier");
}

#[test]
fn a_conditional_provision_is_decided_at_run_time_not_at_load() {
    // HOLE 2 of 3. `Wrap provides Sh[T = Wrap] :- Sh[A]` is not decided by the BOUND:
    // `sort_provides` is type-argument-blind, so `Wrap[A = Bad]` — whose `A` provides
    // nothing — passed the load-time verdict and the clause ran with the requirement
    // unmet, answering the spec default. The bind twin correctly left a residual.
    //
    // The row asserts the CHECK tier now leaves a runtime goal for the question, which is
    // the only thing that can decide it: `A` is not known until a carrier arrives.
    let src = conditional(
        "  rule answer(?r) :- checked(?x, ?r)\n  \
         rule checked(?x: Wrap, ?r) :- requires(Sh[T = Wrap]), seedb(?x), Sh.tag(?r)\n",
    );
    let kb = crate::common::load_kb_with(&src);
    assert!(
        has_find_dictionary_goal(&kb, "test.qmfc5c.checked"),
        "a conditional provision cannot be discharged at load — the goal must survive",
    );
}

#[test]
fn a_witness_supplied_provision_anchors_too() {
    // HOLE 3 of 3, and this one was a REFUSAL rather than a wrong answer: anchor
    // selection asked bare `sort_provides`, which is blind to a provision another sort
    // declares FOR the carrier (`sort Rival provides Desc[T = Leaf]`, WI-1043).
    // `carrier_provides_spec` is the documented two-channel owner and both ends now ask
    // it — the load site AND `anchor_guard`. Widening only one end was measured to turn
    // the loud refusal into a silent no-answer, which is why they move together.
    //
    // ASSERTED BY VALUE: `9` is `Rival`'s, and it is reachable only through the
    // dictionary — `tag()` is nullary, so nothing else can produce it.
    assert_eq!(
        rival_answer(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored(?x: Leaf, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), Desc.tag(?r)\n"
        ),
        9,
    );
}

#[test]
fn equation_headed_anchor_keeps_its_body() {
    // AND THE DELETED ARM COULD EMPTY A RULE BODY. A `[simp]` equation whose ONLY body
    // atom is the `requires` goal had that atom dropped, so `set_rule_body_nodes` was
    // handed `[]` and its fact-ness assert fired — `assertion left == right failed:
    // set_rule_body_nodes must not flip a rule's fact-ness`. With `debug_assertions` off
    // the assert vanishes and the rule silently becomes an UNCONDITIONAL law.
    //
    // NO ANCHORED EQUATION-HEADED ROW EXISTED, which is why the whole suite shipped green
    // over it: every fixture in this file is relational, and a relational typed head gets
    // a prepended `domain(?x, Leaf)` goal that keeps the body non-empty. This is that row.
    let src = refining(
        "  rule answer(?r) :- f(sub(), ?r)\n  \
         operation f(x: Sub) -> Int64\n  \
         rule fe: f(?x: Leaf) <=> 1 :- requires(Desc[T = Leaf]) [simp]\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    // The point is that loading and querying do not PANIC; the answer is incidental.
    let _ = crate::common::query_unary(&mut kb, "test.qmfc5r.answer");
}

#[test]
fn the_check_tier_still_refuses_a_bound_that_does_not_provide() {
    // Resolved at load means DECIDED at load, in both directions. The failing side is the
    // same located refusal the bind tier gets — one relation, one answer.
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored(?x: Plain, ?r) :- requires(Desc[T = Plain]), seedp(?x), Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("head bound(s) — Plain — provide no `Desc`"),
        "got:\n{errs}"
    );
}

// ── a boundary, measured and pinned rather than left to be discovered ────────

#[test]
fn a_self_representing_spec_whose_provider_pins_a_sibling_concretely_delays() {
    // NOT DELIVERED, AND NOT SILENT. `Cap` is SELF-REPRESENTING (`touch(c: Cap, …)`), so
    // the anchor takes the carrier-by-sort branch and pins no parameter; the sibling `P`
    // then rides as WI-20260830-X9PB4's wildcard, and a wildcard is REFUSED against a
    // provider's CONCRETE binding (`Box provides Cap[P = Int64]`). No provider answers,
    // so the fetch reports `Undecided` and the call delays.
    //
    // THE FIX IS ALREADY HALF-BUILT AND NAMED: the author WROTE `Cap[P = Int64]`, and
    // WI-20260909-51W18 retains that bracket on the goal's slot 0. Reading it is the
    // retained bracket's real first consumer — but slot 0 never reaches `fetch_dictionary`
    // (it takes `spec_sort`, `op_functor`, `arg_vals`), so closing this is a resolver
    // signature change, which is why it is recorded here instead of grown into this
    // ticket.
    //
    // ASSERTED AS THE DELAY IT IS, so closing it has to come here and change this row.
    let src = r#"namespace test.qmfc5.xz
  import anthill.prelude.Int64
  sort Cap
    sort P = ?
    operation touch(c: Cap, x: P) -> Int64 = 1
    operation tag() -> Int64 = 1
  end
  sort Box
    import anthill.prelude.Int64
    entity box
    provides Cap[P = Int64]
    operation touch(c: Box, x: Int64) -> Int64 = 7
    operation tag() -> Int64 = 7
  end
  fact seed(box())
  rule answer(?r) :- anchored(?x, ?r)
  rule anchored(?x: Box, ?r) :- ?d = require[Cap[P = Int64]], seed(?x), Cap.tag(?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let got = crate::common::query_unary(&mut kb, "test.qmfc5.xz.answer");
    assert_eq!(got.len(), 1, "one solution, got {got:?}");
    assert!(
        !got[0].1,
        "it must be INDEFINITE — the requirement delayed. A definite answer here means \
         the boundary closed and this row is what has to change: {got:?}",
    );
}

// ── what `/code-review` found, driven and pinned ─────────────────────────────

#[test]
fn two_head_variables_of_one_data_sort_are_still_two_dictionaries() {
    // A COLLAPSE WAS BUILT HERE AND THEN REMOVED. `rule p(?x: Leaf, ?y: Leaf)` is a
    // natural spelling, and an earlier fix in this ticket admitted it by collapsing two
    // anchors of one DATA sort into one dictionary — nothing can widen to a
    // constructor-declaring sort, so both carriers ARE that sort at run time. The first
    // clause is true; "and therefore select the same row" does not follow, and
    // `/code-review` drove three counterexamples:
    //
    //   * a PARAMETERIZED data sort (`?x: Box[E = Leaf], ?y: Box[E = Other]`) collapses on
    //     the head symbol alone and the conditional provision's sub-dictionary differs —
    //     and that shape SHIPS, in `pair`, `list` and `option`;
    //   * two BARE, byte-identical `Wrap` bounds still diverge under a conditional
    //     provision — `7` one way and a residual the other, decided by which head
    //     variable was written first, so comparing the full bound TERMS does not rescue
    //     it either;
    //   * the gate itself read `kind_of` and so was source-order dependent.
    //
    // SO THE REFUSAL STANDS AND THIS SPELLING IS REFUSED WITH IT. That is a real cost,
    // taken deliberately: a refusal is loud and names its owner, where the collapse
    // silently threaded one carrier's dictionary into the other's call. WI-20260909-96ZTM
    // owns the honest repair — one goal per anchor plus a carrier-directed weave.
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
         rule anchored(?x: Leaf, ?y: Leaf, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), seed(?y), Desc.tag(?r)\n"
    ));
    assert!(errs.contains("96ZTM"), "got:\n{errs}");
}

#[test]
fn a_parameterized_data_sort_at_two_instantiations_is_refused() {
    // THE COUNTEREXAMPLE THE COLLAPSE COULD NOT SEE, kept as its own row because it is
    // the one that ships: `sort_functor_of_view` answers `Box` for both bounds and
    // discards the arguments, so a collapse keyed on the head symbol merged two carriers
    // whose conditional sub-dictionaries differ. `pair`, `list` and `option` are all this
    // shape. Refused now, and the refusal names the owner.
    let errs = refusal(&boxed(
        "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
         rule anchored(?x: Box[E = Leaf], ?y: Box[E = Other], ?r) :- ?d = require[Desc[T = Box]], seedbl(?x), seedbo(?y), Desc.tag(?r)\n"
    ));
    assert!(errs.contains("96ZTM"), "got:\n{errs}");
}

#[test]
fn a_spec_that_receives_on_a_non_carrier_parameter_is_refused() {
    // THE SECOND GATE [`spec_carrier_param_or_sole`]'s OWN DOC DEMANDS, and it was
    // missing: this site performed only a PRESENCE test and never compared the answer
    // against anything. I had recorded "no independent second gate" as a stated boundary,
    // on the argument that the shape the doc warns about takes the self-representing
    // branch. `/code-review` falsified that by driving it.
    //
    // `Sp` receives on `P` (`touch(x: P)`) while `Leaf provides Sp[C = Leaf, P = Int64]`
    // carries the carrier in `C`. Before the gate the clause LOADED CLEAN and answered a
    // residual — the silent non-grounding VVM1R's acceptance forbids in as many words.
    //
    // BACKING OUT the gate makes this row fail by LOADING; nothing else in the file moves.
    let errs = refusal(&mismatched(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored(?x: Leaf, ?r) :- ?d = require[Sp[C = Leaf, P = Int64]], seed(?x), Sp.tag(?r)\n"
    ));
    assert!(
        errs.contains("receives on `P`") && errs.contains("binds `P` to `Int64`"),
        "the refusal must name the parameter and what the provision binds it to; got:\n{errs}"
    );
}

#[test]
fn a_written_binding_that_disagrees_with_the_bound_is_refused() {
    // THE RETENTION'S FIRST REAL READER ON THIS PATH. `require[Desc[T = Other]]` under
    // `?x: Leaf` loaded clean and answered `7` — `Leaf`'s dictionary — silently ignoring
    // the author's explicit `T = Other`. `060-implementation.md` §8.6 said "nothing
    // decides that today because nothing can"; S1's retention is what makes it possible.
    //
    // THE CONTROL IS THE AGREEING SPELLING, which every acceptance row in this file uses
    // and which must keep loading: `require[Desc[T = Leaf]]` under `?x: Leaf`.
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored(?x: Leaf, ?r) :- ?d = require[Desc[T = Other]], seed(?x), Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("it names `Other`") && errs.contains("anchors `Leaf`"),
        "got:\n{errs}"
    );
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored(?x: Leaf, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), Desc.tag(?r)\n"
        )),
        7,
        "the AGREEING spelling is the ordinary one and must still thread",
    );
}

#[test]
fn two_variables_bounded_by_the_spec_are_still_two_dictionaries() {
    // THE CONTROL FOR THE ROW ABOVE, and the reason the collapse is a filter and not a
    // `dedup`: `?x: A` and `?y: A` under `:- Desc[A]` may carry DIFFERENT providers at run
    // time, so picking one would thread the wrong carrier's row into the other's call.
    // Same bound symbol as each other, opposite verdict from the data-sort case.
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
         rule anchored[A](?x: A, ?y: A, ?r) :- Desc[A], ?d = require[Desc[T = A]], seed(?x), seedo(?y), Desc.tag(?r)\n",
    ));
    assert!(errs.contains("96ZTM"), "got:\n{errs}");
}

#[test]
fn a_spec_name_that_is_also_a_namespace_still_anchors() {
    // `is_anchor_form` asked `kind_of`, which reports only the FIRST-DECLARED category and
    // whose own doc says to use `has_kind` for "can this name serve as an X". With a
    // `namespace test.…Desc` declared first it answered `Namespace`, so the anchored goal
    // was routed down the WITNESS path with a sort in the op slot, found no signature, and
    // the clause SILENTLY answered nothing. Symbol categories are a SET — the same desync
    // WI-20260824-Q0093 found once already.
    //
    // Asserted BY VALUE: the failure mode was `[]`, which a `loads clean` test would have
    // called a pass.
    let src = r#"namespace test.qmfc5.ns.Desc
end
namespace test.qmfc5.ns
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation tag() -> Int64 = 1
  end
  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation tag() -> Int64 = 7
  end
  fact seed(leaf())
  rule answer(?r) :- anchored(?x, ?r)
  rule anchored(?x: Leaf, ?r) :- ?d = require[Desc[T = Leaf]], seed(?x), Desc.tag(?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    match crate::common::query_unary(&mut kb, "test.qmfc5.ns.answer").as_slice() {
        [(Value::Int(7), true)] => {}
        other => panic!("the anchor must survive a same-named namespace, got {other:?}"),
    }
}
