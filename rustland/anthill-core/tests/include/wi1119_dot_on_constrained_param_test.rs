//! WI-1119 — a dot on a `requires`-CONSTRAINED TYPE-PARAMETER receiver reaches the same
//! spec operation the named spelling does (kernel spec §8.7, "Where the ambiguity error is
//! raised" / "Operation override").
//!
//! WHAT WAS MEASURED, on the shared `common::DESC_INSTANCES` fixture: in one program
//! `Desc.describe(x)` loaded and evaluated while `x.describe()` was refused at load with
//! `<unresolved receiver>.describe: … no such member (dot dispatch)` — identically for all
//! THREE `requires` spellings (an op-param clause, an op-scoped sort-param clause, a
//! sort-level clause), while a CONCRETE receiver and an ABSTRACT-SPEC receiver both worked
//! in both spellings. The receiver's type is a parameter, so `sort_functor_of_view` answers
//! `None` and the entire member ladder — the receiver's own member, the WI-281 provided-spec
//! fallback, the WI-614 required-spec fallback — sat inside `if let Some(s) = recv_sort` and
//! was skipped wholesale. A MISSING RUNG, not a wrong answer from an existing one.
//!
//! TWO BACK-OUTS, BECAUSE THE CHANGE HAS TWO INDEPENDENT AXES, and the first draft of this
//! file got the split wrong: it credited the RUNG with the naming half's rows and they
//! passed with the rung removed. Every "fails on back-out" claim below names WHICH.
//!
//!  * THE RUNG — in `kb/typing.rs`'s `TypeBuildFrame::DotApply` arm, drop the third rung:
//!    restore `} else { None };` in place of the
//!    `else if let Some(param_ty) = constrained_param_receiver_type(…)` arm that calls
//!    `find_spec_op_for_constrained_param`. RUN: 8 of the 11 tests here fail, 3 pass.
//!
//!  * THE NAMING — at the same arm's `DotDispatchNoMatch` construction, replace the
//!    `receiver_param` computation with `None`. RUN: 2 fail, 9 pass — and they are a
//!    DISJOINT pair from the eight, which is what says the two axes are separable rather
//!    than one change measured twice.
//!
//! EVERY POSITIVE HERE IS DRIVEN TO A VALUE, and the values are `DESC_INSTANCES`' depth
//! coding — 1 for the base instance, 12 for the conditional one, combined positionally as
//! 100·a + b where two dictionaries must stay apart. "It loads clean" would pass on a rung
//! that resolved the member to the WRONG spec's operation; a number does not.
use anthill_core::eval::Value;

/// Spec `Desc` + base instance at `Leaf` (describe → 1) + CONDITIONAL instance at `Wrap[E]`
/// given `Desc[E]` (describe → 10·describe(inner) + 2). Shared with the WI-817 / WI-822 /
/// WI-823 / WI-855 files — one owner, see `common::DESC_INSTANCES`.
const INSTANCES: &str = crate::common::DESC_INSTANCES;

fn with_instances(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Function}}
  -- WI-20260825-KD9SW: a WRITTEN bare spec-op name is brought in by import.
  import anthill.prelude.Multiplicative.{{mul}}
  import anthill.prelude.Additive.{{add}}
{INSTANCES}
{body}
end
"#
    )
}

/// Load and call `entry(0)` on a FRESH interpreter. `interp_for` prints every load error and
/// panics on a dirty load, so the "loads clean" half of each pin needs no separate load
/// call; fresh per program because a trapped call poisons later calls on one interpreter.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn assert_int(src: &str, entry: &str, want: i64, why: &str) {
    let got = eval_fresh(src, entry);
    assert!(
        matches!(got, Ok(Value::Int(v)) if v == want),
        "{entry}: expected the depth-coded Ok(Int({want})) — {why}; got {got:?}"
    );
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but the source loaded clean"))
}

fn assert_err_contains(errs: &[String], needles: &[&str], why: &str) {
    assert!(
        errs.iter().any(|e| needles.iter().all(|n| e.contains(n))),
        "{why}: expected one error containing all of {needles:?}; got {errs:?}"
    );
}

// ── THE DIVERGENCE ITSELF: three spellings, two forms each ───────────────────

/// THE THREE `requires` SPELLINGS, EACH IN BOTH FORMS, EACH DRIVEN. This is the ticket's
/// whole claim: the dot and the named spelling accept the same programs and produce the
/// same values. The three spellings are the three the measurement covered — an OP-PARAM
/// clause over the operation's own bracket parameter, an OP-SCOPED clause over the sort's
/// parameter, and a SORT-LEVEL clause — and they matter separately because the constraining
/// spec reaches the dot through DIFFERENT chain sources: `env.op_requires()` for the first
/// two and the enclosing sort's dictionary chain for the third (measured at the miss:
/// `op_requires()` is EMPTY for the sort-level shape).
///
/// Driven on BOTH providers so the answer says which dictionary was reached — the base
/// describer (1) and the CONDITIONAL one (12), whose own `requires Desc[T = E]` must resolve
/// on top of the licence. A rung that resolved the member but reached the wrong dictionary
/// lands on a different number, not on an error.
///
/// Fails on the RUNG back-out: all six DOT rows, at load, with `DotDispatchNoMatch`. The six
/// NAMED rows pass either way BY DESIGN — they are the control that says the divergence was
/// the dot's and not a broken fixture, and they are what the ticket's measurement recorded
/// as already working.
#[test]
fn every_requires_spelling_agrees_between_the_dot_and_the_named_form() {
    for (spelling, holder) in [
        (
            "opparam",
            "  sort Holder\n    operation probe[PT](x: PT) -> Int64 requires Desc[PT] = {BODY}\n  end\n  \
             sort Driver\n    operation drive(n: Int64) -> Int64 = Holder.probe({ARG})\n  end",
        ),
        (
            "opscoped",
            "  sort Holder\n    sort HT = ?\n    operation probe(x: HT) -> Int64 requires Desc[HT] = {BODY}\n  end\n  \
             sort Driver\n    operation drive(n: Int64) -> Int64 = Holder.probe({ARG})\n  end",
        ),
        (
            "sortlevel",
            "  sort Holder\n    sort HT = ?\n    requires Desc[T = HT]\n    operation probe(x: HT) -> Int64 = {BODY}\n  end\n  \
             sort Driver\n    operation drive(n: Int64) -> Int64 = Holder.probe({ARG})\n  end",
        ),
    ] {
        for (form, body) in [("dot", "x.describe()"), ("named", "Desc.describe(x)")] {
            for (provider, arg, want) in
                [("base", "leaf()", 1), ("conditional", "wrap(leaf())", 12)]
            {
                let ns = format!("wi1119.{spelling}.{form}.{provider}");
                let src =
                    with_instances(&ns, &holder.replace("{BODY}", body).replace("{ARG}", arg));
                assert_int(
                    &src,
                    &format!("{ns}.Driver.drive"),
                    want,
                    &format!(
                        "({spelling} clause, {form} form, {provider} provider) the clause \
                         licenses the call and the dot must reach the same spec operation \
                         the named spelling reaches"
                    ),
                );
            }
        }
    }
}

/// THE TWO CONTROLS THAT ALREADY WORKED MUST KEEP WORKING — the guard that the new rung
/// widened nothing else. A CONCRETE receiver resolves through the receiver sort's own member
/// and an ABSTRACT-SPEC receiver through the WI-281/WI-614 fallbacks; both are gated on a
/// resolved `recv_sort`, and the new rung sits in the `else`, so neither can reach it.
///
/// Passes under BOTH back-outs, BY DESIGN, and said here rather than left for a reader to
/// discover: it measures nothing about the new rung and is not meant to. It is the neighbour
/// that stops "the dot now dispatches" from being satisfied by a rung that fired where an
/// earlier one already had.
#[test]
fn the_concrete_and_abstract_spec_receivers_are_unchanged() {
    for (label, param) in [("concrete", "Leaf"), ("abstractspec", "Desc")] {
        for (form, body) in [("dot", "x.describe()"), ("named", "Desc.describe(x)")] {
            let ns = format!("wi1119.ctl.{label}.{form}");
            let src = with_instances(
                &ns,
                &format!(
                    "  sort Holder\n    operation probe(x: {param}) -> Int64 = {body}\n  end\n  \
                     sort Driver\n    operation drive(n: Int64) -> Int64 = Holder.probe(leaf())\n  end"
                ),
            );
            assert_int(
                &src,
                &format!("{ns}.Driver.drive"),
                1,
                &format!("({label} receiver, {form} form) resolved before the new rung"),
            );
        }
    }
}

// ── THE ALIGNMENT: a clause lends its members only over ITS OWN parameter ────

/// THE CLAUSE IS KEYED ON THE PARAMETER IT NAMES — WI-823's rule read at the dot. Two
/// bracket parameters, one clause each, two dots in one body: the clause over `A` must serve
/// the `A` dot and the clause over `B` the `B` dot.
///
/// THE TWO ARGUMENTS CARRY DIFFERENT DEPTH CODES ON PURPOSE (`Leaf` = 1, `Wrap[Leaf]` = 12)
/// and are combined positionally as 100·first + second, so a rung that crossed the two
/// dictionaries lands on 100·12 + 1 = 1201 and one that served both dots from a single
/// clause lands on 101 or 1212 — never on 112 by accident. Passing the same argument twice
/// would make the crossing produce the identical number, which is the trap
/// `wi823_op_param_requires_coverage_test` records having fallen into.
///
/// Fails on the RUNG back-out: at load, with two `DotDispatchNoMatch`es, one per dot.
#[test]
fn each_dot_takes_the_clause_over_its_own_parameter() {
    let src = with_instances(
        "wi1119.keyed",
        r#"  sort Holder
    operation pair[A, B](x: A, y: B) -> Int64 requires Desc[A], Desc[B] =
      add(mul(100, x.describe()), y.describe())
    operation drive(n: Int64) -> Int64 = pair[Leaf, Wrap[A = Leaf]](leaf(), wrap(leaf()))
  end"#,
    );
    assert_int(
        &src,
        "wi1119.keyed.Holder.drive",
        112,
        "each dot resolves through the clause over its OWN parameter: 100·1 (Leaf) + 12 (Wrap)",
    );
}

/// A CLAUSE OVER THE OTHER PARAMETER LENDS NOTHING, and both spellings refuse. This is the
/// neighbour that stops the row above from being satisfied by a blanket licence: the σ
/// alignment must DISCRIMINATE, not merely permit.
///
/// The two refusals differ in wording and that is not a divergence: the named spelling gets
/// as far as dispatching `Desc.describe` and is refused by the WI-325 requires ladder, while
/// the dot never resolves a member at all and is refused at the dot. What the ticket asks
/// them to agree on is which programs are ACCEPTED, and neither is.
///
/// REFUSED UNDER THE RUNG BACK-OUT TOO, BY DESIGN — pre-fix because no rung ran, post-fix
/// because `QT`'s clause does not range over `PT`. It measures the alignment only in company
/// with the row above; alone it would measure nothing. What it DOES measure on its own is
/// the NAMING: with the rung in place and `receiver_param` backed out this row fails, so its
/// dot half is a live witness of the parameter being named — MEASURED, after a first draft
/// claimed the rung back-out changed this wording and the row passed with the rung gone.
#[test]
fn a_clause_over_another_parameter_does_not_lend_its_member() {
    let dot = with_instances(
        "wi1119.wrongdot",
        r#"  sort Holder
    operation probe[PT, QT](x: PT, y: QT) -> Int64 requires Desc[QT] = x.describe()
    operation drive(n: Int64) -> Int64 = probe[Leaf, Leaf](leaf(), leaf())
  end"#,
    );
    assert_err_contains(
        &load_errs(&dot),
        &["?PT.describe", "no `requires` clause constrains it"],
        "the dot must be refused naming the PARAMETER it could not dispatch on",
    );

    let named = with_instances(
        "wi1119.wrongnamed",
        r#"  sort Holder
    operation probe[PT, QT](x: PT, y: QT) -> Int64 requires Desc[QT] = Desc.describe(x)
    operation drive(n: Int64) -> Int64 = probe[Leaf, Leaf](leaf(), leaf())
  end"#,
    );
    assert_err_contains(
        &load_errs(&named),
        &[
            "wi1119.wrongnamed.Desc.describe.requires",
            crate::common::MISSING_DESC_REQUIRES,
        ],
        "the named spelling is refused by the WI-325 ladder — the two forms agree on \
         REJECTION, which is what the ticket asks of them",
    );
}

// ── THE TWO CHAIN SOURCES, COMPOSED AT ONE READ ──────────────────────────────

/// AN OPERATION'S CLAUSE AND ITS SORT'S ARE READ TOGETHER. Two dots in ONE body — one on the
/// operation's bracket parameter `PT`, licensed by the operation's own clause, one on the
/// sort's parameter `HT`, licensed by the sort-level clause — so a rung wired to either
/// source alone fails here while passing the single-source rows above. That is the shape
/// this repo keeps re-finding as a defect when only one channel is wired (WI-945, WI-1098),
/// and it is why the two sources are seeded at one read.
///
/// The two arguments carry different depth codes for the reason the keying test states:
/// correct is 100·1 + 12 = 112 and a crossed pair of licences gives 1201.
///
/// Fails on the RUNG back-out: at load, with two `DotDispatchNoMatch`es.
#[test]
fn an_operations_clause_and_its_sorts_are_read_together() {
    let src = with_instances(
        "wi1119.compose",
        r#"  sort Holder
    sort HT = ?
    requires Desc[T = HT]
    operation probe[PT](x: PT, y: HT) -> Int64 requires Desc[PT] =
      add(mul(100, x.describe()), y.describe())
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe[Leaf](leaf(), wrap(leaf()))
  end"#,
    );
    assert_int(
        &src,
        "wi1119.compose.Driver.drive",
        112,
        "the operation's own clause serves the `PT` dot and the sort-level one the `HT` dot, \
         from one body: 100·1 (Leaf) + 12 (Wrap) — a crossed pair would give 1201",
    );
}

// ── TRANSITIVITY, TIES, AND THE REFINEMENT RULE ──────────────────────────────

/// The declaring spec need not be the one the clause NAMES: `requires Detail[PT]` lends
/// `Desc.describe` because `Detail requires Desc[T = D]`, with the carrier composed across
/// the hop. Transitive coverage is what already licenses the NAMED spelling of this call
/// (WI-644 / proposal 004), so a non-transitive rung would put the two spellings back into
/// disagreement on the shape the ticket exists to close.
///
/// Both forms are driven; the named one is the control, and it passes either way.
///
/// Fails on the RUNG back-out: the DOT row, at load.
#[test]
fn a_transitively_required_spec_lends_its_member() {
    const DETAIL: &str = r#"  sort Detail
    sort D = ?
    requires Desc[T = D]
    operation detail(x: D) -> Int64
  end
  sort LeafDetail
    fact Detail[D = Leaf]
    operation detail(x: Leaf) -> Int64 = 7
  end
"#;
    for (form, body) in [("dot", "x.describe()"), ("named", "Desc.describe(x)")] {
        let ns = format!("wi1119.trans.{form}");
        let src = with_instances(
            &ns,
            &format!(
                "{DETAIL}  sort Holder
    operation probe[PT](x: PT) -> Int64 requires Detail[PT] = {body}
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"
            ),
        );
        assert_int(
            &src,
            &format!("{ns}.Holder.drive"),
            1,
            &format!("({form}) `requires Detail[PT]` reaches `Desc.describe` over the hop"),
        );
    }
}

/// A REFINEMENT IS NOT A TIE. `Detail requires Desc` and BOTH declare `describe`, so §8.7's
/// requires-refinement rule — the same `most_refined_spec` the provides and required-spec
/// rungs use — settles it in favour of `Detail`, and the tie refusal must NOT fire.
///
/// DRIVEN TO THE NUMBER THAT SAYS WHICH ONE WON: `Detail`'s describer is bound to a member
/// returning 5, against `Desc`'s 1. "Loads clean" would pass on the wrong winner; the pair
/// (5, and the same 5 from an explicit `Detail.describe(x)`) says the dot picked the
/// refinement and picked what the qualified spelling picks.
///
/// Fails on the RUNG back-out: the DOT row, at load. The explicit `Detail.describe(x)` row
/// passes either way, and is here as the answer the dot is being compared against.
#[test]
fn a_requires_refinement_wins_the_tie_rather_than_being_refused() {
    const SPECS: &str = r#"  sort Detail
    sort D = ?
    requires Desc[T = D]
    operation describe(x: D) -> Int64
  end
  sort LeafDetail
    fact Detail[D = Leaf, describe = LeafDetail.detailed]
    operation detailed(x: Leaf) -> Int64 = 5
  end
"#;
    for (form, body) in [("dot", "x.describe()"), ("named", "Detail.describe(x)")] {
        let ns = format!("wi1119.refine.{form}");
        let src = with_instances(
            &ns,
            &format!(
                "{SPECS}  sort Holder
    operation probe[PT](x: PT) -> Int64 requires Desc[PT], Detail[PT] = {body}
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"
            ),
        );
        assert_int(
            &src,
            &format!("{ns}.Holder.drive"),
            5,
            &format!(
                "({form}) `Detail` refines `Desc`, so its `describe` wins — 1 would mean the \
                 dot took the LESS specific spec"
            ),
        );
    }
}

/// A GENUINE TIE IS REFUSED NAMING BOTH SPECS, not settled by the order the clauses are
/// written. `Desc` and `Show` are unrelated and each declares `describe`, so no refinement
/// separates them.
///
/// Refusing rather than taking the first match is a deliberate departure from the two
/// sibling rungs: those order their candidates by provision distance / requires pre-order,
/// while a clause on the operation and a clause on its sort have no distance between them,
/// so first-match here would let the ORDER THE CLAUSES ARE WRITTEN decide which
/// implementation runs — the thing §"Where the ambiguity error is raised" refuses.
///
/// The refinement test above is the positive that stops this from being satisfied by a rung
/// that refused every multi-spec case. Fails on the RUNG back-out — differently from the
/// positives: the back-out refuses this program too, as a `DotDispatchNoMatch` that names
/// neither spec, so the assertion is on the MESSAGE and not merely on there being an error.
#[test]
fn two_unrelated_constraining_specs_declaring_one_member_are_refused_naming_both() {
    let src = with_instances(
        "wi1119.tie",
        r#"  sort Show
    sort S = ?
    operation describe(x: S) -> Int64
  end
  sort Holder
    operation probe[PT](x: PT) -> Int64 requires Desc[PT], Show[PT] = x.describe()
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"#,
    );
    assert_err_contains(
        &load_errs(&src),
        &[
            "ambiguous member 'describe'",
            "wi1119.tie.Desc",
            "wi1119.tie.Show",
            "Desc.describe(…)",
        ],
        "the tie must name BOTH constraining specs and the qualified spelling that settles it",
    );
}

/// TWO SPECS DECLARING ONE NAME ARE NOT RIVALS WHEN THE CALL CAN ONLY REACH ONE. `Show`'s
/// `describe` takes an extra argument, so the zero-extra-argument dot names `Desc`'s
/// unambiguously — and the tie must not fire.
///
/// FOUND BY REVIEW, NOT BY THE FIXTURES ABOVE, and it was refusing a working program:
/// keying the tie on the member NAME alone rejected this call AND offered
/// `Show.describe(…)` as a repair, which is itself an arity error — the spelling
/// §"Where the ambiguity error is raised" says a message must not suggest. It was also
/// stricter than the shadowing rule this mirrors, whose distinguishability test (WI-1048)
/// starts at arity.
///
/// DRIVEN, not merely loaded: 1 is `Desc`'s describer, so the row says which candidate the
/// narrowing kept. The tie test above is the neighbour — narrowing must not empty the
/// candidate set, and a genuine same-shape pair is still refused.
#[test]
fn a_candidate_the_call_cannot_reach_is_not_half_of_a_tie() {
    let src = with_instances(
        "wi1119.arity",
        r#"  sort Show
    sort S = ?
    operation describe(x: S, prefix: Int64) -> Int64
  end
  sort Holder
    operation probe[PT](x: PT) -> Int64 requires Desc[PT], Show[PT] = x.describe()
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"#,
    );
    assert_int(
        &src,
        "wi1119.arity.Holder.drive",
        1,
        "only `Desc.describe` can take a dot with no further arguments, so the pair is not \
         a tie and the call reaches Desc's describer",
    );
}

// ── THE REFUSAL NAMES THE PARAMETER ──────────────────────────────────────────

/// A MEMBER NO CONSTRAINING SPEC DECLARES STAYS A `DotDispatchNoMatch` — but one that names
/// the receiver's PARAMETER and the specs that do constrain it, instead of
/// `<unresolved receiver>`. The two rows are the two repairs: a parameter nothing constrains
/// needs a `requires` clause, one whose constraints declare no such member needs a different
/// member (or a different spec).
///
/// Refused under BOTH back-outs — the CONTENT is what changed, so the assertions are on the
/// naming and this is the NAMING axis's own witness: with `receiver_param` backed out both
/// rows revert to `<unresolved receiver>.describe` and fail, while the RUNG back-out leaves
/// them passing (nothing about resolution is at stake once no spec declares the member).
#[test]
fn an_unresolvable_member_names_the_parameter_and_its_constraints() {
    let unconstrained = with_instances(
        "wi1119.bare",
        r#"  sort Holder
    operation probe[PT](x: PT) -> Int64 = x.describe()
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"#,
    );
    assert_err_contains(
        &load_errs(&unconstrained),
        &["?PT.describe", "no `requires` clause constrains it"],
        "an unconstrained parameter must be named, with the missing clause as the repair",
    );

    let no_such_member = with_instances(
        "wi1119.nomember",
        r#"  sort Holder
    operation probe[PT](x: PT) -> Int64 requires Desc[PT] = x.nosuch()
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"#,
    );
    assert_err_contains(
        &load_errs(&no_such_member),
        &[
            "?PT.nosuch",
            "the specs constraining it declare no 'nosuch'",
            "wi1119.nomember.Desc",
        ],
        "a constrained parameter must be named ALONGSIDE the specs that were searched",
    );

    // FOUND BY REVIEW: a spec no declared operation RECEIVES on still CONSTRAINS the
    // parameter, and an earlier draft's walk dropped it — so this program, which writes the
    // clause, was told "no `requires` clause constrains it" and advised to add one. The
    // listing and the resolution are two questions over one walk; only the second may filter
    // on "could this spec lend a member".
    let non_receiving = with_instances(
        "wi1119.zeroed",
        r#"  sort Zeroed
    sort Z = ?
    operation zero() -> Int64
  end
  sort Holder
    operation probe[PT](x: PT) -> Int64 requires Zeroed[PT] = x.nosuch()
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end"#,
    );
    assert_err_contains(
        &load_errs(&non_receiving),
        &[
            "?PT.nosuch",
            "the specs constraining it declare no 'nosuch'",
            "wi1119.zeroed.Zeroed",
        ],
        "a constraining spec must be NAMED even when none of its operations could receive \
         the parameter — the author wrote the clause and must not be told to add one",
    );
}

/// TWO TIED SPECS SHARING A SHORT NAME GET DISTINGUISHABLE REPAIRS. `a.Desc` and `b.Desc`
/// both constrain `PT` and both declare `describe`, so the tie is genuine — and the repair
/// must be two spellings that differ, which short names are not.
///
/// FOUND BY REVIEW. Also the one row here that puts the specs in SEPARATE namespaces, which
/// is what makes the qualified rendering observable at all.
#[test]
fn a_tie_between_same_short_named_specs_suggests_distinguishable_spellings() {
    let src = format!(
        r#"
namespace wi1119.shortname.a
  import anthill.prelude.{{Int64, Bool}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
end

namespace wi1119.shortname.b
  import anthill.prelude.{{Int64, Bool}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
end

namespace wi1119.shortname.use
  import anthill.prelude.{{Int64, Bool}}
  import wi1119.shortname.a
  import wi1119.shortname.b
  sort Leaf
    entity leaf
  end
  sort Holder
    operation probe[PT](x: PT) -> Int64
      requires wi1119.shortname.a.Desc[PT], wi1119.shortname.b.Desc[PT] = x.describe()
    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())
  end
end
"#
    );
    assert_err_contains(
        &load_errs(&src),
        &[
            "ambiguous member 'describe'",
            "wi1119.shortname.a.Desc.describe(…)",
            "wi1119.shortname.b.Desc.describe(…)",
        ],
        "the repair must offer two spellings that DIFFER — short names would print the same \
         suggestion twice, and neither would disambiguate at the call site",
    );
}
