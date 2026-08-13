//! WI-855 — an AMBIGUOUS requirement-dictionary verdict is a COHERENCE finding,
//! and value-directed dispatch now RAISES it instead of entering the frame
//! unsupplied.
//!
//! `resolve_bridge_requirements` used to fold four unrelated verdicts — no
//! provider, AMBIGUOUS provider, cyclic provider, under-determined carrier —
//! into one `Unresolvable { detail }` bucket, and its value-directed consumer
//! turned that into a silently unsupplied frame (a trace line under
//! `ANTHILL_TRACE_REQ`, nothing else). So the ONE place that DETECTED a genuine
//! two-provider tie threw the detection away. MEASURED before the fix, the tie
//! below reached the author as
//!
//!   Internal("DeferToRequirement: requirement param `__req_desc` not bound in
//!            caller frame (running `…WrapDesc.describe`, requires-chain owner
//!            `…WrapDesc`)")
//!
//! — a MISSING-dictionary report naming neither the tie nor the two providers,
//! from a frame the author never wrote. That is the defect: not that the failure
//! was silent (it was loud), but that the loud thing said the wrong cause, and
//! the right one was in hand two frames earlier.
//!
//! NOT a re-litigation of WI-822, which measured that raising at dispatch for
//! EVERY unresolvable cause breaks 29 stdlib tests: those are chains that cannot
//! be PINNED at the argument types (a `Value::Map` handle carries no element
//! type) whose bodies never read the slot and run correctly with none. A TIE is
//! the opposite — the chain IS pinned and a dictionary IS constructible; two
//! provisions cover it and no rule picks one. `other_unresolvable_causes_still_
//! enter_unsupplied` below holds that line in-file.

use anthill_core::eval::{EvalError, Value};

/// Spec `Desc`, a base instance at `Leaf`, and a CONDITIONAL instance at
/// `Wrap[E]` given `Desc[E]` — the shape shared with WI-817 / WI-822, so a
/// correct answer is depth-coded (`Wrap[Leaf]` ⇒ 10·1 + 2 = 12) and a wrong
/// dictionary shows up as a different number rather than as an error.
const INSTANCES: &str = crate::common::DESC_INSTANCES;

/// The SECOND provider of `Desc[T = Leaf]` — the tie.
///
/// It LOADS CLEAN, and the reason is worth stating exactly, because it is not the
/// one that first suggests itself and it CHANGED at WI-859 without the verdict
/// changing with it. `check_provider_operations`'s coherence pass groups candidates
/// per `(spec, dispatch carrier)`; `Rival` is CONCRETE, and the concrete-provider
/// exemption (a manifest backend, distinguished by its values) keeps it out of the
/// grouping, so `Leaf`'s own provision is alone in its group and a group of one is
/// skipped before any rule looks at it.
///
/// The ABSTRACT twin below is what makes that account honest rather than lucky, and
/// it is the arm WI-859 moved. When WI-855 measured this, `Leaf`'s OWN provision was
/// a candidate of NEITHER kind — it binds no op, so `provision_binds_any_op` rejected
/// it as an instance fact, and its provider IS its carrier, so
/// `witness_dispatch_carrier` rejected it as a witness — so the abstract spelling
/// too formed a group of ONE, and a self-provider could never be half of anything.
/// WI-859 (058 phase 8a) added the SELF-PROVIDER kind, so that group now holds TWO
/// candidates and is admitted for a different reason: both are NAMEABLE, which is
/// 058 tier 3's coexistence rule. Same verdict, different mechanism —
/// `load_coherence_admits_the_tie_either_way` below drives both spellings, and
/// `wi859_self_provider_candidate_test` asserts the group's contents.
const RIVAL_CONCRETE: &str = r#"
  sort Rival
    entity rival
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// The same rival with no constructor — a WI-450 witness sort, which the coherence
/// pass DOES admit as a candidate. Since WI-859 `Leaf`'s self-provision joins it, so
/// this is a group of TWO nameable candidates: legal by 058 tier 3, and refused only
/// at a dispatch that selects neither.
const RIVAL_ABSTRACT: &str = r#"
  sort Rival
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// WI-861 — A CARRIER THAT PROVIDES NOTHING ITSELF, with two witnesses, so the
/// sub-goal `Desc[T = Twig]` inside `WrapDesc`'s dictionary genuinely ties.
///
/// The move is forced by 058 §3.2's rung 2a and not cosmetic: a carrier's OWN provision
/// is its default, so `Leaf` beside `RIVAL_*` no longer ties — it RESOLVES to `Leaf`,
/// which `the_self_provider_answers_the_tie_and_the_dictionary_builds` below asserts as
/// a VALUE. Neither `TwigA` nor `TwigB` is the carrier and neither is marked, so nothing
/// answers and this file's subject — a genuine two-provider tie reaching a route with no
/// bracket — is still what the pin measures.
const TWIG: &str = r#"
  sort Twig
    entity twig
  end

  sort TwigA
    fact Desc[T = Twig]
    operation describe(x: Twig) -> Int64 = 3
  end

  sort TwigB
    fact Desc[T = Twig]
    operation describe(x: Twig) -> Int64 = 5
  end
"#;

/// A conditional provider that never READS its dictionary, plus a carrier with
/// no `Desc` provider at all — so its chain resolves to NO provider rather than
/// to a tie.
const QUIET: &str = r#"
  sort Mystery
    entity mystery
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort Quiet
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Box[B = E]]
    operation describe(b: Box[B = E]) -> Int64 = 5
  end
"#;

/// `Holder.probe`'s requirement is OP-SCOPED, so (WI-562) its `Desc.describe(x)`
/// call is served by value-direction rather than by a caller dictionary — the
/// route this ticket is about. `arg` decides which impl the VALUE selects, and
/// with `wrap(leaf())` that is the conditional `WrapDesc.describe`, whose own
/// `requires Desc[T = E]` is what must be resolved at dispatch.
fn program(ns: &str, extra: &str, arg: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
{INSTANCES}{extra}
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe({arg})
  end
end
"#
    )
}

/// One load per program: `common::interp_for` panics (printing every error) on a
/// dirty load, so building the interpreter IS the clean-load gate.
fn drive(src: &str, ns: &str) -> Result<Value, EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(&format!("{ns}.Driver.drive"), &[Value::Int(0)])
}

/// THE PIN, and the claim is unchanged by WI-1091: a genuine two-provider tie surfaces
/// NAMED — the requirement and BOTH candidates — never as a missing-dictionary report
/// from a frame the author never wrote.
///
/// WI-861 moved it onto [`TWIG`] — see that constant. The `Leaf` + rival pair it used to
/// run on now RESOLVES, which the next test asserts as a value; what is pinned here is
/// the tie that no default answers.
///
/// **WI-1091 MOVED WHEN, from the dispatch to the LOAD, and only for a WRITTEN call
/// site.** `Holder.probe`'s requirement is op-scoped; WI-1091 widened the placement so
/// the body reads the dictionary that licence names, which makes BUILDING that dictionary
/// part of classifying `Driver.drive`'s call — and `Holder.probe(wrap(twig()))` pins
/// `HT := Wrap[Twig]`, so the tie is in hand there, with both providers and the bracket
/// that repairs it. Refusing at load is what makes this spelling agree with its
/// SORT-LEVEL twin, which has refused the identical program since WI-828. Earlier,
/// named, with a repair: strictly more than the dispatch-time raise it replaces.
///
/// THE EVAL FACE IS NOT LOST, and this is the part that would be easy to get wrong. A
/// route with no call site cannot be refused at load, and there the SAME
/// `EvalError::AmbiguousRequirement` is raised — now from the host-entry seeding
/// (`Interpreter::seed_entry_op_requirements`), and driven by
/// `wi842_bracketless_readers_test::a_two_provider_value_directed_dispatch_names_both_
/// candidates` and `wi861_rung2a_default_dispatch_test::a_witness_only_value_directed_
/// tie_stays_loud`, both of which assert that error and both of its providers.
///
/// BACKED OUT (WI-1091's widening reverted): this program LOADS and answers
/// `Err(AmbiguousRequirement { op: "…WrapDesc.describe", … })` at the call.
#[test]
fn tie_through_value_directed_dispatch_names_the_requirement_and_both_providers() {
    let ns = "wi855.tie";
    let errs = crate::common::try_load_kb_with(&program(ns, TWIG, "wrap(twig())"))
        .err()
        .expect(
            "two providers of `Desc[Twig]` and a call site that pins the element: the \
             dictionary `Holder.probe` needs cannot be built, and an `Internal(\
             DeferToRequirement …)` at eval would be the pre-WI-855 behaviour — a \
             MISSING-dictionary report naming neither the tie nor the providers",
        );
    let text = errs.join("\n");
    assert!(
        text.contains("Desc") && text.contains("Twig"),
        "the refusal must name the REQUIREMENT that tied (`Desc[T = Twig]`); got: {text}"
    );
    for want in ["TwigA", "TwigB"] {
        assert!(
            text.contains(want),
            "`{want}` must appear among the tied providers; got: {text}"
        );
    }
    assert!(
        text.contains("Holder.probe"),
        "…and the call whose requirement could not be supplied; got: {text}"
    );
}

/// WHY THE RUNTIME OWNS THIS VERDICT — measured, and measured on the shape that
/// refutes the easy explanation. A tie between a SELF-provider and a second provider
/// is ADMITTED by load-time coherence whether that second provider is CONCRETE
/// (exempted from the witness rule as a manifest backend, so the group stays a group
/// of one) or ABSTRACT (a witness beside the self-provider — a group of two, both
/// NAMEABLE, which 058 tier 3 lets coexist). Both spellings load, for two different
/// reasons.
///
/// Without this, `RIVAL_CONCRETE`'s doc would rest on the exemption alone — which is
/// true of that spelling and false as a general account, and would send the next
/// reader to narrow an exemption that is not what admits the other program.
///
/// **WI-861 FLIPPED THE SECOND HALF** — this is the ticket's flip (2), and the change is
/// which verdict the admitted program reaches, not whether it is admitted. It used to
/// say "…and both then TIE at dispatch". They no longer do: `Leaf` PROVIDES `Desc`
/// itself, so 058 §3.6 infers `default_provider(Desc, Leaf, Leaf)` and silence takes the
/// carrier's own implementation (12 = 10·1 + 2 through `WrapDesc`'s dictionary). The
/// rival stays loadable and stays opt-in.
///
/// So the ONLY thing that changed for these two programs is the LADDER, which is what
/// makes the load-admission assertion still worth making: were coherence to start
/// refusing either spelling, the value below would never be reached and this arm would
/// report it.
///
/// The name changed at WI-859: "invisible" was accurate while a self-provider was a
/// candidate of no kind at all, and the abstract arm is now SEEN and admitted.
#[test]
fn load_coherence_admits_the_tie_either_way() {
    for (ns, rival) in [
        ("wi855.tie.concrete", RIVAL_CONCRETE),
        ("wi855.tie.abstract", RIVAL_ABSTRACT),
    ] {
        let src = program(ns, rival, "wrap(leaf())");
        crate::common::try_load_kb_with(&src).unwrap_or_else(|errs| {
            panic!(
                "`{ns}` must still LOAD — a load check that now refuses it would move \
                 this class of tie off the dispatch site, and the pin above must then \
                 be re-shaped rather than deleted:\n{}",
                errs.join("\n")
            )
        });
        let got = drive(&src, ns);
        assert!(
            matches!(got, Ok(Value::Int(12))),
            "`{ns}`: 058 §3.2 rung 2a takes the carrier's own provision, and 12 = \
             10·describe(leaf) + 2 says the DICTIONARY was built from it. A 72 would be \
             `Rival` winning; an `AmbiguousRequirement` is the pre-WI-861 verdict. \
             Got {got:?}"
        );
    }
}

/// ABSENCE CONTROL — the identical program WITHOUT the rival provider computes
/// its 12. Without this, the pin above would pass just as well if the whole
/// shape had stopped working for some unrelated reason; with it, the ONLY
/// difference between an answer and the diagnostic is the second provision.
#[test]
fn the_same_program_with_one_provider_still_computes_its_answer() {
    let ns = "wi855.untied";
    let got = drive(&program(ns, "", "wrap(leaf())"), ns);
    assert!(
        matches!(got, Ok(Value::Int(12))),
        "expected Ok(Int(12)) = 10·describe(leaf) + 2 with `WrapDesc`'s dictionary \
         resolved at the receiver's type; got {got:?}"
    );
}

/// WI-822'S LINE, HELD — and WI-1091 re-shaped this row because the line was being
/// asserted through a body that DOES read the slot.
///
/// The claim is unchanged: a requirement that resolves to NO provider is NOT a coherence
/// violation. It is the "cannot be pinned / may not be needed" class WI-822 measured
/// against the stdlib, so the frame is entered UNSUPPLIED and a body that never reads the
/// slot still runs. `Silent.probe` is such a body — it carries `requires Desc[T = HT]`
/// and answers a constant — and it answers 5 with `box(mystery())`, whose `Desc` chain
/// resolves to no provider at all. If THAT ever flips to an error, the WI-855 raise has
/// leaked out of the ambiguous case and back onto the 29 stdlib tests WI-822 measured.
///
/// WHAT CHANGED. This row used to drive `Holder.probe`, whose body IS `Desc.describe(x)`
/// — a body that reads the slot. It answered 5 because value-direction served that read
/// from the runtime value, which is exactly the placement WI-1091 replaced: the call is
/// licensed by `probe`'s own `requires`, so it now reads the dictionary that licence
/// names, finds nothing, and raises naming the frame. So the old row was measuring the
/// route rather than the line, and the line survives it — restated below on a body that
/// really does not read.
///
/// AND THE TWO SPELLINGS AGREE, which is the other half and the one that says the new
/// verdict is right rather than merely new. The SORT-LEVEL twin of `Holder` — the same
/// text with `requires Desc[T = HT]` on the sort instead of on the operation — loads and
/// raises the SAME frame-naming error, and did so before WI-1091 as well. An unpinnable
/// requirement is not an error for a body that ignores it and IS one for a body that
/// reads it, on EITHER spelling; that is the rule, and it is what §5.2 states.
#[test]
fn other_unresolvable_causes_still_enter_unsupplied() {
    // A body that does NOT read the slot: enters unsupplied, runs.
    const SILENT: &str = r#"
  sort Silent
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = 5
  end
"#;
    let ns = "wi855.nomatch";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
{INSTANCES}{QUIET}{SILENT}
  sort Driver
    operation drive(n: Int64) -> Int64 = Silent.probe(box(mystery()))
  end
end
"#
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call(&format!("{ns}.Driver.drive"), &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(5))),
        "expected Ok(Int(5)): the `Desc` chain resolves to NO provider at `Mystery`, \
         which must still enter the frame unsupplied and run a body that never reads \
         the slot (WI-822's measured behaviour); got {got:?}"
    );
}

/// THE AGREEMENT, driven on both spellings of one program — the half of the rule above
/// that a body which DOES read an unsupplied slot is what makes observable.
///
/// The op-scoped `Holder.probe` and its sort-level twin differ in ONE line (which
/// declaration carries `requires Desc[T = HT]`) and must give one verdict. Both raise,
/// naming the frame and the slot it does not bind. Measured, not assumed: the sort-level
/// spelling answered exactly this before WI-1091 too, so the widening moved the op-scoped
/// spelling ONTO the sort-level answer rather than inventing a third one.
///
/// FAILS IF THE WIDENING IS BACKED OUT — the op-scoped arm answers `Ok(Int(5))` then,
/// served by value-direction, and the two spellings disagree.
#[test]
fn a_body_that_reads_an_unsuppliable_slot_agrees_on_both_spellings() {
    const OP_SCOPED: &str = r#"
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
"#;
    const SORT_LEVEL: &str = r#"
  sort Reader
    sort HT = ?
    requires Desc[T = HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
"#;
    for (which, reader) in [("op-scoped", OP_SCOPED), ("sort-level", SORT_LEVEL)] {
        let ns = format!("wi855.agree.{}", which.replace('-', ""));
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
{INSTANCES}{QUIET}{reader}
  sort Driver
    operation drive(n: Int64) -> Int64 = Reader.probe(box(mystery()))
  end
end
"#
        );
        let mut interp = crate::common::interp_for(&src);
        let got = interp.call(&format!("{ns}.Driver.drive"), &[Value::Int(0)]);
        let err = got.expect_err(&format!(
            "{which}: a body that READS a slot nothing can supply must raise, not answer"
        ));
        let msg = err.to_string();
        assert!(
            msg.contains("__req_desc") && msg.contains("not bound"),
            "{which}: the raise must name the slot the frame does not bind; got {msg}"
        );
    }
}
