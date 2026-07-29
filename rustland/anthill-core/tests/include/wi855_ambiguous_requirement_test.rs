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
/// It LOADS CLEAN, and the reason is worth stating exactly, because it is not
/// the one that first suggests itself. `check_provider_operations`'s coherence
/// pass groups candidates per `(spec, dispatch carrier)` and refuses a group of
/// two — but `Leaf`'s OWN provision is a candidate of NEITHER kind: it binds no
/// op, so `provision_binds_any_op` rejects it as an instance fact, and its
/// provider IS its carrier, so `witness_dispatch_carrier` rejects it as a
/// witness. A self-provider can therefore never be one half of a refused pair,
/// whatever the other half is — MEASURED both ways by
/// `the_tie_is_invisible_to_load_coherence_either_way` below, which drives this
/// concrete `Rival` and an ABSTRACT twin of it. (The concrete-provider exemption
/// noted in proposal 058 §4.9 is a red herring here: it is why the concrete
/// spelling forms no group, but the abstract spelling forms a group of ONE and
/// is admitted just the same.)
const RIVAL_CONCRETE: &str = r#"
  sort Rival
    entity rival
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// The same rival with no constructor — a WI-450 witness sort, which the
/// coherence pass DOES admit as a candidate. It still forms a group of one
/// (`Leaf`'s self-provision never joins it), so it still loads.
const RIVAL_ABSTRACT: &str = r#"
  sort Rival
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
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

/// THE PIN. A genuine two-provider tie, reached through value-directed dispatch,
/// surfaces as `AmbiguousRequirement` naming the requirement and BOTH candidates.
#[test]
fn tie_through_value_directed_dispatch_names_the_requirement_and_both_providers() {
    let ns = "wi855.tie";
    let err = drive(&program(ns, RIVAL_CONCRETE, "wrap(leaf())"), ns).unwrap_err();
    let EvalError::AmbiguousRequirement { op, requirement, candidates } = &err else {
        panic!(
            "expected an AmbiguousRequirement naming the tie; got {err:?} — an \
             `Internal(DeferToRequirement …)` here is the pre-WI-855 behaviour \
             (unsupplied frame, failure reported as a MISSING dictionary)"
        )
    };
    assert!(
        op.ends_with("WrapDesc.describe"),
        "the error must name the impl whose chain could not be built; got `{op}`"
    );
    assert!(
        requirement.contains("Desc") && requirement.contains("Leaf"),
        "the error must name the REQUIREMENT that tied (`Desc[T = Leaf]`); got `{requirement}`"
    );
    assert_eq!(
        candidates.len(),
        2,
        "exactly the two tied providers expected; got {candidates:?}"
    );
    for want in ["Leaf", "Rival"] {
        assert!(
            candidates.iter().any(|c| c.ends_with(want)),
            "`{want}` must appear among the tied providers; got {candidates:?}"
        );
    }
    // The rendered message is what an author actually sees, so it carries the
    // same three facts rather than only the struct fields.
    let rendered = err.to_string();
    for want in ["WrapDesc.describe", "Desc", "Leaf", "Rival"] {
        assert!(
            rendered.contains(want),
            "the rendered diagnostic must mention `{want}`; got: {rendered}"
        );
    }
}

/// WHY THE RUNTIME OWNS THIS VERDICT — measured, and measured on the shape that
/// refutes the easy explanation. A tie between a SELF-provider and a second
/// provider is invisible to load-time coherence whether that second provider is
/// CONCRETE (exempted from the witness rule as a manifest backend) or ABSTRACT
/// (admitted as a witness, but alone in its group, since a self-provider is a
/// candidate of neither kind). Both spellings load, and both then tie at
/// dispatch.
///
/// Without this, `RIVAL_CONCRETE`'s doc would rest on the exemption alone —
/// which is true of that spelling and false as a general account, and would send
/// the next reader to narrow an exemption that is not what admits the program.
#[test]
fn the_tie_is_invisible_to_load_coherence_either_way() {
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
        assert!(
            matches!(drive(&src, ns), Err(EvalError::AmbiguousRequirement { .. })),
            "`{ns}` must reach the runtime tie"
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

/// WI-822'S LINE, HELD. A requirement that resolves to NO provider is NOT a
/// coherence violation — it is the "cannot be pinned / may not be needed" class
/// WI-822 measured against the stdlib — so it still enters the frame UNSUPPLIED
/// and the body that never reads the slot still runs.
///
/// `Quiet` provides `Desc[T = Box[B = E]]` conditional on `Desc[T = E]`, but its
/// body is a constant that never reads the dictionary; `Mystery` has no `Desc`
/// provider at all, so dispatching on `box(mystery())` resolves that chain to
/// `NoMatch`. Answer 5 ⇒ the frame was entered unsupplied and ran. If this ever
/// flips to an error, the WI-855 raise has leaked out of the ambiguous case and
/// back onto the 29 stdlib tests WI-822 measured.
#[test]
fn other_unresolvable_causes_still_enter_unsupplied() {
    let ns = "wi855.nomatch";
    let got = drive(&program(ns, QUIET, "box(mystery())"), ns);
    assert!(
        matches!(got, Ok(Value::Int(5))),
        "expected Ok(Int(5)): `Quiet`'s chain resolves to NO provider at `Mystery`, \
         which must still enter the frame unsupplied and run a body that never reads \
         the slot (WI-822's measured behaviour); got {got:?}"
    );
}
