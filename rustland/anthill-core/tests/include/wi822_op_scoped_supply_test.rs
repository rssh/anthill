//! WI-822 — requirement supply for an op whose `requires` chain is OP-SCOPED
//! (WI-448/WI-562: written on the operation, member-style, not on its sort).
//!
//! The ticket named TWO legs. Only the second turned out to decide the
//! measured failures, and establishing that took a probe — the
//! unbound-dictionary message named no frame (it does now):
//!
//!   LEG 2 (dispatch site) — FIXED HERE. Value-directed dispatch resolves a
//!   body-less spec op's impl from the receiver VALUE at runtime and used to
//!   enter that impl's frame with the SPEC call's own (empty) channel. Fine
//!   while every reachable impl is a LEAF; the moment the value selects a
//!   CONDITIONAL impl (`WrapDesc requires Desc[T = E]`) its body's first
//!   dictionary read died `Internal(… __req_desc not bound)` — naming a frame
//!   the author never wrote. The failing frame was the IMPL's
//!   (`WrapDesc.describe`), NOT the op-scoped caller's (`Holder.probe`), which
//!   is what LEG 1's stated rationale predicted. At dispatch the receiver's
//!   type is concrete, so the impl's chain is resolvable right there:
//!   `requirements_for_value_directed_impl` (eval) reuses WI-625's
//!   `resolve_bridge_requirements` — the identical "concrete op, real argument
//!   values, no caller dictionary" problem. The WI-817 (c) rows flip in
//!   `wi817_polyrec_requirement_test.rs`; this file pins the LOUD-failure and
//!   value-preservation halves.
//!
//!   LEG 1 (call site) — NOT DELIVERED; its residue is PINNED BELOW as a
//!   current defect. An op-scoped chain has no frame slots at all
//!   (`synth_req_names` is keyed by the parent SORT), so there is no dictionary
//!   channel to fill — the requirement is served by value-direction instead,
//!   correctly wherever a receiver VALUE can direct it (WI-817's relay chain
//!   computes its 551 with no dictionary anywhere). It cannot be served where
//!   no value can: a spec op with NO receiver argument (`zero() -> T`). There
//!   the op-scoped spelling is not merely dictionary-less but REJECTED AT LOAD,
//!   while its sort-level twin loads and computes the right answer — an
//!   asymmetry between two spellings of one program, measured in
//!   `receiverless_spec_op_op_scoped_rejected_sort_level_correct`.

use anthill_core::eval::Value;

/// Spec `Desc` + a base instance at `Leaf` (describe → 1) + a CONDITIONAL
/// instance at `Wrap[E]` given `Desc[E]` (describe → 10·describe(inner) + 2),
/// so a correct answer is depth-coded (1, 12, 122, …) and a wrong dictionary
/// at any step shows up as a different number. Same shape as the WI-817
/// witness's `INSTANCES`, restated here so this file reads standalone.
const INSTANCES: &str = r#"
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end

  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end

  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end
"#;

fn eval_fresh(src: &str, entry: &str, n: i64) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(n)])
}

/// The WI-325 ladder's suggestion for an uncovered spec-op call. Spelled once:
/// it carries a U+2026, easy to mistype and awkward to grep for when the
/// diagnostic is reworded. Same constant the WI-817 suite keeps.
const MISSING_REQUIRES: &str = "missing `requires Desc[T = …]`";

// ── LEG 2: the supply is resolved at the VALUE's type, not inherited ──

/// The value-selected impl's chain is resolved at the RECEIVER'S OWN type at
/// each step, so two calls that select the SAME impl operation
/// (`WrapDesc.describe`) at DIFFERENT instantiations each get their own
/// dictionary — 12 for `Wrap[Leaf]`, 122 for `Wrap[Wrap[Leaf]]` — in ONE
/// program, on ONE interpreter. A supply that resolved once and was reused
/// (or inherited from the caller) would measure the same number twice; the
/// pre-fix code measured neither, dying unbound at both.
#[test]
fn value_directed_supply_is_per_call_not_shared() {
    let src = format!(
        r#"
namespace wi822.percall
  import anthill.prelude.{{Int64, Bool}}
{INSTANCES}
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation shallow(n: Int64) -> Int64 = Holder.probe(wrap(leaf()))
    operation deep(n: Int64) -> Int64 = Holder.probe(wrap(wrap(leaf())))
    operation both(n: Int64) -> Int64 =
      add(Driver.shallow(n), mul(1000, Driver.deep(n)))
  end
end
"#
    );
    let got = eval_fresh(&src, "wi822.percall.Driver.both", 0);
    assert!(
        matches!(got, Ok(Value::Int(122012))),
        "expected Ok(Int(122012)) = shallow 12 + 1000·deep 122, each `WrapDesc.describe` \
         frame seeded from its OWN receiver's type; got {got:?}"
    );
}

/// An UNPINNABLE chain never becomes a WRONG dictionary. This is the guard the
/// WI-824 feedback asks of WI-822: an op-scoped construction path meeting an
/// ABSTRACT element must land on a refusal, not build a dictionary.
///
/// It does, and MEASURED it lands EARLIER than WI-822 assumed — at LOAD. To
/// make an impl's own requirement unpinnable from its argument types, that
/// requirement must range over a type-param the parameters do not mention
/// (`Ghost requires Desc[T = U]`, `describe(w: Box[B = G])`); but then it also
/// fails to COVER the body's own dictionary read, and the WI-325 ladder
/// refuses the program before it can run. So "unpinnable chain AND a body that
/// reads it" is not a runnable configuration at all.
///
/// Two independent guards therefore stand between an abstract element and a
/// dictionary, and this pins the outer one. The inner one — the fully-pinned
/// gate in `resolve_bridge_requirements`, which rejects an abstract binding
/// BEFORE candidate matching — still matters and must stay: that resolve is
/// σ-LESS, so WI-824's σ-gated refusal of a rigid against a structured head is
/// NOT in force on this path, and the gate is what stands in for it. The two
/// must be relaxed together or not at all.
///
/// The remaining unpinnable shapes are the ones the stdlib actually runs: an
/// impl whose chain cannot be pinned because the receiver is a HANDLE carrying
/// no element type (`Map.iterator` on a `Value::Map`, against `Map`'s
/// `requires Eq[T = Map.K]`), and whose body never reads it. Those enter
/// unsupplied and run — which is why WI-822's specified loud-at-dispatch error
/// was replaced by loud-at-the-read (pinned by the test below).
#[test]
fn unpinnable_impl_requirement_is_refused_before_it_can_run() {
    let src = format!(
        r#"
namespace wi822.ghost
  import anthill.prelude.{{Int64, Bool}}
{INSTANCES}
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort Ghost
    sort G = ?
    sort U = ?
    requires Desc[T = U]
    fact Desc[T = Box[B = G]]
    operation describe(w: Box[B = G]) -> Int64 = add(7, Desc.describe(w.inner))
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(box(leaf()))
  end
end
"#
    );
    let errs = crate::common::try_load_kb_with(&src).err().unwrap_or_else(|| {
        panic!(
            "the unpinnable-chain program must NOT load — if it does, the only thing \
             left between its abstract element and a dictionary is the fully-pinned \
             gate, and this test must be rewritten to drive it (a wrong dictionary \
             would deliver Ok(Int(8)))"
        )
    });
    let text = errs.join("\n");
    assert!(
        text.contains("wi822.ghost.Desc.describe.requires") && text.contains(MISSING_REQUIRES),
        "expected the WI-325 ladder to refuse `Ghost`'s uncovered dictionary read; got:\n{text}"
    );
}

/// The unbound-dictionary message NAMES ITS FRAME. WI-822's own investigation
/// could not attribute the failure from the text ("requirement param
/// `__req_desc` not bound in caller frame" — which frame?) and had to establish
/// it by probe; the message now carries the running operation and the sort
/// whose requires chain owns the slot.
///
/// Driven through the shape that still reaches it — the WI-415 gap named in
/// `CallClass::ConcreteApplyWithin`'s own doc: a CROSS-SORT call from a
/// `requires`-free caller over an ABSTRACT argument. Nothing can build the
/// callee a dictionary (no caller slot to forward, no concrete binding to
/// construct from), so `Holder.probe` is entered with an empty channel and its
/// deferred read finds no slot. The value-directed route that used to land
/// here no longer does — that is LEG 2 — so this pins the DIAGNOSTIC, on a
/// defect of its own that neither leg of WI-822 claims.
#[test]
fn unbound_requirement_message_names_the_running_frame() {
    let src = format!(
        r#"
namespace wi822.named
  import anthill.prelude.{{Int64, Bool}}
{INSTANCES}
  sort Holder
    sort HT = ?
    requires Desc[HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
  sort Caller
    sort CT = ?
    operation go(x: CT) -> Int64 = Holder.probe(x)
  end
end
"#
    );
    let got = eval_fresh(&src, "wi822.named.Caller.go", 0);
    let msg = match got {
        Err(anthill_core::eval::EvalError::Internal(msg)) => msg,
        other => panic!("expected an Internal requirement error to inspect; got {other:?}"),
    };
    assert!(
        msg.contains("wi822.named.Holder.probe"),
        "the unbound-requirement message must name the RUNNING operation; got {msg}"
    );
    assert!(
        msg.contains("wi822.named.Holder"),
        "the unbound-requirement message must name the requires-chain OWNER; got {msg}"
    );
}

// ── LEG 1 residue: PINS A CURRENT DEFECT ─────────────────────────────

/// PINS A CURRENT DEFECT — the residue LEG 1 would close, measured here for
/// the first time (the ticket predicted LEG 1 from the (c) pins, which LEG 2
/// alone in fact fixed; this is the evidence that actually motivates it).
///
/// `Zeroable.zero()` has NO parameter, so no runtime value can direct its
/// dispatch — a dictionary is the ONLY thing that can pick between two
/// providers. With the requirement written at SORT level the body's call is
/// classified `DeferToRequirement`, the caller's dictionary decides, and the
/// program computes 5 (`Pebble.zero()` → `Pebble.describe` → 5). With the
/// SAME requirement written OP-SCOPED there is no slot to defer to, so the
/// typer tries to pin `zero()` concretely, sees both providers, and REJECTS
/// THE PROGRAM AT LOAD.
///
/// So the two spellings of one program are not "dictionary-served vs
/// value-served" here — one loads and is right, the other does not load at
/// all. CORRECT: the op-scoped spelling loads and also computes 5, which
/// needs a real op-scoped supply channel (frame slots keyed by the OPERATION,
/// not only by its parent sort) — WI-822 LEG 1.
#[test]
fn receiverless_spec_op_op_scoped_rejected_sort_level_correct() {
    const BASE: &str = r#"
  sort Zeroable
    sort T = ?
    operation zero() -> T
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Zeroable[T = Leaf]
    operation zero() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Zeroable[T = Pebble]
    operation zero() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
"#;
    let program = |ns: &str, holder: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
{BASE}
  sort Holder
    sort HT = ?
{holder}
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(pebble())
  end
end
"#
        )
    };

    // CONTROL — sort-level `requires`: loads and is RIGHT.
    let sort_level = program(
        "wi822.recv.sortlevel",
        "    requires Zeroable[HT]\n    operation probe(x: HT) -> Int64 = \
         Zeroable.describe(Zeroable.zero())",
    );
    let got = eval_fresh(&sort_level, "wi822.recv.sortlevel.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(5))),
        "control (sort-level requires): expected Ok(Int(5)) — the caller's dictionary \
         picks `Pebble.zero`; got {got:?}"
    );

    // DEFECT — the same requirement written OP-SCOPED: rejected at LOAD.
    let op_scoped = program(
        "wi822.recv.opscoped",
        "    operation probe(x: HT) -> Int64 requires Zeroable[HT] = \
         Zeroable.describe(Zeroable.zero())",
    );
    let errs = crate::common::try_load_kb_with(&op_scoped)
        .err()
        .unwrap_or_else(|| {
            panic!(
                "the op-scoped spelling now LOADS — if it also computes 5, WI-822 LEG 1 \
                 has landed and this pin must flip to the control's assertion"
            )
        });
    let text = errs.join("\n");
    assert!(
        text.contains("Zeroable.zero.dispatch") && text.contains("multiple impls match"),
        "expected the load-time dispatch rejection of the receiver-less `zero()` \
         (CURRENT DEFECT; correct = loads and computes 5, as the sort-level control \
         does — WI-822 LEG 1); got:\n{text}"
    );
}
