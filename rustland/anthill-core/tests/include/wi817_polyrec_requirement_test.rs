//! WI-817 — the witness: POLYMORPHIC RECURSION whose requirement changes to
//! the type-argument type at each step (`Desc[Leaf]`, `Desc[Wrap[Leaf]]`,
//! `Desc[Wrap[Wrap[Leaf]]]`, … — unbounded, so `PinNow` is unreachable), with
//! the g→f leg once direct (the operation-only CONTROL) and once routed
//! through a lambda invoked by a requirement-free applier (the WITNESS).
//!
//! THE PREDICTION UNDER TEST (ticket): per-call resolution can serve the
//! changing requirement and resolve-once-at-creation cannot, so the case
//! should be EXPRESSIBLE AS AN OPERATION and INEXPRESSIBLE AS A LAMBDA.
//!
//! THE MEASURED VERDICT: the prediction is NOT OBSERVABLE TODAY — the
//! operation-only CONTROL fails in every expressible spelling, and the lambda
//! witness NEVER fails differently from its control. A shared defect upstream
//! of any operation/lambda asymmetry decides every outcome: the CALL-SITE
//! REQUIREMENT SUPPLY for a requirement instantiated at a CHANGED type.
//! Concretely (`build_dep_projection`, kb/typing.rs): Strategy 1's
//! `entries_cover` is wildcard-tolerant — a caller `requires Desc[GT]` covers
//! a callee dep `Desc[FT]` whenever either element is a type param — and its
//! σ-class check (WI-419) only disambiguates 2+ covering entries, so a SOLE
//! covering wildcard entry blindly FORWARDS the caller's dictionary even when
//! the call-site substitution maps the dep's element to a COMPOUND of the
//! caller's element (FT := Wrap[GT]). Strategy 3 — SLD construction of the
//! conditional-instance tree, which handles the changed type CORRECTLY when
//! reached (see `sort_level_single_conditional_level_is_correct`) — is
//! shadowed by that early return. Op-scoped `requires` chains additionally
//! have NO call-site supply channel at all (`ConcreteApplyWithin` gates on
//! the callee's PARENT SORT chain), and value-directed dispatch pushes an
//! impl frame without the impl's own requires.
//!
//! Outcome matrix (all pinned below; letters are the ticket's outcome codes —
//! (b) load error, (c) eval error, (d) silently wrong answer):
//!
//! | requires channel                  | 1 cond. level | mutual recursion | + lambda leg |
//! |-----------------------------------|---------------|------------------|--------------|
//! | op-scoped over OP type param      | (b) load err  | (b) load err     | (b) load err |
//! | op-scoped over SORT param         | (c) unbound   | (c) unbound      | (c) unbound  |
//! | SORT-level                        | CORRECT (12)  | (d) WRONG (1)    | (d) WRONG (1)|
//!
//! The `requires`-eval-path hazard flagged by the ticket ("sort-level
//! `requires` makes ops untrappable"; two competing error spellings, neither
//! established) is SETTLED: neither reported error reproduces; sort-level
//! requires works end-to-end through a conditional instance (V8 pins the
//! correct 12). The real failures are the two supply defects above, plus a
//! bonus hazard: an UNCONDITIONED parametric provider fact silently mis-pins
//! an abstract spec-op call at load (see
//! `unconditioned_parametric_fact_mispins_abstract_call`).
//!
//! Tests here PIN CURRENT DEFECTS on purpose (the ticket's instruction): the
//! (b)/(c)/(d) rows are wrong behaviour, named as such — the correct values
//! are stated beside each pin. When the supply defect is fixed, the (d) pins
//! must flip to 12/122/1222 and the (c) pins to values; the (b) pins flip to
//! clean loads when the separate §5.4 op-param-requires gap closes.

use anthill_core::eval::Value;

/// The shared instance block: spec `Desc` with one op, base instance at
/// `Leaf` (describe → 1), CONDITIONAL instance at `Wrap[E]` given `Desc[E]`
/// (describe → 10·describe(inner) + 2). Correct values are therefore
/// depth-coded: describe(wrapⁿ(leaf)) = 1, 12, 122, 1222, … — a wrong
/// dictionary at any step produces a detectably different number.
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

fn with_instances(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Function}}
{INSTANCES}
{body}
end
"#
    )
}

/// Load `src` and call `entry(n)` on a FRESH interpreter, returning the
/// verbatim result. Fresh per call because a trapped call poisons later
/// calls on the same interpreter; the load doubles as the clean-load gate —
/// `interp_for` prints every load error and panics on a dirty load, so the
/// "loads clean" half of each pin needs no separate load.
fn eval_fresh(src: &str, entry: &str, n: i64) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(n)])
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but the source loaded clean"))
}

// ── Positive controls: the harness must actually report breakage ─────

/// A deliberately broken program (unknown sort in a signature) must FAIL the
/// load — proves the load path reports errors, so the loads-clean half of
/// the pins below (enforced by `interp_for`'s panic-on-error) is not vacuous.
#[test]
fn positive_control_load_error_is_reported() {
    let src = with_instances(
        "wi817.posload",
        "  sort Holder\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    );
    let errs = load_errs(&src);
    assert!(!errs.is_empty());
}

/// A bogus operation name must Err at eval — proves `interp.call` verdicts
/// are real, so the Ok-value assertions below are not vacuous.
#[test]
fn positive_control_eval_error_is_reported() {
    let mut interp = crate::common::interp_for("");
    let got = interp.call("wi817.no_such.op", &[Value::Int(0)]);
    assert!(got.is_err(), "a bogus op name must Err; got {got:?}");
}

// ── (b) op-scoped requires over an OP-level type param: LOAD-rejected ─

/// PINS A CURRENT GAP. An op-scoped `requires Desc[PT]` over the operation's
/// OWN `[PT]` type param does not license the abstract spec-op call the way
/// the same clause over a SORT param does (`op_requires_covers_call` misses
/// it): the covered call is rejected at load with DispatchNoMatch. Both
/// binding spellings (`Desc[PT]`, `Desc[T = PT]`) fail identically. The
/// kernel spec (§5.4) says operation type parameters may appear in requires
/// positions, so this is a gap, not a rule.
#[test]
fn op_param_requires_is_rejected_at_load() {
    for req in ["requires Desc[PT]", "requires Desc[T = PT]"] {
        let src = with_instances(
            "wi817.opparam",
            &format!(
                "  sort Holder\n    operation probe[PT](x: PT) -> Int64 {req} = Desc.describe(x)\n    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())\n  end"
            ),
        );
        let errs = load_errs(&src);
        let text = errs.join("\n");
        assert!(
            text.contains("wi817.opparam.Desc.describe.dispatch")
                && text.contains("no impl matches"),
            "expected DispatchNoMatch on the covered describe call ({req}); got:\n{text}"
        );
    }
}

/// PINS THE SAME §5.4 GAP as the test above, at full scale: the op-param
/// CONTROL and WITNESS (mutual recursion via explicit per-call type
/// arguments, proposal 042) are rejected at load the same way — outcome (b)
/// for BOTH forms, at the same site (f's covered describe call), so the
/// lambda changes nothing. CORRECT would be: both load clean and evaluate
/// (drive → 1, 12, 122, …); when the op-param gap closes, this pin flips.
#[test]
fn op_param_control_and_witness_rejected_identically() {
    let control = with_instances(
        "wi817.control",
        r#"  sort Poly
    operation f[FT](n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else g[FT](n, x)
    operation g[GT](n: Int64, x: GT) -> Int64 requires Desc[GT] =
      f[Wrap[A = GT]](sub(n, 1), wrap(x))
    operation drive(n: Int64) -> Int64 = f[Leaf](n, leaf())
  end"#,
    );
    let witness = with_instances(
        "wi817.lam",
        r#"  sort Poly
    operation apply_fn[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
    operation f[FT](n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else g[FT](n, x)
    operation g[GT](n: Int64, x: GT) -> Int64 requires Desc[GT] =
      apply_fn[Wrap[A = GT]](lambda w -> f[Wrap[A = GT]](sub(n, 1), w), wrap(x))
    operation drive(n: Int64) -> Int64 = f[Leaf](n, leaf())
  end"#,
    );
    for (label, src, ns) in [("control", &control, "wi817.control"), ("witness", &witness, "wi817.lam")] {
        let errs = load_errs(src);
        let text = errs.join("\n");
        assert!(
            text.contains(&format!("{ns}.Desc.describe.dispatch")) && text.contains("no impl matches"),
            "{label}: expected DispatchNoMatch at f's describe; got:\n{text}"
        );
    }
}

// ── op-scoped requires over a SORT param ─────────────────────────────

/// The BASELINE that works: op-scoped requires over a sort param, simple
/// concrete binding (`probe(leaf())`). Serves via value-directed eval
/// (WI-562 licensing) — no dictionary involved.
#[test]
fn op_scoped_sort_param_simple_concrete_works() {
    let src = with_instances(
        "wi817.v1",
        r#"  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(leaf())
  end"#,
    );
    let got = eval_fresh(&src, "wi817.v1.Driver.drive", 0);
    assert!(matches!(got, Ok(Value::Int(1))), "expected Ok(Int(1)); got {got:?}");
}

/// PINS A CURRENT DEFECT — outcome (c). One conditional level
/// (`probe(wrap(leaf()))`), no recursion, no lambda: loads clean, then dies
/// at eval. Value-directed dispatch finds `WrapDesc.describe` from the wrap
/// value, but pushes its frame WITHOUT the impl's own `requires Desc[T = E]`
/// dictionary, so the body's inner describe read fails. CORRECT would be
/// Ok(Int(12)).
#[test]
fn op_scoped_single_conditional_level_dies_unbound() {
    let src = with_instances(
        "wi817.v6",
        r#"  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(wrap(leaf()))
  end"#,
    );
    let got = eval_fresh(&src, "wi817.v6.Driver.drive", 0);
    match got {
        Err(anthill_core::eval::EvalError::Internal(ref msg)) => assert!(
            msg.contains("__req_desc") && msg.contains("not bound"),
            "expected the unbound-__req_desc message (CURRENT DEFECT; correct = Ok(Int(12))); got {msg}"
        ),
        other => panic!(
            "expected Err(Internal(unbound __req_desc)) (CURRENT DEFECT; correct = Ok(Int(12))); got {other:?}"
        ),
    }
}

/// PINS A CURRENT DEFECT — outcome (c), CONTROL and WITNESS identical. The
/// mutual recursion on op-scoped sort-param requires: depth 0 works (no
/// changed type yet), depth ≥ 1 dies at the same unbound-dictionary read —
/// with the lambda leg (witness) and without it (control), indistinguishably.
/// CORRECT would be drive(1) = 12, drive(2) = 122.
#[test]
fn op_scoped_recursion_control_and_lambda_witness_fail_identically() {
    let control = with_instances(
        "wi817.v4",
        r#"  sort FHolder
    sort FT = ?
    operation f(n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    operation g(n: Int64, x: GT) -> Int64 requires Desc[GT] =
      FHolder.f(sub(n, 1), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    let witness = with_instances(
        "wi817.v7",
        r#"  sort Applier
    operation apply_fn[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
  end
  sort FHolder
    sort FT = ?
    operation f(n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    operation g(n: Int64, x: GT) -> Int64 requires Desc[GT] =
      Applier.apply_fn(lambda w -> FHolder.f(sub(n, 1), w), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    for (label, src, ns) in [("control", &control, "wi817.v4"), ("witness", &witness, "wi817.v7")] {
        let entry = format!("{ns}.Driver.drive");
        // One interpreter for both depths: the trapped call is the LAST one,
        // so the poisoning footgun (a trapped call breaks LATER calls on the
        // same interpreter) cannot bite, and the second stdlib load is saved.
        let mut interp = crate::common::interp_for(src);
        let d0 = interp.call(&entry, &[Value::Int(0)]);
        assert!(matches!(d0, Ok(Value::Int(1))), "{label} drive(0): expected Ok(Int(1)); got {d0:?}");
        let d1 = interp.call(&entry, &[Value::Int(1)]);
        match d1 {
            Err(anthill_core::eval::EvalError::Internal(ref msg)) => assert!(
                msg.contains("__req_desc") && msg.contains("not bound"),
                "{label} drive(1): expected the unbound-__req_desc message (CURRENT DEFECT; correct = Ok(Int(12))); got {msg}"
            ),
            other => panic!(
                "{label} drive(1): expected Err(Internal(unbound __req_desc)) (CURRENT DEFECT; correct = Ok(Int(12))); got {other:?}"
            ),
        }
    }
}

// ── SORT-level requires ──────────────────────────────────────────────

/// The requires-eval-path hazard SETTLED: sort-level requires + a
/// CONDITIONAL instance at a concrete compound binding works end-to-end —
/// the call site resolves `Desc[Wrap[Leaf]]` to the nested
/// `construct_requirement(WrapDesc, [Leaf])` tree and eval expands it
/// correctly (12 = 10·1 + 2). Neither error spelling reported in the ticket
/// (`projection index 0 out of range` / `UnknownOperation`) reproduces here.
#[test]
fn sort_level_single_conditional_level_is_correct() {
    let src = with_instances(
        "wi817.v8",
        r#"  sort Holder
    sort HT = ?
    requires Desc[HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(wrap(leaf()))
  end"#,
    );
    let got = eval_fresh(&src, "wi817.v8.Driver.drive", 0);
    assert!(matches!(got, Ok(Value::Int(12))), "expected Ok(Int(12)); got {got:?}");
}

/// PINS A CURRENT DEFECT — outcome (d), SILENTLY WRONG ANSWER, the worst
/// case, CONTROL and WITNESS identical. Sort-level requires + the mutual
/// recursion: loads clean, evaluates, and returns 1 AT EVERY DEPTH — the
/// caller's `Desc[GT]` dictionary is forwarded UNCHANGED into f's
/// `Desc[FT := Wrap[GT]]` slot (the Strategy-1 wildcard forward — see the
/// module header for the mechanism), so the final describe dispatches the
/// LEAF impl on a WRAPPED value. The conditional
/// instance is never consulted. CORRECT would be drive(1) = 12,
/// drive(2) = 122 (proven reachable by the V8 pin above). The lambda leg
/// changes nothing: the closure faithfully restores its creation scope, and
/// the creation scope already holds the wrong dictionary.
#[test]
fn sort_level_recursion_silently_wrong_control_and_lambda_identical() {
    let control = with_instances(
        "wi817.v9",
        r#"  sort FHolder
    sort FT = ?
    requires Desc[FT]
    operation f(n: Int64, x: FT) -> Int64 =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    requires Desc[GT]
    operation g(n: Int64, x: GT) -> Int64 =
      FHolder.f(sub(n, 1), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    let witness = with_instances(
        "wi817.v10",
        r#"  sort Applier
    operation apply_fn[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
  end
  sort FHolder
    sort FT = ?
    requires Desc[FT]
    operation f(n: Int64, x: FT) -> Int64 =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    requires Desc[GT]
    operation g(n: Int64, x: GT) -> Int64 =
      Applier.apply_fn(lambda w -> FHolder.f(sub(n, 1), w), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    for (label, src, ns) in [("control", &control, "wi817.v9"), ("witness", &witness, "wi817.v10")] {
        let entry = format!("{ns}.Driver.drive");
        // One interpreter for all three depths: every call is asserted Ok
        // (no trap ever occurs), so the poisoning footgun does not apply and
        // two of the three stdlib loads are saved.
        let mut interp = crate::common::interp_for(src);
        for (n, wrong_today, correct) in [(0, 1, 1), (1, 1, 12), (2, 1, 122)] {
            let got = interp.call(&entry, &[Value::Int(n)]);
            assert!(
                matches!(got, Ok(Value::Int(v)) if v == wrong_today),
                "{label} drive({n}): pinning TODAY'S value Ok(Int({wrong_today})) \
                 (CURRENT DEFECT for n ≥ 1; correct = {correct}); got {got:?}"
            );
        }
    }
}

// ── Multi-hop: lambda relayed through ops holding DIFFERENT dicts ────

/// PINS A CURRENT DEFECT — and one correct half. The lambda is created under
/// one dictionary (Desc[Leaf], describe→1) and RELAYED through two further
/// operations that each hold their OWN, DIFFERENT `Desc` dictionary
/// (Desc[Pebble], describe→5) before being invoked two frames from its
/// creation scope. Every requirement binding is CONCRETE, so this isolates
/// the dictionary-FLOW question from the changed-type recursion.
///
/// Value coding, CORRECT = 551: invoke = fn(0) + 10·describe(pebble)
/// = 1 + 50 = 51; relay = invoke + 100·describe(pebble) = 51 + 500 = 551
/// (a hop-dict leak INTO the closure would read 555).
///
/// MEASURED TODAY = 111 = 1 + 10·1 + 100·1, which decomposes as:
///   - fn(0) = 1 — the CLOSURE IS CORRECT: it reads its creation dictionary
///     even two frames away (creation-scope capture holds through the chain);
///   - each hop's OWN describe reads 1, not 5 — the MAKER's Leaf dictionary
///     is FORWARDED into Relay's and Invoker's frames over each call site's
///     concrete Pebble resolution. Same Strategy-1 wildcard-forward defect as
///     the recursion pins, here proven to hit ALL-CONCRETE bindings whenever
///     the caller holds a same-spec wildcard `requires` (the V8 pin works
///     only because its driver holds NO requires, so Strategy 3 is reached).
///     wi419 measured the 2-covering-entries disambiguation; the SOLE-entry
///     different-instantiation forward was unmeasured — and is wrong.
#[test]
fn lambda_relay_chain_closure_correct_but_hop_dicts_forwarded() {
    let src = format!(
        r#"
namespace wi817.hops
  import anthill.prelude.{{Int64, Bool, Function}}
{INSTANCES}
  sort Pebble
    entity pebble
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end

  sort Invoker
    sort IT = ?
    requires Desc[IT]
    operation invoke(fn: Function[A = Int64, B = Int64], z: IT) -> Int64 =
      add(fn(0), mul(10, Desc.describe(z)))
  end

  sort Relay
    sort RT = ?
    requires Desc[RT]
    operation relay(fn: Function[A = Int64, B = Int64], y: RT) -> Int64 =
      add(Invoker.invoke(fn, y), mul(100, Desc.describe(y)))
  end

  sort Maker
    sort MT = ?
    requires Desc[MT]
    operation make(x: MT) -> Int64 =
      Relay.relay(lambda ignored -> Desc.describe(x), pebble())
  end

  sort Driver
    operation drive(n: Int64) -> Int64 = Maker.make(leaf())
  end
end
"#
    );
    let got = eval_fresh(&src, "wi817.hops.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(111))),
        "pinning TODAY'S value Ok(Int(111)) = correct closure (1) + hop dicts \
         wrongly forwarded (10 + 100) — CURRENT DEFECT; correct = 551; got {got:?}"
    );
}

/// THE SEARCHED CASE (user framing), measured — and the answer INVERTS the
/// sort-level twin above. The relay chain's requirements are OP-SCOPED and
/// their instantiation CHANGES at each hand-off (make holds Desc[Leaf],
/// relay/invoke each hold Desc[Pebble]); the sort-based mechanism can only
/// pass a dictionary AS IS, which the twin above shows arrives WRONG (111).
/// This op-scoped spelling measures the CORRECT 551 TODAY — but NOT because
/// the op-scoped supply works (it supplies nothing; see the unbound pins):
/// every describe here resolves VALUE-DIRECTED — the runtime value itself
/// picks Leaf/Pebble.describe, no dictionary is ever consulted — so the
/// changed instantiation is served by the values. The two channels fail on
/// COMPLEMENTARY shapes: dict-directed pass-as-is is wrong the moment the
/// instantiation changes; value-directed no-supply is right until a
/// dictionary is semantically REQUIRED (a conditional impl's own chain),
/// where it dies unbound. WI-822's supply channel must KEEP this 551 green.
#[test]
fn op_scoped_relay_chain_correct_via_value_direction() {
    let src = format!(
        r#"
namespace wi817.ophops
  import anthill.prelude.{{Int64, Bool, Function}}
{INSTANCES}
  sort Pebble
    entity pebble
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end

  sort Invoker
    sort IT = ?
    operation invoke(fn: Function[A = Int64, B = Int64], z: IT) -> Int64 requires Desc[IT] =
      add(fn(0), mul(10, Desc.describe(z)))
  end

  sort Relay
    sort RT = ?
    operation relay(fn: Function[A = Int64, B = Int64], y: RT) -> Int64 requires Desc[RT] =
      add(Invoker.invoke(fn, y), mul(100, Desc.describe(y)))
  end

  sort Maker
    sort MT = ?
    operation make(x: MT) -> Int64 requires Desc[MT] =
      Relay.relay(lambda ignored -> Desc.describe(x), pebble())
  end

  sort Driver
    operation drive(n: Int64) -> Int64 = Maker.make(leaf())
  end
end
"#
    );
    let got = eval_fresh(&src, "wi817.ophops.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(551))),
        "the op-scoped relay chain must compute 551 (today via value-directed \
         dispatch, no dictionaries; must SURVIVE the WI-822 supply channel); got {got:?}"
    );
}

/// TWO DESCRIBERS FOR ONE CARRIER (user requirement: with a single
/// describer the system just discovers the only candidate and pins it —
/// nothing about selection is tested). Providers for Desc[Pebble] in TWO
/// scopes: LoudDesc (describe→5) in wi817.tdl, QuietDesc (describe→7) in
/// wi817.tdq; a loud-scope op creates the lambda, a quiet-scope op invokes
/// it and describes the same value itself (scoped-correct would be
/// 5 + 10·7 = 75; both-loud 55; both-quiet 77).
///
/// PINS A CURRENT DEFECT (direction DECIDED — WI-648, modular typeclasses:
/// scoped/named non-canonical instances, SortedSet/sorted-Map-by-chosen-
/// comparator as its standing example). MEASURED: the
/// configuration is REJECTED AT LOAD — DispatchAmbiguous at BOTH describe
/// sites ("multiple impls match (coherence rule)") plus the global witness
/// check ("ambiguous witness: 2 distinct witness sorts provide ... (keep
/// exactly one)"): the implementation enforces GLOBAL
/// one-provider-per-carrier where kernel-language.md §Instance coherence
/// specifies SCOPED selection ("different scopes may resolve the same
/// Spec[carrier] to different providers, the per-import choice").
///
/// The global rule is the WRONG rule, and not merely a spec drift: an
/// algebraic-specification language must express Int carrying BOTH the
/// additive and the multiplicative monoid — two instances of one spec on
/// one carrier — and the VALUE cannot select between them (5 does not say
/// which group it is in); only a requirement/scope can. Today the stdlib
/// dodges Num-style (algebra.Ring bundles both operation families in one
/// spec). Until WI-648 lands, the provider-selection dimension of the
/// WI-816/817 question is unconstructible and dictionaries vary only along
/// the TYPE dimension (the polymorphic-recursion pins above). CORRECT
/// (WI-648 implement-phase acceptance): this program LOADS and computes 75 — lambda keeps
/// its creation-scope provider (5), the quiet hop uses its own (7);
/// 55/77 would betray a both-one-way selection.
#[test]
fn two_describers_for_one_carrier_rejected_globally() {
    let src = r#"
namespace wi817.tds
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Pebble
    entity pebble
  end
  sort Mk
    operation mk() -> Pebble = pebble()
  end
end

namespace wi817.tdq
  import anthill.prelude.{Int64, Function}
  import wi817.tds.{Desc, Pebble}
  sort QuietDesc
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 7
  end
  sort QuietOps
    operation invoke(fn: Function[A = Pebble, B = Int64], z: Pebble) -> Int64 =
      add(fn(z), mul(10, Desc.describe(z)))
  end
end

namespace wi817.tdl
  import anthill.prelude.{Int64, Function}
  import wi817.tds.{Desc, Pebble}
  import wi817.tdq.{QuietOps}
  sort LoudDesc
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort LoudOps
    operation run(z: Pebble) -> Int64 =
      QuietOps.invoke(lambda w -> Desc.describe(w), z)
  end
end

namespace wi817.tdd
  import anthill.prelude.{Int64}
  import wi817.tds.{Mk}
  import wi817.tdl.{LoudOps}
  sort Driver
    operation drive(n: Int64) -> Int64 = LoudOps.run(Mk.mk())
  end
end
"#;
    let errs = load_errs(src);
    let text = errs.join("\n");
    assert!(
        text.contains("multiple impls match")
            && text.contains("ambiguous witness: 2 distinct witness sorts provide"),
        "expected the global two-provider rejection (DispatchAmbiguous at the \
         describe sites + the ambiguous-witness check); got:\n{text}"
    );
}

/// PINS A CURRENT DEFECT — the essence-of-the-bug measurement (user
/// framing: every earlier fixture gave all operations the SAME singleton
/// set, so as-is frame inheritance and correct per-callee supply were
/// indistinguishable; the essence is that the SETS DIFFER and a hand-off
/// must REBUILD the callee's set). Caller a requires {Desc[AT]}; callee b
/// requires {Desc[BT], Tagd[BT]} — overlapping in Desc, disjoint in Tagd —
/// and the call instantiates BT := Pebble concretely while a holds
/// AT := Leaf. CORRECT: b(pebble) = 5 + 10·3 = 35, drive = 1 + 1000·35
/// = 35001.
///
/// MEASURED TODAY = 31001 = 1 + 1000·(1 + 10·3): in the SAME call, the
/// OVERLAPPING dep is wrong — a's Leaf dictionary is wildcard-forwarded
/// into b's Desc[BT := Pebble] slot, so describe(pebble) runs the LEAF
/// impl (1) — while the DISJOINT dep is correct — a has no Tagd entry to
/// falsely cover it, so Strategy 3 statically constructs the PebbleTag
/// dictionary (tag = 3). The callee's set is rebuilt exactly where the
/// caller's set does NOT overlap, and inherited as-is exactly where it
/// does. This is also live proof that the WI-821 σ-gate's fall-through
/// (Strategy-3 construction) already works in this shape — the gate only
/// needs to stop the overlap-forward. Flips to 35001 under WI-821.
#[test]
fn different_sets_overlapping_dep_forwarded_disjoint_dep_constructed() {
    let src = r#"
namespace wi817.dsets
  import anthill.prelude.{Int64, Bool}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tagd
    sort T = ?
    operation tag(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort PebbleTag
    fact Tagd[T = Pebble]
    operation tag(x: Pebble) -> Int64 = 3
  end

  sort BOps
    sort BT = ?
    requires Desc[BT]
    requires Tagd[BT]
    operation b(y: BT) -> Int64 = add(Desc.describe(y), mul(10, Tagd.tag(y)))
  end
  sort AOps
    sort AT = ?
    requires Desc[AT]
    operation a(x: AT) -> Int64 = add(Desc.describe(x), mul(1000, BOps.b(pebble())))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = AOps.a(leaf())
  end
end
"#;
    let got = eval_fresh(src, "wi817.dsets.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(31001))),
        "pinning TODAY'S value Ok(Int(31001)) = overlap dep forwarded wrong (1) + \
         disjoint dep constructed right (3) — CURRENT DEFECT; correct = 35001; got {got:?}"
    );
}

// ── Bonus hazard found while constructing the witness ────────────────

/// PINS A CURRENT DEFECT. With WrapDesc's `requires Desc[T = E]` REMOVED —
/// leaving an UNCONDITIONED parametric provider `fact Desc[T = Wrap[A = E]]`
/// with free `E` — the abstract `Desc.describe(x)` call inside f is silently
/// MIS-PINNED to `WrapDesc.describe` at load (var-var unification makes the
/// parametric head match the abstract binding; the WI-325 protection only
/// guards NoCandidates/NoMatch, not a bogus Unique). The program then dies at
/// eval doing `w.inner` on a `leaf` entity. A load-time rejection (or a
/// MissingRequires-style diagnostic) would be the sound behaviour.
#[test]
fn unconditioned_parametric_fact_mispins_abstract_call() {
    let src = with_instances(
        "wi817.v5",
        r#"  sort Poly
    operation f[FT](n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else g[FT](n, x)
    operation g[GT](n: Int64, x: GT) -> Int64 requires Desc[GT] =
      f[Wrap[A = GT]](sub(n, 1), wrap(x))
    operation drive(n: Int64) -> Int64 = f[Leaf](n, leaf())
  end"#,
    )
    .replace("    requires Desc[T = E]\n", "");
    assert!(!src.contains("requires Desc[T = E]"), "the conditional's requires must be removed");
    let got = eval_fresh(&src, "wi817.v5.Poly.drive", 0);
    match got {
        Err(anthill_core::eval::EvalError::Internal(ref msg)) => assert!(
            msg.contains("no field 'inner'"),
            "expected the mis-pin to die on field 'inner' (CURRENT DEFECT; sound = load rejection); got {msg}"
        ),
        other => panic!(
            "expected Err(Internal(no field 'inner')) (CURRENT DEFECT; sound = load rejection); got {other:?}"
        ),
    }
}
