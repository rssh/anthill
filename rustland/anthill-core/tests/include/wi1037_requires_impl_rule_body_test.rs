//! WI-1037 — a supplied spec-op implementation whose PARENT SORT declares
//! `requires` must be REACHED from the SLD path, not replaced by the spec's own
//! default.
//!
//! WI-1026 made a rule-body call on a defaulted spec op honour the typer's pin, but
//! only for `CallClass::PinNow`. `classify_pin_or_apply_within` writes
//! `ConcreteApplyWithin` instead the moment `sort_reads_requirement_slots(impl_sort)`
//! — exactly when the supplied implementation's own sort has `requires` — and the
//! decode answered `None` for it. `reduce_op_value` then kept the SPELLED functor,
//! which is the spec op, and folded ITS body: the DEFAULT.
//!
//! ## MEASURED BEFORE THE FIX, on the fixture below
//!
//! The ticket asserts two different current behaviours and says to establish which
//! fixture produces which before writing the arm. Both claims were checked; ONE of
//! them was already false when the work started.
//!
//! | fixture | before | after |
//! |---|---|---|
//! | defaulted spec op, RULE body | `1` — the DEFAULT | `7` |
//! | defaulted spec op, OP body | `DeferToRequirement: … `__req_tag` not bound` | `7` |
//! | abstract spec op, RULE body | **`7` already** | `7` |
//! | abstract spec op, OP body | **`7` already** | `7` |
//!
//! **The abstract rows were the ticket's own prediction and it is STALE.** It says an
//! abstract spec op "hits `op_body_node -> None -> return v` … so it never bridges at
//! all and the goal delays (answers `[]`)", and names that early return as a SECOND
//! site the fix must change. That was true when the ticket was filed and **WI-1057**
//! closed it in between, by giving a body-less spec op the eval bridge under
//! `body_less_dispatchable`. Verified rather than assumed: with WI-1057's arm alone
//! disabled (`None if false && dispatch_body_less && …`), `abstract / RULE BODY`
//! answers `[]` exactly as predicted, and restoring it brings back `7`. So part (c)
//! of the ticket's three-part fix was already delivered and this change is (a) + (b).
//!
//! ## Why the fix is a TYPE and not a wider `Option<Symbol>`
//!
//! `classified_apply_target` merged two questions — "which operation" and "may I
//! enter it bare" — and answered only the first. Widening it to name
//! `ConcreteApplyWithin` would have been a WRONG ANSWER, not a fix: the fold has no
//! frame, so it would inline a body whose `requires` slot nothing filled. The verdict
//! is now [`ApplyDispatch`], whose `NeedsDict` arm names the same impl `PinNow` would
//! AND says the caller owes it a dictionary. `reduce_op_value` reads it and declines
//! the fold; eval reads the same decode and is unchanged, because the two classes
//! needing a requirements channel are matched before its plain-apply arm.
//!
//! Both decodes are now EXHAUSTIVE over `CallClass` (no `_` arm), which is the
//! implementation guard WI-1037's review asked for: a sixth variant is a compile
//! error at both sites rather than a silent plain-apply of the spelled spec op.
//!
//! ## The bridge is what makes this an ANSWER rather than a delay
//!
//! `bridge_op_to_eval`'s own doc said the opposite — "only requirement-FREE ops
//! decide" (WI-625 gap 3) — and that has been stale since **WI-300 Tier B**:
//! `call_op_bridged` resolves REAL dictionaries at the concrete argument types via
//! `resolve_bridge_requirements`, so the impl's `Tag[G = Leaf]` is built from the
//! argument being `Leaf`. Residualize is the fallback for `Unresolvable`/`Ambiguous`
//! alone. The doc is corrected at the site.
//!
//! ## Naming the class also CREATED a hazard, caught by `/code-review`
//!
//! Once the decode names `ConcreteApplyWithin`, a site that carries that stamp
//! answers with the STATIC PIN — and `reduce_op_value`'s woven arm rebuilds a call
//! through `rebuilt_expr`, which carries the stamp verbatim. So a woven call, whose
//! whole point is that the CALLER's dictionary selects the member, would have had
//! that choice overridden by the pin. While the decode answered `None` for the class
//! the rebuild fell through to its own functor — the dictionary's target — and won by
//! accident. The arm now re-stamps `PinNow(dictionary target)`, and
//! `a_rebuilt_call_carries_the_pin_so_the_woven_arm_must_restamp` drives both halves.
//!
//! ## What fails when this is backed out — MEASURED, not predicted
//!
//! | test | backed out |
//! |---|---|
//! | `a_rule_body_reaches_a_requires_declaring_impl` | **FAILS** — answers `1` |
//! | `an_operation_body_reaches_a_requires_declaring_impl` | **FAILS** — internal-error assert |
//! | `a_rebuilt_call_carries_the_pin_so_the_woven_arm_must_restamp` | see its own doc |
//! | `an_abstract_spec_op_reaches_it_from_both_sites` | ok — **WI-1057** owns it |
//! | `a_carrier_with_no_supplier_still_runs_the_default` | ok — by design |
//! | `an_unbound_carrier_answers_nothing_rather_than_the_default` | ok — by design |
//!
//! The last three pass either way deliberately. The abstract row is here because the
//! ticket named it as work and it is not; the other two are the controls this refusal
//! must not consume — a default must still fill a GAP, and an undecidable call must
//! still decline rather than fall back to the default.
//!
//! REFERENCE: WI-1026; WI-1057; WI-444; WI-300 Tier B; WI-415's `dispatch_dict` doc;
//! `docs/design/requirement-channel.md`.

/// The shape `classify_pin_or_apply_within` writes `ConcreteApplyWithin` for: the
/// supplied implementation `LeafDesc.describeLeaf` lives in a sort that declares
/// `requires`, and reaching its answer means resolving that requirement — so `7`
/// can only come from the impl actually RUNNING with a dictionary, never from a
/// lucky structural fold. The spec's default is `1`, so the two are distinguishable
/// (a test whose default and impl agreed would measure nothing).
///
/// `desc_body` is `" = 1"` for the DEFAULTED spec op and `""` for the ABSTRACT one.
fn program(ns: &str, desc_body: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64{desc_body}
  end

  sort Tag
    sort G = ?
    operation tagval(x: G) -> Int64
  end

  sort Leaf
    entity leaf
    fact Tag[G = Leaf]
    operation tagval(x: Leaf) -> Int64 = 7
  end

  sort LeafDesc
    sort L = ?
    requires Tag[G = L]
    operation describeLeaf(x: L) -> Int64 = Tag.tagval(x)
  end

  fact Desc[T = Leaf, describe = LeafDesc.describeLeaf]

{tail}end
"#
    )
}

/// The rule-body spelling — the path this ticket owns.
const RULE: &str = "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n";
/// The same call inside an OPERATION body, driven through a rule so one helper
/// answers both. Not a redundant spelling: it reaches the callee by a different
/// route (the enclosing op is bridged whole), and before this change that route
/// raised an internal-error assert.
const OP: &str = "  operation probe() -> Int64 = Desc.describe(leaf())\n  \
                  rule answer(?r) :- probe(?r)\n";

/// The single definite `Int` answer of `{ns}.answer`. Panics on any other shape,
/// `[]` included: "the query returned nothing" is a symptom this cluster exists to
/// stop, so it must never read as a pass.
fn answer(ns: &str, src: &str) -> i64 {
    use anthill_core::eval::Value;
    let mut kb = crate::common::load_kb_with(src);
    let qn = format!("{ns}.answer");
    match crate::common::query_unary(&mut kb, &qn).as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`{qn}` must answer exactly one definite Int, got {other:?}\n{src}"),
    }
}

/// THE HEADLINE. Backed out: answers `1`, the spec's default, with the supplied
/// implementation invisible — WI-444/WI-1010's rule ("defaults fill GAPS, they do
/// not SHADOW") absent from the SLD path for exactly the impls that carry a
/// `requires`.
#[test]
fn a_rule_body_reaches_a_requires_declaring_impl() {
    let ns = "test.wi1037.rule";
    assert_eq!(
        answer(ns, &program(ns, " = 1", RULE)),
        7,
        "a rule body must reach the supplied impl even when its parent sort declares \
         `requires` — the dictionary is resolvable at the concrete argument type",
    );
}

/// The same call reached through an OPERATION body. This one is NOT a duplicate
/// spelling: the enclosing op is bridged whole, so the inner call would otherwise
/// ride that bridge and be started by eval's `start_apply_same_sort` with the
/// classification's `dispatch_dict` — which is `None` for a cross-sort call from a
/// namespace-level caller (WI-415's recorded gap). Backed out, this raises
/// `DeferToRequirement: requirement param `__req_tag` not bound in caller frame` and
/// trips `bridge_op_to_eval`'s internal-error `debug_assert`.
///
/// That is why the resolver bridges a `NeedsDict` callee at EVERY depth while the
/// two arms beside it stay `depth == 0`: their premise is that the enclosing bridge
/// covers nested calls, and for this class it does not.
#[test]
fn an_operation_body_reaches_a_requires_declaring_impl() {
    let ns = "test.wi1037.op";
    assert_eq!(
        answer(ns, &program(ns, " = 1", OP)),
        7,
        "an operation body must reach the same impl the rule body does",
    );
}

/// THE ROW THE TICKET NAMED AS WORK AND IS NOT. Passes either way — **WI-1057**
/// closed it by giving a body-less spec op the eval bridge. Kept because the ticket
/// says to measure the abstract fixture and state its behaviour at the test site,
/// and because a later change to `body_less_dispatchable` would land here first.
///
/// Verified as WI-1057's and not this ticket's: with that arm alone disabled the
/// rule-body half answers `[]` and this assertion fails; with THIS ticket backed out
/// instead, both halves still answer `7`.
#[test]
fn an_abstract_spec_op_reaches_it_from_both_sites() {
    for (label, tail) in [("rule", RULE), ("op", OP)] {
        let ns = format!("test.wi1037.abs{label}");
        assert_eq!(
            answer(&ns, &program(&ns, "", tail)),
            7,
            "an ABSTRACT spec op has no default to fall back to; the {label} spelling \
             must dispatch to the supplied impl",
        );
    }
}

/// THE CONTROL THIS MUST NOT CONSUME: a carrier with NO supplier still runs the
/// spec's default. This is every defaulted spec-op call in the tree and it is what
/// makes a default a default. Passes either way, by design.
///
/// Reached by deleting the instance fact, so `Desc.describe` has no candidate at all
/// and the call is never classified — the `Unclassified` arm, which keeps the
/// spelled functor and folds `1`.
#[test]
fn a_carrier_with_no_supplier_still_runs_the_default() {
    let ns = "test.wi1037.gap";
    let src = program(ns, " = 1", RULE).replace(
        "  fact Desc[T = Leaf, describe = LeafDesc.describeLeaf]\n",
        "",
    );
    assert!(
        !src.contains("fact Desc["),
        "the fixture must really have no supplier"
    );
    assert_eq!(
        answer(ns, &src),
        1,
        "no supplier — the spec's default must still run"
    );
}

/// THE OTHER CONTROL: an UNBOUND carrier must not be answered by the default either.
/// The bridge requires deeply-ground arguments, so it declines, the call stays
/// un-reduced, and the WI-938 hook refuses to `unify` on an undecided call — the
/// WI-483 leave-uninterpreted outcome. Measured as `[]`, and asserted as "not a
/// definite answer" rather than as an empty list, because what must never happen is
/// a CONFIDENT `1`.
///
/// Passes either way by design: backed out, the goal folds the default over an
/// unbound argument and still fails to reduce. It is here so that any later widening
/// of the bridge's ground gate has to come and state what this row became.
#[test]
fn an_unbound_carrier_answers_nothing_rather_than_the_default() {
    let ns = "test.wi1037.unbound";
    let src = program(ns, " = 1", "  rule answer(?r) :- Desc.describe(?x, ?r)\n");
    let mut kb = crate::common::load_kb_with(&src);
    let sols = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    assert!(
        !sols
            .iter()
            .any(|(v, definite)| *definite && matches!(v, anthill_core::eval::Value::Int(1))),
        "an unbound carrier must not be answered with the spec's default: {sols:?}",
    );
}

/// THE PRECEDENCE THE WOVEN ARM RESTS ON, driven at the mechanism rather than
/// through a program — because the mechanism is what makes the hazard real and a
/// program exhibiting it may not exist today.
///
/// Found by `/code-review` on this change. `reduce_op_value`'s `Expr::ApplyWithin`
/// arm does not RETURN a decision; it rebuilds the call as an `Expr::Apply` on the
/// member the dictionary selected and RECURSES. `rebuilt_expr` carries the typer
/// stamps verbatim, `CallClass` included — so the rebuilt node arrives at the
/// `Expr::Apply` decode still carrying whatever the SPEC-op site said.
///
/// While the decode answered `None` for `ConcreteApplyWithin` that was harmless: the
/// callee fell to the rebuilt functor, which IS the dictionary's target, so the
/// dictionary won by accident. The moment the decode names that class — this
/// ticket — the carried static pin would OVERRIDE the dictionary's choice, inverting
/// what the weave exists for. The arm therefore re-stamps.
///
/// Asserted in two halves, because only together do they say why the re-stamp is
/// needed: (1) the carry is REAL, so a rebuild really would arrive pinned; (2) the
/// re-stamp is what makes the dictionary's target the answer. Delete the
/// `set_classification` call in the woven arm and half (1) is exactly what the
/// recursion would then read.
#[test]
fn a_rebuilt_call_carries_the_pin_so_the_woven_arm_must_restamp() {
    use anthill_core::kb::node_occurrence::{ApplyDispatch, Expr, NodeOccurrence};
    use anthill_core::kb::typing::CallClass;
    use anthill_core::span::{SourceId, SourceSpan};

    let ns = "test.wi1037.restamp";
    let mut kb = crate::common::load_kb_with(&program(ns, " = 1", RULE));
    let spec = kb
        .try_resolve_symbol(&format!("{ns}.Desc.describe"))
        .expect("spec op");
    let pinned = kb
        .try_resolve_symbol(&format!("{ns}.LeafDesc.describeLeaf"))
        .expect("impl");
    let dict_choice = kb
        .try_resolve_symbol(&format!("{ns}.Leaf.tagval"))
        .expect("other member");
    assert_ne!(
        pinned, dict_choice,
        "the two routes must name DIFFERENT operations"
    );

    let site = NodeOccurrence::new_expr(
        Expr::Apply {
            functor: spec,
            pos_args: Vec::new(),
            named_args: Vec::new(),
            type_args: Vec::new(),
        },
        SourceSpan::new(SourceId::from_raw(0), 0, 0),
        None,
    );
    site.set_classification(CallClass::ConcreteApplyWithin {
        fn_target_sym: pinned,
        callee_spec_sort: kb
            .try_resolve_symbol(&format!("{ns}.Desc"))
            .expect("spec sort"),
        spec_op_sym: spec,
        enclosing_sort: None,
        resolved_tree: None,
        dispatch_dict: None,
    });

    // (1) the carry is real — a plain rebuild on the DICTIONARY's target still
    //     decodes to the PIN, which is the override the woven arm must prevent.
    let rebuilt = site.rebuilt_expr(Expr::Apply {
        functor: dict_choice,
        pos_args: Vec::new(),
        named_args: Vec::new(),
        type_args: Vec::new(),
    });
    assert_eq!(
        rebuilt.apply_dispatch(),
        ApplyDispatch::NeedsDict(pinned),
        "rebuilt_expr carries the CallClass, so an un-restamped rebuild names the \
         static pin and not the member the dictionary chose",
    );

    // (2) the re-stamp is what makes the dictionary's choice the answer.
    rebuilt.set_classification(CallClass::PinNow {
        spec_op_sym: spec,
        impl_op_sym: dict_choice,
    });
    assert_eq!(
        rebuilt.apply_dispatch(),
        ApplyDispatch::Pin(dict_choice),
        "after the woven arm re-stamps, the dictionary's target is what reduces",
    );
}
