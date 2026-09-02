//! WI-1036 — should WI-1026's rule-body spec-op dispatch also cover a BUILTIN-MAPPED
//! defaulted spec op? **DECIDED: YES — the `!is_builtin` clause is DELETED**, and this
//! file is the driver that decides it, because the suite cannot: the workspace is green
//! with the clause and without it.
//!
//! THE EXCLUSION'S TWO STATED REASONS WERE BOTH FALSE. WI-1026's feedback refuted the
//! first (`reduce_op_value` reads the pin BEFORE the builtin early-return, not after).
//! `a_rule_body_classification_emits_no_dispatch_rewrite` refutes the second: a rule-body
//! classification emits NO dispatch rewrite at all, so widening cannot emit "60 new
//! rewrites" — `req_insertion::run` walks `kb.op_bodies_iter()`, and a rule body is not
//! an operation body. (The rewrite is diagnostic-only anyway since WI-248: the runtime
//! reads `CallClass` off the `NodeOccurrence`.)
//!
//! WHAT THE CLAUSE WITHHELD, and neither is about the pin — each has a test here:
//!
//!   * **the 058 §3.7 tie refusal** — a carrier supplying one of these ops TWICE was
//!     refused at load from an operation body and ACCEPTED from a rule body. One program,
//!     two verdicts, decided by where the call is written;
//!   * **§3.1 dispatch by value in OPERAND position** — a rule-body operand on a carrier
//!     with a supplied override answered an indefinite residual instead of the override.
//!     The pin IS readable there: the carrier's own `gt` is an ordinary bodied operation,
//!     so "both sides are builtin" was only ever true of the STDLIB family.
//!
//! COST, measured at the acting arm of `dispatch_calls_in_occ`: FOUR newly decided sites
//! on a stdlib + host-bindings load (2 × `PartialOrd.gt`, 1 × `lt`, 1 × `gte` — all in
//! stdlib rule bodies, since the count is the same with an empty user file), five with
//! `anthill-testcases`, none added by `examples/github-todo` or `anthill-todo`. Counted
//! by functor; the individual sites were not located, so none is named. The ticket's 60
//! counted something else and is not reproducible at this commit. All four are
//! GOAL-position calls pinned to `Int64.gt` / `Float.gt`, both builtins, so
//! `reduce_op_value` returns early exactly as before — the corpus gets the refusal, not a
//! dispatch change.
//!
//! WHAT IS STILL BROKEN AND IS NOT THIS GATE'S — see
//! `a_supplied_override_of_a_builtin_mapped_spec_op_is_unreachable_from_a_rule_body_goal`.
//! Deleting the clause does not fix the GOAL-position silence, and its owner is **WI-879**.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

/// WI-1026's own fixture, minus everything not needed to observe a dispatch rewrite: a
/// DEFAULTED spec op whose carrier supplies an implementation by a WI-431 instance fact.
/// `Desc.describe` is NOT builtin, so the WI-1026 arm fires on it — this file's subject is
/// what that firing produces, not whether it fires.
fn describe_program(tail: &str) -> String {
    crate::wi1026_rule_body_spec_op_dispatch_test::program(
        "wi1036.rewrite",
        "",
        "\n  operation leafDescribe(x: Leaf) -> Int64 = 7\n\n  \
         fact Desc[T = Leaf, describe = leafDescribe]\n",
        tail,
    )
}

/// Dispatch rewrites recorded against `qn` as their ORIGINAL spec op — the
/// `dispatch_origin` half of `record_apply_rewrite`, which is what the WI-218 tests
/// observe and what the ticket expected widening to add 60 of.
fn rewrites_naming(kb: &KnowledgeBase, qn: &str) -> usize {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("no symbol `{qn}`"));
    kb.dispatch_origin_iter().filter(|(_, s)| *s == sym).count()
}

/// THE OBSERVER THE TICKET ASKED FOR, and it reports an ABSENCE. One classified call,
/// two positions: in an operation body it produces a dispatch rewrite; in a rule body it
/// produces none. Both calls are classified — the rule-body one is exactly what WI-1026
/// delivered and `wi1026_rule_body_spec_op_dispatch_test` proves answers `7` — so this is
/// not "the rule body was not typed", it is `req_insertion::run` walking
/// `kb.op_bodies_iter()` and a rule body not being an operation body.
///
/// THE RULE-BODY ARM ASSERTS THE ANSWER TOO, and that is what stops its `0` from passing
/// for the wrong reason: `7` is the SUPPLIED implementation, which only a classified call
/// reaches (unclassified, WI-1026 measured `1`, the spec's default). So the two assertions
/// together say "classified AND no rewrite", not "no rewrite because nothing happened".
///
/// CONTROL: this ticket changes no code, so every assertion here is a pin rather than a
/// diff, and what would flip each is what it is for. The op-body `1` flips to `0` if the
/// rewrite recorder or this observer breaks. The rule-body `7` flips to `1` if WI-1026's
/// classification regresses. The rule-body `0` flips to `1` the day `req_insertion::run`
/// walks rule bodies — which is the day this ticket's cost argument must be re-made.
#[test]
fn a_rule_body_classification_emits_no_dispatch_rewrite() {
    let op_kb = crate::common::load_kb_with(&describe_program(
        "  operation probe() -> Int64 = Desc.describe(leaf())\n",
    ));
    assert_eq!(
        rewrites_naming(&op_kb, "wi1036.rewrite.Desc.describe"),
        1,
        "an OPERATION body's classified spec-op call must emit its dispatch rewrite",
    );

    let rule_tail = "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n";
    assert_eq!(
        crate::wi1026_rule_body_spec_op_dispatch_test::answer(
            "wi1036.rewrite",
            &describe_program(rule_tail),
        ),
        7,
        "the rule body must reach the SUPPLIED impl (WI-1026) — otherwise the rewrite \
         count below would be zero because nothing was classified",
    );
    let rule_kb = crate::common::load_kb_with(&describe_program(rule_tail));
    assert_eq!(
        rewrites_naming(&rule_kb, "wi1036.rewrite.Desc.describe"),
        0,
        "a RULE body's classified call emits NO dispatch rewrite — `req_insertion::run` \
         walks operation bodies. Widening the walk trigger therefore cannot emit \
         the rewrites WI-1036 was filed over",
    );
}

/// THE BOUND ON WHAT DELETING THE CLAUSE CHANGES FOR THE CORPUS — a pin is stamped at
/// the four newly-decided stdlib sites, and it redirects nothing, because both the
/// spelled spec op and the impls it names are registered builtins and `reduce_op_value`
/// returns early on either. So the corpus behaviour change is the load REFUSAL the other
/// two tests drive, not a dispatch redirect in the stdlib's `gt(?i, 0)` goals.
///
/// STATED AS A BOUND, NOT AS THE REASON, because the reason was wrong that way round:
/// "every carrier impl a pin would redirect to is a builtin" is true of THIS family and
/// false of the population — `wi1036.own.Point.gt` below is an ordinary bodied operation,
/// and the operand-position test measures exactly the redirect that follows from it.
///
/// CONTROL: this passes with the clause and without it (nothing here depends on the
/// clause — it is the bound, and the two drivers are what depend on it). It fails when a
/// carrier in the stdlib family stops being builtin-backed on either side — WI-879's
/// registry rewrite is that change — at which point the corpus DOES get a dispatch
/// redirect and this comment's bound has to be re-measured.
#[test]
fn the_stdlib_family_is_builtin_on_both_sides_of_the_pin() {
    let kb = crate::common::load_kb_with("namespace wi1036.tags\nend\n");
    let builtin = |qn: &str| {
        let s = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("no symbol `{qn}`"));
        kb.is_builtin(s)
    };
    for short in ["gt", "gte", "lt", "lte"] {
        assert!(
            builtin(&format!("anthill.prelude.PartialOrd.{short}")),
            "`PartialOrd.{short}` is the spelled functor of the newly-decided sites",
        );
        for carrier in ["Int64", "Float"] {
            assert!(
                builtin(&format!("anthill.prelude.{carrier}.{short}")),
                "`{carrier}.{short}` is what their pins name; if it is not a builtin, \
                 `reduce_op_value` stops returning early and the corpus gets a dispatch \
                 redirect this ticket did not measure",
            );
        }
    }
}

/// A carrier that provides `PartialOrd` and SUPPLIES ITS OWN `gt`. The override answers
/// `false` for every pair, so the three candidate implementations are told apart by their
/// answer: the carrier's own member `false`, the spec's DEFAULT body (derived from
/// `WeakOrd.compare`) `true`, the resolver's `builtin_cmp` on two entities neither.
fn own_gt_program(tail: &str) -> String {
    format!(
        r#"namespace wi1036.own
  import anthill.prelude.{{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}}
  -- WI-909: the `tail` fixtures write a bare `unify(?r, …)` — a WRITTEN CALL, not the
  -- `<=>` operator's mint — and `unify` left `kb::load::PRELUDE_QUALIFIED` when it took
  -- an address. A written name takes an import; only the OPERATOR needs nothing. Same
  -- migration KD9SW made for `gt` / `eq` and the other ten spec operations.
  import anthill.kernel.{{unify}}

  sort Point
    import anthill.prelude.{{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}}
    entity pt(x: Int64, y: Int64)

    provides PartialEq[Point]
    provides Eq[Point]
    provides PartialOrd[Point]
    provides Ord[Point]

    operation eq(a: Point, b: Point) -> Bool =
      match a
        case pt(ax, ay) ->
          match b
            case pt(bx, by) ->
              if PartialEq.eq(ax, bx) then PartialEq.eq(ay, by) else false

    operation compare(a: Point, b: Point) -> Int64 =
      match a
        case pt(ax, ay) ->
          match b
            case pt(bx, by) ->
              let c = WeakOrd.compare(ax, bx)
              if PartialEq.eq(c, 0) then WeakOrd.compare(ay, by) else c

    -- THE SUPPLIED OVERRIDE, deliberately disagreeing with the derived default so the
    -- answer says which implementation ran.
    operation gt(a: Point, b: Point) -> Bool = false
  end

{tail}end
"#
    )
}

/// The answers of `wi1036.own.answer`, rendered — `Value` carries no `PartialEq`, and a
/// rendered row makes the three candidate implementations readable in a failure message.
fn own_gt_answer(tail: &str) -> String {
    let mut kb = crate::common::load_kb_with(&own_gt_program(tail));
    let rows = crate::common::query_unary(&mut kb, "wi1036.own.answer");
    if rows.is_empty() {
        return "[]".to_string();
    }
    rows.iter()
        .map(|(v, definite)| match v {
            Value::Bool(b) if *definite => b.to_string(),
            other => format!("{other:?} (definite = {definite})"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// THE ONE HOLE DELETING THE CLAUSE DOES NOT CLOSE, PINNED WITH ITS OWNER.
/// `PartialOrd.gt(pt(2,1), pt(1,9))` on a carrier that supplies its own `gt` answers the
/// override (`false`) from an operation body and NOTHING from a rule-body GOAL.
///
/// MEASURED BOTH WAYS, which is what says it is not this ticket's: with the clause and
/// without it the goal answers `[]`. The call IS classified now and the pin IS stamped
/// (`PartialOrd.gt -> wi1036.own.Point.gt`, observed at `classify_pin_or_apply_within`) —
/// and never read, because a goal takes `BuiltinTag::Gt` off its SPELLED functor and no
/// goal-position reader consults a pin; `builtin_cmp` then fails silently on two
/// entities. **WI-879 owns that** — its acceptance is that such a comparison "either
/// answers correctly or raises, never silently fails".
///
/// CONTROL: the operation-body arm fails if the WI-444 supplied-override pin regresses.
/// The rule-body arm fails when WI-879 lands, which is the intended flip and the reason
/// it is named here. The OPERAND-position sibling above is the contrast that makes this a
/// position gap rather than a rule-body one: same carrier, same override, same rule — and
/// in operand position the pin IS read.
#[test]
fn a_supplied_override_of_a_builtin_mapped_spec_op_is_unreachable_from_a_rule_body_goal() {
    let from_op_body = own_gt_answer(
        "  operation probe() -> Bool = PartialOrd.gt(pt(2, 1), pt(1, 9))\n\
         \n  rule answer(?r) :- unify(?r, probe())\n",
    );
    assert_eq!(
        from_op_body, "false",
        "an OPERATION body reaches the carrier's supplied `gt` (WI-444): `false`, not the \
         spec default's `true`",
    );

    let from_rule_goal =
        own_gt_answer("  rule answer(?r) :- PartialOrd.gt(pt(2, 1), pt(1, 9), ?r)\n");
    assert_eq!(
        from_rule_goal, "[]",
        "PINNED DEFECT, owner WI-879: the same call as a rule-body GOAL answers nothing — \
         the goal takes `BuiltinTag::Gt` off the spelled functor and `builtin_cmp` fails \
         silently on two entities. Deleting `!is_builtin` did NOT change this (measured): \
         the pin is stamped and no goal-position reader consults it. When WI-879 makes \
         this answer `false`, or raise, this assertion is the one to update",
    );
}

/// **THE DRIVER THE TICKET ASKED FOR: it fails when the clause is restored.** A carrier
/// supplying `gt` TWICE — its own member and a WI-431 instance fact — is an 058 §3.7
/// ambiguity, and §3.7 does not say "unless the call is written in a rule body".
///
/// MEASURED with the clause in place: the operation body refuses at load and the rule
/// body LOADS CLEAN. That is the whole of what the clause bought, it was in neither
/// reason WI-1026 gave for it, and it is why the clause goes.
///
/// CONTROL: restore `!kb.is_builtin(f)` at `call_dispatch_shape` and this test's
/// second assertion fails (driven, not predicted — the program loads clean and the query
/// answers nothing). The operation-body assertion passes either way BY DESIGN: it is the
/// both-ways half that says the two positions now agree, and it fails only if WI-1012's
/// refusal itself regresses.
#[test]
fn a_rule_body_tie_on_a_builtin_mapped_spec_op_refuses_at_load() {
    const RIVAL: &str = "\n  operation otherGt(a: Point, b: Point) -> Bool = true\n\n  \
                         fact PartialOrd[T = Point, gt = otherGt]\n";
    let refusal = |tail: String| match crate::common::try_load_kb_with(&own_gt_program(&tail)) {
        Ok(_) => None,
        Err(errs) => Some(errs.join(" | ")),
    };

    let from_op_body = refusal(format!(
        "  operation probe() -> Bool = PartialOrd.gt(pt(2, 1), pt(1, 9))\n{RIVAL}"
    ))
    .expect("an operation body refuses a two-supplier tie at load (WI-1012)");
    assert!(
        from_op_body.contains("ambiguous dispatch of `anthill.prelude.PartialOrd.gt`"),
        "unexpected operation-body refusal: {from_op_body}",
    );

    let from_rule_body = refusal(format!(
        "  rule answer(?r) :- PartialOrd.gt(pt(2, 1), pt(1, 9), ?r)\n{RIVAL}"
    ))
    .expect(
        "WI-1036: the SAME tie named in a rule body must refuse too — with the \
         `!is_builtin` clause it loaded clean, so one program was refused in an operation \
         body and accepted in a rule body",
    );
    assert!(
        from_rule_body.contains("ambiguous dispatch of `anthill.prelude.PartialOrd.gt`")
            && from_rule_body.contains("wi1036.own.Point"),
        "the rule-body refusal must be the same refusal, naming the carrier: \
         {from_rule_body}",
    );
}

/// **THE SECOND DRIVER: §3.1 in OPERAND position.** The same carrier and override, in a
/// rule-body operand rather than a goal — where `reduce_op_value` DOES read the pin, and
/// where `wi1036.own.Point.gt` being an ordinary bodied operation makes the pin
/// consequential (the stdlib family's impls are builtins; this population's need not be).
///
/// CONTROL: restore the clause and this fails — the call is unclassified, `op` falls back
/// to the spelled `PartialOrd.gt`, which IS a builtin, so the fold declines and the
/// operand stays an indefinite residual (measured: `Term { .. } (definite = false)`).
#[test]
fn a_supplied_override_reaches_a_rule_body_operand() {
    assert_eq!(
        own_gt_answer("  rule answer(?r) :- unify(?r, PartialOrd.gt(pt(2, 1), pt(1, 9)))\n"),
        "false",
        "a rule-body OPERAND on a carrier with a supplied override must fold to the \
         override (058 §3.1); unclassified it is an indefinite residual",
    );
}
