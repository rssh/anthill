//! WI-879 — the resolver's builtin registry is FACT-DRIVEN, and `builtin_cmp` no longer
//! fails silently on operands it cannot compare.
//!
//! THE TWO HALVES, and they are two because WI-876 could only move one of them.
//!
//! (1) THE REGISTRY. `KnowledgeBase::register_builtin_tags` runs BEFORE `load_all`, so it
//! cannot read facts — and WI-876 and WI-880 therefore hand-wrote a `(qualified name ->
//! BuiltinTag)` array for the scalar carriers (sixteen comparisons, nine arithmetic
//! entries), hand-synced with four `.anthill` files in another crate, plus two lines beside
//! it for `Int64.div` / `Int64.mod`. Those twenty-seven rows are now DERIVED post-load
//! (`load::derive_carrier_builtin_tags`) by MIRRORING each spec op's tag onto the carrier
//! members a binding block gave a host implementation — and the derivation yields THIRTY,
//! which is the measurement: `BigInt.div`, `Float.div` and `BigInt.mod` were never in the
//! array, so those goals stopped computing in a rule body while `Int64.div` answered.
//!
//! (2) THE COMPARISON. `builtin_cmp` read NUMERIC operands only (`value_num`: Int / BigInt
//! / Float) and returned `BuiltinResult::Failure` on anything else. So an SLD
//! `PartialOrd.gt("b", "a")` yielded NO SOLUTIONS — indistinguishable from `"b" <= "a"` —
//! while the same comparison in an operation body answered `true`. One program, two
//! engines, opposite answers. It now reads every ORDERED LITERAL through the view
//! (`value_ord`, the set eval's `value_compare` already answered), and a pair it still has
//! no order for is UNDECIDED and traced, never a silent false.
//!
//! Reference: `docs/design/058-implementation.md` §10; kb/mod.rs `register_builtin_tags`;
//! kb/load.rs `derive_carrier_builtin_tags`; kb/resolve.rs `builtin_cmp` / `value_ord`.

use anthill_core::kb::KnowledgeBase;

/// A rule body holding `goals`, answering `?r` from `unify` so a SUCCESS is one definite
/// row and a FAILURE is none. `unify` is written, so it takes an import (WI-909).
fn probe(goals: &str) -> String {
    format!(
        "namespace wi879.probe\n  \
           import anthill.prelude.{{Int64, BigInt, Float, String, Bool, PartialOrd, \
             Divisible, EuclideanDomain}}\n  \
           import anthill.kernel.{{unify}}\n\n  \
         rule answer(?r) :- {goals}\nend\n"
    )
}

/// The rows of `wi879.probe.answer`, rendered so a failure message says which of the three
/// outcomes happened: a definite value, an UNDECIDED residual (WI-879's new arm — the row
/// exists and `definite` is false), or nothing at all.
fn answer(goals: &str) -> String {
    let mut kb = crate::common::load_kb_with(&probe(goals));
    rows_of(&mut kb, "wi879.probe.answer")
}

/// Rendered CARRIER-NEUTRALLY, through `TermView::as_literal`. A builtin's computed result
/// arrives as a hash-consed `Value::Term(Const)` while a written literal arrives native, so
/// a `match` on the `Value` variant reports `Term` for exactly the rows this file measures
/// — which is how the first draft of `the_derived_arithmetic_…` test read a working
/// `Float.div` as a failure.
fn rows_of(kb: &mut KnowledgeBase, qn: &str) -> String {
    use anthill_core::kb::term::Literal;
    use anthill_core::kb::term_view::TermView;
    let rows = crate::common::query_unary(kb, qn);
    if rows.is_empty() {
        return "[]".to_string();
    }
    rows.iter()
        .map(|(v, definite)| {
            if !definite {
                return "UNDECIDED".to_string();
            }
            match v.as_literal(kb) {
                Some(Literal::Int(n)) => n.to_string(),
                Some(Literal::BigInt(n)) => n.to_string(),
                Some(Literal::Float(f)) => format!("{}", f.into_inner()),
                Some(Literal::String(s)) => format!("{s:?}"),
                Some(Literal::Bool(b)) => b.to_string(),
                None => format!("non-literal {}", v.type_name()),
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

// ── (2) the comparison ─────────────────────────────────────────────────────────

/// **THE TICKET'S HEADLINE ACCEPTANCE.** An SLD comparison of two STRINGS answers, and
/// answers CORRECTLY — both directions, which is what tells "compares strings" from
/// "always succeeds".
///
/// CONTROL, RUN: restore `builtin_cmp`'s numeric-only read (`value_ord` refusing
/// `String`/`Bool`, `NoOrder` returning `Failure`) and SIX of this file's eight tests fail,
/// plus `wi1036…::a_supplied_override_of_a_builtin_mapped_spec_op_is_unreachable_from_a_
/// rule_body_goal`. The two that pass are the derivation's own —
/// `the_mirror_declines_three_members_it_must_not_tag` and
/// `the_derived_arithmetic_closes_a_gap_the_array_had` — which is the split that says the
/// two halves of this ticket are independent. Within this test the `gt("b","a")` row goes to
/// `[]` while `gt("a","b")` stays `[]` — the PAIR is what pins the direction. The `Int64`
/// row passes either way BY DESIGN: it is the both-ways half saying the numeric comparison
/// this widening rides on was not disturbed.
#[test]
fn an_sld_string_comparison_answers_and_answers_correctly() {
    assert_eq!(
        answer("PartialOrd.gt(\"b\", \"a\"), unify(?r, 1)"),
        "1",
        "`\"b\" > \"a\"` is TRUE, and before WI-879 the resolver answered nothing — \
         `builtin_cmp` read numeric operands only and returned Failure on a string pair",
    );
    assert_eq!(
        answer("PartialOrd.gt(\"a\", \"b\"), unify(?r, 1)"),
        "[]",
        "`\"a\" > \"b\"` is FALSE; without this row the test above would pass on a \
         comparison that merely stopped refusing",
    );
    assert_eq!(
        answer("PartialOrd.lt(\"a\", \"b\"), unify(?r, 1)"),
        "1",
        "`lt` is the spelling the ticket's acceptance names",
    );
    assert_eq!(
        answer("PartialOrd.lte(\"a\", \"a\"), unify(?r, 1)"),
        "1",
        "the non-strict pair reads the EQUAL ordering, which a `Failure`-on-non-numeric \
         comparison could never reach",
    );
    assert_eq!(
        answer("PartialOrd.gt(3, 1), unify(?r, 1)"),
        "1",
        "CONTROL, both ways by design: the numeric comparison is undisturbed",
    );
}

/// `Bool` is the other literal eval's `value_compare` orders and the resolver did not.
/// `false < true`.
///
/// CONTROL, RUN: back out `value_ord`'s `Bool` arm and the first row goes to `[]`; the
/// second stays `[]` either way and is what says the order is the right way round.
#[test]
fn an_sld_bool_comparison_answers() {
    assert_eq!(
        answer("PartialOrd.gt(true, false), unify(?r, 1)"),
        "1",
        "`true > false`, the order `value_compare` has always given eval",
    );
    assert_eq!(
        answer("PartialOrd.gt(false, true), unify(?r, 1)"),
        "[]",
        "and not the other way round",
    );
}

// ── (1) the registry ───────────────────────────────────────────────────────────

/// **THE DERIVATION, DRIVEN**, and the spelling matters — the 2-ARY form would measure
/// NOTHING. MEASURED with the derivation disabled: `String.gt("b", "a")` as a two-place
/// goal still answers, because a tag-LESS body-less Bool operation is read as its
/// relational view (§5, `bare_bodied_bool_relation`) and decided through the eval bridge.
/// It is the RESULT-COLUMN form that needs the tag: at three positional args the
/// relational reading is declined at the operation's declared arity, so with no tag the
/// goal has no clauses and answers nothing.
///
/// CONTROL, RUN: neutralize the `derive_carrier_builtin_tags(kb)` call in
/// `load_phase_inner` and every `{carrier}.gt(…, ?r)` row here goes to `[]`. FOUR tests
/// fail on that back-out: this one, `the_derived_arithmetic_closes_a_gap_the_array_had`,
/// `a_new_carriers_binding_block_is_enough`, and — the one that is not this file's —
/// `wi1036…::the_stdlib_family_is_builtin_on_both_sides_of_the_pin`, which asserts
/// `is_builtin` for eight of the carrier members the deleted array used to register. The
/// `PartialOrd.gt` rows pass either way BY DESIGN: that is the spec op, still registered in
/// `register_builtin_tags`, and they are here to say that deleting the carrier array did
/// not take the generic caller's comparison with it.
#[test]
fn a_carrier_member_gets_its_tag_from_the_binding_block() {
    for (carrier, a, b) in [
        ("String", "\"b\"", "\"a\""),
        ("Int64", "3", "1"),
        ("Float", "3.0", "1.0"),
        ("BigInt", "?big3", "?big1"),
    ] {
        // `BigInt` literals come from a conversion, not from source.
        let pre = if carrier == "BigInt" {
            "BigInt.to_bigint(3, ?big3), BigInt.to_bigint(1, ?big1), "
        } else {
            ""
        };
        assert_eq!(
            answer(&format!("{pre}{carrier}.gt({a}, {b}, ?r)")),
            "true",
            "`{carrier}.gt` is host-mapped and overrides `PartialOrd.gt`, so the mirror \
             gives it `BuiltinTag::Gt`",
        );
        assert_eq!(
            answer(&format!("{pre}{carrier}.gt({b}, {a}, ?r)")),
            "false",
            "and it COMPUTES the comparison rather than merely answering",
        );
    }
    assert_eq!(
        answer("PartialOrd.gt(3, 1, ?r)"),
        "true",
        "CONTROL, both ways by design: the SPEC-op registrations stay — a bare `gt` \
         written outside a scalar carrier resolves there",
    );
    assert_eq!(
        answer("PartialOrd.gt(1, 3, ?r)"),
        "false",
        "CONTROL for the control: the spec op computes too",
    );
}

/// **THE GAP THE HAND-WRITTEN ARRAY HAD.** `BigInt.div`, `Float.div` and `BigInt.mod` were
/// never in it, though `builtin_arith`'s `Div` fills the Int, BigInt AND Float slots and
/// its `Mod` fills Int and BigInt. So these goals stopped computing in a rule body while
/// `Int64.div` — the one line somebody remembered to write — answered. Nothing said so.
///
/// CONTROL, RUN: neutralize the derivation and the three rows this ticket adds go to `[]`;
/// the `Int64` rows go to `[]` too, since their hand-written lines are deleted with the
/// array.
#[test]
fn the_derived_arithmetic_closes_a_gap_the_array_had() {
    assert_eq!(
        answer("Float.div(7.0, 2.0, ?r)"),
        "3.5",
        "NEW: `Float.div` had no tag, so this goal answered nothing",
    );
    assert_eq!(
        answer("BigInt.to_bigint(7, ?a), BigInt.to_bigint(2, ?b), BigInt.div(?a, ?b, ?r)"),
        "3",
        "NEW: `BigInt.div` had no tag either",
    );
    assert_eq!(
        answer("BigInt.to_bigint(7, ?a), BigInt.to_bigint(2, ?b), BigInt.mod(?a, ?b, ?r)"),
        "1",
        "NEW: `BigInt.mod` — `builtin_arith`'s `Mod` has always filled the BigInt slot",
    );
    assert_eq!(
        answer("Int64.div(7, 2, ?r)"),
        "3",
        "the one the array DID hold, now derived from the same `operation_map` entry",
    );
    assert_eq!(answer("Int64.mod(7, 2, ?r)"), "1", "likewise");
}

/// **THE THREE THINGS THE MIRROR MUST *NOT* TAG**, each a distinct condition of the
/// derivation, and each one a wrong answer if the condition were dropped.
///
/// TWO CONTROLS, BOTH RUN, and this is the only test in the file either one moves — which
/// is why the conditions are asserted here rather than left to the driven tests:
///   * ADD a short-name lookup beside the `directly_provided_specs` walk (`anthill.kernel.
///     <short>`, the namespace holding the free-operation tags) and the CONDITION 3
///     assertion fails: `Bool.not` becomes `BuiltinTag::Not`, negation-as-failure.
///   * REPLACE the `host_op_mappings` population with `sorts_and_own_ops` — condition 1
///     backed out — and the CONDITION 1 assertion fails: `Point.gt`, an ordinary anthill
///     body, gets `BuiltinTag::Gt` and `builtin_cmp` shadows it.
/// Every other test in this file passes under both back-outs.
#[test]
fn the_mirror_declines_three_members_it_must_not_tag() {
    let kb = crate::common::load_kb_with(&own_gt_program());
    let builtin = |qn: &str| {
        let s = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("no symbol `{qn}`"));
        kb.is_builtin(s)
    };
    assert!(
        !builtin("anthill.prelude.Bool.not"),
        "CONDITION 3 — the spec op must be reached through a spec the CARRIER PROVIDES, \
         never by a short-name match: `anthill.kernel.not` is `BuiltinTag::Not` \
         (negation-as-failure) and `Bool`'s binding maps a member spelled `not`. `Bool` \
         provides `PartialEq`/`Eq` and neither declares `not`, so nothing leads there",
    );
    assert!(
        !builtin("wi879.own.Point.gt"),
        "CONDITION 1 — the `operation_map` entry is the enablement. `Point.gt` is an \
         ordinary anthill body; tagging it would make `builtin_cmp` SHADOW the body it \
         was written to run",
    );
    assert!(
        !builtin("anthill.prelude.Int64.compare"),
        "AN UNTAGGED SPEC OP DERIVES NOTHING: `Int64.compare` is host-mapped like its \
         four ordering neighbours, but `Ordered.compare` carries no tag (the resolver has \
         no `compare` primitive), so the mirror correctly gives it none",
    );
    assert!(
        builtin("anthill.prelude.Int64.divExact"),
        "AND THE ONE HAND-WRITTEN CARRIER ENTRY THAT STAYS, for the reason that makes the \
         mirror a mirror: `divExact` is an Int64-only ALIAS declared by no spec, so there \
         is nothing to mirror — its line in `register_builtin_tags` is load-bearing",
    );
}

/// **THE ACCEPTANCE SENTENCE, ON A NAME THE RUST LIST NEVER HELD**: "adding
/// `operation_map { lt: … }` to a new carrier's binding is enough". `Tick` declares a
/// body-less `lt`, provides `PartialOrd`, and names a host function for `lt` in its binding
/// block — and NOTHING else. That is the whole of what a carrier now does to reach the
/// resolver's comparison primitive; before WI-879 it also took an edit to a `&'static str`
/// array in `kb/mod.rs`.
///
/// THE ANSWER IS THE WITHHELD ONE, and that is the fixture exercising both halves at once:
/// `Tick`'s values are ENTITIES, which `builtin_cmp` has no order for, so the routed goal
/// residualizes rather than claiming `false`. The trace observed at this fixture names the
/// DERIVED functor — `` `wi879.newc.Tick.lt` has no order for this operand pair (tick and
/// tick) `` — which is what says the tag reached a brand-new name rather than some
/// neighbouring reading answering by accident.
///
/// CONTROL, RUN: the `unmapped` arm is the same program with the `operation_map` clause
/// replaced by a `carrier` one — no mapping, no mirror, and the goal answers `[]`. It is
/// the control the stdlib carriers cannot be: their members are mapped in files this test
/// does not write. This test also fails on the OTHER half's back-out (restore the
/// numeric-only comparison and the mapped arm goes to `[]` too), which is what "exercises
/// both halves" means here — it is not a control for either half ALONE, and the two tests
/// that are appear in the derivation control above.
#[test]
fn a_new_carriers_binding_block_is_enough() {
    let program = |entry: &str| {
        format!(
            r#"namespace wi879.newc
  import anthill.prelude.{{Int64, Bool, PartialOrd, PartialEq, WeakOrd, Ord}}
  import anthill.kernel.{{unify}}

  sort Tick
    import anthill.prelude.{{Int64, Bool, PartialOrd, PartialEq, WeakOrd, Ord}}
    entity tick(v: Int64)
    operation eq(a: Tick, b: Tick) -> Bool = true
    -- BODY-LESS: its implementation is the host's, named below and nowhere else.
    operation lt(a: Tick, b: Tick) -> Bool
    provides PartialEq[T = Tick]
    provides PartialOrd[T = Tick]
  end

  provides Tick language rust
    artifact "nowhere.rs"
    {entry}
  end

  rule answer(?r) :- Tick.lt(tick(1), tick(2), ?r)
end
"#
        )
    };
    let rows = |entry: &str| {
        let mut kb = crate::common::load_kb_with(&program(entry));
        rows_of(&mut kb, "wi879.newc.answer")
    };
    assert_eq!(
        rows("operation_map { lt: \"ordered_lt\" }"),
        "UNDECIDED",
        "the mapping alone routes `Tick.lt` to the resolver's comparison primitive, which \
         then withholds an answer for two entities — one row, `definite = false`",
    );
    assert_eq!(
        rows("carrier { Tick: \"i64\" }"),
        "[]",
        "CONTROL: the same program with no `operation_map` derives no tag, so the \
         three-place goal has no clauses and answers nothing",
    );
}

/// **THE TWO-ENGINE DIVERGENCE THIS TICKET EXISTS FOR, both sides in one file.** The same
/// string comparison, written twice: once in an OPERATION BODY (eval) and once as a
/// rule-body GOAL (SLD). Before WI-879 the first answered `true` and the second answered
/// nothing.
///
/// CONTROL, RUN, and it came out exactly this way: restore `builtin_cmp`'s numeric-only
/// read and the GOAL row alone fails, `[]` against `true`. The operation-body row passes
/// either way BY DESIGN — eval's `value_compare` has always ordered strings, and it is the
/// row that says which of the two engines was wrong.
#[test]
fn the_two_engines_now_agree_on_a_string_comparison() {
    let mut kb = crate::common::load_kb_with(
        "namespace wi879.eng\n  \
           import anthill.prelude.{String, Bool, PartialOrd}\n  \
           import anthill.kernel.{unify}\n\n  \
         operation sgt() -> Bool = PartialOrd.gt(\"b\", \"a\")\n\n  \
         rule from_body(?r) :- unify(?r, sgt())\n  \
         rule from_goal(?r) :- PartialOrd.gt(\"b\", \"a\", ?r)\nend\n",
    );
    assert_eq!(
        rows_of(&mut kb, "wi879.eng.from_body"),
        "true",
        "EVAL has always answered this — `value_compare` orders strings",
    );
    assert_eq!(
        rows_of(&mut kb, "wi879.eng.from_goal"),
        "true",
        "and SLD now answers the same. It used to answer NOTHING, indistinguishably from \
         `\"b\" <= \"a\"`: one program, two engines, opposite answers",
    );
}

// ── the three defects /code-review found in this ticket's own first draft ──────

/// **A NaN OPERAND IN THE THREE-PLACE FORM.** IEEE says every partial comparison over NaN
/// is false, and eval's `float_gt` says `false` — but this ticket's first draft returned
/// `BuiltinResult::Failure` from the `Unordered` arm, which jumped PAST the result column it
/// had just added. So `Float.gt(nan, 1.0, ?r)` answered NOTHING while `Float.gt(1.0, 2.0,
/// ?r)` answered `false`: two spellings of false, observably different, in the very form the
/// fix introduced — and the WI-645 acceptance (resolver == interpreter == codegen on Float)
/// broken by the fix. Raised by /code-review.
///
/// THE NaN COMES FROM `Float.div(0.0, 0.0, ?n)`, and that is the reachable route rather
/// than a convenience: the float `Div` slot is `|a, b| Some(a / b)` with NO zero guard (its
/// int and bigint siblings have one), so IEEE division produces the value. The `Float.nan`
/// CONST does not work here — measured, a rule-body `nan` stays an unforced `Value::Node`
/// and lands in the no-order arm instead, which is a separate pre-existing thing about
/// consts in SLD and not this ticket's.
///
/// CONTROL, RUN: restore `OrdVerdict::Unordered => return BuiltinResult::Failure` and all
/// three 3-place rows go to `[]`. The 2-place row passes either way BY DESIGN — it is the
/// row that says IEEE's `false` still FAILS a test, which is what a stdlib guard needs.
#[test]
fn a_nan_operand_answers_false_in_the_result_column() {
    let src = "namespace wi879.nan\n  \
                 import anthill.prelude.{Float, Bool, PartialOrd, Divisible}\n  \
                 import anthill.kernel.{unify}\n\n  \
               rule gt3(?r) :- Float.div(0.0, 0.0, ?n), Float.gt(?n, 1.0, ?r)\n  \
               rule lte3(?r) :- Float.div(0.0, 0.0, ?n), Float.lte(?n, 1.0, ?r)\n  \
               rule gt2(?r) :- Float.div(0.0, 0.0, ?n), Float.gt(?n, 1.0), unify(?r, 7)\n  \
               rule plain3(?r) :- Float.gt(1.0, 2.0, ?r)\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        rows_of(&mut kb, "wi879.nan.gt3"),
        "false",
        "IEEE: `nan > 1.0` is FALSE, and the result column must carry it — eval's \
         `float_gt` answers `false` for exactly this pair",
    );
    assert_eq!(
        rows_of(&mut kb, "wi879.nan.lte3"),
        "false",
        "the NON-STRICT comparison is false over NaN too; `Unordered` is not `Equal`",
    );
    assert_eq!(
        rows_of(&mut kb, "wi879.nan.gt2"),
        "[]",
        "CONTROL, both ways by design: at TWO args an IEEE-false comparison still FAILS \
         the test — a stdlib guard's whole content",
    );
    assert_eq!(
        rows_of(&mut kb, "wi879.nan.plain3"),
        "false",
        "and the ordinary false is the same `false`, which is the point: before the fix \
         these two rows were `[]` and `false`",
    );
}

/// **A CROSS-SORT LITERAL PAIR REACHES THE RESOLVER, from a program that LOADS.** This
/// ticket's first draft asserted it could not — "`PartialOrd.lt(a: T, b: T)` cannot type
/// it" — and /code-review measured that false: a rule variable bound by a predicate that
/// declares no argument types has no stamped type, so the typer has nothing to refuse.
///
/// The answer is UNDECIDED, and the point of the finding was the DIAGNOSIS: the message
/// used to send the reader after ordering dispatch, which would not have helped an
/// ill-typed comparison. `OrdVerdict` now separates the two causes and the trace observed
/// at this fixture reads `` `anthill.prelude.PartialOrd.gt` compares String against Int64 —
/// two DIFFERENT literal sorts ``.
///
/// CONTROL, RUN: the second arm is the same comparison written DIRECTLY, which the typer
/// does refuse — so the pair says the escape is the untyped variable and not the
/// comparison. Fold `SortMismatch` back into `NoOrder` and the answer here does not change;
/// what changes is the message, which is why this test also asserts the load.
#[test]
fn a_cross_sort_literal_pair_is_undecided_and_diagnosed() {
    let via_untyped_var = "namespace wi879.mix\n  \
                             import anthill.prelude.{Int64, String, Bool, PartialOrd}\n  \
                             import anthill.kernel.{unify}\n\n  \
                           fact tag(\"a\")\n  \
                           rule answer(?r) :- tag(?x), PartialOrd.gt(?x, 1), unify(?r, 5)\nend\n";
    let mut kb = crate::common::load_kb_with(via_untyped_var);
    assert_eq!(
        rows_of(&mut kb, "wi879.mix.answer"),
        "UNDECIDED",
        "a `String` against an `Int64` has no common order, so the goal withholds a \
         verdict — it used to answer `[]`, claiming `\"a\" <= 1`",
    );

    let written_directly = "namespace wi879.mix2\n  \
                              import anthill.prelude.{Int64, String, Bool, PartialOrd}\n\n  \
                            rule answer(?r) :- PartialOrd.gt(\"a\", 1, ?r)\nend\n";
    let errs = crate::common::try_load_kb_with(written_directly)
        .err()
        .unwrap_or_else(|| panic!("the DIRECTLY written mismatch must be a load error"));
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "CONTROL: the typer refuses the pair wherever it can SEE the operand types — which \
         is what made the first draft's claim look true. Got: {errs:?}",
    );
}

/// **AN EAGER GUARD MUST NOT DECIDE FROM A COMPARISON THAT NEVER RAN.** The `NoOrder` arm's
/// whole justification for delaying instead of failing is that a NAF/guard consumer reading
/// an empty result as refutation would decide from nothing — and this ticket's first draft
/// returned a plain `delay()`, which protects only `step_naf`. The three EAGER consumers
/// (`eval_negation_guard`, `eval_forall_guard`, the counting-quantifier config) resolve with
/// `definite_only: true`, so the residual never reaches them and
/// `GuardStatus::from_emptiness` reads the empty result as a verdict unless `truncated` is
/// set. Raised by /code-review; the arm now sets it.
///
/// CONTROL, RUN: change the arm back to `BuiltinResult::delay()` and this program LOADS
/// CLEAN with one registered guard — the constraint reporting HOLDS off a comparison that
/// produced no answer. That measurement is the finding.
#[test]
fn an_eager_constraint_guard_cannot_decide_from_a_comparison_with_no_order() {
    let src = r#"namespace wi879.guard
  import anthill.prelude.{Int64, Bool, PartialOrd, PartialEq, Eq}

  sort Pt
    import anthill.prelude.{Int64, Bool, PartialOrd, PartialEq, Eq}
    entity p(v: Int64)
    provides PartialEq[T = Pt]
    provides PartialOrd[T = Pt]
    operation eq(a: Pt, b: Pt) -> Bool = true
  end

  fact has(p(1))
  fact has(p(2))

  constraint no_bigger: no ?x: has(?x) -: PartialOrd.gt(?x, ?x)
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("the constraint must not be DECIDED from a comparison that answered nothing");
    assert!(
        errs.iter()
            .any(|e| e.contains("no_bigger") && e.contains("undecidable")),
        "the guard must report the constraint UNDECIDABLE. (Its message says \"within the \
         resolver depth budget\", which is imprecise for this cause — nothing was cut short \
         — and is why the arm also traces the real one.) Got: {errs:?}",
    );
}

/// WI-1036's `Point`: a carrier that provides `PartialOrd` and supplies its own `gt` as an
/// anthill body. Kept here (rather than reached across files) because the two conditions
/// above need it in the same KB as the stdlib carriers.
fn own_gt_program() -> String {
    r#"namespace wi879.own
  import anthill.prelude.{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
  import anthill.kernel.{unify}

  sort Point
    import anthill.prelude.{Int64, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
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

    operation gt(a: Point, b: Point) -> Bool = false
  end

  rule answer(?r) :- PartialOrd.gt(pt(2, 1), pt(1, 9), ?r)
end
"#
    .to_string()
}

/// **THE SILENT FAILURE, NOW UNDECIDED.** `PartialOrd.gt` over two ENTITIES is a pair the
/// resolver has no order for. It used to answer `[]` — a definite refutation of a
/// comparison that never happened, which a NAF or constraint guard reading emptiness as
/// falsity would then decide from. It now residualizes: the row comes back with
/// `definite = false`, and the trace says why.
///
/// NOT `false`, WHICH WOULD BE THE *CORRECT* ANSWER (the carrier supplies `gt = false`,
/// and WI-1036 measured an operation body reaching it). Reaching it from goal position
/// needs ORDERING DISPATCH — the analogue of `sem_eq_dispatch` — which this ticket does
/// not build and WI-20260909-SM910 owns. What WI-879 does is stop the engine from claiming
/// the opposite.
///
/// CONTROL, RUN: restore `BuiltinResult::Failure` in the `NoOrder` arm and this row goes
/// back to `[]`. It is ALSO the row `wi1036…::a_supplied_override_of_a_builtin_mapped_spec_
/// op_is_unreachable_from_a_rule_body_goal` pins from the other side; that test named this
/// ticket as its owner and its assertion moved with this change.
#[test]
fn a_comparison_with_no_order_is_undecided_not_false() {
    let mut kb = crate::common::load_kb_with(&own_gt_program());
    assert_eq!(
        rows_of(&mut kb, "wi879.own.answer"),
        "UNDECIDED",
        "an operand pair `builtin_cmp` has no order for suspends as a WI-519 residual; \
         before WI-879 it was an indistinguishable `Failure`",
    );
}
