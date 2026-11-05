//! WI-1040 — `require[X]` brought a requirement dictionary into a rule clause's
//! scope, so a body call that needs one can be PASSED it instead of only being
//! checked against it.
//!
//! ## Since proposal 060.1 §5
//!
//! `require[X]`, `?d = require[X]` and `requires(X)` are removed. A clause declares its
//! requirement as an operation does — a type parameter on the head's introducer and a guard
//! at it, `rule via[A](?x: A, ?r) :- Desc[T = A]` — and its dictionary is read as the written
//! one was (`find_dictionary(…, out: ?d, carrier_type: true)`) and woven into the calls at
//! its carrier. A call that writes no instance names the requirement it reads, `require d:
//! Desc[T = A]` and `d.name(?r)`. The rows below drive the same capabilities through those
//! spellings and check the answers the dictionary gives; the table that follows was measured
//! on the removed forms. Rows whose subject was the removed form itself went with it or were
//! turned to the form that replaces it: the named spelling is the call through a name, the
//! check-only spelling the guard, the two refusals the guard's own (an introducer no column
//! names) and the removed form's. A dictionary handed through a rule HEAD went with every
//! column a dictionary could ride; a caller's requirement crosses a goal instead, and a
//! citation that would hand a clause a dictionary at another carrier is refused at load.
//!
//! Design: `docs/design/requirement-channel.md`; surface: proposal 060 §1.
//!
//! Three spellings, three distinct things — and the third and fourth are what this
//! file drives:
//!
//! ```text
//!   sort S requires Eq[T] … end             -- DECLARES a slot        (untouched)
//!   p(?x,?y) :- requires(Eq[T]), eq(?x,?y)  -- CHECKS                 (WI-300)
//!   p(?x,?y) :- require[Eq[T]], eq(?x,?y)   -- DENOTES: in clause scope
//!   p(?x,?y) :- ?d = require[Eq[T]], f(?d)  -- …and names it
//! ```
//!
//! All three lower to one kernel relation, `anthill.kernel.find_dictionary`.
//! `require[X]` reads it with an OUTPUT: `find_dictionary(spec, op, args…, out: ?d)`.
//! `out` is a NAMED argument on purpose — the converter's idempotence gate, the
//! typer sweep's, and the resolver arm's argument reads are all POSITIONAL, so a
//! goal without one is byte-identical to what WI-300 delivered. That is how
//! acceptance (f) ("the arity-1 `requires(X)` form behaves exactly as before")
//! holds STRUCTURALLY rather than by re-testing the WI-300 suite here.
//!
//! ## What the dictionary IS — ONE representation
//!
//! `?d` binds to `Dictionary(sub₀ … subₙ₋₁, impl: S)`: the EXACT shape WI-1019's
//! `TermView` announces for an eval `RequirementHandle`, built through the same
//! `dictionary_view_syms` pair so producer and reader cannot drift. That is
//! `requirement-channel.md` §9's rule — one functor, one key set, one comparison —
//! and it is what the binding test below asserts. Storage is a separate question the
//! rule does not decide; this path builds an ordinary structured `Value` and interns
//! nothing.
//!
//! ## What fails when each half is backed out — MEASURED, per half
//!
//! | test | surface+sweep | resolver `out` arm | weave |
//! |---|---|---|---|
//! | `a_covered_call_dispatches_through_the_clause_dictionary` | FAILS (load) | FAILS (`[]`) | ~~FAILS (`1`)~~ — see below |
//! | `the_same_clause_without_require_dispatches_by_value` | ok | ok | ok |
//! | `a_two_supplier_carrier_has_no_reading_through_the_dictionary_either` | — | — | ok — see below |
//! | `a_carrier_less_defaulted_call_answers_through_the_clause_dictionary` | — | — | **FAILS (`1`)** — the CONTROL |
//! | `every_covered_call_in_the_clause_is_woven` | FAILS (load) | FAILS | **FAILS (`[]`)** |
//! | `the_named_spelling_binds_the_dictionary_by_hand` | FAILS (load) | **FAILS (`[]`)** | ok |
//! | `a_require_with_no_anchor_is_refused_at_typing` | **FAILS** | ok | ok |
//! | `a_nested_require_is_refused_at_parse` | **FAILS** | ok | ok |
//! | `a_body_less_builtin_spec_op_behaves_exactly_as_the_check_only_spelling` | FAILS (load) | ok | ok |
//! | `the_check_only_spelling_is_unchanged` | ok | ok | ok — acceptance (f) |
//!
//! The last pins acceptance (f) and passes either way BY DESIGN — see its site.
//!
//! **WI-1044 MOVED ROWS 1–3, and the weave column is where.** The resolver now
//! classifies an UNCLASSIFIED spec-op call from its argument values, so on THIS
//! ticket's one-supplier fixture the plain call reaches the supplied `7` with no
//! dictionary at all — row 1's weave column no longer discriminates, and row 2 (which
//! existed to make it discriminate) is re-aimed at its site with the argument for why
//! the old `1` was a defect rather than a baseline. The discrimination moves to the
//! TWO-SUPPLIER fixture, where value-direction REFUSES (058 §4.9) and only the
//! dictionary answers: `a_two_supplier_carrier_dispatches_silently_through_the_-
//! dictionary` was documented "PASSES EITHER WAY by design" and is now the live
//! control for the whole weave. Each affected test says so at its own site.
//!
//! **WI-20261025-ZAWX9 MOVED IT AGAIN.** A dictionary now refuses a provider's two
//! suppliers as the call by name does, so the two-supplier fixture has no answer woven
//! or not, and is renamed for what it asserts. The weave's control is a CARRIER-LESS
//! defaulted call, which no value can direct: woven it answers the carrier's `7`, and
//! its un-woven twin, asserted at the site, the default's `1`. The two `—` columns of
//! these rows were not re-measured.
//!
//! ## WHICH CALLS ARE WOVEN — a narrower population than "every covered call"
//!
//! `collect_covered_calls` weaves only a callee some GOAL-SHAPE READER recognizes.
//! When this file was written that meant one predicate — the WI-938
//! functional-relation hook, i.e. a rule-less BODIED operation — and the note here
//! said a **body-less** spec op and a **builtin-backed** one are both left alone,
//! because "`Expr::ApplyWithin` heads `Opaque` and a goal-position reader for it does
//! not exist".
//!
//! **HALF OF THAT EXPIRED.** WI-1057 built the missing reader for a body-less spec
//! op (`body_less_relation_arity`, reached through `dispatched_relation_arity`'s
//! woven-head arm), and WI-20260909-NAR1X admits the CARRIER-LESS ones through it —
//! `Monoid.unit()` / `Zeroable.zero()`, the shape no value can ever dispatch. See
//! `nar1x_carrier_less_spec_op_test`, which owns those rows.
//!
//! **The builtin-backed half stands, and it is the same measurement:**
//! `require[PartialEq[T]], eq(?x, ?y)` went from ONE solution to ZERO when the weave
//! reached it. `eq` is refused by the reader test itself (`body_less_relation_arity`
//! bails on a builtin), so this file's own row keeps pinning it. A body-less
//! CARRIER-BEARING spec op is also still left alone — deliberately, and the reason is
//! at `collect_covered_calls`: the value route already decides it, so the dictionary
//! would be a second answer rather than the only one.
//!
//! ## TWO BOUNDARIES, MEASURED AND PINNED BELOW — not delivered, not silent
//!
//! Each has a test that asserts what the code ACTUALLY does, so closing it has to
//! come here and change the assertion:
//!
//!  * **Acceptance (c) is DELIVERED, by WI-20260905-N20EZ** —
//!    `a_clause_dictionary_crosses_a_rule_boundary_and_is_checked`. It used to be a
//!    pinned boundary ("a dictionary passed through a rule head does NOT reach the
//!    callee's own goal"), which was not a boundary of the design but a hole in the
//!    resolver's goal walk: the caller's `?d`, bound to a non-`Term` dictionary, was
//!    walked as an unbound var and the callee's head match overwrote it. With every
//!    carrier σ-applied on the walk, the supplied dictionary reaches the callee's
//!    `?d = require[…]`, and the CHECK mode fires (WI-860). Its control,
//!    `…_agrees_with_its_own_carrier`, answers through the supplied dictionary.
//!  * **`an_unbound_carrier_delays_rather_than_reaching_a_definite_answer`** — acceptance (d).
//!    The `find_dictionary` goal itself delays correctly, and a woven call whose
//!    dictionary is unbound now routes to `unify` (which delays on an unevaluated
//!    call) instead of falling through to a silent no-answer. Since
//!    WI-20260819-9C2PZ the guard also SUSPENDS rather than deciding the requirement
//!    false — the carried type it used to read was a shared spec parameter, not a type
//!    of anything at the call — so the clause now yields one INDEFINITE residual. It
//!    still reaches no DEFINITE answer when the carrier binds only in a LATER goal.
//!  * **Acceptance (e) is CLOSED, by WI-20261025-ZAWX9** —
//!    `a_two_supplier_carrier_has_no_reading_through_the_dictionary_either`. Channel doc
//!    §4 says a runtime tie is unreachable because overlap is refused at typing/load:
//!    TRUE for a `provides` overlap, FALSE for two SUPPLIERS of one op at one carrier
//!    (WI-1012/WI-1026/WI-1035's refusal). The pinned path refuses that at load, and the
//!    dictionary path resolved it silently to the carrier's own member, reading a single
//!    sort-ops entry. It reads the provider's suppliers now and refuses the second, so
//!    the woven clause, like its un-woven twin, reaches no answer.

use anthill_core::eval::Value;

/// The program shape, shared by every case below: a spec `Desc` with a DEFAULT
/// `describe` answering `1`, and a carrier `Leaf` supplying its own answering `7`.
/// The two differing values are the CONTROL — every "dispatched through the
/// dictionary" assertion below is `7`, and `1` is what the same call answers when
/// nothing supplies a dictionary, so neither number can be produced by accident.
///
/// Lifted from `wi1026_rule_body_spec_op_dispatch_test`'s builder rather than
/// re-derived: that file established this exact shape as the one where the spec's
/// default and the carrier's supply are distinguishable at the SLD goal path.
fn program(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  -- WI-20260825-KD9SW: a WRITTEN bare `eq` in a rule body names the operation by
  -- import; a minted `=` carries its own address and needs nothing.
  import anthill.prelude.PartialEq.{{eq}}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

{tail}end
"#
    )
}

/// [`program`] plus a SECOND carrier `Other`, supplying `9`. Used by the check
/// tests, where the subject is two derivations of one requirement at two different
/// carriers: `Other` is a legitimate provider, so a dictionary derived at it is a
/// real dictionary — just not the one a `Leaf` call's carried type selects.
fn two_carriers(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  -- WI-20260825-KD9SW: a WRITTEN bare `eq` in a rule body names the operation by
  -- import; a minted `=` carries its own address and needs nothing.
  import anthill.prelude.PartialEq.{{eq}}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation describe(x: Other) -> Int64 = 9
  end

{tail}end
"#
    )
}

/// The single Int answer of `{ns}.answer`, driven as an SLD GOAL. Panics on any
/// other shape, including `[]` — "the query returned nothing" must never read as a
/// pass.
fn answer(ns: &str, src: &str) -> i64 {
    let mut kb = crate::common::load_kb_with(src);
    let qn = format!("{ns}.answer");
    match crate::common::query_unary(&mut kb, &qn).as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`{qn}` must answer exactly one definite Int, got {other:?}\n{src}"),
    }
}

/// Every solution of `{ns}.answer(?r)`, without the single-definite-Int demand —
/// for the cases whose subject is "how many, and are they definite".
fn answers(ns: &str, src: &str) -> Vec<(Value, bool)> {
    let mut kb = crate::common::load_kb_with(src);
    crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
}

/// The load errors of `src`, joined. Panics if it loads clean — "the query returned
/// nothing" and "it loaded and did nothing" are the two symptoms a refusal test
/// exists to replace.
fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal; the program loaded clean:\n{src}"))
        .join("\n")
}

// ── (a) the headline: a covered call dispatches through the dictionary ──────

/// THE HEADLINE. The receiver is a rule VARIABLE bound only by the caller, so the
/// typer cannot pin the call — which is the common case in a rule body and exactly
/// why 058 §3.3 puts rule bodies out of scope for compile-stage selection. The
/// clause's declared `Desc[T = A]` resolves the dictionary from the runtime carried
/// type and the covered call dispatches through it.
#[test]
fn a_covered_call_dispatches_through_the_clause_dictionary() {
    let ns = "test.wi1040.covered";
    let src = program(
        ns,
        "  rule via[A](?x: A, ?r) :- Desc[T = A], Desc.describe(?x, ?r)\n  \
           rule answer(?r) :- via(leaf(), ?r)\n",
    );
    assert_eq!(
        answer(ns, &src),
        7,
        "the covered call must reach the implementation `Leaf` SUPPLIES, not the \
         spec's own default",
    );
}

/// THIS WAS THE CONTROL FOR THE TEST ABOVE, AND **WI-1044 CONSUMED IT** — re-aimed
/// here at what it now measures, rather than deleted, because the reason it stopped
/// discriminating is itself the thing a reader of this file needs told.
///
/// It asserted `1`: the identical clause with the `require` deleted folded the spec's
/// DEFAULT, so the headline's `7` could not have been produced by accident. WI-1044
/// made the resolver classify an UNCLASSIFIED spec-op call from the values its
/// arguments carry, and `?x` is bound to `leaf()` by the time this call reduces — so
/// the plain call now reaches the supplied `7` too, WITHOUT any dictionary.
///
/// **That is a correction, not a regression, and the argument is eval's:**
/// `dispatch_resolved_operation`'s step-3 `resolve_carrier_override_by_value` has
/// always dispatched this exact call by value, so `operation probe(x: T) = Desc.
/// describe(x)` answered `7` while the identical unpinnable call in a rule body
/// answered `1`. 058 §3.3 puts rule bodies out of scope for COMPILE-STAGE selection;
/// it does not say the runtime must then run the default over a supplied impl, and
/// WI-444/WI-1010's rule ("defaults fill GAPS, they do not SHADOW") says it must not.
///
/// **WHERE THE HEADLINE'S DISCRIMINATION WENT:**
/// [`a_carrier_less_defaulted_call_answers_through_the_clause_dictionary`], since
/// WI-20261025-ZAWX9. It was the two-supplier fixture until a dictionary refused a
/// provider's two suppliers as value direction refuses them (058 §4.9); a call with no
/// operand is one no value can direct, so there the weave is still the only thing that
/// reaches the carrier's member. The header table says which rows moved.
#[test]
fn the_same_clause_without_require_dispatches_by_value() {
    let ns = "test.wi1040.control";
    let src = program(
        ns,
        "  rule via(?x, ?r) :- Desc.describe(?x, ?r)\n  \
           rule answer(?r) :- via(leaf(), ?r)\n",
    );
    assert_eq!(
        answer(ns, &src),
        7,
        "WI-1044: an unpinnable spec-op call is classified from its ARGUMENT VALUES at \
         reduction time, so it reaches what `Leaf` supplies — the same answer eval's \
         step-3 override has always given for this call. It folded the spec's `1` \
         before, which was the resolver and the interpreter disagreeing about one call",
    );
}

/// EVERY covered call is woven, not just the one the witness scan reached.
///
/// Review finding (2026-08-07), MEASURED before the fix: with a single
/// `covered_call`, the first `Desc.describe` folded the SPEC DEFAULT (`1`) while the
/// second dispatched through the dictionary (`7`) — a silent wrong answer inside a
/// clause that had explicitly asked for the dictionary. Back the collector out and
/// this returns `(1, 7)`.
#[test]
fn every_covered_call_in_the_clause_is_woven() {
    let ns = "test.wi1040.multi";
    let src = program(
        ns,
        "  rule via[A](?x: A, ?a, ?b) :- Desc[T = A], Desc.describe(?x, ?a), \
             Desc.describe(?x, ?b)\n  \
           rule answer(?r) :- via(leaf(), ?r, ?b), eq(?r, ?b)\n",
    );
    assert_eq!(
        answer(ns, &src),
        7,
        "both calls must dispatch through the clause dictionary; the `eq(?r, ?b)` is \
         what turns a one-call-woven regression into NO solution (1 vs 7) instead of \
         a plausible first value",
    );
}

/// WI-20260925-PRVA2 (a) — a covered call NESTED in another covered call is woven, and so is
/// the call around it. The weave used to go call by call: weaving the inner
/// `Desc.describe(?a)` rebuilt the `Scale.scale(…)` holding it, so the outer call's identity
/// match then missed — a debug build PANICKED at load (`debug_assert!(wove)`) and a release
/// build left the outer call unwoven, value-dispatched. One pass over the body finds both.
///
/// FAILS on the call-by-call weave: the load panics. The ANSWER passes either way by design
/// — `Rod` is `Scale`'s one provider, so value dispatch reaches it too; the structure is
/// what discriminates in a release build. `Rod`'s `scale` is `= n`, FOLDED: a bridged call
/// reduces no argument but a host operation's, so a nested call answers only where the
/// outer body folds (`wi_p7vp4…::a_call_nested_in_a_woven_call_is_woven_too` says the same
/// of its slot call).
#[test]
fn a_covered_call_nested_in_another_covered_call_is_woven_with_it() {
    let ns = "test.wi1040.nested";
    let src = program(
        ns,
        "  sort Scale\n    sort T = ?\n    operation scale(n: Int64, y: T) -> Int64 = 0\n  end\n  \
           sort Rod\n    import anthill.prelude.Int64\n    import anthill.prelude.Numeric.{mul}\n    \
             entity rod\n    provides Scale[T = Rod]\n    \
             operation scale(n: Int64, y: Rod) -> Int64 = n\n  end\n  \
           rule r[A, B](?a: A, ?b: B, ?s, ?r) :- Desc[T = A], Scale[T = B], \
             Desc.describe(?a, ?s), Scale.scale(Desc.describe(?a), ?b, ?r)\n  \
           rule answer(?r) :- r(leaf(), rod(), ?s, ?r)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    // Every call to `describe` / `scale` in `r`'s stored body.
    let calls: Vec<(String, bool, Vec<String>)> = crate::common::body_calls(&kb, &format!("{ns}.r"))
        .into_iter()
        .filter(|(f, _, _)| f == "describe" || f == "scale")
        .collect();
    assert!(
        calls.iter().all(|(_, woven, _)| *woven),
        "no covered call is left unwoven: {calls:?}",
    );
    assert!(
        calls.iter().any(|(f, _, inner)| f == "scale" && inner == &["describe".to_string()]),
        "the outer `scale` is woven, holding the woven `describe`: {calls:?}",
    );
    assert_eq!(answer_in(&mut kb, ns), 7, "`Rod`'s `scale` of `Leaf`'s `7`");
}

/// [`answer`] over a KB the caller already loaded.
fn answer_in(kb: &mut anthill_core::kb::KnowledgeBase, ns: &str) -> i64 {
    let qn = format!("{ns}.answer");
    match crate::common::query_unary(kb, &qn).as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`{qn}` must answer exactly one definite Int, got {other:?}"),
    }
}

/// A BODY-LESS, builtin-backed spec op — the ordinary typeclass shape — beside a requirement
/// under a name must behave exactly as beside the unnamed guard. It is deliberately NOT
/// woven. (The two spellings were `require[PartialEq[T]]` and the check-only
/// `requires(PartialEq[T])`, removed by proposal 060.1 §5.)
///
/// Review finding (2026-08-07), MEASURED before the gate: weaving it turned
/// `require[PartialEq[T]], eq(?x, ?y)` from ONE solution into ZERO. An
/// `Expr::ApplyWithin` heads `Opaque`, so at goal position it is invisible to
/// builtin dispatch, to the discrim query and to the WI-938 hook — a clause that
/// worked before the weave silently failing after it. `collect_covered_calls` now
/// admits only callees the WI-938 hook recognizes.
///
/// The unnamed guard is the CONTROL, queried in the same KB: the claim is that the two
/// AGREE, so asserting only the named side would keep passing if both broke together.
#[test]
fn a_body_less_builtin_spec_op_behaves_exactly_as_the_check_only_spelling() {
    let ns = "test.wi1040.bodyless";
    let src = format!(
        r#"namespace {ns}
  -- WI-1089: an import binds the name it writes, so the spec names and the body's
  -- `eq` are each imported. `import anthill.prelude.Int64` no longer carries the
  -- rest of the prelude in with it.
  import anthill.prelude.{{Int64, PartialEq, Eq}}
  import anthill.prelude.PartialEq.eq
  import anthill.prelude.PartialEq.{{eq}}
  sort Witheq
    entity we(v: Int64)
  end
  namespace Witheq
    provides PartialEq[T = Witheq]
    provides Eq[T = Witheq]
  end
  rule checked[A](?x: A, ?y: A) :- PartialEq[T = A], eq(?x, ?y)
  rule denoted[A](?x: A, ?y: A) :- require d: PartialEq[T = A], eq(?x, ?y)
  rule control(?r) :- checked(we(v: 1), we(v: 1)), ?r <=> 1
  rule answer(?r) :- denoted(we(v: 1), we(v: 1)), ?r <=> 1
end
"#
    );
    let mut kb = crate::common::load_kb_with(&src);
    let control = crate::common::query_unary(&mut kb, &format!("{ns}.control"));
    let denoted = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    assert_eq!(
        control.len(),
        1,
        "the CONTROL itself must answer — the guard over a builtin-backed body-less spec \
         op is the delivered WI-300 behaviour: {control:?}",
    );
    // Compared on CONTENT, not on the `Debug` rendering: two occurrences of the
    // same answer carry different source spans, which say nothing about whether the
    // two spellings agree. Count, definiteness and the answer itself are what the
    // claim is about — and the measured regression was one solution vs NONE.
    let shape = |v: &Vec<(Value, bool)>| {
        v.iter()
            .map(|(val, definite)| (format!("{val:?}").contains("Int(1)"), *definite))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        shape(&denoted),
        shape(&control),
        "a named requirement beside a body-less builtin-backed spec op must answer exactly \
         what the unnamed guard answers — weaving it made the clause answer nothing",
    );
}

// ── (b) the named spelling ─────────────────────────────────────────────────

/// The requirement under a NAME, and the call made through it: `d.describe(?x, ?r)` reads
/// `d`'s dictionary, `Leaf`'s, and answers its 7. The row was `?d = require[Desc[T]]`, the
/// author binding the dictionary by hand, and asserted the binding was the `Dictionary` node
/// over `Leaf`; proposal 060.1 §5 removed the form — no clause binds a dictionary to a
/// column — and the dictionary is read by the answer it gives.
#[test]
fn the_named_spelling_binds_the_dictionary_by_hand() {
    let ns = "test.wi1040.named";
    let src = program(
        ns,
        "  rule via[A](?x: A, ?r) :- require d: Desc[T = A], d.describe(?x, ?r)\n  \
           rule answer(?r) :- via(leaf(), ?r)\n",
    );
    assert_eq!(answer(ns, &src), 7, "`Leaf`'s own `describe`, through the named requirement");
}

// ── (c) a caller's requirement crosses into another clause ────────────────

/// Acceptance (c) — a dictionary crosses a rule boundary. The caller's requirement is handed
/// to the callee's at the goal `use(?x, ?r)` (a citation passes the caller's requirement,
/// 060.1 §1), and `describe` dispatches through it: `Leaf`'s 7.
///
/// The row was a dictionary handed through a rule HEAD — `get(?x, ?d)` binding `?d =
/// require[Desc[T]]` and `use(?x, ?d, ?r)` receiving it — and its twin handed `use` the
/// `Other` dictionary at a `Leaf` call, which WI-860's check refused (no answer). Proposal
/// 060.1 §5 removed every column a dictionary rides, and no spelling hands a clause a
/// dictionary at another carrier now: a citation's bracket naming a witness that does not
/// provide at the goal's type is refused at load
/// (`wi_j9ssg_rule_citation_bracket_test`). The disagreeing twin is gone.
#[test]
fn a_clause_dictionary_crossing_a_rule_boundary_agrees_with_its_own_carrier() {
    let ns = "test.wi1040.cross_agree";
    let src = two_carriers(
        ns,
        "  rule use[A](?x: A, ?r) :- Desc[T = A], Desc.describe(?x, ?r)\n  \
           rule mid[A](?x: A, ?r) :- Desc[T = A], use(?x, ?r)\n  \
           rule answer(?r) :- mid(leaf(), ?r)\n",
    );
    assert_eq!(
        answer(ns, &src),
        7,
        "the `Leaf` dictionary `mid` holds reaches `use`'s call, which dispatches through it",
    );
}

// ── (d) an under-determined carrier ────────────────────────────────────────

/// BOUNDARY, PINNED — acceptance (d) is NOT delivered as a whole, and this measures
/// how far it gets.
///
/// Two halves ARE in place, and each is load-bearing on its own: the guard suspends
/// on an unreadable carried type (rather than deciding the requirement false — never
/// NAF-decide, WI-067), and a woven call whose dictionary is still unbound routes to
/// `unify`, which delays on an unevaluated call, instead of falling through to a
/// silent no-answer. What is missing is the clause-level re-fire: with the carrier
/// bound only by a LATER body goal, the clause never reaches a DEFINITE answer.
///
/// The binder is written AFTER the requirement on purpose. With it before, the
/// carrier is already readable and no delay is entered at all — the test would then
/// measure nothing, which is exactly what a boundary test must not do.
///
/// WI-20260819-9C2PZ MOVED THIS BOUNDARY, and it moved in the direction the three-way
/// [`FindDictOutcome`] contract asks for. The clause used to answer NOTHING. `?x`'s only
/// typing source is `Desc.describe(x: T)`, and the typer recorded it at the bare spec
/// parameter `Desc.T` — a symbol every `describe` call in the KB shares — which WI-603
/// stamped onto the variable occurrence and `witness_arg_types` then read back as the
/// carried type. `sort_functor_of_view` answered `Desc.T`, a perfectly readable nominal
/// head that provides nothing, so the guard decided `DontFire`: a requirement decided
/// FALSE off an under-determined binding, which is the one thing `FindDictOutcome`'s own
/// doc says it must never do. Per-application instantiation makes that stamp a fresh
/// unbound variable, which is headless, so the guard now SUSPENDS as designed and the
/// clause yields one INDEFINITE residual.
///
/// So the assertion moved from "no answers" to "one answer, and it is not definite", and
/// the test was RENAMED with it — the old name asserted the opposite of what it now
/// measures. Closing acceptance (d) — the clause-level re-fire — must change it again, to
/// a single DEFINITE `7`.
///
/// HOW MANY OTHER GUARDS FLIPPED: exactly none, measured rather than reasoned. With
/// `guard_over_arg_types` instrumented, every `find_dictionary` guard outcome across the
/// whole `wi_tests` corpus was compared before and after; the two censuses are identical
/// except for THIS fixture, whose one `DontFire` became a `Suspend` (twice, the suspended
/// goal being re-entered). Nothing else in the corpus reaches a guard through a
/// spec-parameter-typed witness argument.
#[test]
fn an_unbound_carrier_delays_rather_than_reaching_a_definite_answer() {
    let ns = "test.wi1040.delay";
    let src = program(
        ns,
        "  rule shape(?x) :- eq(?x, leaf())\n  \
           rule via[A](?x: A, ?r) :- Desc[T = A], Desc.describe(?x, ?r), shape(?x)\n  \
           rule answer(?r) :- via(?x, ?r)\n",
    );
    let got = answers(ns, &src);
    assert_eq!(
        got.len(),
        1,
        "the suspended guard leaves exactly one residual, got {got:?}",
    );
    assert!(
        !got[0].1,
        "PINS a boundary: the residual is INDEFINITE — the guard suspended rather than \
         deciding the requirement false. Closing acceptance (d) must change this to a \
         DEFINITE `7`; got {got:?}",
    );
}

// ── (f) / the anchor rule / the position restriction ───────────────────────

/// THE ANCHOR RULE (proposal 060 §3). A requirement with nothing to project the spec's
/// parameters from is refused at load, never left to delay forever: an introducer no head
/// column's type names has nothing to read its guard at. (The row was `?d = require[Desc[T]]`
/// with no covered call and no typed binding, refused "to ground the requirement"; proposal
/// 060.1 §5 removed the form.)
#[test]
fn a_require_with_no_anchor_is_refused_at_typing() {
    let ns = "test.wi1040.anchor";
    let src = program(ns, "  rule answer[A](?r) :- Desc[T = A], eq(?r, 1)\n");
    let msg = refusal(&src);
    assert!(
        msg.contains("rule type-variable `A` is the type of no head column"),
        "the refusal must name the introducer no column carries: {msg}",
    );
}

/// THE POSITION RESTRICTION (channel doc §3), and the removal (proposal 060.1 §5). A nested
/// `require[X]` was refused at parse in its own sentence, "legal only as a bare rule-body
/// goal"; the form is removed now, and a nested occurrence is refused as every other is, with
/// the repair — not left to escape into scope resolution, which would report an unresolved
/// name `require` and say nothing about which rule it belongs to.
#[test]
fn a_nested_require_is_refused_at_parse() {
    let ns = "test.wi1040.nested";
    // NOT `eq(?r, require[…])` — that IS the named spelling (`=` desugars to
    // `eq`), which is legal. A genuine nesting puts it under another functor.
    let src = program(ns, "  rule answer(?r) :- eq(?r, some(require[Desc[T]]))\n");
    // `parse_errs`, not the loader: the converter owns the name, so the refusal is
    // raised in the parse phase and never reaches a load verdict.
    let msg = crate::common::parse_errs(&src).join("\n");
    assert!(
        msg.contains("`require[Desc[T]]` is no longer written"),
        "the refusal must name the removed form and its repair: {msg}",
    );
}

/// §4 — a runtime tie is UNREACHABLE, not refused: overlap between provider heads
/// is decided at typing/load. TRUE for a `provides` overlap and FALSE for two SUPPLIERS
/// of one op at one carrier, which this row pinned: the same program with a GROUND
/// receiver is refused at load (WI-1026/WI-1035), and through the dictionary it
/// answered the carrier's own member silently, because `resolve_op_target_checked`
/// read one sort-ops entry.
///
/// **WI-20261025-ZAWX9 CLOSED IT.** The dictionary reads the suppliers its provider
/// writes, and two of them are refused at the dispatch (`DispatchRefusal::Tie`), which on
/// this path, as for value direction's refusal, leaves the call unreduced: the clause
/// reaches no answer, woven or not. FAILS with the provider's set backed out — the woven
/// clause answers `7` again. It was the file's live control for the weave (WI-1044) and
/// no longer discriminates it; that is
/// [`a_carrier_less_defaulted_call_answers_through_the_clause_dictionary`].
#[test]
fn a_two_supplier_carrier_has_no_reading_through_the_dictionary_either() {
    let ns = "test.wi1040.tie";
    // `clause` is the rule-body prefix under test — the WHOLE difference between the
    // subject and its control, so the control cannot drift into a different program.
    let tie_program = |ns: &str, clause: &str| {
        format!(
            r#"namespace {ns}
  import anthill.prelude.Int64
  -- WI-20260825-KD9SW: a WRITTEN bare `eq` in a rule body names the operation by
  -- import; a minted `=` carries its own address and needs nothing.
  import anthill.prelude.PartialEq.{{eq}}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  operation otherDescribe(x: Leaf) -> Int64 = 9

  namespace Leaf
    provides Desc[T = Leaf, describe = otherDescribe]
  end

  rule via{clause}Desc.describe(?x, ?r)
  rule answer(?r) :- via(leaf(), ?r)
end
"#
        )
    };
    // THE CONTROL, MEASURED AT THE SITE rather than predicted in the header: the same
    // program with the requirement deleted answers NOTHING. Value-directed classification
    // (WI-1044) sees two suppliers for `Leaf` and declines to reduce the call, so the
    // WI-938 hook has nothing to `unify` the result column with. The woven clause below
    // now agrees with it.
    let without = answers(
        &format!("{ns}.control"),
        &tie_program(&format!("{ns}.control"), "(?x, ?r) :- "),
    );
    assert!(
        !without
            .iter()
            .any(|(v, definite)| *definite && matches!(v, Value::Int(_))),
        "the un-woven twin must not answer: a two-supplier carrier has no single \
         reading, and the only Int a fold could produce is the spec's DEFAULT — got \
         {without:?}",
    );
    let src = tie_program(ns, "[A](?x: A, ?r) :- Desc[T = A], ");
    let with = answers(ns, &src);
    assert!(
        !with
            .iter()
            .any(|(v, definite)| *definite && matches!(v, Value::Int(_))),
        "the dictionary's provider supplies `describe` twice — its own `7` and the \
         binding's `9` — and a dictionary refuses the second as value direction does \
         (WI-20261025-ZAWX9); it answered the carrier's own `7`, silently. Got {with:?}",
    );
}

/// THE DICTIONARY'S LIVE CONTROL. A CARRIER-LESS defaulted call — `name()` takes no operand
/// — made through the requirement the clause declares under a name at `Leaf`. No value can
/// direct it, so value direction runs the spec's default `1`, and only the clause dictionary
/// reaches `Leaf`'s own `7`. The un-woven twin is asserted here, at the site, as the control:
/// it is the identical clause with the requirement deleted. (The clause wrote
/// `require[Desc[T]]` and the bare `Desc.name(?r)`; proposal 060.1 §5 removed the form, and a
/// call that writes no instance names the requirement it reads.)
///
/// ADDED BY WI-20261025-ZAWX9, when the two-supplier row stopped discriminating. Its `7`
/// does not depend on that ticket: `Leaf`'s own member answers through the dictionary on
/// either side of it.
#[test]
fn a_carrier_less_defaulted_call_answers_through_the_clause_dictionary() {
    let ns = "test.wi1040.carrierless";
    let src = |ns: &str, clause: &str, name: &str| {
        program(
            ns,
            &format!(
                "  rule via{clause}Desc.describe(?x, ?t), {name}.name(?r)\n  \
                   rule answer(?r) :- via(leaf(), ?r)\n"
            ),
        )
        .replace(
            "    operation describe(x: T) -> Int64 = 1\n",
            "    operation describe(x: T) -> Int64 = 1\n    operation name() -> Int64 = 1\n",
        )
        .replace(
            "    operation describe(x: Leaf) -> Int64 = 7\n",
            "    operation describe(x: Leaf) -> Int64 = 7\n    operation name() -> Int64 = 7\n",
        )
    };
    let control_ns = format!("{ns}.control");
    let control = src(&control_ns, "(?x, ?r) :- ", "Desc");
    assert!(
        control.contains("operation name() -> Int64 = 7"),
        "fixture guard: both members must have been added"
    );
    assert_eq!(
        answer(&control_ns, &control),
        1,
        "the un-woven twin: a call with no operand is one value direction cannot direct"
    );
    assert_eq!(
        answer(ns, &src(ns, "[A](?x: A, ?r) :- require d: Desc[T = A], ", "d")),
        7,
        "the clause dictionary is what reaches `Leaf`'s own `name`",
    );
}

/// ACCEPTANCE (f) — the guard CHECKS: the clause fires where the carrier provides the spec,
/// and does not where it provides none. It was the check-only `requires(Desc[T])`, which
/// lowered to the same relation with no `out` and wove nothing; proposal 060.1 §5 removed
/// it, and the guard is the one form — read with an `out`, woven into the call beside it. So
/// the call answers `Leaf`'s 7 through the guard's dictionary, as it answered by value beside
/// `requires(X)` (WI-1044), and a carrier with no provider is blocked as it was.
#[test]
fn the_check_only_spelling_is_unchanged() {
    let ns = "test.wi1040.checkonly";
    let src = program(
        ns,
        "  rule via[A](?x: A, ?r) :- Desc[T = A], Desc.describe(?x, ?r)\n  \
           rule answer(?r) :- via(leaf(), ?r)\n",
    );
    assert_eq!(answer(ns, &src), 7, "the guard admits `Leaf`, and its call answers `Leaf`'s own");

    // …and it still blocks a carrier that provides nothing, which is the whole of
    // what the guard tier does.
    let ns2 = "test.wi1040.checkonly2";
    let src2 = format!(
        r#"namespace {ns2}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Bare
    entity bare
  end

  rule via[A](?x: A, ?r) :- Desc[T = A], Desc.describe(?x, ?r)
  rule answer(?r) :- via(bare(), ?r)
end
"#
    );
    // A goal at concrete types builds its callee's dictionary at load (060.1 §1): refused
    // there, as an operation's call at `Bare` is.
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&src2),
        &["answer.body", "no provider answers `test.wi1040.checkonly2.Desc[T = test.wi1040.checkonly2.Bare]`"],
        "a carrier with no provider must not satisfy the guard",
    );
}
