//! WI-1040 — `require[X]` brings a requirement dictionary into a rule clause's
//! scope, so a body call that needs one can be PASSED it instead of only being
//! checked against it.
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
//! | `a_two_supplier_carrier_dispatches_silently_through_the_dictionary` | FAILS (load) | FAILS | **FAILS (`[]`)** — the CONTROL |
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
//! ## WHICH CALLS ARE WOVEN — a narrower population than "every covered call"
//!
//! `collect_covered_calls` weaves only a callee the WI-938 functional-relation hook
//! recognizes: a rule-less BODIED operation. A **body-less** spec op (the typeclass
//! norm — `PartialEq.eq`) and a **builtin-backed** one are deliberately left alone,
//! and keep exactly the `requires(X)` behaviour they had. MEASURED: weaving them
//! turned a clause that answered into one that answers nothing, because
//! `Expr::ApplyWithin` heads `Opaque` and a goal-position reader for it does not
//! exist. Both halves are pinned by tests above.
//!
//! ## THREE BOUNDARIES, MEASURED AND PINNED BELOW — not delivered, not silent
//!
//! Each has a test that asserts what the code ACTUALLY does, so closing it has to
//! come here and change the assertion:
//!
//!  * **`a_clause_dictionary_does_not_cross_a_rule_boundary`** — the CHECK mode
//!    (acceptance (c)) is unreachable from any surface spelling. `unify` performs
//!    bind and check as one operation, so the arm is not dead code; but nothing can
//!    pre-bind `out`. A second `require` on one spec base is refused by the guard
//!    tier (needs the un-stripped spec, channel doc §10 item 1), and a dictionary
//!    passed through a rule head does NOT reach the callee's own goal — MEASURED:
//!    the callee's variable is a fresh unbound `Global`, the caller's binding riding
//!    in `answer_links`. Reaching it is the automatic call-site synthesis (channel
//!    doc §5) plus §10 item 3.
//!  * **`an_unbound_carrier_delays_rather_than_reaching_a_definite_answer`** — acceptance (d).
//!    The `find_dictionary` goal itself delays correctly, and a woven call whose
//!    dictionary is unbound now routes to `unify` (which delays on an unevaluated
//!    call) instead of falling through to a silent no-answer. Since
//!    WI-20260819-9C2PZ the guard also SUSPENDS rather than deciding the requirement
//!    false — the carried type it used to read was a shared spec parameter, not a type
//!    of anything at the call — so the clause now yields one INDEFINITE residual. It
//!    still reaches no DEFINITE answer when the carrier binds only in a LATER goal.
//!  * **`a_two_supplier_carrier_dispatches_silently_through_the_dictionary`** —
//!    acceptance (e). Channel doc §4 says a runtime tie is unreachable because
//!    overlap is refused at typing/load. TRUE for a `provides` overlap; FALSE for
//!    two SUPPLIERS of one op at one carrier (WI-1012/WI-1026/WI-1035's refusal),
//!    which the pinned path refuses at load and the dictionary path resolves
//!    silently, because `resolve_op_target_checked` reads a single sort-ops entry
//!    and never consults `spec_op_suppliers_for_carrier` (WI-842).

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
/// clause's `require[Desc[T]]` resolves the dictionary from the runtime carried
/// type and the covered call dispatches through it.
#[test]
fn a_covered_call_dispatches_through_the_clause_dictionary() {
    let ns = "test.wi1040.covered";
    let src = program(
        ns,
        "  rule via(?x, ?r) :- require[Desc[T]], Desc.describe(?x, ?r)\n  \
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
/// [`a_two_supplier_carrier_dispatches_silently_through_the_dictionary`], which this
/// file documented as "PASSES EITHER WAY by design" and which is now a LIVE control —
/// value-directed classification REFUSES a two-supplier carrier (058 §4.9), so on that
/// fixture the weave is the only thing that answers at all. The header table's first
/// row is updated accordingly.
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
        "  rule via(?x, ?a, ?b) :- require[Desc[T]], Desc.describe(?x, ?a), \
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

/// A BODY-LESS, builtin-backed spec op — the ordinary typeclass shape — must behave
/// exactly as `requires(X)` does. It is deliberately NOT woven.
///
/// Review finding (2026-08-07), MEASURED before the gate: weaving it turned
/// `require[PartialEq[T]], eq(?x, ?y)` from ONE solution into ZERO. An
/// `Expr::ApplyWithin` heads `Opaque`, so at goal position it is invisible to
/// builtin dispatch, to the discrim query and to the WI-938 hook — a clause that
/// worked before the weave silently failing after it. `collect_covered_calls` now
/// admits only callees the WI-938 hook recognizes.
///
/// The `requires` spelling is the CONTROL, queried in the same KB: the claim is that
/// the two AGREE, so asserting only the `require` side would keep passing if both
/// broke together.
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
  fact PartialEq[T = Witheq]
  fact Eq[T = Witheq]
  rule checked(?x, ?y) :- requires(PartialEq[T]), eq(?x, ?y)
  rule denoted(?x, ?y) :- require[PartialEq[T]], eq(?x, ?y)
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
        "the CONTROL itself must answer — `requires(X)` over a builtin-backed \
         body-less spec op is the delivered WI-300 behaviour: {control:?}",
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
        "`require[X]` over a body-less builtin-backed spec op must answer exactly \
         what `requires(X)` answers — weaving it made the clause answer nothing",
    );
}

// ── (b) the named spelling ─────────────────────────────────────────────────

/// The author names the output and passes it by hand. What is asserted is that the
/// binding is a real dictionary — the `Dictionary` node over the carrier that
/// supplies the spec — not merely that the goal succeeded.
#[test]
fn the_named_spelling_binds_the_dictionary_by_hand() {
    let ns = "test.wi1040.named";
    let src = program(
        ns,
        "  rule dict(?x, ?d) :- ?d = require[Desc[T]], Desc.describe(?x, ?ignored)\n  \
           rule answer(?d) :- dict(leaf(), ?d)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    let sols = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    let [(v, true)] = sols.as_slice() else {
        panic!("`?d = require[…]` must bind exactly one definite dictionary, got {sols:?}");
    };
    let (head, impl_sym) = dictionary_parts(&kb, v);
    assert!(
        head.ends_with("Dictionary"),
        "the binding must present the ONE dictionary shape WI-1019 announces for a \
         handle too (§9) — got head `{head}`",
    );
    assert!(
        impl_sym.ends_with(".Leaf"),
        "the dictionary must name the carrier that supplies `Desc`, got `{impl_sym}`",
    );
}

/// `(head functor, impl_functor)` of a dictionary value, as qualified names.
/// Panics on any other shape — a test whose subject is "what did `?d` bind to" may
/// not shrug at an unexpected carrier.
fn dictionary_parts(kb: &anthill_core::kb::KnowledgeBase, v: &Value) -> (String, String) {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    // Read CARRIER-NEUTRALLY, through the same view an eval `RequirementHandle`
    // answers under. That is the assertion: one shape, whichever side built it.
    let ViewHead::Functor {
        functor: Some(ctor),
        ..
    } = v.head(kb)
    else {
        panic!("a dictionary must present a constructor head, got {v:?}")
    };
    let head = kb.qualified_name_of(ctor).to_string();
    let impl_key = kb
        .try_resolve_symbol("anthill.realization.runtime.Dictionary.impl")
        .expect("the `Dictionary.impl` accessor must resolve");
    let impl_child = v
        .named_arg(kb, impl_key)
        .unwrap_or_else(|| panic!("a dictionary must carry `impl`; head `{head}`"))
        .to_value();
    let ViewHead::Functor {
        functor: Some(s),
        pos_arity: 0,
        named_arity: 0,
    } = impl_child.head(kb)
    else {
        panic!("`impl` must name a sort, got {impl_child:?}")
    };
    (head, kb.qualified_name_of(s).to_string())
}

// ── (c) a supplied dictionary is CHECKED, per WI-860 ───────────────────────

/// BOUNDARY, PINNED — acceptance (c) is NOT delivered, and this test measures why
/// rather than asserting a capability that is absent.
///
/// `read_dictionary_into` performs bind and check as ONE `unify_values` call, so the
/// check mode is not dead code — it is the same line, taken when `out` is bound. But
/// nothing in the surface can bind it: a second `require` on one spec base is refused
/// by the guard tier (it needs the un-stripped spec, channel doc §10 item 1), and a
/// dictionary handed through a rule head does not reach the callee's own goal.
///
/// MEASURED, and this is the fact the assertion pins: `use` re-derives at ITS OWN
/// carrier and answers `7`, ignoring the `Other` dictionary the caller passed. The
/// callee's `?d` is a fresh unbound `Global` at goal time — the caller's binding
/// rides in `answer_links`, not in the callee's substitution (rustland/CLAUDE.md,
/// De Bruijn step 4). Were the check reachable here, this would be `[]`.
#[test]
fn a_clause_dictionary_does_not_cross_a_rule_boundary() {
    let ns = "test.wi1040.cross";
    let src = two_carriers(
        ns,
        "  rule get(?x, ?d) :- ?d = require[Desc[T]], Desc.describe(?x, ?i)\n  \
           rule use(?x, ?d, ?r) :- ?d = require[Desc[T]], Desc.describe(?x, ?r)\n  \
           rule answer(?r) :- get(other(), ?d), use(leaf(), ?d, ?r)\n",
    );
    assert_eq!(
        answer(ns, &src),
        7,
        "PINS a boundary, not a capability: a dictionary passed through a rule head \
         does not reach the callee's `find_dictionary`, so the callee re-derives at \
         its own carrier. Closing this (call-site synthesis + channel doc \u{00a7}10 item 3) \
         must change this assertion to `[]`, because the supplied `Other` dictionary \
         would then DISAGREE with the local `Leaf` row and fail (WI-860)",
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
           rule via(?x, ?r) :- require[Desc[T]], Desc.describe(?x, ?r), shape(?x)\n  \
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

/// THE ANCHOR RULE (proposal 060 §3). A `require[X]` with nothing to project the
/// spec's parameters from — no covered body call, no typed binding — is refused at
/// typing, never left to delay forever.
#[test]
fn a_require_with_no_anchor_is_refused_at_typing() {
    let ns = "test.wi1040.anchor";
    let src = program(
        ns,
        "  rule answer(?r) :- ?d = require[Desc[T]], eq(?r, 1)\n",
    );
    let msg = refusal(&src);
    assert!(
        msg.contains("to ground the requirement"),
        "the refusal must say the requirement cannot be grounded: {msg}",
    );
    assert!(msg.contains("Desc"), "the spec must be named: {msg}");
}

/// THE POSITION RESTRICTION (channel doc §3). `require[X]` denotes a dictionary in
/// the CLAUSE's scope, so there is no lifting rule that would give a nested
/// occurrence a meaning. Refused loudly at parse, with its own sentence — not left
/// to escape into scope resolution, which would report an unresolved name `require`
/// and say nothing about which rule it belongs to.
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
        msg.contains("bare rule-body goal"),
        "the refusal must name the two legal positions: {msg}",
    );
}

/// §4 — a runtime tie is UNREACHABLE, not refused: overlap between provider heads
/// is decided at typing/load. Pinned here so that a change which lets one through
/// to run time has to come and edit this test.
///
/// **WI-1044 MADE THIS THE FILE'S LIVE CONTROL FOR THE WEAVE**, and it used to pass
/// EITHER WAY by design. Its assertion is unchanged; what changed is what happens when
/// the weave is backed out. Value-directed classification refuses a two-supplier
/// carrier (058 §4.9), so the un-woven call now answers NOTHING here — while the
/// dictionary still answers `7`, because `resolve_op_target_checked` reads one
/// sort-ops entry and never consults `spec_op_suppliers_for_carrier`. That is the same
/// boundary the assertion below already named, seen from the other side: the two
/// derivations of one dispatch DISAGREE about this program, and only one of them
/// notices. It is the one fixture in this file on which the weave is the difference
/// between an answer and none.
#[test]
fn a_two_supplier_carrier_dispatches_silently_through_the_dictionary() {
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

  fact Desc[T = Leaf, describe = otherDescribe]

  rule via(?x, ?r) :- {clause}Desc.describe(?x, ?r)
  rule answer(?r) :- via(leaf(), ?r)
end
"#
        )
    };
    // THE CONTROL, MEASURED AT THE SITE rather than predicted in the header: the same
    // program with `require[…]` deleted answers NOTHING. Value-directed classification
    // (WI-1044) sees two suppliers for `Leaf` and declines to reduce the call, so the
    // WI-938 hook has nothing to `unify` the result column with. That `7` below is
    // therefore the dictionary's and no other path's.
    let without = answers(
        &format!("{ns}.control"),
        &tie_program(&format!("{ns}.control"), ""),
    );
    assert!(
        !without
            .iter()
            .any(|(v, definite)| *definite && matches!(v, Value::Int(_))),
        "the un-woven twin must not answer: a two-supplier carrier has no single \
         reading, and the only Int a fold could produce is the spec's DEFAULT — got \
         {without:?}",
    );
    let src = tie_program(ns, "require[Desc[T]], ");
    assert_eq!(
        answer(ns, &src),
        7,
        "PINS a boundary, and CORRECTS channel doc \u{00a7}4's \"a runtime tie is \
         unreachable\": true for a `provides` overlap, FALSE for two SUPPLIERS of one \
         op at one carrier. The same program with a GROUND receiver is refused at \
         load (WI-1026/WI-1035); through the dictionary it answers the carrier's own \
         member silently, because `resolve_op_target_checked` reads one sort-ops \
         entry and never consults `spec_op_suppliers_for_carrier` (WI-842)",
    );
}

/// ACCEPTANCE (f) — the check-only spelling is unchanged. It lowers to the SAME
/// relation with no `out`, weaves nothing, and decides exactly what WI-300's guard
/// decided: the clause fires where the carrier provides the spec, and does not SUPPLY
/// anything to the call beside it.
///
/// PASSES EITHER WAY by design — that is the point. It is the sentinel for the
/// structural claim in this file's header: were `out` positional, or were the weave
/// keyed on anything but `out`'s presence, this test would move.
///
/// **WI-1044 changed the NUMBER and not the claim.** The assertion was `1`, on the
/// reading "checking is not supplying, so the call still folds the spec's default" —
/// but folding the default was never what "not supplying" MEANT. It is what an
/// unclassified call happened to do, here and in
/// [`the_same_clause_without_require_dispatches_by_value`] alike, and the resolver now
/// classifies such a call from its argument values (see that test for why that is a
/// correction). What acceptance (f) asserts is that this spelling weaves NOTHING, and
/// the number that shows it is the one the plain clause gives — which is `7` for both.
/// The sentinel is intact: a weave here would make this fixture behave like the
/// headline's, and the two-supplier fixture above is where the two now visibly part.
#[test]
fn the_check_only_spelling_is_unchanged() {
    let ns = "test.wi1040.checkonly";
    let src = program(
        ns,
        "  rule via(?x, ?r) :- requires(Desc[T]), Desc.describe(?x, ?r)\n  \
           rule answer(?r) :- via(leaf(), ?r)\n",
    );
    assert_eq!(
        answer(ns, &src),
        7,
        "`requires(X)` CHECKS and does not supply — so the call beside it is decided \
         exactly as the same call with no `requires` at all (WI-1044: by value), and \
         NOT through a dictionary this spelling never builds",
    );

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

  rule via(?x, ?r) :- requires(Desc[T]), Desc.describe(?x, ?r)
  rule answer(?r) :- via(bare(), ?r)
end
"#
    );
    assert!(
        answers(ns2, &src2).is_empty(),
        "a carrier with no provider must not satisfy the guard",
    );
}
