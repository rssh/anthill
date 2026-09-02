//! WI-1016 — `Value::SymbolRef` in production: the seams a reflect `Symbol`
//! crosses once `symbol_value` mints the value carrier.
//!
//! The three producers (`Dictionary.impl`, `OpRef.op`, `OpRef.named`) hand back
//! `Value::SymbolRef`, while the other minters of the same reflect `Symbol` sort
//! (`lookup_symbol`, `scope`, the resolver's `builtin_lookup_symbol`) still hand
//! back a `Value::Term` wrapping `Term::Ref`. BOTH spellings are therefore live
//! at once, deliberately — every seam that keys, dedups or stores a symbol has to
//! give them one answer, and a suite where only one carrier ever appears cannot
//! tell whether it does.
//!
//! What each test here would look like if the change under it were backed out is
//! stated at the test, MEASURED, not predicted.

use smallvec::SmallVec;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::term::Term;
use anthill_core::kb::{ClauseKind, KnowledgeBase};

const DICT: &str = "anthill.realization.runtime.Dictionary";
const MAP: &str = "anthill.prelude.Map";

fn interp() -> Interpreter {
    crate::common::interp_for("namespace test.wi1016\nend\n")
}

fn resolve(interp: &Interpreter, qn: &str) -> Symbol {
    interp
        .kb()
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not found in KB"))
}

/// A `Symbol` value on the MINTED carrier — what `Dictionary.impl` returns.
fn minted_symbol(interp: &mut Interpreter, qn: &str) -> Value {
    let s = resolve(interp, qn);
    let dict = crate::common::dict(&interp, s, []).into_value();
    let got = interp
        .call(&format!("{DICT}.impl"), &[dict])
        .expect("Dictionary.impl");
    assert!(
        matches!(got, Value::SymbolRef(m) if m == s),
        "this file's premise: the reflect Symbol ops mint the value carrier",
    );
    got
}

/// The SAME symbol on the interned carrier — what `lookup_symbol` / `scope`
/// return, and what a `Ref` term in a loaded file is.
fn interned_symbol(interp: &mut Interpreter, qn: &str) -> Value {
    let s = resolve(interp, qn);
    Value::term(interp.kb_mut().alloc(Term::Ref(s)))
}

// ── Map: one symbol, one slot ───────────────────────────────────────────────

/// A `Map` keyed by a symbol must find an entry stored through the OTHER carrier
/// of that symbol. `MapKey` had no `Ref` variant and `try_from_value` no `&kb`,
/// so this was not a missing arm but a representation gap: a `Value::SymbolRef`
/// key hard-errored as an unsupported key type.
///
/// CONTROL, MEASURED in two steps:
///  - with `MapKey::Ref` absent entirely, `Map.put` fails with
///    `TypeMismatch { expected: "Map key (…)" , got: "SymbolRef" }` — the put
///    below never even stores.
///  - with `MapKey::Ref` present but `try_from_value`'s `Term::Ref` arm dropped
///    (so only the new carrier canonicalizes), the put succeeds and the
///    cross-carrier `Map.get` answers `none` — the two-slots-one-symbol bug.
#[test]
fn a_map_keyed_by_a_symbol_finds_it_through_either_carrier() {
    let mut interp = interp();
    let minted = minted_symbol(&mut interp, "anthill.prelude.Int64");
    let interned = interned_symbol(&mut interp, "anthill.prelude.Int64");

    let empty = interp
        .call(&format!("{MAP}.empty"), &[])
        .expect("Map.empty");
    let m = interp
        .call(
            &format!("{MAP}.put"),
            &[empty, minted.clone(), Value::Int(7)],
        )
        .expect("a minted Symbol is a usable Map key");

    // Stored through `SymbolRef`, read through `Term::Ref`.
    let got = interp
        .call(&format!("{MAP}.get"), &[m.clone(), interned])
        .expect("Map.get");
    assert_eq!(
        option_int(&interp, &got),
        Some(7),
        "a symbol addresses one slot whichever carrier reaches the map",
    );

    // …and the reverse direction, so neither carrier is merely the privileged one.
    let bool_interned = interned_symbol(&mut interp, "anthill.prelude.Bool");
    let m2 = interp
        .call(&format!("{MAP}.put"), &[m, bool_interned, Value::Int(9)])
        .expect("Map.put via the interned carrier");
    let bool_minted = minted_symbol(&mut interp, "anthill.prelude.Bool");
    let got2 = interp
        .call(&format!("{MAP}.get"), &[m2, bool_minted])
        .expect("Map.get");
    assert_eq!(option_int(&interp, &got2), Some(9));
}

/// `Map.keys` hands a key back as a `Value` that re-addresses its own slot.
/// A `Ref` key spells itself `Value::SymbolRef` on the way out (the carrier-free
/// form — the read must not need `&mut kb` to re-intern), so this pins that the
/// round-trip is closed rather than merely plausible.
#[test]
fn a_symbol_key_read_back_out_of_a_map_addresses_its_own_slot() {
    let mut interp = interp();
    let minted = minted_symbol(&mut interp, "anthill.prelude.Int64");
    let empty = interp
        .call(&format!("{MAP}.empty"), &[])
        .expect("Map.empty");
    let m = interp
        .call(&format!("{MAP}.put"), &[empty, minted, Value::Int(7)])
        .expect("Map.put");

    let keys = interp
        .call(&format!("{MAP}.keys"), &[m.clone()])
        .expect("Map.keys");
    let first = crate::common::list_heads(&keys)
        .into_iter()
        .next()
        .expect("one key");
    assert!(
        matches!(first, Value::SymbolRef(_)),
        "a symbol key spells itself carrier-free on the way out, got {first:?}",
    );
    let got = interp
        .call(&format!("{MAP}.get"), &[m, first])
        .expect("Map.get");
    assert_eq!(option_int(&interp, &got), Some(7));
}

// ── fn_value: one logical fact, one stored fact ─────────────────────────────

/// `f(<sym>)` is ONE fact whichever carrier the symbol child arrives on.
///
/// `assert_fact_carrier` routes through `fn_value`, whose all-`Term` test decided
/// the head carrier: a `Value::Entity` head keys `value_fact_dedup` (a `GoalKey`)
/// and a `Value::Term` head keys `fact_dedup` (a `TermId`), and those key spaces
/// are DISJOINT (WI-815). So a `SymbolRef` child sent the head down the value-fact
/// path and its `Term::Ref` twin down the term path, storing the same logical fact
/// twice with neither dedup able to see the other.
///
/// CONTROL, MEASURED by restoring `matches!(v, Value::Term { .. })` as the test:
/// the two asserts return DIFFERENT `RuleId`s and `read_facts` yields 2 rows.
#[test]
fn a_symbolref_child_stores_one_fact_not_two() {
    let mut kb = KnowledgeBase::new();
    let f = kb.intern("wi1016_f");
    let domain = kb.intern("test");
    let payload = kb.intern("wi1016_payload");

    let via_minted = kb.assert_fact_carrier(
        f,
        vec![Value::SymbolRef(payload)],
        vec![],
        ClauseKind::Fact,
        domain,
        None,
    );
    let ref_tid = kb.alloc(Term::Ref(payload));
    let via_interned = kb.assert_fact_carrier(
        f,
        vec![Value::term(ref_tid)],
        vec![],
        ClauseKind::Fact,
        domain,
        None,
    );

    assert_eq!(
        via_minted, via_interned,
        "one logical fact, one RuleId — the two carriers of the child dedup together",
    );
    // And the stored head is the hash-consed term, not a value-fact Entity: the
    // whole point is that it rides the SAME key space its twin does.
    assert!(
        matches!(kb.rule_head_value(via_minted), Value::Term { .. }),
        "a SymbolRef child does not force the value-fact carrier",
    );
}

// ── the resolver: a SymbolRef binding keeps answer dedup on ─────────────────

/// ONE answer reached two ways — once as a plain `Term::Ref` fact, once through a
/// rule that binds the same symbol as a `Value::SymbolRef` — collapses to one
/// solution.
///
/// `is_duplicate_answer` skips dedup when σ carries a binding it cannot
/// fingerprint, and the test for that was by CARRIER (`Value::Term | Value::Node`).
/// A `SymbolRef` fingerprints perfectly well (a nullary `ViewHead::Functor`), so excluding it
/// turned answer dedup off according to which carrier the symbol arrived on.
///
/// The σ binding is produced by `resolve_sort_instantiation_param` projecting a
/// `SortView` whose `T` binding IS a `SymbolRef` — `finish_result_value` binds it
/// in its own carrier (WI-1015), which is what puts one into σ at all. It is the
/// rule-LOCAL `?v` that carries it: the answer link into the query var interns on
/// the way out, so `?q` reads back as a `Term`, and the two solutions are
/// therefore INDISTINGUISHABLE to a caller — which is what makes the duplicate a
/// duplicate.
///
/// The two routes are alternatives for ONE goal, not two ways through one rule
/// body. That was FORCED when this test was written — the fingerprint was taken of
/// the NEAREST ancestor ChoicePoint's goal, and a disjunction inside the body made
/// that the body goal (whose two answers genuinely differ) rather than `dup(?q)`.
/// WI-FFPGD projects onto the QUERY's goals, so the body-disjunction shape would
/// measure dedup too; the one-goal shape is kept because it puts `dup(?q)` at both
/// ends and leaves the carrier as the only moving part.
///
/// CONTROL, RE-MEASURED for WI-1023, which deleted the code the original control
/// named: the by-carrier σ list is gone, so "drop `| Value::SymbolRef(_)`" no
/// longer describes anything. The equivalent revert is the PRE-WI-1016 list —
/// restore `is_duplicate_answer`'s σ scan as
/// `!matches!(v, Value::Term { .. } | Value::Node(_))` — which reports 2 solutions
/// instead of 1. Fail-open, which is why nothing caught it. WI-FFPGD changed WHAT
/// is fingerprinted (the query's goals, not the nearest ChoicePoint's) and left
/// this σ scan untouched, so the revert still describes live code.
#[test]
fn a_symbolref_binding_does_not_disable_answer_dedup() {
    use anthill_core::kb::resolve::ResolveConfig;

    // PREMISE, asserted rather than assumed: the rule route ALONE really does put
    // a `Value::SymbolRef` into σ. Check this first when the test goes red —
    // without it the dedup assert below measures dedup, not the carrier. It has to
    // be read BEFORE the second route exists, because dedup drops the very
    // solution that carries the binding.
    let (mut kb, q_term, goal, answer) = dedup_fixture();
    let rule_only = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(rule_only.len(), 1, "the rule alone answers once");
    assert!(
        rule_only[0]
            .subst
            .iter()
            .any(|(_, b)| matches!(b, Value::SymbolRef(a) if *a == answer)),
        "premise: the rule's projection binds the value carrier into σ",
    );

    // Now add the term-carried route to the SAME answer, into the SAME KB — safe
    // because `query_cache` is a `SearchStream` field, built fresh per `resolve`
    // call, so the first query cannot serve stale candidates to the second. The
    // two solutions are then the same answer read two ways: the fact route binds
    // `?q ↦ Term::Ref(answer)` directly, the rule route binds `?q ↦ Term::Var(?v)`
    // with `?v ↦ SymbolRef(answer)` in the same σ — one more link, same symbol. So
    // one is a duplicate, and `reify` (not `resolve_as_value`, which stops at the
    // var term) is what shows they agree.
    add_term_route(&mut kb, answer);
    let answered = answered_symbols(&mut kb, q_term, goal);
    assert!(
        answered.iter().all(|s| *s == Some(answer)),
        "both routes answer the same symbol, got {answered:?}",
    );
    assert_eq!(
        answered.len(),
        1,
        "two spellings of one answer collapse — a SymbolRef binding is fingerprintable",
    );
}

/// Resolve `goal` and read the symbol each solution binds `?q` to, fully walked.
fn answered_symbols(
    kb: &mut KnowledgeBase,
    q_term: anthill_core::kb::term::TermId,
    goal: anthill_core::kb::term::TermId,
) -> Vec<Option<Symbol>> {
    use anthill_core::kb::resolve::ResolveConfig;
    kb.resolve(&[goal], &ResolveConfig::default())
        .into_iter()
        .map(|s| {
            let v = kb.reify(q_term, &s.subst);
            kb.value_symbol(&v)
        })
        .collect()
}

/// The term-carried route: `dup(<answer>)` as a plain hash-consed fact, the
/// duplicate of what the fixture's rule already proves.
fn add_term_route(kb: &mut KnowledgeBase, answer: Symbol) {
    let dup = kb.intern("wi1016_dup");
    let domain = kb.intern("test");
    let answer_ref = kb.alloc(Term::Ref(answer));
    let fact = kb.alloc(Term::Fn {
        functor: dup,
        pos_args: SmallVec::from_elem(answer_ref, 1),
        named_args: SmallVec::new(),
    });
    kb.assert_fact(fact, ClauseKind::Fact, domain, None);
}

/// The KB for [`a_symbolref_binding_does_not_disable_answer_dedup`]: the
/// `SymbolRef`-binding rule alone. Returns `(kb, the `?q` var TERM, the goal
/// term, the answered symbol)`; [`add_term_route`] supplies the second route.
///
/// The rule shape is `crate::common::one_goal_carrier_fixture` (WI-1023 lifted it there
/// on its second use — it needs the same gadget for every carrier, and this file
/// is the special case with one `Value::SymbolRef` slot).
fn dedup_fixture() -> (
    KnowledgeBase,
    anthill_core::kb::term::TermId,
    anthill_core::kb::term::TermId,
    Symbol,
) {
    let answer_name = "wi1016_answer";
    let (mut kb, q_term, goal) = crate::common::one_goal_carrier_fixture("wi1016_dup", |kb| {
        let answer = kb.intern(answer_name);
        vec![vec![Value::SymbolRef(answer)]]
    });
    let answer = kb.intern(answer_name);
    (kb, q_term, goal, answer)
}

// ── helpers ─────────────────────────────────────────────────────────────────

/// The payload of an `Option[Int64]` answer, or `None` for `none()`.
fn option_int(interp: &Interpreter, v: &Value) -> Option<i64> {
    match v {
        Value::Entity { functor, named, .. } => match interp.kb().local_name_of(*functor) {
            "none" => None,
            "some" => match named.first().map(|(_, x)| x) {
                Some(Value::Int(n)) => Some(*n),
                other => panic!("some(value:) should carry an Int, got {other:?}"),
            },
            other => panic!("expected an Option, got {other}"),
        },
        other => panic!("expected an Option entity, got {other:?}"),
    }
}
