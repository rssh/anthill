//! WI-625 (proposal 051 Phase 2, the eval→SLD dual) — the INTERPRETER's
//! semantic `eq`/`neq` must dispatch through a carrier's `Eq` instance, the
//! same way the resolver does (WI-616), instead of answering structurally.
//!
//! `Set`/`Map` equality is membership-based (`insert`/`put` are commutative +
//! idempotent), so two structurally-distinct spellings denote one value. WI-616
//! made the RESOLVER honor that; before WI-625 an operation body evaluated by
//! the interpreter still compared them structurally (`builtin_eq` =
//! `views_structurally_equal`), so the same program answered differently by
//! backend (kernel-language.md documented the caveat).
//!
//! We feed the interpreter's `eq`/`neq` the symbolic set VALUES directly — the
//! same `insert`/`empty` terms WI-616 builds at the resolver — rather than
//! through a typed op body. Dispatching `eq` over `Set` in a typed body needs
//! the typer to resolve `Set`'s `requires Eq[T]` ELEMENT dictionary (the
//! requirement-dictionary tier, WI-300 Tier B), which is a SEPARATE gap; this
//! slice is only about what the interpreter's `eq` does once two symbolic set
//! values reach it (as `List.member`'s abstract `eq(head, x)` does at runtime).
//!
//! Two eval entry points are exercised:
//!   * `PartialEq.eq`/`neq` — the registered builtin (`builtin_eq`/`neq` →
//!     `semantic_equal`): the abstract-spec-op path (gap 5).
//!   * `Set.eq` directly — a body-less, rule-backed Bool predicate the
//!     interpreter cannot run itself; the eval→SLD bridge in the dispatch
//!     fall-through proves it (gaps 4/6, the typed-PinNow shape).

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term::{Literal, Term, TermId};
use smallvec::SmallVec;

fn interp() -> Interpreter {
    // A trivial user namespace; the point is the full stdlib (Set/Map/PartialEq).
    crate::common::interp_for("namespace test.wi625\nend\n")
}

fn int_term(i: &mut Interpreter, n: i64) -> TermId {
    i.kb_mut().alloc(Term::Const(Literal::Int(n)))
}

fn fn_term(i: &mut Interpreter, qualified: &str, args: &[TermId]) -> TermId {
    let sym = i
        .kb()
        .try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    i.kb_mut().alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// `insert(insert(… empty(), e1 …), en)` over `anthill.prelude.Set`, as a Value.
fn set_val(i: &mut Interpreter, elems: &[i64]) -> Value {
    let mut s = fn_term(i, "anthill.prelude.Set.empty", &[]);
    for &e in elems {
        let et = int_term(i, e);
        s = fn_term(i, "anthill.prelude.Set.insert", &[s, et]);
    }
    Value::term(s)
}

/// `put(put(… empty(), k1, v1 …), kn, vn)` over `anthill.prelude.Map`, as a Value.
fn map_val(i: &mut Interpreter, entries: &[(i64, i64)]) -> Value {
    let mut m = fn_term(i, "anthill.prelude.Map.empty", &[]);
    for &(k, v) in entries {
        let kt = int_term(i, k);
        let vt = int_term(i, v);
        m = fn_term(i, "anthill.prelude.Map.put", &[m, kt, vt]);
    }
    Value::term(m)
}

fn call2(i: &mut Interpreter, op: &str, a: Value, b: Value) -> bool {
    i.call(op, &[a, b])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
        .as_bool()
        .unwrap_or_else(|| panic!("call {op}: not a Bool"))
}

const EQ: &str = "anthill.prelude.PartialEq.eq";
const NEQ: &str = "anthill.prelude.PartialEq.neq";
const SET_EQ: &str = "anthill.prelude.Set.eq";

// ── Site A: the `PartialEq.eq`/`neq` builtin dispatches semantically ──────

#[test]
fn eval_eq_set_ignores_insertion_order() {
    let mut i = interp();
    let (a, b) = (set_val(&mut i, &[1, 2]), set_val(&mut i, &[2, 1]));
    assert!(call2(&mut i, EQ, a, b), "eq({{1,2}},{{2,1}}) must hold at eval");
}

#[test]
fn eval_eq_set_ignores_duplicates() {
    let mut i = interp();
    let (a, b) = (set_val(&mut i, &[1]), set_val(&mut i, &[1, 1]));
    assert!(call2(&mut i, EQ, a, b), "eq({{1}},{{1,1}}) must hold at eval");
}

#[test]
fn eval_eq_set_distinguishes_members() {
    let mut i = interp();
    let (a, b) = (set_val(&mut i, &[1, 2]), set_val(&mut i, &[1, 3]));
    assert!(!call2(&mut i, EQ, a, b), "eq({{1,2}},{{1,3}}) must not hold");
}

#[test]
fn eval_neq_set() {
    let mut i = interp();
    let (a, b) = (set_val(&mut i, &[1, 2]), set_val(&mut i, &[2, 1]));
    assert!(!call2(&mut i, NEQ, a, b), "neq({{1,2}},{{2,1}}) must be false (equal by membership)");
    let (c, d) = (set_val(&mut i, &[1, 2]), set_val(&mut i, &[1, 3]));
    assert!(call2(&mut i, NEQ, c, d), "neq({{1,2}},{{1,3}}) must be true");
}

#[test]
fn eval_eq_nested_set_dispatches_elementwise() {
    // Set[Set[Int]]: inner sets compare by membership too (the element compare
    // in `member` is the SEMANTIC eq, so dispatch recurses).
    let mut i = interp();
    let i12 = set_term(&mut i, &[1, 2]);
    let i21 = set_term(&mut i, &[2, 1]);
    let i3 = set_term(&mut i, &[3]);
    let a = Value::term(nest(&mut i, &[i12, i3]));
    let b = Value::term(nest(&mut i, &[i3, i21]));
    assert!(call2(&mut i, EQ, a, b), "eq({{{{1,2}},{{3}}}},{{{{3}},{{2,1}}}}) must hold elementwise");
}

// WI-650 reconciliation: `eval_eq_map_honors_membership_and_shadowing` (map eq via
// the relational `map_eq`/`binds`/`strip_is` apparatus) was DELETED — WI-650 dropped
// that apparatus, deferring Map equality to the WI-625 host bridge. A typed `eq(map,
// map)` is now a LOAD error (`check_eq_override_backing`), locked in by
// `map_eq_error_test`; the eval-side membership/shadowing behavior returns with the
// host bridge. (Set eq — subset-backed — is unaffected; see the nested-Set tests.)

// ── ground structural uses keep their pre-WI-625 answers ─────────────────

#[test]
fn eval_eq_ints_unchanged() {
    let mut i = interp();
    let (a, b) = (Value::Int(7), Value::Int(7));
    assert!(call2(&mut i, EQ, a, b), "eq(7,7)");
    let (a, b) = (Value::Int(7), Value::Int(8));
    assert!(!call2(&mut i, EQ, a, b), "eq(7,8)");
    let (a, b) = (Value::Int(7), Value::Int(8));
    assert!(call2(&mut i, NEQ, a, b), "neq(7,8)");
    let (a, b) = (Value::Int(7), Value::Int(7));
    assert!(!call2(&mut i, NEQ, a, b), "neq(7,7)");
}

// ── Site B: `Set.eq`, a body-less rule-backed predicate, runs via the bridge ─

#[test]
fn eval_rule_backed_set_eq_runs_via_bridge() {
    let mut i = interp();
    let (a, b) = (set_val(&mut i, &[1, 2]), set_val(&mut i, &[2, 1]));
    assert!(call2(&mut i, SET_EQ, a, b), "Set.eq({{1,2}},{{2,1}}) must run via the eval→SLD bridge");
    let (c, d) = (set_val(&mut i, &[1, 2]), set_val(&mut i, &[1, 3]));
    assert!(!call2(&mut i, SET_EQ, c, d), "Set.eq({{1,2}},{{1,3}}) must be false");
}

// ── buried override under non-carrier structure: eval answers STRUCTURALLY
// (non-regressing), NOT a hard error. Full semantic descent is a follow-up. ──

#[test]
fn eval_eq_buried_override_stays_structural_not_error() {
    // `some({1,2})` vs `some({2,1})`: the head (Option.some) has no eq override
    // but a membership-equal Set is buried inside. The resolver SUSPENDS such a
    // compare; eval cannot, and — crucially — must NOT hard-error (that would
    // break any program comparing a compound that embeds a set). It falls back
    // to the structural verdict, exactly as it did before WI-625.
    let mut i = interp();
    let s12 = set_term(&mut i, &[1, 2]);
    let s21 = set_term(&mut i, &[2, 1]);
    let some1 = Value::term(fn_term(&mut i, "anthill.prelude.Option.some", &[s12]));
    let some2 = Value::term(fn_term(&mut i, "anthill.prelude.Option.some", &[s21]));
    // Must return a Bool (not Err); structural spelling differs ⇒ false.
    let r = i
        .call(EQ, &[some1.clone(), some2.clone()])
        .unwrap_or_else(|e| panic!("buried-override eq must return a Bool, not error: {e:?}"));
    assert_eq!(r.as_bool(), Some(false), "buried override falls back to structural (false)");
    // Identical spellings still hold by reflexivity.
    let s12b = set_term(&mut i, &[1, 2]);
    let s12c = set_term(&mut i, &[1, 2]);
    let same1 = Value::term(fn_term(&mut i, "anthill.prelude.Option.some", &[s12b]));
    let same2 = Value::term(fn_term(&mut i, "anthill.prelude.Option.some", &[s12c]));
    assert!(call2(&mut i, EQ, same1, same2), "some({{1,2}}) == some({{1,2}}) by reflexivity");
}

// helpers for nested sets
fn set_term(i: &mut Interpreter, elems: &[i64]) -> TermId {
    let mut s = fn_term(i, "anthill.prelude.Set.empty", &[]);
    for &e in elems {
        let et = int_term(i, e);
        s = fn_term(i, "anthill.prelude.Set.insert", &[s, et]);
    }
    s
}

fn nest(i: &mut Interpreter, elems: &[TermId]) -> TermId {
    let mut s = fn_term(i, "anthill.prelude.Set.empty", &[]);
    for &e in elems {
        s = fn_term(i, "anthill.prelude.Set.insert", &[s, e]);
    }
    s
}
