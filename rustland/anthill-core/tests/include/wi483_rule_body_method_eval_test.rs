//! WI-483 — a dispatched rule-body method-op call EVALUATES at SLD by the
//! occurrence-native by-symbol FOLD (the WI-487-enabled path).
//!
//! WI-282 rewrites a rule-body `?b.peek()` to `peek(?b)` (an operation Apply)
//! BEFORE SLD, but `peek` lives in `kb.op_bodies` (not a rule/fact head), so the
//! goal matched nothing. WI-483 folds a FOLDABLE op-call operand: it inlines the
//! op body with the call args substituted into the param vars by Symbol (WI-487),
//! then the existing WI-482 reductions (field_access) collapse it to a value.
//!
//! DECISION (user, 2026-06-16): a COMPLEX op-call (body needs the interpreter —
//! arithmetic, match/if/let, recursion) is LEFT uninterpreted, treated as
//! un-ground (it residualizes / delays), NOT a loud error — preserving
//! substitution transparency (a rule's validity must not depend on the callee's
//! body complexity). The interpreter bridge for complex bodies is a follow-up.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Term, Literal};
use anthill_core::parse;
use smallvec::SmallVec;

fn load_capturing_errors(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => (kb, vec![]),
        Err(errs) => (kb, errs),
    }
}

fn errors_text(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

/// Resolve `functor_qn(args...)` with explicit GROUND argument terms — a ground
/// query skips the caller-var delay pre-check, so the rule body actually runs
/// and the op-call fold is exercised (the WI-482 pattern).
fn resolve_query_ground(kb: &mut KnowledgeBase, functor_qn: &str, args: &[anthill_core::kb::term::TermId]) -> usize {
    let functor = kb.resolve_symbol(functor_qn);
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    kb.resolve(&[goal], &cfg).len()
}

/// Resolve a ground query and return its solutions (for residual inspection).
fn resolve_ground_solutions(kb: &mut KnowledgeBase, functor_qn: &str, args: &[anthill_core::kb::term::TermId]) -> Vec<Solution> {
    let functor = kb.resolve_symbol(functor_qn);
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    kb.resolve(&[goal], &cfg)
}

/// Build a ground `box(value: <v>)` entity term.
fn make_box(kb: &mut KnowledgeBase, box_qn: &str, v: i64) -> anthill_core::kb::term::TermId {
    let box_sym = kb.resolve_symbol(box_qn);
    let vk = kb.intern("value");
    let vv = kb.alloc(Term::Const(Literal::Int(v)));
    let mut named: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]> = SmallVec::new();
    named.push((vk, vv));
    kb.alloc(Term::Fn { functor: box_sym, pos_args: SmallVec::new(), named_args: named })
}

// ── Acceptance: a foldable rule-body method-op call evaluates at SLD ─────

#[test]
fn rule_body_method_call_folds_and_evaluates() {
    // `peek(b: Box) = ?b.value` is foldable (a single field access). The rule
    // `peeks(?b, ?v) :- holder(b: ?b), eq(?v, ?b.peek())` dispatches `?b.peek()`
    // to `peek(?b)`, which folds to `field_access(?b, value)` and (WI-482)
    // evaluates: `peeks(box(value:5), 5)` succeeds, `…(…, 99)` fails.
    let src = r#"
        namespace wi483.peek
          sort Box
            entity box(value: Int64)
            operation peek(b: Box) -> Int64 = ?b.value
          end
          sort Holder
            entity holder(b: Box)
          end
          rule peeks(?b, ?v)
            :- holder(b: ?b), eq(?v, ?b.peek())
          fact holder(b: box(value: 5))
        end
    "#;
    let (mut kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "clean load expected; got:\n{}", errors_text(&errs));

    let b5 = make_box(&mut kb, "wi483.peek.Box.box", 5);
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let n_match = resolve_query_ground(&mut kb, "wi483.peek.peeks", &[b5, five]);
    assert_eq!(n_match, 1, "?b.peek() must fold to box.value=5 ⇒ eq(5,5) succeeds");

    let b5b = make_box(&mut kb, "wi483.peek.Box.box", 5);
    let ninetynine = kb.alloc(Term::Const(Literal::Int(99)));
    let n_miss = resolve_query_ground(&mut kb, "wi483.peek.peeks", &[b5b, ninetynine]);
    assert_eq!(n_miss, 0, "box.value=5, not 99 ⇒ eq(99,5) fails (no silent success)");
}

// ── Transparency: a COMPLEX op-call is left un-ground, NOT a loud error ──

#[test]
fn rule_body_complex_method_call_is_left_unground_not_loud() {
    // `bump(b: Box) -> Int64 = ?b.value + 1` has arithmetic in its body — the
    // fold's field-access reducer does not collapse it, so it is COMPLEX. Per the
    // transparency rule it must NOT be a loud load error, and an `eq`/`neq` over it
    // must stay UNDECIDED (delay) rather than draw a wrong definite answer.
    //
    //   `bump(box(value:5))` is actually 6, but we cannot fold it. A `neq` operand
    //   treated as a concrete (unfoldable) node would `structural_eq`-mismatch and
    //   `neq` would SPURIOUSLY SUCCEED — claiming `6 ≠ bump` when in truth `6 = bump`.
    //   Treating the residual op-call as un-ground makes `neq` DELAY → the rule does
    //   not spuriously hold (0 solutions). That is the substitution-transparency bar.
    let src = r#"
        namespace wi483.complex
          sort Box
            entity box(value: Int64)
            operation bump(b: Box) -> Int64 = ?b.value + 1
          end
          sort Holder
            entity holder(b: Box)
          end
          rule eq_bumped(?b, ?v)
            :- holder(b: ?b), eq(?v, ?b.bump())
          rule ne_bumped(?b, ?v)
            :- holder(b: ?b), neq(?v, ?b.bump())
          fact holder(b: box(value: 5))
        end
    "#;
    let (mut kb, errs) = load_capturing_errors(src);
    // CORE transparency guarantee: a complex callee must not reject the rule.
    assert!(
        errs.is_empty(),
        "a complex op-call must NOT be a loud load error (substitution transparency); got:\n{}",
        errors_text(&errs)
    );
    // `neq(6, bump(box(value:5)))` must not yield a DEFINITE answer (bump IS 6,
    // but we cannot fold it). The un-ground op-call makes neq DELAY → it
    // RESIDUALIZES: a solution that carries the pending constraint, never a
    // definite (empty-residual) success. A definite solution here would be the
    // transparency bug — claiming `6 ≠ bump` we cannot actually prove.
    let b5 = make_box(&mut kb, "wi483.complex.Box.box", 5);
    let six = kb.alloc(Term::Const(Literal::Int(6)));
    let sols = resolve_ground_solutions(&mut kb, "wi483.complex.ne_bumped", &[b5, six]);
    let definite = sols.iter().filter(|s| s.residual.is_empty()).count();
    assert_eq!(
        definite, 0,
        "a complex op-call must never yield a DEFINITE neq answer (it must residualize); \
         got {} definite of {} solutions", definite, sols.len()
    );

    // `eq` over the same complex op-call also only residualizes — no definite
    // (empty-residual) decision, and no panic.
    let b5b = make_box(&mut kb, "wi483.complex.Box.box", 5);
    let six2 = kb.alloc(Term::Const(Literal::Int(6)));
    let eq_sols = resolve_ground_solutions(&mut kb, "wi483.complex.eq_bumped", &[b5b, six2]);
    assert_eq!(
        eq_sols.iter().filter(|s| s.residual.is_empty()).count(), 0,
        "a complex op-call must never yield a DEFINITE eq answer (it must residualize)"
    );
}
