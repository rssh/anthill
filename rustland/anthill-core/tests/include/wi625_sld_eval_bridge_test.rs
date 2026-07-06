//! WI-625 gap 1 (the SLD→eval op-body dispatch bridge) — the dual of gaps
//! 4/5/6. When the resolver reduces an `eq`/`cmp` operand that is a call to a
//! CONCRETE op with a HOST body (`match`/`if`/`let`/recursion), the WI-483
//! structural fold can't collapse it, so it used to RESIDUALIZE (the operand
//! stayed un-reduced and the compare delayed). This slice bridges that point to
//! a live, bounded interpreter run (`KnowledgeBase::bridge_op_to_eval`): the
//! resolver LENDS its KB to a scratch `Interpreter`, runs the op, and reclaims
//! the KB — so a bodied op finally runs AT RESOLUTION.
//!
//! Soundness (the reason the bridge is three-valued, not decide-or-error):
//!   * ground-gated — `=`/`cmp` are tests that must never bind, so a non-ground
//!     operand delays instead of running (`nonground_operand_residualizes`).
//!   * suspend — the scratch interpreter runs in `bridge_mode`, so a semantic
//!     comparison that reaches a genuinely undecided point (a truncated proof or
//!     an eq-overriding carrier buried under non-overriding structure) raises
//!     `EvalError::Suspended` rather than importing a membership-wrong structural
//!     verdict into resolution (`bridge_mode_suspends_on_buried_override`).

use anthill_core::eval::{EvalConfig, EvalError, Interpreter, Value};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use crate::common;
use smallvec::SmallVec;

// A host-bodied op with ZERO spec dispatch in its body: a pure `match` over an
// enum returning Int literals. (A `requires`-carrying op like `List.member`
// needs its element `Eq` dictionary threaded — WI-300 Tier B / gap 3 — which
// the bridge's placeholder requirements don't supply, so it would residualize.)
const MATCH_SRC: &str = r#"
    namespace gap1.matchop
      import anthill.prelude.{Int64}
      sort Color
        entity red
        entity green
        entity blue
      end
      operation code(c: Color) -> Int64 =
        match c
          case red() -> 1
          case green() -> 2
          case blue() -> 3
      rule code_is(?c, ?v) :- eq(code(?c), ?v)
    end
"#;

fn int_term(kb: &mut KnowledgeBase, n: i64) -> TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

fn ref_term(kb: &mut KnowledgeBase, qualified: &str) -> TermId {
    let sym = kb
        .try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    kb.alloc(Term::Ref(sym))
}

fn fresh(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

fn goal(kb: &mut KnowledgeBase, functor: &str, args: &[TermId]) -> TermId {
    let f = kb
        .try_resolve_symbol(functor)
        .unwrap_or_else(|| panic!("symbol {functor} not in KB"));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

#[test]
fn host_bodied_match_op_decides_true_at_resolution() {
    // code_is(green(), 2): the operand `code(green())` is a match-bodied op the
    // fold can't reduce — the bridge runs it to `2`, so `eq(2, 2)` succeeds.
    // Before gap 1 this residualized (no definite solution).
    let mut kb = common::load_kb_with(MATCH_SRC);
    let green = ref_term(&mut kb, "gap1.matchop.Color.green");
    let two = int_term(&mut kb, 2);
    let g = goal(&mut kb, "gap1.matchop.code_is", &[green, two]);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "code(green())=2 must decide TRUE via the bridge");
    assert!(
        sols[0].residual.is_empty(),
        "must be a DEFINITE solution — the op ran at resolution, not a residual",
    );
}

#[test]
fn host_bodied_match_op_decides_false_at_resolution() {
    // code_is(green(), 3): the bridge runs code(green())=2; 2 ≠ 3 ⇒ NO solution.
    let mut kb = common::load_kb_with(MATCH_SRC);
    let green = ref_term(&mut kb, "gap1.matchop.Color.green");
    let three = int_term(&mut kb, 3);
    let g = goal(&mut kb, "gap1.matchop.code_is", &[green, three]);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    assert_eq!(sols.len(), 0, "code(green())=2 ≠ 3 ⇒ the bridge decides FALSE");
}

#[test]
fn nonground_operand_residualizes_no_bridge() {
    // code_is(?c, ?v) with BOTH unbound: `code(?c)` has a non-ground arg, so the
    // ground-gate blocks the bridge (`=` must never bind) — the compare delays.
    // The key soundness property: NO definite (empty-residual) solution appears,
    // which would mean the bridge bound a resolution variable.
    let mut kb = common::load_kb_with(MATCH_SRC);
    let c = fresh(&mut kb, "_c");
    let v = fresh(&mut kb, "_v");
    let g = goal(&mut kb, "gap1.matchop.code_is", &[c, v]);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    assert!(
        sols.iter().all(|s| !s.residual.is_empty()),
        "a non-ground operand must delay (residualize), never yield a definite \
         solution — got {} solution(s), some with empty residual",
        sols.len(),
    );
}

// A RECURSIVE host body — the case the structural fold fundamentally can't do
// (it caps at FOLD_DEPTH_CAP and never unrolls recursion): `last` walks a list
// to its final element via nested `match` + self-call. No spec ops in the body.
const REC_SRC: &str = r#"
    namespace gap1.recop
      import anthill.prelude.{Int64, List}
      operation last(xs: List[T = Int64]) -> Int64 =
        match xs
          case nil() -> 0
          case cons(h, t) ->
            match t
              case nil() -> h
              case cons(h2, t2) -> last(t)
      rule last_is(?xs, ?v) :- eq(last(?xs), ?v)
    end
"#;

fn list_term(kb: &mut KnowledgeBase, elems: &[i64]) -> TermId {
    let nil = kb.try_resolve_symbol("anthill.prelude.List.nil").expect("List.nil");
    let cons = kb.try_resolve_symbol("anthill.prelude.List.cons").expect("List.cons");
    let head = kb.intern("head");
    let tail = kb.intern("tail");
    let mut list = kb.alloc(Term::Fn { functor: nil, pos_args: SmallVec::new(), named_args: SmallVec::new() });
    for &e in elems.iter().rev() {
        let et = int_term(kb, e);
        list = kb.alloc(Term::Fn {
            functor: cons,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head, et), (tail, list)]),
        });
    }
    list
}

#[test]
fn recursive_host_bodied_op_runs_at_resolution() {
    // last([1,2,3]) = 3 — the bridge runs the recursion the fold can't unroll.
    let mut kb = common::load_kb_with(REC_SRC);
    let xs = list_term(&mut kb, &[1, 2, 3]);
    let three = int_term(&mut kb, 3);
    let g = goal(&mut kb, "gap1.recop.last_is", &[xs, three]);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "last([1,2,3])=3 must decide TRUE via the recursive bridge");
    assert!(sols[0].residual.is_empty(), "the recursion ran at resolution — a definite solution");

    // …and last([1,2,3]) ≠ 2 ⇒ no solution.
    let xs2 = list_term(&mut kb, &[1, 2, 3]);
    let two = int_term(&mut kb, 2);
    let g2 = goal(&mut kb, "gap1.recop.last_is", &[xs2, two]);
    assert_eq!(kb.resolve(&[g2], &ResolveConfig::default()).len(), 0, "last([1,2,3])=3 ≠ 2");
}

// ── The suspend channel (the user's soundness point) ─────────────────────────

const EQ: &str = "anthill.prelude.PartialEq.eq";

fn set_term(kb: &mut KnowledgeBase, elems: &[i64]) -> TermId {
    let empty = kb.try_resolve_symbol("anthill.prelude.Set.empty").expect("Set.empty");
    let insert = kb.try_resolve_symbol("anthill.prelude.Set.insert").expect("Set.insert");
    let mut s = kb.alloc(Term::Fn { functor: empty, pos_args: SmallVec::new(), named_args: SmallVec::new() });
    for &e in elems {
        let et = int_term(kb, e);
        s = kb.alloc(Term::Fn {
            functor: insert,
            pos_args: SmallVec::from_slice(&[s, et]),
            named_args: SmallVec::new(),
        });
    }
    s
}

/// `some({elems…})` — an eq-overriding `Set` carrier BURIED under `Option.some`
/// (whose own eq is structural), as a `Value`.
fn some_of_set(kb: &mut KnowledgeBase, elems: &[i64]) -> Value {
    let set = set_term(kb, elems);
    let some = kb.try_resolve_symbol("anthill.prelude.Option.some").expect("Option.some");
    Value::term(kb.alloc(Term::Fn {
        functor: some,
        pos_args: SmallVec::from_slice(&[set]),
        named_args: SmallVec::new(),
    }))
}

fn plain_interp() -> Interpreter {
    let kb = common::load_kb_with("namespace test.wi625.plain\nend\n");
    let mut i = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut i)
        .expect("register eval builtins");
    i
}

fn bridge_interp() -> Interpreter {
    let kb = common::load_kb_with("namespace test.wi625.bridge\nend\n");
    let mut i = Interpreter::with_config(kb, EvalConfig { bridge_mode: true, ..Default::default() });
    anthill_core::eval::builtins::register_standard_builtins(&mut i)
        .expect("register eval builtins");
    i
}

#[test]
fn bridge_mode_suspends_on_buried_override() {
    // {1,2} and {2,1} are one Set by membership but structurally distinct; buried
    // under `some(…)` the head is Option (structural eq), so eval's step-5 verdict
    // is the membership-WRONG `false`.
    //
    // Top-level eval keeps that documented structural answer; under the resolver
    // bridge (bridge_mode) importing it into resolution would be unsound, so eval
    // must SUSPEND — the resolver then delays exactly as its own `builtin_sem_eq`
    // does on a buried override.
    let mut plain = plain_interp();
    let (a, b) = (some_of_set(plain.kb_mut(), &[1, 2]), some_of_set(plain.kb_mut(), &[2, 1]));
    let r = plain.call(EQ, &[a, b]);
    assert!(
        matches!(r, Ok(Value::Bool(false))),
        "top-level eval keeps its documented structural verdict, got {r:?}",
    );

    let mut bridged = bridge_interp();
    let (a, b) = (some_of_set(bridged.kb_mut(), &[1, 2]), some_of_set(bridged.kb_mut(), &[2, 1]));
    let r = bridged.call(EQ, &[a, b]);
    assert!(
        matches!(r, Err(EvalError::Suspended { .. })),
        "under the resolver bridge a buried override must SUSPEND, got {r:?}",
    );
}
