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
// enum returning Int literals. (A `requires`-carrying op whose body dispatches to
// a NON-builtin required spec op would residualize — the bridge's placeholder
// requirements don't supply that dictionary, WI-300 Tier B / gap 3. `List.member`
// is NOT such a case: its `eq(head, x)` is builtin-backed at eval, so it runs
// through the bridge fine — see `transitive_requires_contains_decides_via_member`.)
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

// ── WI-300 Tier B — transitive-requires rule (the integration goal) ──────────
//
// A rule whose `requires(Eq[T])` is grounded NOT by a direct Eq-op call but by a
// body call to `List.member` (which itself declares `requires Eq[T]`). The typer
// accepts `member` as a TRANSITIVE witness and rewrites the guard to check the
// element type at the concrete `member(?x, ?xs)` call; at resolution the operand
// runs through the gap-1 bridge (`member`'s abstract `eq(head, x)` is builtin-
// backed at eval, so its own `Eq` obligation needs no threaded dict here).
const CONTAINS_SRC: &str = r#"
    namespace gap3.membertest
      import anthill.prelude.{Int64, List, Bool, Eq}
      import anthill.prelude.List.{member}
      import anthill.prelude.PartialEq.{eq}
      -- A carrier that declares NO Eq instance: the fire-time guard must block
      -- has_elem over it, proving the transitive requirement is real, not vacuous.
      sort NoEq
        entity nt(v: Int64)
      end
      rule has_elem(?xs, ?x) :- requires(Eq[T]), eq(member(?x, ?xs), true)
    end
"#;

/// Build a `List` from a slice of already-built element terms (generalizes
/// `list_term`, which is Int64-only).
fn list_of(kb: &mut KnowledgeBase, elems: &[TermId]) -> TermId {
    let nil = kb.try_resolve_symbol("anthill.prelude.List.nil").expect("List.nil");
    let cons = kb.try_resolve_symbol("anthill.prelude.List.cons").expect("List.cons");
    let head = kb.intern("head");
    let tail = kb.intern("tail");
    let mut list = kb.alloc(Term::Fn { functor: nil, pos_args: SmallVec::new(), named_args: SmallVec::new() });
    for &e in elems.iter().rev() {
        list = kb.alloc(Term::Fn {
            functor: cons,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head, e), (tail, list)]),
        });
    }
    list
}

/// A `gap3.membertest.NoEq.nt(v: n)` entity term (a carrier with no `Eq`).
fn nt_entity(kb: &mut KnowledgeBase, n: i64) -> TermId {
    let f = kb.try_resolve_symbol("gap3.membertest.NoEq.nt").expect("NoEq.nt");
    let v = kb.intern("v");
    let nv = int_term(kb, n);
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(v, nv)]),
    })
}

#[test]
fn transitive_requires_rule_types_via_member() {
    // The whole point: this rule did NOT type before Layer A — the grounding scan
    // witnessed `requires(Eq[T])` only on a DIRECT Eq-op call, and neither `member`
    // (a List op) nor the `eq(_, true)` (a PartialEq op over Bool) is one.
    assert!(
        common::try_load_kb_with(CONTAINS_SRC).is_ok(),
        "a rule whose requires(Eq[T]) is witnessed by a member() call must load",
    );
}

#[test]
fn transitive_requires_contains_decides_via_member() {
    let mut kb = common::load_kb_with(CONTAINS_SRC);
    // contains([1,2,3], 2): guard fires (Int64 provides Eq), member(2,[1,2,3]) runs
    // to `true` via the bridge, eq(true, true) succeeds ⇒ one definite solution.
    let xs = list_term(&mut kb, &[1, 2, 3]);
    let two = int_term(&mut kb, 2);
    let g = goal(&mut kb, "gap3.membertest.has_elem", &[xs, two]);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "contains([1,2,3], 2) must decide TRUE via the transitive witness");
    assert!(sols[0].residual.is_empty(), "the member() operand ran at resolution — a definite solution");

    // contains([1,2,3], 5): member(5,[1,2,3]) = false, eq(false, true) fails ⇒ none.
    let xs2 = list_term(&mut kb, &[1, 2, 3]);
    let five = int_term(&mut kb, 5);
    let g2 = goal(&mut kb, "gap3.membertest.has_elem", &[xs2, five]);
    assert_eq!(
        kb.resolve(&[g2], &ResolveConfig::default()).len(),
        0,
        "5 is not a member of [1,2,3]",
    );
}

#[test]
fn transitive_requires_guard_blocks_non_eq_element() {
    // The requirement is enforced, not vacuous: `NoEq` declares no `Eq` instance, so
    // the guard `DontFire`s at a `NoEq` element even though `nt(1)` IS structurally in
    // the list — the transitive witness checks the ELEMENT type, exactly as a direct
    // `requires(Eq[T])` would. Without the guard (plain member) this would succeed.
    let mut kb = common::load_kb_with(CONTAINS_SRC);
    let e1 = nt_entity(&mut kb, 1);
    let e2 = nt_entity(&mut kb, 2);
    let list = list_of(&mut kb, &[e1, e2]);
    let x = nt_entity(&mut kb, 1);
    let g = goal(&mut kb, "gap3.membertest.has_elem", &[list, x]);
    assert_eq!(
        kb.resolve(&[g], &ResolveConfig::default()).len(),
        0,
        "NoEq provides no Eq: the guard must block has_elem despite nt(1) being present",
    );
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

#[test]
fn transitive_requires_rejects_wrong_type_param_witness() {
    // Soundness gate: `pick(t: T, u: U) requires Eq[U]` must NOT witness a rule's
    // `requires(Eq[T])`. Its `Eq` obligation ranges over `U` (the `u` argument), but
    // the fire-time guard keys on `Eq`'s type-param NAME ("T"), so it would read the
    // name-coincident `t: T` — discharging the requirement against the WRONG argument.
    // The witness is declined and the rule is a loud load error instead of grounding
    // unsoundly. (Without the gate, `op_requires_covers` would accept `pick` because
    // `Eq` is merely present in its requires-chain.)
    let src = r#"
        namespace gap3.unsound
          import anthill.prelude.{Int64, Bool, Eq}
          import anthill.prelude.PartialEq.{eq}
          sort Two
            sort T = ?
            sort U = ?
            entity mk(t: T, u: U)
            operation pick(t: T, u: U) -> Bool requires Eq[U] = eq(u, u)
          end
          import gap3.unsound.Two.{pick}
          rule uses(?t, ?u) :- requires(Eq[T]), eq(pick(?t, ?u), true)
        end
    "#;
    let errs = match common::try_load_kb_with(src) {
        Ok(_) => panic!("a witness requiring Eq over a DIFFERENT type-param must not ground"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("ground the requirement")),
        "expected the ungroundable-requires error, got: {errs:?}",
    );
}

// ── WI-625 Layer B — bridged op dispatching a USER spec op via a real dict ────
//
// `Box.combineBox` has a host body that dispatches the user-defined `Combiner.combine`
// on its abstract element (`Box requires Combiner[T]`). At the bridge the resolver
// builds the REAL `Combiner` provider dictionary at the concrete element type and
// threads it into the op's frame, so the dispatch reaches `TagCombiner.combine` and
// DECIDES — where the gap-1 empty-dict floor would residualize. `Other` provides no
// `Combiner`, so a box over it is the unresolvable case (must residualize, not
// mis-decide).
const COMBINER_SRC: &str = r#"
    namespace gap3b.combiner
      import anthill.prelude.{Int64, Bool}
      import anthill.prelude.PartialEq.{eq}
      sort Combiner
        sort T = ?
        operation combine(x: T, y: T) -> T
      end
      sort Tag
        entity tag(n: Int64)
      end
      sort Other
        entity other(k: Int64)
      end
      sort TagCombiner
        provides Combiner[T = Tag]
        operation combine(x: Tag, y: Tag) -> Tag = tag(n: 99)
      end
      sort Box
        sort T = ?
        requires Combiner[T]
        entity box(content: T)
        operation combineBox(b: Box) -> T =
          match b
            case box(c) -> combine(c, c)
      end
      import gap3b.combiner.Box.{combineBox}
      rule combines_to(?b, ?r) :- eq(combineBox(?b), ?r)
    end
"#;

/// A `gap3b.combiner.Tag.tag(n: v)` entity term.
fn tag_entity(kb: &mut KnowledgeBase, v: i64) -> TermId {
    let f = kb.try_resolve_symbol("gap3b.combiner.Tag.tag").expect("Tag.tag");
    let n = kb.intern("n");
    let nv = int_term(kb, v);
    kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::new(), named_args: SmallVec::from_slice(&[(n, nv)]) })
}

/// A `gap3b.combiner.Box.box(content: <content>)` entity term.
fn box_of(kb: &mut KnowledgeBase, content: TermId) -> TermId {
    let f = kb.try_resolve_symbol("gap3b.combiner.Box.box").expect("Box.box");
    let c = kb.intern("content");
    kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::new(), named_args: SmallVec::from_slice(&[(c, content)]) })
}

fn definite_count(kb: &mut KnowledgeBase, g: TermId) -> usize {
    kb.resolve(&[g], &ResolveConfig::default())
        .iter()
        .filter(|s| s.residual.is_empty())
        .count()
}

#[test]
fn layerb_bridged_op_dispatches_user_spec_via_threaded_dict() {
    let mut kb = common::load_kb_with(COMBINER_SRC);
    // combineBox(box(tag(5))) = combine(tag(5), tag(5)) = tag(99) via the threaded
    // TagCombiner dict; eq(tag(99), tag(99)) succeeds ⇒ one definite solution.
    let tag5 = tag_entity(&mut kb, 5);
    let b = box_of(&mut kb, tag5);
    let tag99 = tag_entity(&mut kb, 99);
    let g = goal(&mut kb, "gap3b.combiner.combines_to", &[b, tag99]);
    assert_eq!(
        definite_count(&mut kb, g),
        1,
        "combineBox must DECIDE via the real Combiner dict built at the bridge",
    );

    // eq(tag(99), tag(5)) fails ⇒ no solution (the op still ran; the compare is false).
    let tag5b = tag_entity(&mut kb, 5);
    let b2 = box_of(&mut kb, tag5b);
    let tag5r = tag_entity(&mut kb, 5);
    let g2 = goal(&mut kb, "gap3b.combiner.combines_to", &[b2, tag5r]);
    assert_eq!(definite_count(&mut kb, g2), 0, "combineBox = tag(99) ≠ tag(5)");
}

#[test]
fn layerb_unresolvable_provider_residualizes() {
    // box(other(1)): the element `Other` provides no `Combiner`, so the bridge cannot
    // resolve the dictionary — it SUSPENDS and the operand residualizes. The soundness
    // property: NO definite solution (never run combineBox with a wrong/missing dict).
    let mut kb = common::load_kb_with(COMBINER_SRC);
    let otherf = kb.try_resolve_symbol("gap3b.combiner.Other.other").expect("Other.other");
    let k = kb.intern("k");
    let one = int_term(&mut kb, 1);
    let other1 = kb.alloc(Term::Fn { functor: otherf, pos_args: SmallVec::new(), named_args: SmallVec::from_slice(&[(k, one)]) });
    let b = box_of(&mut kb, other1);
    let r = int_term(&mut kb, 0);
    let g = goal(&mut kb, "gap3b.combiner.combines_to", &[b, r]);
    assert_eq!(
        definite_count(&mut kb, g),
        0,
        "Other provides no Combiner: the bridge must residualize, never mis-decide",
    );
}
