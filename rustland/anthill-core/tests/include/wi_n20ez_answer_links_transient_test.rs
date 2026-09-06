//! **WI-20260905-N20EZ — AN ANSWER LINK IS TRANSIENT, SO IT DOES NOT ENTER THE
//! HASH-CONSED STORE.**
//!
//! WI-20260904-J0RM4 moved the query PATTERN off the store and measured what was left:
//! resolving a rule goal still grew `term_store_len` once per rebuilt spine node, for
//! ever. The site was `with_fresh_vars` building each query var's ANSWER LINK through
//! `term_from_debruijn`, whose De Bruijn arm allocated a `Term::Var(Global(fresh))` —
//! a fresh `VarId` makes every such term NEW, so hash-consing cannot dedup it — and
//! whose `Fn` arm re-allocated the rebuilt spine above it. The store is monotone under
//! a scoped-KB layer by design (WI-SPGBP), so a release afterwards is not available
//! exactly where a long-running process would need it.
//!
//! The links now ride the carriers the substitution already stores: `Value::Var` for a
//! fresh leaf, `Value::Entity` for a rebuilt spine, and the SHARED `Value::Term` for any
//! subterm with no variable beneath it (`substitute_vars_transient`). The obstacle was
//! never the storage — `Substitution.bindings` was already `ImHashMap<VarId, Value>` —
//! it was `KnowledgeBase::walk`, which chased var chains in `TermId` space and so could
//! not say "this chain ended at var v" without a term for v. `walk` is retired; every
//! chase sits on the carrier-neutral `chase_var`.
//!
//! WHAT IS CLOSED, AND WHAT WAS LOOKED FOR AND NOT FOUND. The answer link is closed.
//! `term_from_debruijn` still exists for the opener's `TermId`-typed type channels
//! (`OpenTypeRewrite::term`, reached from `open_debruijn_node`), and calling that
//! opener DIRECTLY on an `Apply` whose `recv_type` carries a De Bruijn var does intern
//! (`/code-review` measured +2 per call). Whether any path a PROGRAM takes reaches it
//! repeatedly was then measured end-to-end, and it does not: five shapes — a
//! `Modifiable[T = ?t]` goal, `is_modifiable(List[T = ?t])` under `eq` with `?t` bound
//! and free, `Modifiable[?t]`, and `wi_h054k`'s `[simp]` equation `mkr(?k) <=> Map[K =
//! ?k, V = Int64].empty()` fired through three evaluations of `dr()` — all grow the
//! store by 0 after the first run (goal type positions ride occurrence children; a
//! fired equation's rewrite is cached). So no row pins that channel.
//!
//! THE ONE RESIDUAL THAT IS REACHABLE is the goal walk's: the resolver σ-applies a
//! `Value::Term` goal through `reify`, whose `fn_value` lowers an all-leaf result
//! back to a hash-consed term — and interns a linked leaf that is still UNBOUND at
//! that walk as a new `Term::Var`. That only arises for a `Value::Term`
//! CONJUNCTION whose earlier goal linked a var the later goal mentions before
//! anything bound it (a rule body walks its own vars as occurrences and pays
//! nothing; the CLI's goals are occurrence patterns since J0RM4). MEASURED +2 per
//! resolve, and pinned red by [`a_term_conjunction_with_an_unbound_link_still_interns`]:
//! it goes red the day the walk stops interning — which needs every goal reader
//! (the constraint guard, the Bool hook, simp reassembly) to fold an `Entity` goal,
//! since a non-interning walk makes one; a non-interning twin was tried and those
//! readers went blind — and is deleted then, as J0RM4's row was for this ticket.
//!
//! # What each row measures, and what fails when the change is backed out
//!
//! The six FLATNESS rows are the measurement. Each runs one query shape N times against
//! a loaded KB and asserts `term_store_len` is UNCHANGED after the first. MEASURED on
//! the baseline (the growth per query, all of it after the pattern's conversion):
//!
//!  * [`a_simple_link_is_flat`] — `simple(?x)`: +1, the one fresh var term.
//!  * [`two_links_are_flat`] — `two_var(?a, ?b)`: +2, one per linked query var.
//!  * [`a_chained_clause_is_flat`] — `chain(?x)` :- `simple(?x)`: +2, one per clause
//!    opened.
//!  * [`a_compound_head_subterm_is_flat`] — head `wrapped(Box(v: #0))` queried
//!    `wrapped(?p)`: +2, the fresh var AND the rebuilt `Box` spine above it. This and
//!    the next row are what a leaf-only repair would leave leaking.
//!  * [`a_two_slot_compound_head_subterm_is_flat`] — `wrapped2(Pair(a: #0, b: #1))`
//!    queried `wrapped2(?p)`: +3.
//!  * [`a_fact_with_omitted_fields_is_flat`] — `Top(a: ?x)` against `fact Top(a: 1)`,
//!    whose omitted `b`/`c` are the loader's fresh Globals: the arity-0 legacy path of
//!    `with_fresh_vars`, which allocated a var term per head Global per match. Not in
//!    the ticket's list, but the same mechanism one branch over, and "no `kb.alloc` on
//!    the answer-link path" covers it.
//!
//! The GOAL-WALK rows are the regression guards `/code-review` measured the first
//! cut of this change against. A link on the new carriers must be σ-APPLIED by every
//! later reader exactly as the interned term was: the resolver's lazy goal walk
//! (`subst_var_leaf`, `step_init`), whose one-hop spelling of a `Value::Var` alias and
//! raw splice of an `Entity` spine let the discrimination tree match a bound fresh
//! leaf as a WILDCARD, after which the fact fast-path's `bind_compressed` overwrote
//! the proved binding; and the groundness owner `value_is_ground`, whose `Value::Var`
//! arm never consulted σ. They PASS on the baseline (the term carrier had no such
//! hole) and FAIL on that first cut:
//!
//!  * [`a_conjunct_after_a_compound_link_reads_the_bound_leaf`] — `h3(?p) :-
//!    wrapped(?p), q3(?p)` answered `Box(v: 3)`, a `Box` no fact declares, where the
//!    truth is NO solution; `h2` (`chk` instead of `q3`) is the positive twin.
//!  * [`naf_after_a_compound_link_reads_the_bound_leaf`] — `n1(?p) :- wrapped(?p),
//!    not(chk(?p))` answered nothing where the truth is `Box(v: 1)`; `n3` (against
//!    `q3`) answered nothing where the truth is both.
//!  * [`ground_after_a_compound_link_sees_through_the_leaf`] — `ground(?p)` after
//!    `wrapped(?p)` in a top-level conjunction delayed on the leaf `f` inside the
//!    `Entity` link although σ had bound `f`.
//!
//! The AGREEMENT rows PASS EITHER WAY by design: the carrier may not change an answer,
//! so a row that went red on the baseline would be measuring a behaviour change this
//! ticket promises not to make. [`compound_links_still_answer_their_matched_subterm`]
//! reads a compound link back through `answer_binding` and `TermView`, which is the
//! point — the link now arrives as a `Value::Entity`, and a carrier-specific read
//! would make this suite pass for the old carrier only.
//!
//! The J0RM4 row `resolution_of_a_rule_goal_still_grows_the_store_by_one` asserted the
//! baseline's growth on purpose so that closing this leak would trip it; it tripped, and
//! it is deleted as designed.

use std::rc::Rc;

use anthill_core::eval::value::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Var, VarId};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_kb_bare, load_kb_with, query_pattern_term, scalar_int};

/// Every shape the ticket measured, plus the omitted-field fact for the legacy path.
const SRC: &str = r#"
namespace n20ez
  entity Box(v: Int64)
  entity Pair(a: Int64, b: Int64)
  entity Top(a: Int64, b: Int64, c: Int64)
  fact Box(v: 1)
  fact Box(v: 2)
  fact Pair(a: 1, b: 2)
  fact Top(a: 1)
  rule simple(?x) :- Box(v: ?x)
  rule two_var(?a, ?b) :- Pair(a: ?a, b: ?b)
  rule chain(?x) :- simple(?x)
  rule wrapped(Box(v: ?x)) :- Box(v: ?x)
  rule wrapped2(Pair(a: ?a, b: ?b)) :- Pair(a: ?a, b: ?b)
end
"#;

/// Run `pattern` once to intern whatever shared vocabulary it names, then N more times
/// asserting the store did not move and the answer count did not either.
fn assert_flat(pattern: &str, expected_solutions: usize) {
    let mut kb = load_kb_bare(&[SRC]);
    let cfg = ResolveConfig::default();
    let warm = query_pattern_term(&mut kb, pattern);
    assert_eq!(
        kb.resolve(&[warm], &cfg).len(),
        expected_solutions,
        "`{pattern}` must actually answer, or this measures nothing",
    );
    let after_first = kb.term_store_len();

    for i in 0..4 {
        let goal = query_pattern_term(&mut kb, pattern);
        assert_eq!(
            kb.term_store_len(),
            after_first,
            "`{pattern}` round #{i}: the pattern's CONVERSION grew the store (J0RM4)",
        );
        assert_eq!(kb.resolve(&[goal], &cfg).len(), expected_solutions);
        let now = kb.term_store_len();
        assert_eq!(
            now,
            after_first,
            "`{pattern}` round #{i}: RESOLVING grew the hash-consed store by {} — an \
             answer link was interned; opening a clause must not enter the store",
            now as i64 - after_first as i64,
        );
    }
}

/// Baseline: +1 per query.
#[test]
fn a_simple_link_is_flat() {
    assert_flat("n20ez.simple(?x)", 2);
}

/// Baseline: +2 per query, one per linked query var.
#[test]
fn two_links_are_flat() {
    assert_flat("n20ez.two_var(?a, ?b)", 1);
}

/// Baseline: +2 per query, one per clause opened.
#[test]
fn a_chained_clause_is_flat() {
    assert_flat("n20ez.chain(?x)", 2);
}

/// Baseline: +2 per query — the leaf AND the rebuilt `Box` spine. A leaf-only repair
/// leaves this row red.
#[test]
fn a_compound_head_subterm_is_flat() {
    assert_flat("n20ez.wrapped(?p)", 2);
}

/// Baseline: +3 per query — two leaves and the rebuilt `Pair` spine.
#[test]
fn a_two_slot_compound_head_subterm_is_flat() {
    assert_flat("n20ez.wrapped2(?p)", 1);
}

/// The arity-0 legacy path: a fact whose omitted fields are the loader's fresh Globals
/// freshens each per match. Baseline: +2 per query (one per omitted field).
#[test]
fn a_fact_with_omitted_fields_is_flat() {
    assert_flat("n20ez.Top(a: ?x)", 1);
}

// ── The residual site, pinned ───────────────────────────────────────────────

/// `[loose(?x, ?y), simple(?y)]` as `Value::Term` goals: `loose` links `?y` to a
/// fresh var its body never binds, and the walk of `simple(?y)` reifies that link,
/// interning the fresh var — +2 per resolve (the var term and the rebuilt goal).
/// Asserted so the site is REMEMBERED, not relaxed. The control beside it: the same
/// pair with the link BOUND before the second goal walks is flat.
#[test]
fn a_term_conjunction_with_an_unbound_link_still_interns() {
    let mut kb = load_kb_bare(&[
        "namespace n20ez_w
  entity Box(v: Int64)
  fact Box(v: 1)
           rule loose(?x, ?y) :- Box(v: ?x)
  rule simple(?x) :- Box(v: ?x)
end
",
    ]);
    let cfg = ResolveConfig::default();
    let loose = kb.try_resolve_symbol("n20ez_w.loose").expect("loose loaded");
    let simple = kb.try_resolve_symbol("n20ez_w.simple").expect("simple loaded");
    let mut conj = |kb: &mut KnowledgeBase| {
        let (x_sym, y_sym) = (kb.intern("x"), kb.intern("y"));
        let x = kb.fresh_var(x_sym);
        let y = kb.fresh_var(y_sym);
        let xt = kb.alloc(anthill_core::kb::term::Term::Var(Var::Global(x)));
        let yt = kb.alloc(anthill_core::kb::term::Term::Var(Var::Global(y)));
        let g1 = kb.alloc(anthill_core::kb::term::Term::Fn {
            functor: loose,
            pos_args: smallvec::SmallVec::from_slice(&[xt, yt]),
            named_args: smallvec::SmallVec::new(),
        });
        let g2 = kb.alloc(anthill_core::kb::term::Term::Fn {
            functor: simple,
            pos_args: smallvec::SmallVec::from_elem(yt, 1),
            named_args: smallvec::SmallVec::new(),
        });
        assert_eq!(kb.resolve(&[Value::term(g1), Value::term(g2)], &cfg).len(), 1);
    };
    conj(&mut kb);
    let after_first = kb.term_store_len();
    conj(&mut kb);
    conj(&mut kb);
    let grew = kb.term_store_len() as i64 - after_first as i64;
    // The query terms themselves are new each round (fresh vars), so subtract what
    // the two goal terms cost: two var terms and two applications.
    assert!(
        grew > 2 * 4,
        "the walk of `simple(?y)` no longer interns the unbound link: the residual \
         site named in this file's header has been closed — delete this row rather \
         than relax it (grew {grew} over two rounds, of which 8 are the query terms)",
    );
}

// ── The goal walk reads the new carriers ────────────────────────────────────

/// The conjunction fixture, loaded WITH the stdlib so `not` and `ground` resolve.
const CONJ_SRC: &str = r#"
namespace n20ez_c
  entity Box(v: Int64)
  fact Box(v: 1)
  fact Box(v: 2)
  fact q3(Box(v: 3))
  fact chk(Box(v: 2))
  rule wrapped(Box(v: ?x)) :- Box(v: ?x)
  rule h3(?p) :- wrapped(?p), q3(?p)
  rule h2(?p) :- wrapped(?p), chk(?p)
  rule n1(?p) :- wrapped(?p), not(chk(?p))
  rule n3(?p) :- wrapped(?p), not(q3(?p))
end
"#;

/// The `v` slots of every definite `Box` answer for `name(?p)`, sorted.
fn box_values(kb: &mut KnowledgeBase, name: &str) -> Vec<i64> {
    let v = kb.intern("v");
    let (vids, sols) = resolve_with_vars(kb, name, 1);
    let mut got: Vec<i64> = sols
        .iter()
        .map(|s| {
            let p = kb.answer_binding(vids[0], &s.subst).expect("?p binds");
            let inner = p.named_arg(kb, v).expect("`v` slot").to_value();
            scalar_int(kb, &inner).expect("an Int64 in `v`")
        })
        .collect();
    got.sort();
    got
}

/// `wrapped(?p)` links `?p` to the head's `Box(v: ?f)` spine and its body binds `?f`;
/// the NEXT conjunct must see `Box(v: 1)` / `Box(v: 2)`, not a `Box` with a wildcard
/// slot that any stored `Box` matches.
#[test]
fn a_conjunct_after_a_compound_link_reads_the_bound_leaf() {
    let mut kb = load_kb_with(CONJ_SRC);
    assert_eq!(
        box_values(&mut kb, "n20ez_c.h3"),
        Vec::<i64>::new(),
        "`q3` holds only `Box(v: 3)`, which `wrapped` never produces: a solution here \
         means the link's bound leaf matched `q3`'s slot as a wildcard",
    );
    assert_eq!(
        box_values(&mut kb, "n20ez_c.h2"),
        vec![2],
        "`chk` holds `Box(v: 2)` and `wrapped` produces it",
    );
}

/// The same reading under negation: NAF over the link must be over the BOUND spine.
#[test]
fn naf_after_a_compound_link_reads_the_bound_leaf() {
    let mut kb = load_kb_with(CONJ_SRC);
    assert_eq!(
        box_values(&mut kb, "n20ez_c.n1"),
        vec![1],
        "`not(chk(?p))` must exclude exactly `Box(v: 2)`",
    );
    assert_eq!(
        box_values(&mut kb, "n20ez_c.n3"),
        vec![1, 2],
        "`not(q3(?p))` excludes nothing `wrapped` produces",
    );
}

/// `ground(?p)` after `wrapped(?p)` in a top-level conjunction: the link is an
/// `Entity` over the leaf `?f`, and σ has bound `?f` — the groundness owner must chase
/// that leaf rather than read the value-level var as unbound and delay.
#[test]
fn ground_after_a_compound_link_sees_through_the_leaf() {
    let mut kb = load_kb_with(CONJ_SRC);
    let wrapped = kb
        .try_resolve_symbol("n20ez_c.wrapped")
        .expect("wrapped loaded");
    let ground = kb
        .try_resolve_symbol("anthill.reflect.ground")
        .expect("the `ground` builtin is registered");
    let p_sym = kb.intern("p");
    let p = kb.fresh_var(p_sym);
    let goal = |functor| Value::Entity {
        functor,
        pos: Rc::from(vec![Value::Var(Var::Global(p))]),
        named: Rc::from(Vec::new()),
    };
    let sols = kb.resolve(&[goal(wrapped), goal(ground)], &ResolveConfig::default());
    assert_eq!(sols.len(), 2, "both `Box` facts reach `ground`");
    assert!(
        sols.iter().all(|s| s.is_definite()),
        "`ground(?p)` must DECIDE once `?f` is bound, not delay on the leaf; got \
         residuals {:?}",
        sols.iter().map(|s| s.residual.len()).collect::<Vec<_>>(),
    );
}

// ── Agreement: the answers are identical to the baseline's ──────────────────
//
// Every row below PASSES EITHER WAY by design.

/// Build `functor(?v1, …, ?vn)` as a value goal so the query vars' ids are in hand,
/// and return every definite solution.
fn resolve_with_vars(
    kb: &mut KnowledgeBase,
    name: &str,
    arity: usize,
) -> (Vec<VarId>, Vec<anthill_core::kb::resolve::Solution>) {
    let functor = kb
        .try_resolve_symbol(name)
        .unwrap_or_else(|| panic!("`{name}` did not load"));
    let v_sym = kb.intern("v");
    let vids: Vec<VarId> = (0..arity).map(|_| kb.fresh_var(v_sym)).collect();
    let goal = Value::Entity {
        functor,
        pos: Rc::from(
            vids.iter()
                .map(|&v| Value::Var(Var::Global(v)))
                .collect::<Vec<_>>(),
        ),
        named: Rc::from(Vec::new()),
    };
    let mut sols = kb.resolve(&[goal], &ResolveConfig::default());
    sols.retain(|s| s.is_definite());
    (vids, sols)
}

fn as_int(kb: &KnowledgeBase, v: &Value) -> i64 {
    scalar_int(kb, v).unwrap_or_else(|| panic!("expected an Int64 answer, got {v:?}"))
}

/// A direct link (`simple`) and a chained one (`chain`) both read back as the fact's
/// value: the fresh var the link named was bound by the body and the answer sees
/// through it.
#[test]
fn direct_and_chained_links_still_answer() {
    let mut kb = load_kb_bare(&[SRC]);
    for name in ["n20ez.simple", "n20ez.chain"] {
        let (vids, sols) = resolve_with_vars(&mut kb, name, 1);
        let mut got: Vec<i64> = sols
            .iter()
            .map(|s| {
                let b = kb.answer_binding(vids[0], &s.subst).expect("?x binds");
                as_int(&kb, &b)
            })
            .collect();
        got.sort();
        assert_eq!(got, vec![1, 2], "`{name}(?x)` must answer both `Box` facts");
    }
}

/// Two links in one clause each reach their own slot.
#[test]
fn two_links_still_answer_independently() {
    let mut kb = load_kb_bare(&[SRC]);
    let (vids, sols) = resolve_with_vars(&mut kb, "n20ez.two_var", 2);
    assert_eq!(sols.len(), 1);
    let a = kb.answer_binding(vids[0], &sols[0].subst).expect("?a binds");
    let b = kb.answer_binding(vids[1], &sols[0].subst).expect("?b binds");
    assert_eq!((as_int(&kb, &a), as_int(&kb, &b)), (1, 2));
}

/// A query var matched against a COMPOUND head subterm answers that subterm with its
/// slots filled by the body — read through `TermView`, since the link now arrives as a
/// `Value::Entity` spine over the bound leaves rather than a rebuilt term.
#[test]
fn compound_links_still_answer_their_matched_subterm() {
    let mut kb = load_kb_bare(&[SRC]);
    let box_sym = kb
        .try_resolve_symbol("n20ez.Box")
        .expect("Box is declared");
    let v = kb.intern("v");

    let (vids, sols) = resolve_with_vars(&mut kb, "n20ez.wrapped", 1);
    let mut got: Vec<i64> = sols
        .iter()
        .map(|s| {
            let p = kb.answer_binding(vids[0], &s.subst).expect("?p binds");
            match p.head(&kb) {
                ViewHead::Functor {
                    functor: Some(f), ..
                } => assert_eq!(f, box_sym, "the link is the head's `Box(…)` subterm"),
                other => panic!("expected a `Box` application, got {other:?}"),
            }
            let inner = p.named_arg(&kb, v).expect("`v` slot").to_value();
            as_int(&kb, &inner)
        })
        .collect();
    got.sort();
    assert_eq!(got, vec![1, 2]);

    let pair_sym = kb
        .try_resolve_symbol("n20ez.Pair")
        .expect("Pair is declared");
    let (a_sym, b_sym) = (kb.intern("a"), kb.intern("b"));
    let (vids, sols) = resolve_with_vars(&mut kb, "n20ez.wrapped2", 1);
    assert_eq!(sols.len(), 1);
    let p = kb.answer_binding(vids[0], &sols[0].subst).expect("?p binds");
    match p.head(&kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => assert_eq!(f, pair_sym),
        other => panic!("expected a `Pair` application, got {other:?}"),
    }
    let a = p.named_arg(&kb, a_sym).expect("`a` slot").to_value();
    let b = p.named_arg(&kb, b_sym).expect("`b` slot").to_value();
    assert_eq!((as_int(&kb, &a), as_int(&kb, &b)), (1, 2));
}

// ── The compound-carrier descent must also REASSEMBLE ────────────────────────
//
// `children_of` descends a `Value::Entity` / `Value::Tuple` because a goal whose var
// is linked to a compound head subterm now walks into one, so a `[simp]` redex nested
// inside is as reachable as one inside a `Term::Fn`. Descent alone is not enough:
// `build_node` pops the rewritten children and hands them to `reassemble_value`, which
// had no arm for either carrier and fell through to `node.clone()` — so the nested
// redex was visited, matched, FIRED, and its result silently DISCARDED (found by
// /code-review, after the descent had already landed).

/// A `[simp]` equation plus a compound to nest its redex inside.
const SIMP_SRC: &str = r#"
namespace n20ez_s
  entity Box(v: Int64)
  rule twice(?n) <=> dbl(?n) [simp]
end
"#;

/// Build `n20ez_s.twice(7)` as a hash-consed TERM value — the nested redex. Built by
/// hand rather than via `query_pattern_term`, which yields an OCCURRENCE (J0RM4) and so
/// would drive the `Value::Node` arm this pair of rows is not about.
fn twice_redex(kb: &mut KnowledgeBase) -> Value {
    use anthill_core::kb::term::{Literal, Term};
    let twice = kb
        .try_resolve_symbol("n20ez_s.twice")
        .expect("`twice` resolves");
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    Value::term(kb.alloc(Term::Fn {
        functor: twice,
        pos_args: smallvec::SmallVec::from_elem(seven, 1),
        named_args: smallvec::SmallVec::new(),
    }))
}

/// The functor of a value, whatever carrier it rides.
fn head_functor(kb: &KnowledgeBase, v: &Value) -> Option<String> {
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => Some(kb.qualified_name_of(f).to_string()),
        _ => None,
    }
}

/// CONTROL for the two rows below: the SAME redex at the TOP level fires. MEASURED to
/// pass with AND without the reassembly arm — it is what already worked, and it is here
/// so a failure of the nested rows cannot be blamed on the fixture not firing at all.
/// Backing the arm out leaves exactly the two nested rows red, each reading back the
/// unrewritten `n20ez_s.twice`.
#[test]
fn a_top_level_redex_fires() {
    let mut kb = load_kb_bare(&[SIMP_SRC]);
    let redex = twice_redex(&mut kb);
    let (out, changes) = kb.apply_eq_rules(&redex, 8, &Default::default());
    assert!(!changes.is_empty(), "the `[simp]` equation must fire at all");
    assert_eq!(
        head_functor(&kb, &out).as_deref(),
        Some("dbl"),
        "a top-level `twice(7)` rewrites to `dbl(7)`",
    );
}

/// A redex nested inside a `Value::Entity` spine. FAILS when `reassemble_value`'s
/// `Entity` arm is backed out: the child comes back `twice`, because the rewritten
/// children are popped and thrown away.
#[test]
fn a_redex_nested_in_an_entity_is_rewritten() {
    let mut kb = load_kb_bare(&[SIMP_SRC]);
    let redex = twice_redex(&mut kb);
    let functor = kb.try_resolve_symbol("n20ez_s.Box").expect("Box resolves");
    let spine = Value::Entity {
        functor,
        pos: std::rc::Rc::from(vec![redex].as_slice()),
        named: std::rc::Rc::from(Vec::new().as_slice()),
    };

    let (out, changes) = kb.apply_eq_rules(&spine, 8, &Default::default());
    assert!(!changes.is_empty(), "the nested redex must fire");
    let Value::Entity { pos, .. } = &out else {
        panic!("the spine must stay an Entity, got {}", out.type_name());
    };
    assert_eq!(
        head_functor(&kb, &pos[0]).as_deref(),
        Some("dbl"),
        "the nested `twice(7)` must be REWRITTEN in the reassembled spine, not discarded",
    );
}

/// The same for a `Value::Tuple`, the other carrier `children_of` descends.
#[test]
fn a_redex_nested_in_a_tuple_is_rewritten() {
    let mut kb = load_kb_bare(&[SIMP_SRC]);
    let redex = twice_redex(&mut kb);
    let tup = Value::Tuple {
        pos: std::rc::Rc::from(vec![redex].as_slice()),
        named: std::rc::Rc::from(Vec::new().as_slice()),
    };

    let (out, changes) = kb.apply_eq_rules(&tup, 8, &Default::default());
    assert!(!changes.is_empty(), "the nested redex must fire");
    let Value::Tuple { pos, .. } = &out else {
        panic!("the tuple must stay a Tuple, got {}", out.type_name());
    };
    assert_eq!(
        head_functor(&kb, &pos[0]).as_deref(),
        Some("dbl"),
        "the nested `twice(7)` must be REWRITTEN in the reassembled tuple",
    );
}

// ── A spliced link's leaves must stay VISIBLE to the occurrence var-walkers ───
//
// `subst_var_leaf` splices a compound answer link into a body occurrence as
// `Expr::Spliced(value)`, and `for_each_child` yields OCCURRENCE children — a spliced
// payload is a `Value`, so the walk structurally cannot descend it and `Spliced` sits in
// the no-children arm. Before N20EZ the same link was a rebuilt `Value::Term`, which
// `materialize_from_handle` turned into real `Expr::Var` leaves the walkers DID see; the
// transient link moved the common case onto the blind carrier (found by /code-review).
//
// The rows above all use a rule body that BINDS the compound's leaf, so none of them can
// see this: the question only bites when the leaf is still UNBOUND.

/// `loose`'s body never constrains the `Box` slot, so `?p` links to `Box(v: ?f)` with
/// `?f` genuinely unbound — the shape every row above lacks. `chk` holds a fact of a
/// DIFFERENT sort, so a ground `not(chk(?p))` would succeed outright.
const LOOSE_SRC: &str = r#"
namespace n20ez_l
  entity Box(v: Int64)
  entity Other(w: Int64)
  fact anchor()
  fact chk(Other(w: 1))
  rule loose(Box(v: ?x)) :- anchor()
  rule risky(?p) :- loose(?p), not(chk(?p))
end
"#;

/// `not(...)` in a RULE BODY is the path that actually goes blind: `step_naf` asks
/// `value_is_ground` about the whole `Value::Node` inner goal, and that walks the
/// occurrence — reaching the spliced link through `occurrence_has_unbound_var`. The
/// `ground(?x)` BUILTIN does not: it reads its argument through `walk_arg`, whose view
/// unwraps `Expr::Spliced` to the value it carries, so `value_is_ground` gets the
/// `Value::Entity` directly and its own (correct) Entity arm answers. That distinction
/// is why this row drives a rule body and not a top-level `ground` conjunct.
///
/// NAF over `Box(v: ?f)` with `?f` UNBOUND must FLOUNDER, not succeed: `?f` ranges over
/// values, and `chk` holding no `Box` fact does not make `not(chk(Box(v: ?f)))` provable
/// for every `?f` — that is the unsoundness NAF's groundness gate exists to prevent.
///
/// MEASURED CONTROL — backing out `occurrence_has_unbound_var`'s `Expr::Spliced` arm
/// leaves exactly this row red, and it fails as `got 1 solution(s), definiteness
/// [true]`: the walker sees a childless leaf, reports no unbound var, the gate reads
/// GROUND, and NAF runs over the non-ground goal and SUCCEEDS. Every other row in this
/// file stays green there, including the bound-leaf control below.
#[test]
fn naf_over_an_unbound_leaf_in_a_spliced_link_flounders() {
    let mut kb = load_kb_with(LOOSE_SRC);
    let risky = kb.try_resolve_symbol("n20ez_l.risky").expect("risky loaded");
    let p_sym = kb.intern("p");
    let p = kb.fresh_var(p_sym);
    let sols = kb.resolve(
        &[Value::Entity {
            functor: risky,
            pos: Rc::from(vec![Value::Var(Var::Global(p))]),
            named: Rc::from(Vec::new()),
        }],
        &ResolveConfig::default(),
    );
    assert!(
        !sols.iter().any(|s| s.is_definite()),
        "NAF over `Box(v: ?f)` with `?f` unbound must flounder, not answer definitely; \
         got {} solution(s), definiteness {:?}",
        sols.len(),
        sols.iter().map(|s| s.is_definite()).collect::<Vec<_>>(),
    );
}

/// CONTROL for the row above: the SAME rule-body NAF over a link whose leaf IS bound
/// still decides definitely. Passes either way — it is here so a failure above cannot be
/// read as "the Spliced arm made every rule-body NAF flounder".
#[test]
fn naf_over_a_bound_leaf_in_a_spliced_link_still_decides() {
    let mut kb = load_kb_with(CONJ_SRC);
    assert_eq!(
        box_values(&mut kb, "n20ez_c.n1"),
        vec![1],
        "a BOUND leaf must still decide — the Spliced arm must not blanket-flounder",
    );
}
