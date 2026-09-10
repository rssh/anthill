//! **WI-20260906-7YPGM — THE RESOLVER'S GOAL WALK DOES NOT INTERN, AND EVERY GOAL
//! READER FOLDS THE CARRIER IT NOW BUILDS.**
//!
//! WI-20260905-N20EZ moved the ANSWER LINK off the hash-consed store and measured what
//! was left: the lazy goal walk (`resolve.rs::step_init`) σ-applied a `Value::Term` goal
//! through `KnowledgeBase::reify`, whose `fn_value` lowers an all-leaf result back to a
//! hash-consed term — and `lowers_to_leaf_term` accepts a `Value::Var`. A linked leaf
//! still UNBOUND at that walk was therefore interned as a fresh `Term::Var(Global(v))`,
//! which can NEVER dedup (`with_fresh_vars` mints a new `VarId` per clause opening), plus
//! the rebuilt goal above it. MEASURED +2 per resolve of `[loose(?x, ?y), simple(?y)]`
//! as `Value::Term` goals, for ever, under a store that is monotone by design
//! (WI-SPGBP). N20EZ pinned that site red in
//! `wi_n20ez_answer_links_transient_test::a_term_conjunction_with_an_unbound_link_still_interns`;
//! this ticket closes it and that row is DELETED, as J0RM4's was for N20EZ.
//!
//! **THE TICKET NAMED A SECOND SITE — `node_occurrence.rs::subst_var_leaf`'s `Term` arm
//! — AND IT IS NOT ONE.** Corrected by measurement rather than inherited: instrumented
//! with `term_store_len()` either side of that `reify` and run over `wi_tests`, it is
//! **31 084 entries, 0 that grew the store, and 0 that rebuilt an application at all**
//! (its `Entity`/`Tuple` sibling: 0 of both too). Reaching that arm means σ bound an
//! occurrence's var to a `Value::Term`, and the compound bindings with a var beneath
//! them to move do not arrive on that carrier — an answer link is a `Value::Var` /
//! `Value::Entity` / an UNTOUCHED shared `Value::Term` since N20EZ, and a fact match
//! binds ground subterms. So it is a chase-and-materialize, never a rebuild, and
//! switching it would have turned ~31k materialized occurrences into `Expr::Spliced`
//! spines with nothing measuring the difference. The reasoning is recorded at the site.
//!
//! # The change, and why it is not a one-liner
//!
//! `reify` gained a carrier parameter (`ReifyCarrier`) and the goal walk takes the
//! `Transient` one: a σ-MOVED application is rebuilt as a `Value::Entity` spine instead
//! of an interned `Term::Fn`. Nothing else moves — an untouched goal is still the SHARED
//! `Value::Term` it already was, and an `Entity` and its interned twin read identically
//! through `TermView`, index to the same `DiscrimKey`s and fingerprint to the same
//! `GoalKey`.
//!
//! What that costs is that `Value::Entity` becomes a GOAL carrier, and four readers
//! folded `Term` / `Node` only. Each answered NOTHING (or worse) for the new one, and
//! only ONE of them had a test — which is why they are driven here:
//!
//!  * **The WI-580 Bool relational view** — `constraint c: no ?ls: Box(items: ?ls) -:
//!    contains(?ls, "z")` LOADED CLEAN over a row that violates it. Its `other =>
//!    other.clone()` arm handed `reduce_op_value` a value it returns untouched, and the
//!    arm below then rebuilt it as the NULLARY `apply_f()`, DROPPING the goal's
//!    arguments. DRIVEN by `wi_dqd5w_spec_op_relational_view_test::
//!    a_constraint_guard_body_takes_the_relational_view` — the one existing row that
//!    caught any of this; it is not duplicated here.
//!  * **The WI-938 arity+1 functional-relation view** — [`the_arity_plus_one_view_reads_an_entity_goal`].
//!  * **`is_unreduced_builtin_call`** — [`an_entity_carried_builtin_operand_still_delays`].
//!    A WRONG ANSWER, not a missing one: the WI-738 soundness floor stopped firing, so a
//!    structural verdict was committed over an unevaluated call.
//!  * **`op_call_as_occ`** — [`an_entity_carried_op_call_operand_still_case_splits`].
//!    The WI-580 case-split was abandoned, so an equation that solves lost its solution.
//!  * **`walk_arg`** — [`a_rotated_builtin_reads_the_link_its_sibling_bound`]. A FIFTH,
//!    found by `/code-review` after the four above were fixed, and the one that LOST AN
//!    ANSWER: a builtin's argument slot can now hold a bare `Value::Var` (WI-109) and
//!    that function chased only the `Term::Var` and `Expr::Var` spellings, so a
//!    rotated `eq` read a link its sibling goal had already bound as still unbound and
//!    floundered. The four-reader list above is kept as written because it is what the
//!    first census found; this bullet is what says a census of goal readers is not
//!    finished when the goal itself reads right.
//!
//! **CARRIER-NEUTRAL MEANS READING `TermView`, NOT ADDING AN ARM PER CARRIER** — the
//! rule this ticket's first cut broke in four places and now follows. `walk_arg` and
//! `is_unreduced_builtin_call` are ONE VIEW READ each (`value_global_var` over
//! `index_var`; `head`), `op_call_as_occ` names only the `Node` carrier that has an
//! extra condition of its own and reads the view for the rest, and
//! `node_occurrence::value_as_occurrence` names only the two carriers that OWN a
//! materializer (`Node` IS an occurrence; `Term` has `materialize_from_handle`) and
//! reads `head` / `pos_arg` / `named_arg` for everything else. An arm list is what
//! drifted here in the first place: `walk_arg`'s had two of the three VAR spellings
//! and `is_unreduced_builtin_call`'s two of the three APPLICATION spellings. Where
//! the view is WIDER than the old list the difference is written out rather than
//! absorbed — `head` canonicalizes a bare `Ref` / `SymbolRef` to a nullary
//! application, which `is_unreduced_builtin_call` must NOT read as a call (§5.4's
//! unapplied function value is DATA) and `op_call_as_occ` MUST (WI-20260902-CZJ2N's
//! `tau()`); each says so at its site.
//!
//! Two readers named in the ticket needed NO change and are recorded so the list is not
//! read as complete-by-omission: `simp_rewrite`'s `children_of` / `reassemble_value`
//! already grew their `Entity` / `Tuple` arms in N20EZ (driven by
//! `wi_n20ez_answer_links_transient_test::a_redex_nested_in_an_entity_is_rewritten`), and
//! `value_is_ground` / `collect_unbound_vars_value` / `value_has_open_world_ref` are
//! carrier-neutral since WI-629.
//!
//! # WHAT THIS TICKET DOES NOT CLOSE
//!
//! The leak is HALVED on a goal that then makes a HEAD MATCH, not closed — corrected
//! here after `/code-review` measured the first cut's `with_fresh_vars` note ("nothing
//! on this path enters" the store) FALSE. That function normalizes every non-`Term`
//! `tree_subst` entry back through `value_to_term`, because the walks beneath it read
//! `tree_subst` term-only (the WI-636 boundary), and an `Entity` goal is exactly what
//! now arrives there. `[loose(?a, ?y), unify(?x, Box(v: ?y)), takes(?x)]` grew +4 per
//! resolve at HEAD and grows +2 here. Pinned by
//! [`a_head_match_over_an_entity_goal_still_interns`], which is deleted the day that
//! boundary is retired.
//!
//! # What each row measures, and what fails when the change is backed out
//!
//! MEASURED by mutating each shipped line one at a time (`if false` on a guard, the old
//! carrier match restored) and re-running — not predicted. Each back-out leaves exactly
//! ONE row red:
//!
//! | back out | red row |
//! |---|---|
//! | `step_init`'s walk → HEAD's `Term`-only interning match | [`the_walk_is_flat_over_an_unbound_link`] |
//! | `reify_value_transient`: `Transient` → `HashConsed` (the CARRIER alone) | [`the_walk_is_flat_over_an_unbound_link`] |
//! | the Bool view's `value_as_occurrence` → the `Term`/`Node` match | `wi_dqd5w_spec_op_relational_view_test::a_constraint_guard_body_takes_the_relational_view` **and** `…::a_quantified_constraint_over_a_spec_op_holds_for_well_formed_rows` |
//! | the arity+1 view's `value_as_occurrence` → the `Term`/`Node` match | [`the_arity_plus_one_view_reads_an_entity_goal`] |
//! | `is_unreduced_builtin_call`'s view read → the `Node`/`Term` carriers only | [`an_entity_carried_builtin_operand_still_delays`] |
//! | `op_call_as_occ`'s view read → the `Term` carrier only | [`an_entity_carried_op_call_operand_still_case_splits`] |
//! | `walk_arg`'s view read → every var spelling but the bare `Value::Var` | *(green alone — see the PAIR below)* |
//! | `value_as_occurrence`'s `is_reflect_form_functor` branch | [`a_reflect_form_reads_the_same_from_both_carriers`] |
//!
//! TWO REPAIRS SHARE ONE ROW, AND NEITHER IS SEPARATELY ATTRIBUTED — said here rather
//! than left for a reader to discover from a back-out that changes nothing.
//! [`a_rotated_builtin_reads_the_link_its_sibling_bound`] goes red ONLY when BOTH of
//! these are backed out, and stays green under either one alone (measured, all three
//! ways):
//!
//!  * **the walk applies σ to EVERY carrier** — `step_init` calls
//!    `reify_value_transient` on the whole goal rather than matching `Term` / `Node`
//!    with an `other => other` fall-through. It MEMOIZES the walked goal back into
//!    `goals[0]`, so once a goal first moves onto the `Entity` carrier that
//!    fall-through froze it at the first visit's σ for every later visit — the
//!    interning walk got this for free by always handing back a `Value::Term`.
//!  * **`walk_arg` asks the view** — `value_global_var` over `TermView::index_var`,
//!    ONE question covering `Term::Var`, `Expr::Var` and the bare `Value::Var`
//!    (WI-109) its old arm list left out.
//!
//! Both are kept. The first is the root — the freeze reaches EVERY σ-free reader of
//! `goals[0]` (`query_view`'s candidate selection, `apply_eq_rules`' redex,
//! `gather_extent_rows`' push-down), and only the one reader this row drives is
//! repaired by the second. The second is `walk_arg`'s own stated contract ("the
//! representation-agnostic analog of `walk(goal's positional arg, σ)`", and
//! `value_is_unbound_var`'s doc names it as the caller that walks first); 2 of 3
//! spellings is the asymmetry class this whole ticket is about, and asking the view
//! removes the list that could drift again. No fixture separates them, and none is
//! claimed to.
//!
//! CONTROLS — each passes with every one of those backed out:
//!
//!  * [`a_bound_link_was_already_flat`] — the same conjunction with the link BOUND. A
//!    ground rebuild dedups, so the interning walk was ALREADY flat here; the row above
//!    needs an UNBOUND link to see anything, and this says so rather than leaving it to
//!    be inferred.
//!  * The in-row control at the head of each reader row: the SAME call with no
//!    preceding goal, so σ is empty, `step_init` skips the walk entirely, and the goal
//!    stays the `Value::Term` that reader has always folded. That is what attributes
//!    each failure to the CARRIER rather than to the fixture — and the builtin row's
//!    binding goal is additionally asserted to ANSWER, because an earlier cut of it
//!    used a positional goal against a named-arg fact and passed by falling through
//!    before reaching the operand at all.
//!  * `wi738_operand_call_delay_test`'s six rows and
//!    `push_choice_test::wi668_term_carried_opcall_eq_case_splits` — the `Node` and
//!    `Term` faces of the two predicates widened here. They stay green under every
//!    back-out above, which is what says the arms were ADDED and not moved.
//!
//! No performance change is claimed: `wi_tests` ran 365.45 s at HEAD (4438 rows) and
//! 367.47 s here (4445), and suite-granularity sampling cannot resolve a few percent
//! either way. A paired in-process measurement is what would, and none was taken —
//! `reify_value_children`'s doc records the one place a rebuild could be shared and
//! why that is not taken on this ticket's evidence.

use anthill_core::eval::value::Value;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

use crate::common::{load_kb_bare, scalar_int};

// ── Term-goal plumbing ───────────────────────────────────────────────────────
//
// Every row here builds its goals as hash-consed TERMS and calls `kb.resolve` directly.
// That is the carrier the ticket is about: a rule body carries OCCURRENCES (WI-246) and
// walks its own vars through `subst_var_leaf`, and the CLI's queries have been
// occurrence patterns since J0RM4 — so only a direct `kb.resolve(&[Value::term(..)])`,
// `execute_logical_query`, a constraint guard (`lower_query`) or the reflect
// `execute(and(..))` reaches the `Value::Term` goal walk at all.

/// A fresh logic variable as a term.
fn var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let s = kb.intern(name);
    let v = kb.fresh_var(s);
    kb.alloc(Term::Var(Var::Global(v)))
}

/// `qn(args…)` as a hash-consed application term.
fn call(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let f = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("`{qn}` must resolve"));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// Resolve a term conjunction, keeping only DEFINITE solutions — the WI-519 decision
/// boundary, so a floundered residual cannot be counted as a proof.
///
/// FILTERED, not `definite_only: true`, and the difference is measured: that flag
/// PRUNES the search as well as the answers, and the WI-580 case-split reaches its
/// solution through a branch it drops (`eq(append(?a, [3]), [1,3])` answers 1 filtered
/// and 0 pruned). `push_choice_test::wi668_term_carried_opcall_eq_case_splits` — this
/// file's own control for that row — reads it the filtered way for the same reason.
fn definite(kb: &mut KnowledgeBase, goals: &[TermId]) -> Vec<anthill_core::kb::resolve::Solution> {
    let gs: Vec<Value> = goals.iter().map(|&t| Value::term(t)).collect();
    kb.resolve(&gs, &ResolveConfig::default())
        .into_iter()
        .filter(anthill_core::kb::resolve::Solution::is_definite)
        .collect()
}

/// The stdlib **and the Rust bindings** plus one extra file — the shape the reader rows
/// need (`eq`, `append`, `Numeric.add` all live there). `collect_stdlib_and_rust_bindings`
/// rather than the stdlib alone: the primitive spec FACTS (`fact Numeric[Int64]` and
/// friends) live in the binding files, and without them a `dbl(3, ?r)` control answers
/// nothing for a reason that has nothing to do with this ticket — measured.
fn load_with_stdlib(extra: &str) -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}")));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|e| panic!("load: {e:?}"));
    kb
}

// ── THE MEASUREMENT ──────────────────────────────────────────────────────────

/// `loose`'s body never constrains `?y`, so the head match links the caller's `?y` to a
/// fresh var that stays UNBOUND — the one shape whose walk interned, since a fresh
/// `VarId` makes every var term new.
const FLAT_SRC: &str = r#"
namespace ypgm_f
  entity Box(v: Int64)
  fact Box(v: 1)
  rule loose(?x, ?y) :- Box(v: ?x)
  rule simple(?x) :- Box(v: ?x)
end
"#;

/// Build the goals ONCE and resolve N times: the store must not move at all after the
/// first resolve. (N20EZ's own row had to subtract the query terms because it rebuilt
/// them per round; hoisting them out of the loop makes the assertion exact.)
///
/// FAILS when `step_init`'s walk is narrowed back to `kb.reify`: +2 per resolve, the
/// fresh `Term::Var` and the rebuilt `simple(…)` above it.
#[test]
fn the_walk_is_flat_over_an_unbound_link() {
    let mut kb = load_kb_bare(&[FLAT_SRC]);
    let (x, y) = (var(&mut kb, "x"), var(&mut kb, "y"));
    let g1 = call(&mut kb, "ypgm_f.loose", &[x, y]);
    let g2 = call(&mut kb, "ypgm_f.simple", &[y]);

    assert_eq!(
        definite(&mut kb, &[g1, g2]).len(),
        1,
        "the conjunction must actually answer, or this measures nothing",
    );
    let after_first = kb.term_store_len();
    for round in 0..4 {
        assert_eq!(definite(&mut kb, &[g1, g2]).len(), 1);
        let now = kb.term_store_len();
        assert_eq!(
            now,
            after_first,
            "round #{round}: RESOLVING grew the hash-consed store by {} — the walk of \
             `simple(?y)` interned the still-unbound link `loose` wrote for `?y`. The \
             store is monotone under a scoped-KB layer (WI-SPGBP), so this is an \
             unbounded leak, not a one-off",
            now as i64 - after_first as i64,
        );
    }
}

/// CONTROL, and it PASSES EITHER WAY by design: the same pair with the link BOUND
/// before the second goal walks. `simple(?x)` reifies to a GROUND term, which
/// hash-consing dedups, so the interning walk was already flat here — which is exactly
/// why the row above needs an UNBOUND link to see anything at all.
#[test]
fn a_bound_link_was_already_flat() {
    let mut kb = load_kb_bare(&[FLAT_SRC]);
    let (x, y) = (var(&mut kb, "x"), var(&mut kb, "y"));
    let g1 = call(&mut kb, "ypgm_f.loose", &[x, y]);
    let g2 = call(&mut kb, "ypgm_f.simple", &[x]);

    assert_eq!(definite(&mut kb, &[g1, g2]).len(), 1);
    let after_first = kb.term_store_len();
    for round in 0..4 {
        assert_eq!(definite(&mut kb, &[g1, g2]).len(), 1);
        assert_eq!(
            kb.term_store_len(),
            after_first,
            "round #{round}: a GROUND rebuild dedups, so this row was flat on the \
             baseline too",
        );
    }
}

// ── The residue this ticket does NOT close, pinned ───────────────────────────

/// `takes(?b)` gives the goal a HEAD MATCH to make; `unify` binds `?x` to a spine
/// whose leaf is the still-unbound link, so the third goal reaches that head match
/// carrying a `Value::Entity`.
const RESIDUE_SRC: &str = r#"
namespace ypgm_z
  entity Box(v: Int64)
  fact Box(v: 1)
  rule loose(?x, ?y) :- Box(v: ?x)
  rule takes(?b) :- Box(v: 1)
end
"#;

/// THE LEAK IS HALVED, NOT CLOSED, AND THE RESIDUE IS AT A DIFFERENT SITE. Found by
/// `/code-review` against the first cut of this ticket, whose `with_fresh_vars` note
/// claimed "nothing on this path enters" the store — which was false.
///
/// `with_fresh_vars` normalizes every NON-`Term` `tree_subst` entry back through
/// `value_to_term` (mod.rs, the WI-636 choke point) because the De Bruijn / rename /
/// answer-link walks beneath it read `tree_subst` term-only. Its own comment calls
/// that the fast path's rare case — "an all-`Term` `tree_subst` (every stdlib case
/// today) passes through untouched" — and this ticket makes it LESS rare: a σ-moved
/// goal is now an `Entity`, so the head match it makes binds an `Entity` and the
/// normalization re-interns the spine, fresh var and all.
///
/// MEASURED on `[loose(?a, ?y), unify(?x, Box(v: ?y)), takes(?x)]`, one definite
/// solution throughout, growth per resolve:
///
/// | tree | growth | interned at |
/// |---|---|---|
/// | HEAD | **+4** | `step_init`'s walk (`fn_value`) |
/// | `Transient` carrier backed out (`reify_value_on`) | **+4** | same |
/// | this ticket | **+2** | `with_fresh_vars` → `value_to_term` |
///
/// So the ticket is a net −2 on this shape and a full close on
/// [`the_walk_is_flat_over_an_unbound_link`]'s (which has no head match over a
/// non-`Term` entry, so it never reaches the normalization). ASSERTED SO THE SITE IS
/// REMEMBERED, not relaxed: this row goes red the day the `tree_subst` term-only
/// boundary is retired, and is DELETED then — as N20EZ's residual row was by this
/// ticket, and J0RM4's by N20EZ.
#[test]
fn a_head_match_over_an_entity_goal_still_interns() {
    let mut kb = load_with_stdlib(RESIDUE_SRC);
    let box_sym = kb.try_resolve_symbol("ypgm_z.Box").expect("Box resolves");
    let v_sym = kb.intern("v");
    let (a, y, x) = (var(&mut kb, "a"), var(&mut kb, "y"), var(&mut kb, "x"));
    let g1 = call(&mut kb, "ypgm_z.loose", &[a, y]);
    let mut na: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    na.push((v_sym, y));
    let boxed = kb.alloc(Term::Fn {
        functor: box_sym,
        pos_args: SmallVec::new(),
        named_args: na,
    });
    let unify_sym = kb.unify_functor();
    let g2 = kb.alloc(Term::Fn {
        functor: unify_sym,
        pos_args: SmallVec::from_slice(&[x, boxed]),
        named_args: SmallVec::new(),
    });
    let g3 = call(&mut kb, "ypgm_z.takes", &[x]);

    assert_eq!(
        definite(&mut kb, &[g1, g2, g3]).len(),
        1,
        "the conjunction must actually answer, or this measures nothing",
    );
    let after_first = kb.term_store_len();
    assert_eq!(definite(&mut kb, &[g1, g2, g3]).len(), 1);
    let grew = kb.term_store_len() - after_first;
    assert!(
        grew > 0,
        "`with_fresh_vars`' `value_to_term` normalization no longer interns the \
         `Entity` goal's head match — the residue named in this file's header has \
         been closed. DELETE this row rather than relax it (grew {grew}; it was 2 \
         when this ticket landed and 4 before it)",
    );
}

// ── THE READERS, each driven with an Entity-carried goal ─────────────────────

/// A bodied, rule-less operation at arity 1, queried at arity 2 — the WI-938
/// functional-relation view — plus a fact to bind its argument in a PRECEDING goal, so
/// σ is non-empty when the call walks.
const VIEW_SRC: &str = r#"
namespace ypgm_r
  import anthill.prelude.{Int64}
  import anthill.prelude.Numeric.{add}

  entity Box(v: Int64)
  fact Box(v: 3)
  rule box(?v) :- Box(v: ?v)

  operation dbl(n: Int64) -> Int64 = add(n, n)
end
"#;

/// `[box(?x), dbl(?x, ?r)]` as TERM goals: the first binds `?x`, so the second walks
/// under a non-empty σ and — since this ticket — arrives at the hook as a
/// `Value::Entity`. It must still bind `?r = 6`.
///
/// FAILS when the hook's `goal_occ` is narrowed back to `match &goal_val { Node =>…,
/// Term =>…, _ => None }`: `None` skips the rebuild, the goal falls through to ordinary
/// candidate selection, and a rule-less operation has no clauses — zero solutions.
#[test]
fn the_arity_plus_one_view_reads_an_entity_goal() {
    let mut kb = load_with_stdlib(VIEW_SRC);
    let three = kb.alloc(Term::Const(Literal::Int(3)));

    // CONTROL FIRST: the same call with its argument written GROUND and no preceding
    // goal. σ is empty at `step_init`, so the walk is skipped entirely and the goal
    // stays the `Value::Term` the hook has always read. Passes either way.
    let r0 = var(&mut kb, "r0");
    let ground = call(&mut kb, "ypgm_r.dbl", &[three, r0]);
    let sols = definite(&mut kb, &[ground]);
    assert_eq!(
        sols.len(),
        1,
        "CONTROL: `dbl(3, ?r)` alone rides the Term carrier and bound its result \
         before this ticket — if it moved, the row below measures something other \
         than the carrier",
    );

    let x = var(&mut kb, "x");
    let r = var(&mut kb, "r");
    let g1 = call(&mut kb, "ypgm_r.box", &[x]);
    let g2 = call(&mut kb, "ypgm_r.dbl", &[x, r]);
    let sols = definite(&mut kb, &[g1, g2]);
    assert_eq!(
        sols.len(),
        1,
        "`[box(?x), dbl(?x, ?r)]` must answer once; `[]` is the hook declining the \
         Entity carrier the goal walk now builds",
    );
    let r_vid = match kb.get_term(r) {
        Term::Var(Var::Global(v)) => *v,
        other => panic!("`?r` is not a global var: {other:?}"),
    };
    let bound = kb.answer_binding(r_vid, &sols[0].subst).expect("?r binds");
    assert_eq!(
        scalar_int(&kb, &bound),
        Some(6),
        "the view must BIND the result column through the body, not merely answer",
    );
}

/// `is_unreduced_builtin_call` — WI-738's soundness floor, on the carrier the walk
/// builds. `[num(?x), neq(sub(?x, 1), 1)]` with `fact Num(v: 2)`: `2 - 1 = 1`, so the
/// guard is FALSE and the conjunction has NO definite solution.
///
/// FAILS when the predicate's `Entity` arm is removed: the operand reads as ordinary
/// DATA, `neq` compares the TERM `sub(2,1)` to the term `1` structurally, they differ,
/// and the goal is PROVED — WI-738's "silently, unconditionally TRUE" verbatim, one
/// carrier over. That is a wrong answer, not a missing one.
#[test]
fn an_entity_carried_builtin_operand_still_delays() {
    const SRC: &str = r#"
namespace ypgm_b
  import anthill.prelude.{Int64, Bool}
  entity Num(v: Int64)
  fact Num(v: 2)
  rule num(?v) :- Num(v: ?v)
end
"#;
    let mut kb = load_with_stdlib(SRC);
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let two = kb.alloc(Term::Const(Literal::Int(2)));

    // CONTROL: the operand written GROUND in a single goal — no σ, no walk, so it
    // stays a `Value::Term` and takes the arm WI-738 added. Passes either way.
    let sub_g = call(&mut kb, "anthill.prelude.Additive.sub", &[two, one]);
    let neq_g = call(&mut kb, "anthill.prelude.PartialEq.neq", &[sub_g, one]);
    assert!(
        definite(&mut kb, &[neq_g]).is_empty(),
        "CONTROL: `neq(sub(2,1), 1)` as a lone Term goal already delayed (WI-738)",
    );

    let x = var(&mut kb, "x");
    let g1 = call(&mut kb, "ypgm_b.num", &[x]);
    assert_eq!(
        definite(&mut kb, &[g1]).len(),
        1,
        "the binding goal must answer, or the conjunction below falls through before \
         reaching the operand at all",
    );
    let sub_x = call(&mut kb, "anthill.prelude.Additive.sub", &[x, one]);
    let g2 = call(&mut kb, "anthill.prelude.PartialEq.neq", &[sub_x, one]);
    assert!(
        definite(&mut kb, &[g1, g2]).is_empty(),
        "`[num(?x), neq(sub(?x,1), 1)]` must NOT be proved — `?x` is 2 and 2-1 = 1, \
         so the guard is false. A definite solution here is the structural lie the \
         WI-738 floor exists to stop, reached through the `Value::Entity` operand the \
         goal walk builds once σ has bound `?x`",
    );
}

/// `op_call_as_occ` — the WI-580 case-split, on the carrier the walk builds.
/// `[tail3(?t), eq(append(?a, ?t), [1,3])]` binds `?t = [3]` first, so the `append`
/// operand is σ-MOVED and arrives as a `Value::Entity` while `?a` stays unground. The
/// equation solves `?a = [1]`.
///
/// FAILS when the predicate's `Entity` arm is removed: the case-split is abandoned,
/// the `eq` builtin compares `append(?a,[3])` to `cons(1, cons(3, nil))` structurally,
/// the head functors differ, and the goal answers NOTHING — a lost solution.
#[test]
fn an_entity_carried_op_call_operand_still_case_splits() {
    const SRC: &str = r#"
namespace ypgm_u
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{append}
  entity Tail(t: List[T = Int64])
  fact Tail(t: [3])
  rule tail3(?t) :- Tail(t: ?t)
end
"#;
    let mut kb = load_with_stdlib(SRC);
    let conss = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("cons");
    let nils = kb
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("nil");
    let fields = kb.entity_field_names(conss).expect("cons fields").to_vec();
    let (head_f, tail_f) = (fields[0], fields[1]);
    let mut cons = |kb: &mut KnowledgeBase, h: TermId, t: TermId| -> TermId {
        let mut na: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
        na.push((head_f, h));
        na.push((tail_f, t));
        na.sort_by_key(|(s, _)| s.index());
        kb.alloc(Term::Fn {
            functor: conss,
            pos_args: SmallVec::new(),
            named_args: na,
        })
    };
    let nil_t = kb.alloc(Term::Ref(nils));
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let three = kb.alloc(Term::Const(Literal::Int(3)));
    let three_nil = cons(&mut kb, three, nil_t); // [3]
    let one_three = cons(&mut kb, one, three_nil); // [1, 3]
    let eq_sym = kb.eq_functor();

    // CONTROL: the SAME equation with the tail written literally — σ never touches the
    // goal, the operand stays a `Value::Term`, and `op_call_as_occ`'s Term arm splits
    // it. This is `push_choice_test::wi668_term_carried_opcall_eq_case_splits`, re-run
    // here so a failure below cannot be blamed on the fixture. Passes either way.
    let a0 = var(&mut kb, "a0");
    let app0 = call(&mut kb, "anthill.prelude.List.append", &[a0, three_nil]);
    let eq0 = kb.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::from_slice(&[app0, one_three]),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        definite(&mut kb, &[eq0]).len(),
        1,
        "CONTROL: the Term-carried operand case-splits (WI-668)",
    );

    let t = var(&mut kb, "t");
    let a = var(&mut kb, "a");
    let g1 = call(&mut kb, "ypgm_u.tail3", &[t]);
    let app = call(&mut kb, "anthill.prelude.List.append", &[a, t]);
    let g2 = kb.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::from_slice(&[app, one_three]),
        named_args: SmallVec::new(),
    });
    let sols = definite(&mut kb, &[g1, g2]);
    assert_eq!(
        sols.len(),
        1,
        "`[tail3(?t), eq(append(?a, ?t), [1,3])]` must still solve `?a = [1]`; `[]` is \
         the case-split abandoning the `Value::Entity` operand the walk builds",
    );
    let a_vid = match kb.get_term(a) {
        Term::Var(Var::Global(v)) => *v,
        other => panic!("`?a` is not a global var: {other:?}"),
    };
    let bound = kb.answer_binding(a_vid, &sols[0].subst).expect("?a binds");
    let got = anthill_core::kb::node_occurrence::value_to_term(&mut kb, &bound)
        .expect("`?a` lowers to a ground term on any carrier");
    let expected = cons(&mut kb, one, nil_t);
    assert_eq!(
        got, expected,
        "the split must SOLVE the equation (`?a = [1]`), not merely answer",
    );
}

/// `walk_arg` — THE FIFTH READER, and the one that LOST AN ANSWER. Found by
/// `/code-review` after the four in the header were fixed, which is why it is stated
/// here as a correction rather than as part of that list.
///
/// A logic variable reaches a builtin's argument slot on three carriers, and
/// `walk_arg`'s ARM LIST chased two: `Term::Var(Global)` and `Expr::Var(Global)`. The bare
/// value-level `Value::Var(Global)` (WI-109) was returned UNWALKED, so
/// `value_is_unbound_var` answered `true` for it by carrier however deeply σ had bound
/// it. Nothing put one in an argument slot while the walk interned — `fn_value` lowered
/// an answer link's leaf to `Term::Var`, which the first arm chases, and that interning
/// IS the leak this ticket closes.
///
/// `[loose(?x, ?y), eq(?y, 1), simple(?y)]` as TERM goals: `loose` links `?y` to a
/// fresh var its body never binds, so `eq` delays on it and ROTATES behind `simple`;
/// `simple(?y)` then binds the link to 1; `eq` retries and must now decide. The truth
/// is ONE definite solution.
///
/// MEASURED: 1 at HEAD, 0 with the walk transient and this arm missing, 1 again with
/// it. `walk_arg` is one `value_global_var` read now, so there is no list to leave a
/// spelling out of. The row FAILS when that read is narrowed back to
/// `v.clone()` / `v`.
#[test]
fn a_rotated_builtin_reads_the_link_its_sibling_bound() {
    let mut kb = load_with_stdlib(
        "namespace ypgm_w
  entity Box(v: Int64)
  fact Box(v: 1)
  rule loose(?x, ?y) :- Box(v: ?x)
  rule simple(?x) :- Box(v: ?x)
end
",
    );
    let (x, y) = (var(&mut kb, "x"), var(&mut kb, "y"));
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let g1 = call(&mut kb, "ypgm_w.loose", &[x, y]);
    let eq_sym = kb.eq_functor();
    let g2 = kb.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::from_slice(&[y, one]),
        named_args: SmallVec::new(),
    });
    let g3 = call(&mut kb, "ypgm_w.simple", &[y]);

    // CONTROL: the same pair WITHOUT the loose link, so `?y` is never on the
    // `Value::Var` carrier at all. Passes either way — it is what says the row below
    // measures the CARRIER and not the rotation.
    assert_eq!(
        definite(&mut kb, &[g2, g3]).len(),
        1,
        "CONTROL: `[eq(?y, 1), simple(?y)]` decides without an answer link in play",
    );

    assert_eq!(
        definite(&mut kb, &[g1, g2, g3]).len(),
        1,
        "`eq(?y, 1)` delayed on the link, rotated behind `simple(?y)`, and must read \
         the binding `simple` made. `0` here is the retry reading a `Value::Var` \
         `walk_arg` never chased — a LOST SOLUTION, not a delay",
    );
}

// ── The materializer's two carriers stay ONE reading ─────────────────────────

/// `node_occurrence::value_as_occurrence` builds `visit_fn`'s `UnknownFn` shape
/// DIRECTLY for an `Entity` rather than routing through `value_to_term` +
/// `materialize_from_handle`, because that pair ALLOCATES and the arity+1 view's own
/// `?r` column is an unbound fresh var — interning it is the leak this ticket closed.
/// The cost of building directly is that `visit_fn` keys on the functor's LAST DOTTED
/// SEGMENT, so a functor naming a reflect FORM materializes as that FORM from a `Term`
/// and would have become a plain `Expr::Apply` from an `Entity`. The function asks
/// `is_reflect_form_functor` and sends those through the one materializer.
///
/// `int_lit(value: 7)` is the smallest such form: `build_frame` collapses it to an
/// `Expr::Const` LEAF. So the two carriers are driven side by side and must agree.
///
/// FAILS when the `is_reflect_form_functor` branch is backed out: the `Entity` comes
/// back `Expr::Apply { functor: int_lit, … }` while its term twin is `Expr::Const(7)`
/// — one value, two readings, decided by carrier, which is the WI-425/WI-815 class of
/// divergence this whole file exists to keep closed.
#[test]
fn a_reflect_form_reads_the_same_from_both_carriers() {
    use anthill_core::kb::node_occurrence::{value_as_occurrence, Expr};

    let mut kb = load_with_stdlib("namespace ypgm_x\n  entity Anchor(v: Int64)\nend\n");
    let int_lit = kb
        .try_resolve_symbol("anthill.reflect.Expr.int_lit")
        .expect("`anthill.reflect.Expr.int_lit` must resolve");
    let value_f = kb.intern("value");
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let mut named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    named.push((value_f, seven));
    let term = kb.alloc(Term::Fn {
        functor: int_lit,
        pos_args: SmallVec::new(),
        named_args: named,
    });

    let from_term = value_as_occurrence(&mut kb, &Value::term(term));
    assert!(
        matches!(from_term.as_expr(), Some(Expr::Const(Literal::Int(7)))),
        "CONTROL: the TERM carrier takes `visit_fn`'s keyed `int_lit` arm and collapses \
         to a `Const` leaf — got {:?}",
        from_term.as_expr(),
    );

    let entity = Value::Entity {
        functor: int_lit,
        pos: std::rc::Rc::from(Vec::new().as_slice()),
        named: std::rc::Rc::from(vec![(value_f, Value::Int(7))].as_slice()),
    };
    let from_entity = value_as_occurrence(&mut kb, &entity);
    assert!(
        matches!(from_entity.as_expr(), Some(Expr::Const(Literal::Int(7)))),
        "the ENTITY carrier must read as the SAME keyed form, not as a plain \
         `Expr::Apply` on `int_lit` — got {:?}",
        from_entity.as_expr(),
    );
}
