//! WI-739 — a REORDERABLE builtin must not delay its whole rule on a caller var.
//! Generate-and-test must enumerate in the (out,out) mode.
//!
//! THE BUG. The WI-246 caller-var pre-check
//! (`body_builtins_delay_on_caller_vars_nodes`) delays a WHOLE RULE, before its
//! body opens, whenever a body builtin's first arg is an unbound CALLER var —
//! the premise being "nothing here can make progress, so let the caller's
//! siblings bind it first". For generate-and-test — THE logic-programming idiom
//! — that premise is false. In
//!
//!   rule distinct_pair(?x, ?y) :- num(v: ?x), num(v: ?y), neq(?x, ?y)
//!
//! `neq`'s first arg IS a caller var when both columns are queried free, so the
//! whole rule delayed and the enumeration collapsed into ONE floundered residual
//! with unbound columns, where 6 ground rows were owed.
//!
//! THE DIVERGENCE THAT WAS THE BUG. The logically identical `not(eq(?x, ?y))`
//! enumerated the correct 6 all along, because the pre-check SKIPS `Not`. Same
//! logical content, two different answers — one of the two had to be wrong, and
//! the divergence itself was the defect. These tests pin the two AGREEING.
//!
//! THE FIX, AND WHY IT IS ABOUT BUILTINS RATHER THAN BODIES. `Not`'s exemption
//! was the clue: it is skipped because NAF suspends and goal rotation re-asks
//! it. That is true of `neq` too — of every builtin that SUSPENDS on a flex
//! operand rather than answering. So the pre-check should fire only for a
//! builtin that must NOT be reordered past whatever binds its var, which is a
//! property of the BUILTIN (`builtin_is_reorderable`), not of the body. Two
//! families qualify, for different reasons, and each has a test below:
//! `nonvar`/`ground` (rotation makes them vacuously succeed) and `ho_apply`
//! (hard-fails instead of suspending, so rotation destroys the question).
//!
//! A REJECTED DESIGN, RECORDED so it is not re-attempted: qualify the gate with
//! "can one of the rule's own body conjuncts bind this var?" It looks right and
//! is wrong twice over. (a) It is unnecessary — rotation already reaches both
//! the body's generators AND the caller's siblings, since an opened body is
//! spliced into the caller's goal list; every test here passes without it. (b)
//! It is unsound in both directions — it must guess which conjuncts bind, and
//! excluding builtin binders left WI-739's own bug alive for the arithmetic
//! spelling (`graph_guard` below, the shape WI-740's queens diagonal needs),
//! while counting `forall_impl`/`ho_apply` bodies as binders broke every
//! `<Sort>.induction(?P)`. "Which conjunct might bind this var" is a question
//! the gate cannot answer and does not need to ask.

use anthill_core::eval::value::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::parse;
use smallvec::SmallVec;

const SRC: &str = r#"
namespace wi739.guard
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Numeric.{add}

  sort N
    entity num(v: Int64)
  end
  fact num(v: 1)
  fact num(v: 2)
  fact num(v: 3)

  -- Plain enumeration, no guard: the (out,out) baseline — 9 rows.
  rule any_pair(?x, ?y) :- num(v: ?x), num(v: ?y)

  -- THE BUG: both guard vars are caller vars, but `num` binds them both.
  rule distinct_pair(?x, ?y) :- num(v: ?x), num(v: ?y), neq(?x, ?y)

  -- The SAME logical content via NAF. `Not` is skipped by the pre-check, so this
  -- always worked. It is the oracle the guard form must now match.
  rule distinct_naf(?x, ?y) :- num(v: ?x), num(v: ?y), not(eq(?x, ?y))

  -- No head params ⇒ no caller vars ⇒ the pre-check never fired. Already correct
  -- before the fix; pinned so the gate change does not disturb it.
  rule distinct_local() :- num(v: ?x), num(v: ?y), neq(?x, ?y)

  -- Nothing in this body can ever bind ?x. `neq` suspends on its flex operand
  -- and there is nothing to rotate against, so this flounders honestly.
  rule unbindable(?x) :- neq(?x, 1)

  -- The ARITHMETIC spelling of generate-and-test: the 3-arg graph form binds ?z
  -- (WI-738 pinned it), then the guard tests it. This is the shape WI-740's
  -- queens diagonal needs.
  rule graph_guard(?z) :- add(1, 2, ?z), neq(?z, 5)
  rule graph_only(?z) :- add(1, 2, ?z)
end
"#;


/// `.fix()` over the floundering rule — the case WI-739's feedback flagged.
const FIX_SRC: &str = r#"
namespace wi739.fixcase
  import anthill.prelude.{Int64, List, Bool}
  import anthill.prelude.List.{length}

  sort N
    entity num(v: Int64)
  end
  fact num(v: 1)
  fact num(v: 2)
  fact num(v: 3)

  rule distinct_pair(?x, ?y) :- num(v: ?x), num(v: ?y), neq(?x, ?y)
  operation fixedCount() -> Int64 effects Error =
    length(distinct_pair.fix(x: 1).takeN(10))
end
"#;

fn load_kb() -> KnowledgeBase {
    load_src(SRC)
}

fn load_src(src: &str) -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(src).unwrap_or_else(|e| panic!("parse extra: {e:?}")));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|e| panic!("load: {e:?}"));
    kb
}

fn fresh(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

fn goal(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let f = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not in KB"));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// Query a binary relation with BOTH columns free — the (out,out) mode this
/// ticket is about — and read back each row as a concrete `(x, y)` pair.
///
/// Rows are collected ONLY from DEFINITE solutions, and a row counts only if
/// both columns reify to a concrete Int. That is the honest lens here: the bug's
/// signature was a row whose columns were still VARIABLES (a floundered residual
/// presented as an answer), so a test that merely counted solutions would read
/// "1 solution" before the fix and could be mistaken for progress. WI-738's
/// lesson — measuring through `isEmpty` hid a working fix twice — applies
/// directly: assert on the ROWS, not the count.
fn ground_pairs(kb: &mut KnowledgeBase, qn: &str) -> Vec<(i64, i64)> {
    let x = fresh(kb, "x");
    let y = fresh(kb, "y");
    let g = goal(kb, qn, &[x, y]);
    let cfg = ResolveConfig { max_solutions: 100, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);
    let mut out = Vec::new();
    for sol in &sols {
        if !sol.is_definite() {
            continue;
        }
        if let (Some(a), Some(b)) = (int_of(kb, sol, x), int_of(kb, sol, y)) {
            out.push((a, b));
        }
    }
    out.sort_unstable();
    out
}

/// Reify a query var through the answer substitution, yielding `Some(n)` only if
/// it landed on a concrete Int — `None` if it is still a VARIABLE. The `None`
/// case is the bug's own signature (an unbound column), so it must be a readable
/// outcome here rather than a panic.
///
/// NOTE `reify` of a KB-resident answer hands back `Value::Term { id }` — the
/// hash-consed `Term::Const`, not an unboxed `Value::Int` (the unboxed scalars
/// are an in-flight eval representation). Matching `Value::Int` alone silently
/// answered `None` for every row, which read as "0 ground rows" even for the
/// unguarded 9-row baseline. Both carriers are accepted here so the lens cannot
/// lie about groundness again.
fn int_of(kb: &mut KnowledgeBase, sol: &Solution, v: TermId) -> Option<i64> {
    match kb.reify(v, &sol.subst) {
        Value::Int(n) => Some(n),
        Value::Term { id, .. } => match kb.get_term(id) {
            Term::Const(Literal::Int(n)) => Some(*n),
            _ => None,
        },
        _ => None,
    }
}

/// Every definite solution's binding for `v`, as a concrete Int.
fn definite_ints(kb: &mut KnowledgeBase, qn: &str) -> Vec<i64> {
    let v = fresh(kb, "v");
    let g = goal(kb, qn, &[v]);
    let cfg = ResolveConfig { max_solutions: 10, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);
    let mut out = Vec::new();
    for sol in &sols {
        if !sol.is_definite() {
            continue;
        }
        if let Some(n) = int_of(kb, sol, v) {
            out.push(n);
        }
    }
    out
}

/// The baseline: enumeration in (out,out) works when no guard is present. If
/// this ever fails, the other assertions here mean nothing.
#[test]
fn wi739_unguarded_enumeration_yields_all_nine() {
    let mut kb = load_kb();
    let rows = ground_pairs(&mut kb, "wi739.guard.any_pair");
    assert_eq!(
        rows.len(),
        9,
        "3 facts x 3 facts with no guard must enumerate 9 ground rows in (out,out); got {rows:?}",
    );
}

/// THE TICKET. `neq(?x, ?y)` after the generators must let them bind first.
/// Before the fix this returned ONE row whose columns were unbound variables —
/// the whole rule delayed on its caller vars, so `num` never ran.
#[test]
fn wi739_guarded_enumeration_yields_the_six_ground_rows() {
    let mut kb = load_kb();
    let rows = ground_pairs(&mut kb, "wi739.guard.distinct_pair");
    let want: Vec<(i64, i64)> = vec![(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)];
    assert_eq!(
        rows, want,
        "distinct_pair queried (out,out) must yield the 6 distinct ground pairs. The \
         rule's own `num` goals bind both caller vars, so the guard must not delay \
         the whole rule. Got {rows:?}",
    );
}

/// THE DIVERGENCE, PINNED. `neq(..)` and `not(eq(..))` carry the same logical
/// content; before the fix they disagreed (1 unbound row vs the correct 6), and
/// that disagreement was the bug. They must now agree exactly.
#[test]
fn wi739_neq_and_naf_spellings_agree() {
    let mut kb = load_kb();
    let guard = ground_pairs(&mut kb, "wi739.guard.distinct_pair");
    let naf = ground_pairs(&mut kb, "wi739.guard.distinct_naf");
    assert_eq!(
        guard, naf,
        "neq(?x,?y) and not(eq(?x,?y)) are the same logical content and must \
         enumerate identically — the divergence WAS the bug. neq gave {guard:?}, \
         not(eq(..)) gave {naf:?}",
    );
    assert_eq!(naf.len(), 6, "the NAF oracle itself must still give 6; got {naf:?}");
}

/// Mode (in,out) must be unaffected: with the first column bound at the call the
/// guard's first arg was never an unbound caller var, so the pre-check never
/// fired and this always gave the right answer.
#[test]
fn wi739_bound_first_column_still_yields_two() {
    let mut kb = load_kb();
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let y = fresh(&mut kb, "y");
    let g = goal(&mut kb, "wi739.guard.distinct_pair", &[one, y]);
    let cfg = ResolveConfig { max_solutions: 100, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);
    let mut got: Vec<i64> = Vec::new();
    for sol in &sols {
        if !sol.is_definite() {
            continue;
        }
        if let Some(n) = int_of(&mut kb, sol, y) {
            got.push(n);
        }
    }
    got.sort_unstable();
    assert_eq!(
        got,
        vec![2, 3],
        "distinct_pair(1) is mode (in,out) and must still yield exactly 2 rows",
    );
}

/// The zero-head-param spelling — correct before the fix (no caller vars ⇒ no
/// pre-check) and the evidence that the machinery below the gate was always
/// right. It must stay correct: the gate change must not disturb the path that
/// never went through the gate.
#[test]
fn wi739_zero_head_param_spelling_still_proves() {
    let mut kb = load_kb();
    let g = goal(&mut kb, "wi739.guard.distinct_local", &[]);
    let cfg = ResolveConfig { max_solutions: 100, definite_only: true, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);
    assert_eq!(
        sols.len(),
        6,
        "distinct_local() has no caller vars, so it never hit the pre-check and \
         already enumerated its 6 solutions; it must still do so",
    );
}

/// A guard on a var NOTHING can bind must still flounder honestly rather than be
/// forced to a verdict — it must produce a residual, not a decision.
///
/// HONESTY NOTE: this is a CONTROL, not a regression guard for the gate. It
/// passes with the caller-var gate deleted entirely, because `neq` suspends at
/// the BUILTIN level (`eq_operands` → `Delay` on a flex operand) whether or not
/// the rule delayed wholesale. It therefore pins the OUTCOME (an unbindable
/// guard stays undecided) and says nothing about which mechanism delivered it.
/// An earlier version of this test claimed the opposite — that dropping the gate
/// would make it "wrongly come back proved" — which is false; the claim was
/// written from reasoning and never checked. Asserting on the residual rather
/// than on `definite_only` is what makes the outcome legible here.
#[test]
fn wi739_guard_on_unbindable_var_still_flounders_honestly() {
    let mut kb = load_kb();
    let x = fresh(&mut kb, "x");
    let g = goal(&mut kb, "wi739.guard.unbindable", &[x]);
    let cfg = ResolveConfig { max_solutions: 10, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);
    assert_eq!(sols.len(), 1, "expected the single floundered answer; got {}", sols.len());
    assert!(
        !sols[0].is_definite() && !sols[0].residual.is_empty(),
        "unbindable(?x) :- neq(?x, 1) must stay UNDECIDED and carry its pending \
         goal as a residual — never be decided on an unbound var",
    );
}

/// THE REGRESSION THAT KILLED THE FIRST DESIGN — pinned against REAL stdlib, not
/// a fixture, because that is where it bites.
///
/// `ho_apply` is not reorderable: on an unbound predicate var it HARD-FAILS —
/// `step_init` pops the frame ("can't apply unbound predicate") rather than
/// suspending. There is no pending goal for rotation to re-ask, so letting the
/// body open does not DEFER the question, it DESTROYS it, and the rule reports
/// exhaustion for a goal it never tried.
///
/// `BigInt.induction(?P) :- ?P(0), (forall(?n), gt(?n,0), ?P(sub(?n,1)) -: ?P(?n))`
/// opens with `ho_apply(?P, 0)` and `?P` is a head param — a caller var. Queried
/// with `?P` free it must stay an honest UNDECIDED residual (nobody can enumerate
/// all predicates). The first design let `forall_impl` count as a "generator" for
/// `?P` — it cannot bind anything, it skolemises and pushes assumptions — which
/// cancelled the delay and turned that residual into 0 solutions. Every
/// auto-generated `<Sort>.induction` on a recursive sort has this shape.
#[test]
fn wi739_hard_failing_builtin_is_not_reordered() {
    let mut kb = load_kb();
    let p = fresh(&mut kb, "p");
    let g = goal(&mut kb, "anthill.prelude.BigInt.induction", &[p]);
    let cfg = ResolveConfig { max_solutions: 10, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);
    assert!(
        !sols.is_empty(),
        "BigInt.induction(?P) with ?P FREE must not report zero solutions — \
         ho_apply(?P, 0) hard-fails on an unbound predicate var, so the rule must \
         DELAY and residualize honestly rather than open and be silently refuted",
    );
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "and it must not be PROVED either — an unenumerable ?P is undecided, not \
         a theorem",
    );
}

/// The ARITHMETIC spelling of generate-and-test, and the shape WI-740's queens
/// diagonal needs: the 3-arg graph form binds `?z`, then the guard tests it.
///
/// This is the case that condemned the rejected generator design: that design
/// asked "can a body conjunct bind this var?" and answered by scanning for
/// NON-builtin conjuncts — so `add(1, 2, ?z)`, a builtin that genuinely binds,
/// did not count, the rule delayed wholesale, and `graph_guard` returned nothing
/// while `graph_only` returned 3. WI-739's own bug, alive in the arithmetic
/// spelling, inside its own fix.
#[test]
fn wi739_arith_graph_form_then_guard_enumerates() {
    let mut kb = load_kb();
    assert_eq!(
        definite_ints(&mut kb, "wi739.guard.graph_only"),
        vec![3],
        "control: add(1,2,?z) alone must bind ?z = 3, else this test proves nothing",
    );
    assert_eq!(
        definite_ints(&mut kb, "wi739.guard.graph_guard"),
        vec![3],
        "add(1,2,?z) binds ?z = 3 and neq(3,5) holds, so graph_guard(?z) must \
         yield 3 — the guard must not delay the rule past its own arithmetic \
         generator",
    );
}

/// WI-739's own feedback recorded that `.fix()` did NOT rescue the floundering
/// rule: `distinct_pair.fix(x: 1)` still delayed (2 residual goals) even though
/// the direct SLD call `distinct_pair(1)` gave the correct 2 rows — because `fix`
/// WRAPS the query as `guarded(query, eq(col, 1))` rather than substituting the
/// constant into the head, so the pre-check still saw `?x` as a free caller var.
/// The feedback asked that any fix "treat the fix/where-supplied binding as
/// satisfying the pre-check".
///
/// Keying on REORDERABILITY settles that without ever looking at where a binding
/// came from: `neq` is reorderable, so the rule never delays wholesale, the body
/// opens, `num` binds both columns, and the outer `guarded` filters to the 2 rows
/// — whether the binding is head-supplied, fix-supplied, or a caller's sibling.
/// The question "did something supply this var?" simply stops being asked.
#[test]
fn wi739_fix_supplied_binding_drains() {
    let mut interp = crate::common::interp_for(FIX_SRC);
    let n = interp
        .call("wi739.fixcase.fixedCount", &[])
        .expect("distinct_pair.fix(x: 1) must drain, not raise RelationFloundered");
    assert_eq!(
        n.as_int(),
        Some(2),
        "fix(x: 1) restricts the first column to 1, leaving (1,2) and (1,3)",
    );
}
