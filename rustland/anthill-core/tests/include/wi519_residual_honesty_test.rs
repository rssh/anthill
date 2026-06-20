//! WI-519 — residual honesty (proposal 049 build step 1 [R]).
//!
//! A FLOUNDERED solution — one whose `residual` is non-empty because the search
//! delayed a goal it could not decide (e.g. `eq(?a, ?b)` with both operands
//! unbound) and gave up — must not masquerade as a DEFINITE answer. The residual
//! mechanism stays (a solution is still returned by default, for inspection),
//! but `Solution::is_definite()` codifies "definite = empty residual", and a
//! decision boundary that asks "is there a solution?" sets
//! `ResolveConfig.definite_only` so a floundered residual is skipped (never
//! counts toward `max_solutions`, never reported as success). NAF is made
//! three-way honest: `not(P)` over a floundered `P` is itself undecided
//! (residualizes), not a silent success/failure.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::parse;
use smallvec::SmallVec;

fn load_with(extra: &str) -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}")));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|e| panic!("load: {e:?}"));
    kb
}

fn fresh_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let s = kb.intern(name);
    let v = kb.fresh_var(s);
    kb.alloc(Term::Var(Var::Global(v)))
}

fn goal(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let f = kb.resolve_symbol(qn);
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

fn resolve(kb: &mut KnowledgeBase, g: TermId, definite_only: bool) -> Vec<Solution> {
    let cfg = ResolveConfig { max_solutions: 10, definite_only, ..Default::default() };
    kb.resolve(&[g], &cfg)
}

// ── 1. A floundered goal is a residual, never a definite solution ────────

#[test]
fn floundered_goal_is_residual_not_definite() {
    // `maybe(?x, ?y)` runs `eq(?x, ?y)` with both operands unbound — `eq` is a
    // pure test and cannot decide it, so it delays and (as the sole goal)
    // residualizes.
    let src = r#"
        namespace wi519.flounder
          rule maybe(?a, ?b) :- eq(?a, ?b)
        end
    "#;
    let mut kb = load_with(src);
    let x = fresh_var(&mut kb, "_x");
    let y = fresh_var(&mut kb, "_y");

    // Default mode still returns the branch, but it is NOT definite.
    let g = goal(&mut kb, "wi519.flounder.maybe", &[x, y]);
    let sols = resolve(&mut kb, g, false);
    assert_eq!(sols.len(), 1, "the floundered branch yields one (residual) solution by default");
    assert!(
        !sols[0].is_definite(),
        "eq(?a,?b) floundered → residual non-empty → not a definite solution; got residual {:?}",
        sols[0].residual,
    );

    // Definite-only mode: the floundered residual must NOT count as a solution.
    let g2 = goal(&mut kb, "wi519.flounder.maybe", &[x, y]);
    let defs = resolve(&mut kb, g2, true);
    assert!(
        defs.is_empty(),
        "definite-only must skip the floundered residual; got {} solution(s)",
        defs.len(),
    );
}

// ── 2. A genuine definite solution survives definite-only mode ───────────

#[test]
fn definite_solution_survives_definite_only() {
    let src = r#"
        namespace wi519.def
          import anthill.prelude.{Int64}
          sort Thing
            entity thing(id: Int64)
          end
          fact thing(id: 1)
          rule has(?i) :- thing(id: ?i)
        end
    "#;
    let mut kb = load_with(src);
    let i = fresh_var(&mut kb, "_i");
    let g = goal(&mut kb, "wi519.def.has", &[i]);
    let sols = resolve(&mut kb, g, false);
    assert!(!sols.is_empty(), "the fact-backed query has at least one solution");
    assert!(
        sols.iter().all(|s| s.is_definite()),
        "every fact-backed solution is definite (empty residual)",
    );

    // The key invariant: definite-only must NOT drop genuine definite
    // solutions — it returns exactly the same (all-definite) answers.
    let g2 = goal(&mut kb, "wi519.def.has", &[i]);
    let defs = resolve(&mut kb, g2, true);
    assert_eq!(
        defs.len(), sols.len(),
        "definite-only returns the same definite solutions, dropping none",
    );
    assert!(defs.iter().all(|s| s.is_definite()));
}

// ── 3. NAF is three-way honest over a floundered inner goal ──────────────

#[test]
fn naf_three_way_over_ground_inner() {
    // p_def(1) holds (fact), p_def(999) fails (no fact), p_flounder(1)
    // flounders (its body `eq(?a,?b)` is undecidable). All three `not(...)`
    // inners are GROUND, exercising step_naf's ground three-way.
    let src = r#"
        namespace wi519.naf
          import anthill.prelude.{Int64}
          sort Thing
            entity thing(id: Int64)
          end
          fact thing(id: 1)
          rule p_def(?x) :- thing(id: ?x)
          rule p_flounder(?x) :- eq(?a, ?b)
          rule nf_holds(?z) :- not(p_def(1))
          rule nf_fails(?z) :- not(p_def(999))
          rule nf_flounder(?z) :- not(p_flounder(1))
        end
    "#;
    let mut kb = load_with(src);

    // not(P) where P holds → not FAILS → no solution.
    let w = fresh_var(&mut kb, "_w");
    let g = goal(&mut kb, "wi519.naf.nf_holds", &[w]);
    assert!(resolve(&mut kb, g, false).is_empty(), "not(definite P) fails");

    // not(P) where P has no solution → not SUCCEEDS definitely.
    let g = goal(&mut kb, "wi519.naf.nf_fails", &[w]);
    let s = resolve(&mut kb, g, false);
    assert_eq!(s.len(), 1, "not(no-solution P) succeeds");
    assert!(s[0].is_definite(), "and the success is definite");

    // not(P) where P FLOUNDERS → undecided → residualizes (NOT a silent success).
    let g = goal(&mut kb, "wi519.naf.nf_flounder", &[w]);
    let s = resolve(&mut kb, g, false);
    assert_eq!(s.len(), 1, "not(floundered P) yields a residual solution by default");
    assert!(
        !s[0].is_definite(),
        "not(floundered P) is undecided → residual, not a definite success",
    );
    // definite-only skips it.
    let g = goal(&mut kb, "wi519.naf.nf_flounder", &[w]);
    assert!(
        resolve(&mut kb, g, true).is_empty(),
        "definite-only skips the floundered not()",
    );
}
