//! Cut (`!`) — the kernel control primitive (proposal 033.1 / WI-568).
//!
//! `!` commits to the current rule invocation: when it fires it discards the
//! other clauses of the rule whose body it appears in, and every choice point
//! created while resolving the goals before it; choice points created after it
//! are untouched. The resolver opens the surface `!` to a barrier-tagged
//! `cut(B)` at rule-body entry (`step_choice_point`), and `apply_cut` prunes the
//! stack back to the frame tagged with `B`.
//!
//! Coverage: commit-to-first-clause, inner choice-point pruning, disjunction
//! transparency (outer cut prunes an inner `or`; an inner cut is opaque to the
//! outer `or`), cut under NAF (scoped to the sub-proof), and cut alongside
//! delay / residualization.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::parse;
use smallvec::SmallVec;

/// Build a `Term::Ref(qualified_name_sym)` term — matches how entities stored
/// in args appear in the KB after loading.
fn ref_term(kb: &mut KnowledgeBase, qualified: &str) -> TermId {
    let sym = kb
        .try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    kb.alloc(Term::Ref(sym))
}

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let parsed_extra = parse::parse(extra).unwrap_or_else(|e| panic!("parse extra: {e:?}"));
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap();
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parsed_extra);
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => {}
        Err(errs) => {
            for e in &errs {
                eprintln!("LOAD ERR: {}", e);
            }
            panic!("load failed with {} errors", errs.len());
        }
    }
    kb
}

/// A fresh `Term::Var(Global)` query variable.
fn fresh(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

/// A unary goal `functor(arg)`.
fn goal1(kb: &mut KnowledgeBase, functor: &str, arg: TermId) -> TermId {
    let f = kb
        .try_resolve_symbol(functor)
        .unwrap_or_else(|| panic!("symbol {functor} not in KB"));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(&[arg]),
        named_args: SmallVec::new(),
    })
}

#[test]
fn cut_commits_to_first_clause() {
    // `a(?x) :- first(?x), !` followed by `a(?x) :- second(?x)`. The cut in the
    // first clause discards the second clause — only `first`'s solution surfaces.
    let src = r#"
        namespace cuttest.commit
          sort Tag
            entity c1
            entity c2
          end
          fact first(c1)
          fact second(c2)
          rule a(?x) :- first(?x), !
          rule a(?x) :- second(?x)
        end
    "#;
    let mut kb = load_with(src);
    let x = fresh(&mut kb, "_x");
    let goal = goal1(&mut kb, "cuttest.commit.a", x);
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        solutions.len(),
        1,
        "cut in clause 1 must discard clause 2 (without cut this is 2)"
    );
    let c1 = ref_term(&mut kb, "cuttest.commit.Tag.c1");
    assert_eq!(kb.reify(x, &solutions[0].subst).expect_term(), c1);
}

#[test]
fn cut_prunes_inner_choice_points() {
    // `pick(?x, ?y) :- bb(?x), !, mk(?y)` where `bb` has two facts. The cut after
    // `bb` prunes `bb`'s remaining alternative, so only the first `bb` survives;
    // the tail `mk(?y)` still runs.
    let src = r#"
        namespace cuttest.inner
          sort Item
            entity i1
            entity i2
          end
          sort Mark
            entity mk1
          end
          fact bb(i1)
          fact bb(i2)
          fact mk(mk1)
          rule pick(?x, ?y) :- bb(?x), !, mk(?y)
        end
    "#;
    let mut kb = load_with(src);
    let x = fresh(&mut kb, "_x");
    let y = fresh(&mut kb, "_y");
    let pick = kb.try_resolve_symbol("cuttest.inner.pick").unwrap();
    let goal = kb.alloc(Term::Fn {
        functor: pick,
        pos_args: SmallVec::from_slice(&[x, y]),
        named_args: SmallVec::new(),
    });
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        solutions.len(),
        1,
        "cut after bb must drop bb's second fact (without cut this is 2)"
    );
    let mk1 = ref_term(&mut kb, "cuttest.inner.Mark.mk1");
    assert_eq!(
        kb.reify(y, &solutions[0].subst).expect_term(),
        mk1,
        "the tail goal after the cut still runs"
    );
}

#[test]
fn outer_cut_prunes_inner_or() {
    // Disjunction transparency: `t(?x) :- or(p(?x), q(?x)), !`. The cut after the
    // `or` prunes the `or`'s second branch (its push_choice continuation sits
    // above the cut's barrier frame), so only the left branch `p` survives.
    let src = r#"
        namespace cuttest.distrans
          sort Tag
            entity p1
            entity q1
          end
          fact p(p1)
          fact q(q1)
          rule t(?x) :- or(p(?x), q(?x)), !
        end
    "#;
    let mut kb = load_with(src);
    let x = fresh(&mut kb, "_x");
    let goal = goal1(&mut kb, "cuttest.distrans.t", x);
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        solutions.len(),
        1,
        "cut must prune the inner or's right branch (without cut this is 2)"
    );
    let p1 = ref_term(&mut kb, "cuttest.distrans.Tag.p1");
    assert_eq!(
        kb.reify(x, &solutions[0].subst).expect_term(),
        p1,
        "the surviving solution is the or's left branch"
    );
}

#[test]
fn inner_cut_is_opaque_to_outer_or() {
    // The dual of transparency: a cut inside an inner rule (`viaInner`) commits
    // only to that rule's invocation — it does NOT prune the OUTER `or`'s
    // branches. So `viaInner` yields one (`opt`'s first fact, its own second
    // pruned) and the outer `or`'s `plain` branch still contributes.
    let src = r#"
        namespace cuttest.opaque
          sort Tag
            entity o1
            entity o2
            entity d1
          end
          fact opt(o1)
          fact opt(o2)
          fact plain(d1)
          rule viaInner(?x) :- opt(?x), !
          rule outer(?x) :- or(viaInner(?x), plain(?x))
        end
    "#;
    let mut kb = load_with(src);
    let x = fresh(&mut kb, "_x");
    let goal = goal1(&mut kb, "cuttest.opaque.outer", x);
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    let o1 = ref_term(&mut kb, "cuttest.opaque.Tag.o1");
    let o2 = ref_term(&mut kb, "cuttest.opaque.Tag.o2");
    let d1 = ref_term(&mut kb, "cuttest.opaque.Tag.d1");
    let got: std::collections::HashSet<u32> = solutions
        .iter()
        .map(|s| kb.reify(x, &s.subst).expect_term().raw())
        .collect();
    // Order-independent invariants (which `opt` fact the inner cut commits to is
    // resolver-order-dependent, so don't pin o1-vs-o2):
    //  - the outer or's `plain` branch survives — `d1` present — which is the
    //    "inner cut is opaque to the outer or" property (a leaked cut would drop
    //    `plain` and yield only the single `opt` solution);
    //  - the inner cut pruned `opt`'s second fact — EXACTLY one of {o1, o2}.
    assert_eq!(solutions.len(), 2, "one pruned `opt` solution + the `plain` branch");
    assert!(
        got.contains(&d1.raw()),
        "outer or's `plain` branch survives — inner cut is opaque to it"
    );
    let opt_hits = [o1.raw(), o2.raw()].iter().filter(|b| got.contains(b)).count();
    assert_eq!(opt_hits, 1, "inner cut pruned opt's second fact — exactly one opt solution");
}

#[test]
fn cut_under_naf_is_scoped_to_the_sub_proof() {
    // A cut inside a goal proved under `not(...)` runs in the NAF sub-stream — it
    // prunes only that sub-proof's choice points, never the outer candidate
    // search. `check(?x) :- candidate(?x), not(blocked(?x))` with
    // `blocked(?x) :- block(?x), !`: a1 is blocked (excluded), a2 is not.
    let src = r#"
        namespace cuttest.naf
          sort Tag
            entity a1
            entity a2
          end
          fact candidate(a1)
          fact candidate(a2)
          fact block(a1)
          rule blocked(?x) :- block(?x), !
          rule check(?x) :- candidate(?x), not(blocked(?x))
        end
    "#;
    let mut kb = load_with(src);
    let x = fresh(&mut kb, "_x");
    let goal = goal1(&mut kb, "cuttest.naf.check", x);
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        solutions.len(),
        1,
        "only the unblocked candidate survives; the inner cut must not leak to \
         the outer candidate choice point"
    );
    let a2 = ref_term(&mut kb, "cuttest.naf.Tag.a2");
    assert_eq!(kb.reify(x, &solutions[0].subst).expect_term(), a2);
}

#[test]
fn cut_with_a_ground_guard_succeeds_definitely() {
    // `g(?x) :- gt(?x, 0), !`. A ground guard reduces, the cut fires, and the
    // result is a definite (empty-residual) solution.
    let src = r#"
        namespace cuttest.delay
          rule g(?x) :- gt(?x, 0), !
        end
    "#;
    let mut kb = load_with(src);
    let five = kb.alloc(Term::Const(Literal::Int(5)));
    let goal = goal1(&mut kb, "cuttest.delay.g", five);
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(solutions.len(), 1, "ground guard satisfied → one solution");
    assert!(
        solutions[0].is_definite(),
        "a satisfied guard before the cut yields a definite answer"
    );
}

#[test]
fn cut_coexists_with_delay_and_residualization() {
    // The same rule with an UNBOUND guard: `gt(?y, 0)` delays, the frame
    // rotates, the cut fires (a harmless commit), and the guard ultimately
    // flounders. The owning frame's barrier was already used; resolution must
    // not panic and the result must be reported honestly as non-definite.
    let src = r#"
        namespace cuttest.delay2
          rule g(?x) :- gt(?x, 0), !
        end
    "#;
    let mut kb = load_with(src);
    let y = fresh(&mut kb, "_y");
    let goal = goal1(&mut kb, "cuttest.delay2.g", y);
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(solutions.len(), 1, "the floundered branch is reported once");
    assert!(
        !solutions[0].is_definite(),
        "an unbound guard floundered → the solution is non-definite (has residual)"
    );
    assert!(
        !solutions[0].residual.is_empty(),
        "the undischarged guard is carried as a residual goal"
    );
}
