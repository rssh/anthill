//! Integration test: the `examples/classic-mini` collection loads and produces
//! the right answers, so the examples cannot rot.
//!
//! Precedent: `github_todo_test.rs`. The examples are meant to be run via
//! `anthill run <dir>` (they provide `anthill.cli.Main`); this test drives the
//! same rules through the resolver directly, which is what pins the ANSWER
//! rather than merely that the file parses.
//!
//! LOAD-ORDER (WI-719): stdlib must be collected BEFORE the example dir.
//! `classic-mini` sorts lexicographically before `github-todo` and before
//! `stdlib`, so a naive "walk everything" collection would load an example ahead
//! of the prelude it imports. `collect_anthill_files(stdlib)` first, then extend
//! — the same order github_todo_test.rs uses.

mod common;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::parse;
use smallvec::SmallVec;

fn load_example(name: &str) -> KnowledgeBase {
    let mut files = common::collect_anthill_files(&common::stdlib_dir());
    files.extend(common::collect_anthill_files(
        &common::examples_dir().join("classic-mini").join(name),
    ));
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {
        for e in &errs {
            eprintln!("load error: {e}");
        }
        panic!("examples/classic-mini/{name} must LOAD; got {} error(s)", errs.len());
    }
    kb
}

fn fresh(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

fn text(kb: &mut KnowledgeBase, s: &str) -> TermId {
    kb.alloc(Term::Const(Literal::String(s.to_string())))
}

/// Resolve `qn(args)` and return its solutions.
fn query(
    kb: &mut KnowledgeBase,
    qn: &str,
    args: &[TermId],
) -> Vec<anthill_core::kb::resolve::Solution> {
    let functor = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("the `{qn}` rule must be in scope"));
    let g = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig { max_solutions: 100, ..Default::default() };
    kb.resolve(&[g], &cfg)
}

/// Ancestor: the transitive closure of `parent`, and the three modes the example
/// advertises (both columns free, first bound, both bound).
///
/// LOADING this example is itself the regression test for WI-714's recursive
/// schema synthesis, and is the reason the assertions below can be reached at all.
/// The example cites `ancestor` BY NAME as a relation value, so the typer
/// synthesizes its schema while type-checking `main`'s body at LOAD; before the
/// fix, the column typed only by the rule's own recursive self-reference came out
/// untyped, the cross-clause lub read that absence as a conflict, and
/// `load_example` panicked with "disjoint types for column `elder`". Recursive
/// rules always RESOLVED fine as subgoals — so the resolver queries here would have
/// passed on their own; it is the load that pins the fix. The relation VALUE face
/// (takeN / where / applied citation over a recursive rule) is covered end-to-end
/// in `wi714_recursive_relation_test`.
#[test]
fn classic_mini_ancestor_yields_the_transitive_closure() {
    let mut kb = load_example("ancestor");

    // Mode (out, out): the whole closure.
    let cols: Vec<TermId> = ["child", "elder"].iter().map(|n| fresh(&mut kb, n)).collect();
    let sols = query(&mut kb, "classic.ancestry.ancestor", &cols);
    assert!(
        sols.iter().all(|s| s.is_definite()),
        "every ancestor pair must be DECIDED — an undecided row would read as an answer",
    );
    assert_eq!(
        sols.len(),
        12,
        "5 parent facts close transitively into 12 ancestor pairs (3+3+3+2+1); the \
         base clause alone would yield only the 5 parent edges, so this pins that \
         the RECURSIVE clause ran",
    );

    // Mode (in, out): bart's ancestors — homer, abe, orville.
    let bart = text(&mut kb, "bart");
    let elder = fresh(&mut kb, "elder");
    let sols = query(&mut kb, "classic.ancestry.ancestor", &[bart, elder]);
    assert_eq!(sols.len(), 3, "bart has three ancestors: homer, abe, orville");

    // Mode (in, in): a membership question, derivable exactly once — and its
    // converse is not derivable at all (the relation is not symmetric).
    let (bart, orville) = (text(&mut kb, "bart"), text(&mut kb, "orville"));
    let sols = query(&mut kb, "classic.ancestry.ancestor", &[bart, orville]);
    assert_eq!(sols.len(), 1, "orville is bart's ancestor, three `parent` links up");
    let sols = query(&mut kb, "classic.ancestry.ancestor", &[orville, bart]);
    assert!(sols.is_empty(), "ancestry runs one way — bart is not orville's ancestor");
}

/// Map colouring: six free columns, three colours, nine border constraints.
///
/// Pins the ANSWER (6), not just that it loads — and pins that every row is
/// DEFINITE. The bug this example exists to demonstrate (WI-739, composing with
/// WI-737) produced exactly one row whose columns were unbound logic variables,
/// which a solution COUNT alone would have read as "1 solution" rather than as
/// the non-answer it was. So: count the definite rows, and require all rows to
/// be definite.
#[test]
fn classic_mini_map_colouring_yields_six_definite_colourings() {
    let mut kb = load_example("map-colouring");
    let cols: Vec<TermId> = ["wa", "nt", "sa", "q", "nsw", "v"]
        .iter()
        .map(|n| fresh(&mut kb, n))
        .collect();
    let sols = query(&mut kb, "classic.mapcolouring.colouring", &cols);

    assert!(
        sols.iter().all(|s| s.is_definite()),
        "every colouring must be DECIDED — an undecided row here is the WI-739 \
         flounder returning, and it would read as an answer",
    );
    assert_eq!(
        sols.len(),
        6,
        "WA/NT/SA form a triangle (3! = 6) and Q/NSW/V are then forced, so there \
         are exactly 6 three-colourings of the Australian mainland",
    );
}
