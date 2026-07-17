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
use anthill_core::kb::term::{Term, TermId, Var};
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
    let f = kb
        .try_resolve_symbol("classic.mapcolouring.colouring")
        .expect("the `colouring` rule must be in scope");
    let g = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(&cols),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig { max_solutions: 100, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);

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
