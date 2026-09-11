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

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
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
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {
        for e in &errs {
            eprintln!("load error: {e}");
        }
        panic!(
            "examples/classic-mini/{name} must LOAD; got {} error(s)",
            errs.len()
        );
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
    let cfg = ResolveConfig {
        max_solutions: 100,
        ..Default::default()
    };
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
    let cols: Vec<TermId> = ["child", "elder"]
        .iter()
        .map(|n| fresh(&mut kb, n))
        .collect();
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
    assert_eq!(
        sols.len(),
        3,
        "bart has three ancestors: homer, abe, orville"
    );

    // Mode (in, in): a membership question, derivable exactly once — and its
    // converse is not derivable at all (the relation is not symmetric).
    let (bart, orville) = (text(&mut kb, "bart"), text(&mut kb, "orville"));
    let sols = query(&mut kb, "classic.ancestry.ancestor", &[bart, orville]);
    assert_eq!(
        sols.len(),
        1,
        "orville is bart's ancestor, three `parent` links up"
    );
    let sols = query(&mut kb, "classic.ancestry.ancestor", &[orville, bart]);
    assert!(
        sols.is_empty(),
        "ancestry runs one way — bart is not orville's ancestor"
    );
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

/// Words over an alphabet: the domain of a RECURSIVE type as a relation over
/// (value, type term), hand-written in the shape WI-743 derives.
///
/// Pins the ANSWERS (27 and 12) and that every row is DEFINITE. A typed head over
/// `List[T = Letter]` gives TODAY one CONDITIONAL answer with the domain goal
/// undischarged (measured 2026-09-11, `wi742_typed_relational_head_test` pins the
/// shape), which a count alone would read as "1 solution". When WI-743 lands the
/// example drops its hand-written `domain` for the typed head, and these numbers
/// must hold unchanged — that is what makes the example a driver rather than a
/// demo.
#[test]
fn classic_mini_alphabet_words_enumerates_every_word() {
    let mut kb = load_example("alphabet-words");

    let w = fresh(&mut kb, "w");
    let sols = query(&mut kb, "classic.alphabet.word", &[w]);
    assert!(
        sols.iter().all(|s| s.is_definite()),
        "every word must be DECIDED — a conditional row is the domain goal left \
         undischarged, not a word",
    );
    assert_eq!(
        sols.len(),
        27,
        "3^3 three-letter words over {{a, b, c}}: the spine fixes three cells and \
         the domain relation fills each from `Letter`",
    );

    let w = fresh(&mut kb, "w");
    let sols = query(&mut kb, "classic.alphabet.no_repeat", &[w]);
    assert!(sols.iter().all(|s| s.is_definite()));
    assert_eq!(
        sols.len(),
        12,
        "3 * 2 * 2 words with no letter next to itself — the `!=` guards prune \
         after the domain has filled the cells",
    );

    // The domain with NOTHING binding the spine is an INFINITE relation. It must
    // yield exactly the solution cap (`query` asks for 100) and then stop — the
    // enumeration is fair by length, so answers keep arriving and the cap is
    // reached; a depth-first descent into one branch would never return.
    let w = fresh(&mut kb, "w");
    let sols = query(&mut kb, "classic.alphabet.any_word", &[w]);
    assert!(sols.iter().all(|s| s.is_definite()));
    assert_eq!(
        sols.len(),
        100,
        "an infinite, fair domain stops at the solution cap rather than hanging \
         or running dry",
    );
}

/// Tiny SAT: the same domain relation over `List[T = Bit]`, the formula as the
/// test. Pins that there are exactly two models and that each is one DEFINITE row
/// — the `or2` cases are exclusive, so an assignment satisfying both literals of
/// a clause is not counted twice.
#[test]
fn classic_mini_tiny_sat_finds_both_models() {
    let mut kb = load_example("tiny-sat");
    let vs = fresh(&mut kb, "vs");
    let sols = query(&mut kb, "classic.sat.model", &[vs]);
    assert!(
        sols.iter().all(|s| s.is_definite()),
        "a model is a fully bound assignment, never a conditional row",
    );
    assert_eq!(
        sols.len(),
        2,
        "(p or not q) and (q or r) and (not p or not r) has exactly two models — \
         p q r = yes yes no and no no yes — and exclusive `or2` cases count each once",
    );
}
