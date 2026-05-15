//! WI-139: equational rules are cite-required by default; opt-in
//! via `[simp]` / `[unfold]` to enter the `by_functor` index for
//! SLD goal resolution. (`[hint]` is recognised by the parser but
//! its SMT-side semantics — auto-include in proof preamble — are
//! deferred for v0; the attribute itself parses and stores cleanly.)


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, is_equational_head, NullResolver};
use anthill_core::parse;
use anthill_core::kb::term::Term;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

/// Count equational-headed rules indexed in by_functor. Walks
/// every by_functor entry whose head term parses as an equation
/// (head functor's QN ends in `eq` or `=`). Sidesteps the
/// scope-resolution complexity of finding the right `eq` symbol
/// by checking the head shape directly.
fn equational_indexed_count(mut kb: KnowledgeBase) -> usize {
    let mut count = 0usize;
    let rule_sort_term = kb.make_name_term("Rule");
    let all_rules = kb.by_sort(rule_sort_term);
    for &rid in &all_rules {
        let head = kb.rule_head(rid);
        if !is_equational_head(&kb, head) { continue; }
        // Is this rule still in by_functor under its head's
        // functor? Probe directly.
        if let Term::Fn { functor, .. } = kb.get_term(head) {
            let f = *functor;
            if kb.by_functor(f).iter().any(|&r| r == rid) {
                count += 1;
            }
        }
    }
    count
}

#[test]
fn bare_equational_rule_is_excluded_from_by_functor() {
    let baseline = equational_indexed_count(load_with(r#"
        namespace test.eqattr.bare
          export Marker
          rule Marker(?x) :- ?x = 1
        end
    "#));
    let with_law = equational_indexed_count(load_with(r#"
        namespace test.eqattr.bare
          export Marker, my_law
          rule Marker(?x) :- ?x = 1
          rule {
            my_law: foo(?a, ?b) = foo(?b, ?a)
          }
        end
    "#));
    assert_eq!(
        baseline, with_law,
        "bare equational rule must NOT add to the by_functor index — \
         got baseline {baseline} → with_law {with_law}"
    );
}

#[test]
fn simp_attributed_equational_rule_is_indexed() {
    // Top-level rule_declaration with attached meta_block.
    let baseline = equational_indexed_count(load_with(r#"
        namespace test.eqattr.simp_baseline
          export Marker
          rule Marker(?x) :- ?x = 1
        end
    "#));
    let with_simp = equational_indexed_count(load_with(r#"
        namespace test.eqattr.simp_with
          export Marker
          rule Marker(?x) :- ?x = 1
          rule my_def: foo(?a) = bar(?a) [simp]
        end
    "#));
    assert!(
        with_simp > baseline,
        "[simp]-tagged equational rule must be in by_functor — \
         got baseline {baseline} → with_simp {with_simp}"
    );
}

#[test]
fn unfold_attributed_equational_rule_is_indexed() {
    let baseline = equational_indexed_count(load_with(r#"
        namespace test.eqattr.unfold_baseline
          export Marker
          rule Marker(?x) :- ?x = 1
        end
    "#));
    let with_unfold = equational_indexed_count(load_with(r#"
        namespace test.eqattr.unfold_with
          export Marker
          rule Marker(?x) :- ?x = 1
          rule my_def: g(?a) = h(?a) [unfold]
        end
    "#));
    assert!(
        with_unfold > baseline,
        "[unfold]-tagged equational rule must be in by_functor — \
         got baseline {baseline} → with_unfold {with_unfold}"
    );
}

#[test]
fn hint_attributed_equational_rule_stays_unindexed_in_v0() {
    // [hint] currently doesn't gate the by_functor index — its
    // semantics are SMT-only auto-emission, which v0 hasn't wired
    // yet. The attribute parses cleanly; the rule remains
    // cite-required for SLD-side resolution. Once SMT-emission
    // integration lands the rule will additionally appear in the
    // discharge's preamble within scope.
    let baseline = equational_indexed_count(load_with(r#"
        namespace test.eqattr.hint
          export Marker
          rule Marker(?x) :- ?x = 1
        end
    "#));
    let with_hint = equational_indexed_count(load_with(r#"
        namespace test.eqattr.hint
          export Marker, my_lemma
          rule Marker(?x) :- ?x = 1
          rule {
            my_lemma: comm(?a, ?b) = comm(?b, ?a)
            [hint]
          }
        end
    "#));
    assert_eq!(
        baseline, with_hint,
        "[hint] alone must NOT add to the by_functor index in v0 \
         — got baseline {baseline} → with_hint {with_hint}"
    );
}

#[test]
fn horn_rule_is_indexed_regardless_of_attributes() {
    // Horn rules (head is a non-`=` term, body via `:-`) are
    // unaffected by the equational gate. Always indexed in
    // by_functor for SLD goal resolution.
    let kb = load_with(r#"
        namespace test.eqattr.horn
          export horny
          rule horny(?x, ?y)
            :- ?x = 1,
               ?y = 2
        end
    "#);
    let sym = kb.try_resolve_symbol("test.eqattr.horn.horny")
        .expect("horny rule must resolve");
    assert!(
        !kb.by_functor(sym).is_empty(),
        "Horn rule must be in by_functor for goal resolution"
    );
}
