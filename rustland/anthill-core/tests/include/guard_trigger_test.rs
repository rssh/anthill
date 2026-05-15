//! WI-022: trigger sorts auto-extracted from a LogicalQuery guard term.


use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

use crate::common::load_kb_with;

fn alloc_named(kb: &mut KnowledgeBase, functor_qn: &str, named: &[(&str, TermId)]) -> TermId {
    let f_sym = kb.try_resolve_symbol(functor_qn)
        .unwrap_or_else(|| panic!("symbol not resolved: {functor_qn}"));
    let args: SmallVec<[(_, _); 2]> = named.iter()
        .map(|(k, v)| (kb.intern(k), *v))
        .collect();
    kb.alloc(Term::Fn { functor: f_sym, pos_args: SmallVec::new(), named_args: args })
}

#[test]
fn pattern_query_extracts_parent_sort() {
    let source = r#"
namespace test.guard
  sort Family
    entity ancestor(parent: Person, child: Person)
  end
  sort Person
    entity alice
    entity bob
  end
end
"#;
    let mut kb = load_kb_with(source);

    let ancestor_sym = kb.try_resolve_symbol("test.guard.Family.ancestor").unwrap();
    let family_sym = kb.try_resolve_symbol("test.guard.Family").unwrap();

    let p_sym = kb.intern("p");
    let var_p = kb.fresh_var(p_sym);
    let var_p_term = kb.alloc(Term::Var(Var::Global(var_p)));
    let parent = kb.intern("parent");
    let ancestor_pat = kb.alloc(Term::Fn {
        functor: ancestor_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(parent, var_p_term)]),
    });

    let guard = alloc_named(&mut kb, "anthill.reflect.LogicalQuery.pattern_query",
        &[("term", ancestor_pat)]);
    let cid = kb.add_guard(guard);

    let family_term = kb.make_name_term_from_sym(family_sym);
    assert_eq!(kb.guard_trigger_sorts(cid), &[family_term]);
}

#[test]
fn conjunction_collects_sorts_from_both_branches() {
    let source = r#"
namespace test.guard2
  sort Family
    entity ancestor(parent: Person, child: Person)
  end
  sort Person
    entity alice
  end
  sort Place
    entity home
  end
end
"#;
    let mut kb = load_kb_with(source);

    let ancestor_sym = kb.try_resolve_symbol("test.guard2.Family.ancestor").unwrap();
    let home_sym = kb.try_resolve_symbol("test.guard2.Place.home").unwrap();
    let family_sym = kb.try_resolve_symbol("test.guard2.Family").unwrap();
    let place_sym = kb.try_resolve_symbol("test.guard2.Place").unwrap();

    let p_sym = kb.intern("p");
    let var_p = kb.fresh_var(p_sym);
    let var_p_term = kb.alloc(Term::Var(Var::Global(var_p)));
    let parent = kb.intern("parent");
    let ancestor_pat = kb.alloc(Term::Fn {
        functor: ancestor_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(parent, var_p_term)]),
    });
    let home_pat = kb.alloc(Term::Fn {
        functor: home_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    let pq_a = alloc_named(&mut kb, "anthill.reflect.LogicalQuery.pattern_query",
        &[("term", ancestor_pat)]);
    let pq_h = alloc_named(&mut kb, "anthill.reflect.LogicalQuery.pattern_query",
        &[("term", home_pat)]);
    let conj = alloc_named(&mut kb, "anthill.reflect.LogicalQuery.conjunction",
        &[("left", pq_a), ("right", pq_h)]);

    let cid = kb.add_guard(conj);

    let family_term = kb.make_name_term_from_sym(family_sym);
    let place_term = kb.make_name_term_from_sym(place_sym);
    let triggers = kb.guard_trigger_sorts(cid);
    assert!(triggers.contains(&family_term), "missing Family in {:?}", triggers);
    assert!(triggers.contains(&place_term), "missing Place in {:?}", triggers);
    assert_eq!(triggers.len(), 2, "expected exactly two unique trigger sorts");
}
