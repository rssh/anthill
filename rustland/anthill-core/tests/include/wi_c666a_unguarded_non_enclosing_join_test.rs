//! C666A, rebased onto proposal 061 ownership.
//!
//! An UNDECLARED `Spec.p` / `A.p` pair is already refused by 061: two visible scopes
//! may not both auto-declare one name.  The live C666A shape therefore declares `p`
//! explicitly in `Spec`; `A` and `B` then resolve their clause heads through a
//! non-enclosing `requires` edge and silently append both clauses to `Spec.p`.
//!
//! BACK-OUT: removing the C666A check makes the three refusal tests load clean.  The
//! enclosing, rename, and selective-import rows pass either way by design: they are
//! controls proving that the check is about an IMPLICIT whole-scope edge, not merely
//! about two scopes or two files.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

#[test]
fn requires_may_not_append_unguarded_clauses_to_a_declared_predicate() {
    let src = r#"
namespace c666a.requires
  sort Spec
    rule p(?x)
    rule p(0) :- true
  end

  sort A
    requires c666a.requires.Spec
    entity a(n: Int64)
    rule p(1) :- true
  end

  sort B
    requires c666a.requires.Spec
    entity b(n: Int64)
    rule p(2) :- true
  end
end
"#;

    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(src),
        &[
            "the unguarded rule head `p` in 'c666a.requires.A' joins predicate 'c666a.requires.Spec.p' through a non-enclosing scope edge",
            "the unguarded rule head `p` in 'c666a.requires.B' joins predicate 'c666a.requires.Spec.p' through a non-enclosing scope edge",
        ],
    );
}

#[test]
fn wildcard_import_may_not_append_an_unguarded_clause() {
    let src = r#"
namespace c666a.wild.lib
  rule p(?x)
  rule p(0) :- true
end

namespace c666a.wild.user
  import c666a.wild.lib.*
  rule p(1) :- true
end
"#;

    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(src),
        &["the unguarded rule head `p` in 'c666a.wild.user' joins predicate 'c666a.wild.lib.p' through a non-enclosing scope edge"],
    );
}

#[test]
fn provides_may_not_append_an_unguarded_clause() {
    let src = r#"
namespace c666a.provides
  sort Spec
    sort T = ?
    rule p(?x)
    rule p(0) :- true
  end

  sort Implementation
    sort T = ?
    provides c666a.provides.Spec[T = T]
    entity implementation(n: T)
    rule p(1) :- true
  end
end
"#;

    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(src),
        &["the unguarded rule head `p` in 'c666a.provides.Implementation' joins predicate 'c666a.provides.Spec.p' through a non-enclosing scope edge"],
    );
}

#[test]
fn renaming_the_declared_predicate_keeps_implementors_independent() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace c666a.rename
  sort Spec
    rule other(?x)
    rule other(0) :- true
  end

  sort A
    requires c666a.rename.Spec
    entity a(n: Int64)
    rule p(1) :- true
  end

  sort B
    requires c666a.rename.Spec
    entity b(n: Int64)
    rule p(2) :- true
  end
end
"#,
    );

    assert_eq!(clauses(&kb, "c666a.rename.Spec.other"), Some(1));
    assert_eq!(clauses(&kb, "c666a.rename.A.p"), Some(1));
    assert_eq!(clauses(&kb, "c666a.rename.B.p"), Some(1));
    assert_eq!(answers(&mut kb, "c666a.rename.Spec.other(0)"), 1);
    assert_eq!(answers(&mut kb, "c666a.rename.A.p(1)"), 1);
    assert_eq!(answers(&mut kb, "c666a.rename.A.p(2)"), 0);
    assert_eq!(answers(&mut kb, "c666a.rename.B.p(2)"), 1);
    assert_eq!(answers(&mut kb, "c666a.rename.B.p(1)"), 0);
}

#[test]
fn an_enclosing_scope_may_still_contribute_to_its_declared_predicate() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace c666a.enclosing
  rule p(?x)
  rule p(1) :- true

  sort Rec
    entity rec(n: Int64)
    rule p(2) :- true
  end
end
"#,
    );

    assert_eq!(clauses(&kb, "c666a.enclosing.p"), Some(2));
    assert_eq!(clauses(&kb, "c666a.enclosing.Rec.p"), None);
    assert_eq!(answers(&mut kb, "c666a.enclosing.p(1)"), 1);
    assert_eq!(answers(&mut kb, "c666a.enclosing.p(2)"), 1);
}

#[test]
fn a_selective_import_explicitly_opts_into_the_predicate() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace c666a.selected.lib
  rule p(?x)
  rule p(0) :- true
end

namespace c666a.selected.user
  import c666a.selected.lib.{p}
  rule p(1) :- true
end
"#,
    );

    assert_eq!(clauses(&kb, "c666a.selected.lib.p"), Some(2));
    assert_eq!(clauses(&kb, "c666a.selected.user.p"), None);
    assert_eq!(answers(&mut kb, "c666a.selected.lib.p(0)"), 1);
    assert_eq!(answers(&mut kb, "c666a.selected.lib.p(1)"), 1);
}
