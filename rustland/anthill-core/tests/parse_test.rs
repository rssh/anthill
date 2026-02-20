/// Integration tests: parse .anthill source → verify IR structure → load into KB → query.

use anthill_core::parse;
use anthill_core::parse::ir::*;
use anthill_core::kb::{KnowledgeBase, SortKind};
use anthill_core::kb::term::{Term, Literal, FnArg};
use anthill_core::kb::load::{self, NullResolver};

// ── Parsing tests ───────────────────────────────────────────────

#[test]
fn parse_empty_domain() {
    let source = "domain banking {\n}\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Domain(d) => {
            assert_eq!(parsed.interner.resolve(d.name.last()), "banking");
            assert!(d.items.is_empty());
        }
        other => panic!("expected Domain, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_abstract_sort() {
    let source = "sort Scalar\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::AbstractSort(s) => {
            assert_eq!(parsed.interner.resolve(s.name.last()), "Scalar");
            assert!(s.visibility.is_none());
        }
        other => panic!("expected AbstractSort, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_defined_sort() {
    let source = r#"sort WorkStatus = {
  entity Draft
  entity Open
  entity Claimed(agent: String, since: String)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::DefinedSort(s) => {
            assert_eq!(parsed.interner.resolve(s.name.last()), "WorkStatus");
            assert_eq!(s.constructors.len(), 3);
            assert_eq!(parsed.interner.resolve(s.constructors[0].name.last()), "Draft");
            assert_eq!(parsed.interner.resolve(s.constructors[1].name.last()), "Open");
            assert_eq!(parsed.interner.resolve(s.constructors[2].name.last()), "Claimed");
            assert_eq!(s.constructors[2].fields.len(), 2);
        }
        other => panic!("expected DefinedSort, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_fact_with_meta() {
    let source = r#"fact parent("alice", "bob") [trust: axiom, agent: "author"]"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Fact(f) => {
            // The term should be a fn_term: parent("alice", "bob")
            match parsed.terms.get(f.term) {
                Term::Fn { functor, args } => {
                    assert_eq!(parsed.interner.resolve(*functor), "parent");
                    assert_eq!(args.len(), 2);
                    // Check first arg is "alice"
                    match &args[0] {
                        FnArg::Positional(id) => match parsed.terms.get(*id) {
                            Term::Const(Literal::String(s)) => assert_eq!(s, "alice"),
                            other => panic!("expected String, got {:?}", other),
                        },
                        other => panic!("expected Positional, got {:?}", other),
                    }
                }
                other => panic!("expected Fn, got {:?}", other),
            }
            // Check meta block
            let meta = f.meta.as_ref().expect("expected meta block");
            assert_eq!(meta.entries.len(), 2);
        }
        other => panic!("expected Fact, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_domain_with_entity_and_operation() {
    let source = r#"domain banking
  export Account, Money, deposit
  entity Account(id: AccountId, balance: Money)
  operation deposit(a: Account, m: Money) -> Account
    requires gt(m, zero-val)
    ensures eq(balance(result), add(balance(a), m))
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Domain(d) => {
            assert_eq!(parsed.interner.resolve(d.name.last()), "banking");
            assert_eq!(d.exports.len(), 3);
            assert_eq!(d.items.len(), 2); // entity + operation

            // Check entity
            match &d.items[0] {
                Item::Entity(e) => {
                    assert_eq!(parsed.interner.resolve(e.name.last()), "Account");
                    assert_eq!(e.fields.len(), 2);
                }
                other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
            }

            // Check operation
            match &d.items[1] {
                Item::Operation(o) => {
                    assert_eq!(parsed.interner.resolve(o.name.last()), "deposit");
                    assert_eq!(o.params.len(), 2);
                    assert_eq!(o.requires.len(), 1);
                    assert_eq!(o.ensures.len(), 1);
                }
                other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
            }
        }
        other => panic!("expected Domain, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_simple_project() {
    let source = r#"project cps2 {
  language: scala
  build: sbt
  tools: sbt-compile, sbt-test
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Project(p) => {
            assert_eq!(parsed.interner.resolve(p.name.last()), "cps2");
        }
        other => panic!("expected Project, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_tool_declaration() {
    let source = r#"tool sbt-test-only {
  command: "sbt"
  args: ["cps2/testOnly", "$testClass"]
  timeout: 10m
  success: ExitZero
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Tool(t) => {
            assert_eq!(parsed.interner.resolve(t.name.last()), "sbt-test-only");
            assert_eq!(t.command, "sbt");
            assert!(matches!(t.success, SuccessCriterion::ExitZero));
        }
        other => panic!("expected Tool, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_workitem() {
    let source = r#"workitem WI-CPS2-MATCH-001 {
  description: "Add AST pattern matching"
  acceptance:
    Compiles({ path: "src/main/scala", scope: Main })
  status: Open
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::WorkItem(w) => {
            assert_eq!(parsed.interner.resolve(w.id.last()), "WI-CPS2-MATCH-001");
            assert!(matches!(w.status, WorkStatus::Open));
            assert_eq!(w.acceptance.len(), 1);
        }
        other => panic!("expected WorkItem, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_line_comment() {
    let source = "-- this is a comment\nsort T\n";
    let parsed = parse::parse(source).expect("parse failed");
    // Comment should be skipped, only the sort should be parsed
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::AbstractSort(s) => {
            assert_eq!(parsed.interner.resolve(s.name.last()), "T");
        }
        other => panic!("expected AbstractSort, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Loading tests ───────────────────────────────────────────────

#[test]
fn load_domain_into_kb() {
    let source = r#"domain banking {
  entity Account(id: AccountId, balance: Money)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Should have facts: Domain(banking), Entity(Account)
    assert!(kb.fact_count() >= 2);
}

#[test]
fn load_defined_sort_registers_subsorts() {
    let source = r#"sort Nat = {
  entity zero
  entity succ(pred: Nat)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Find the Nat and zero sort terms
    let nat_sym = kb.intern("Nat");
    let zero_sym = kb.intern("zero");

    // Look up sort terms by finding them in the KB
    let nat_term = kb.alloc(Term::Fn {
        functor: nat_sym,
        args: smallvec::SmallVec::new(),
    });
    let zero_term = kb.alloc(Term::Fn {
        functor: zero_sym,
        args: smallvec::SmallVec::new(),
    });

    // Check subsort relationship
    assert!(kb.is_subtype(zero_term, nat_term), "zero should be a subtype of Nat");
    assert!(!kb.is_subtype(nat_term, zero_term), "Nat should not be a subtype of zero");

    // Check sort kinds
    assert_eq!(kb.sort_kind(nat_term), Some(SortKind::Defined));
    assert_eq!(kb.sort_kind(zero_term), Some(SortKind::Constructor));

    // Check children
    let children = kb.sort_children(nat_term);
    assert!(children.len() >= 2, "Nat should have at least 2 children (zero, succ)");
}

#[test]
fn load_fact_and_query_by_sort() {
    let source = r#"fact parent("alice", "bob") [trust: axiom]"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let fact_sort = kb.make_name_term("Fact");
    let facts = kb.by_sort(fact_sort);
    assert!(!facts.is_empty(), "should have at least one Fact");
}

#[test]
fn load_banking_domain() {
    let source = r#"domain banking
  export Account, Money, deposit

  sort Money = {
    entity dollars(amount: Int)
  }

  entity Account(id: AccountId, balance: Money)

  operation deposit(a: Account, m: Money) -> Account
    requires gt(m, zero-val)
    ensures eq(balance(result), add(balance(a), m))

  fact initial-balance(dollars(0)) [trust: axiom]
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Check we have facts of various sorts
    let domain_sort = kb.make_name_term("Domain");
    assert!(!kb.by_sort(domain_sort).is_empty(), "should have Domain fact");

    let entity_sort = kb.make_name_term("Entity");
    assert!(!kb.by_sort(entity_sort).is_empty(), "should have Entity fact");

    let op_sort = kb.make_name_term("Operation");
    assert!(!kb.by_sort(op_sort).is_empty(), "should have Operation fact");

    let fact_sort = kb.make_name_term("Fact");
    assert!(!kb.by_sort(fact_sort).is_empty(), "should have Fact fact");

    // Check sort relationship: dollars < Money
    let money_sym = kb.intern("Money");
    let dollars_sym = kb.intern("dollars");
    let money_term = kb.alloc(Term::Fn {
        functor: money_sym,
        args: smallvec::SmallVec::new(),
    });
    let dollars_term = kb.alloc(Term::Fn {
        functor: dollars_sym,
        args: smallvec::SmallVec::new(),
    });
    assert!(kb.is_subtype(dollars_term, money_term));
}

#[test]
fn load_workitem_and_query() {
    let source = r#"workitem WI-001 {
  description: "Implement feature X"
  acceptance:
    Compiles({ path: "src/main", scope: Main })
  status: Open
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let wi_sort = kb.make_name_term("WorkItem");
    let workitems = kb.by_sort(wi_sort);
    assert_eq!(workitems.len(), 1, "should have one WorkItem");

    // Check the term has the expected structure
    let fid = workitems[0];
    let tid = kb.fact_term(fid);
    match kb.get_term(tid) {
        Term::Fn { functor, args } => {
            assert_eq!(kb.resolve_sym(*functor), "WI-001");
            assert!(!args.is_empty());
        }
        other => panic!("expected Fn term for WorkItem, got {:?}", other),
    }
}

#[test]
fn by_functor_query() {
    let source = r#"fact parent("alice", "bob")
fact parent("bob", "charlie")
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let parent_sym = kb.intern("parent");
    let results = kb.by_functor(parent_sym);
    assert_eq!(results.len(), 2, "should find 2 parent facts");
}

#[test]
fn retract_fact() {
    let source = r#"fact parent("alice", "bob")"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let fact_sort = kb.make_name_term("Fact");
    let facts = kb.by_sort(fact_sort);
    assert_eq!(facts.len(), 1);

    kb.retract(facts[0]);
    assert_eq!(kb.by_sort(fact_sort).len(), 0);
}
