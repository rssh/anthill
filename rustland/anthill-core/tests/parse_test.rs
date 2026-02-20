/// Integration tests: parse .anthill source → verify IR structure → load into KB → query.

use anthill_core::parse;
use anthill_core::parse::ir::*;
use anthill_core::kb::{KnowledgeBase, SortKind};
use anthill_core::kb::term::{Term, TermId, Literal, FnArg};
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
fn parse_sort_with_body() {
    let source = r#"sort WorkStatus {
  entity Draft
  entity Open
  entity Claimed(agent: String, since: String)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            assert_eq!(parsed.interner.resolve(s.name.last()), "WorkStatus");
            assert_eq!(s.items.len(), 3);
            // Check each entity constructor
            match &s.items[0] {
                Item::Entity(e) => assert_eq!(parsed.interner.resolve(e.name.last()), "Draft"),
                other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
            }
            match &s.items[1] {
                Item::Entity(e) => assert_eq!(parsed.interner.resolve(e.name.last()), "Open"),
                other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
            }
            match &s.items[2] {
                Item::Entity(e) => {
                    assert_eq!(parsed.interner.resolve(e.name.last()), "Claimed");
                    assert_eq!(e.fields.len(), 2);
                }
                other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
            }
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
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
fn load_sort_with_body_registers_subsorts() {
    let source = r#"sort Nat {
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

  sort Money {
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
fn load_sort_with_operation() {
    let source = r#"sort Account
  entity checking(id: AccountId, balance: Money)
  entity savings(id: AccountId, balance: Money, rate: Money)

  operation deposit(a: Account, m: Money) -> Account
    requires gt(m, zero-val)
    ensures eq(balance(result), add(balance(a), m))

  operation withdraw(a: Account, m: Money) -> Account
    requires gt(m, zero-val), gte(balance(a), m)
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Operations should be registered as facts with sort "Operation"
    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 2, "should have 2 Operation facts (deposit, withdraw)");

    // The operation facts should be scoped to the Account sort (not a separate domain)
    let account_sym = kb.intern("Account");
    let account_term = kb.alloc(Term::Fn {
        functor: account_sym,
        args: smallvec::SmallVec::new(),
    });
    for &fid in &ops {
        assert_eq!(
            kb.fact_domain(fid), account_term,
            "operation should be scoped to the Account sort"
        );
    }

    // Verify operation terms have the right functors
    let deposit_sym = kb.intern("deposit");
    let withdraw_sym = kb.intern("withdraw");
    let op_functors: Vec<_> = ops.iter().map(|&fid| {
        match kb.get_term(kb.fact_term(fid)) {
            Term::Fn { functor, .. } => *functor,
            other => panic!("expected Fn term for operation, got {:?}", other),
        }
    }).collect();
    assert!(op_functors.contains(&deposit_sym), "should have deposit operation");
    assert!(op_functors.contains(&withdraw_sym), "should have withdraw operation");

    // The sort itself should be Defined (has entities) with constructors as subsorts
    assert_eq!(kb.sort_kind(account_term), Some(SortKind::Defined));

    let checking_sym = kb.intern("checking");
    let checking_term = kb.alloc(Term::Fn {
        functor: checking_sym,
        args: smallvec::SmallVec::new(),
    });
    assert!(kb.is_subtype(checking_term, account_term),
        "checking should be a subtype of Account");
    assert_eq!(kb.sort_kind(checking_term), Some(SortKind::Constructor));
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

// ── Member fact tests ───────────────────────────────────────────

#[test]
fn member_facts_for_sort_with_body() {
    let source = r#"sort Nat {
  entity zero
  entity succ(pred: Nat)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let member_sort = kb.make_name_term("Member");
    let members = kb.by_sort(member_sort);

    // Should have 2 Constructor members (zero, succ)
    assert_eq!(members.len(), 2, "Nat should have 2 member facts");

    // Verify they are Constructor members
    for &fid in &members {
        let term = kb.fact_term(fid);
        match kb.get_term(term) {
            Term::Fn { args, .. } => {
                assert_eq!(args.len(), 3);
                // Second arg should be Ident("Constructor")
                match args[1] {
                    FnArg::Positional(id) => {
                        let ctor_sym = kb.intern("Constructor");
                        assert!(matches!(kb.get_term(id), Term::Ident(s) if *s == ctor_sym));
                    }
                    _ => panic!("expected positional arg"),
                }
            }
            other => panic!("expected Fn term, got {:?}", other),
        }
    }
}

#[test]
fn member_facts_for_sort_with_params_and_ops() {
    let source = r#"sort Account
  sort AccountId
  entity checking(id: AccountId, balance: Int)
  entity savings(id: AccountId, balance: Int)
  operation deposit(a: Account, m: Int) -> Account
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let member_sort = kb.make_name_term("Member");
    let account_term = kb.make_name_term("Account");

    // Get member facts for Account specifically
    let account_facts = kb.by_domain(account_term);
    let member_facts: Vec<_> = account_facts
        .iter()
        .filter(|&&fid| kb.fact_sort(fid) == member_sort)
        .copied()
        .collect();

    // Should have: AccountId (Sort), checking (Constructor), savings (Constructor), deposit (Operation)
    assert!(member_facts.len() >= 4,
        "Account should have at least 4 members, got {}", member_facts.len());
}

#[test]
fn member_facts_for_domain() {
    let source = r#"domain banking {
  entity Account(id: String, balance: Int)
  operation deposit(a: Account, m: Int) -> Account
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let member_sort = kb.make_name_term("Member");
    let banking_term = kb.make_name_term("banking");

    let domain_facts = kb.by_domain(banking_term);
    let member_facts: Vec<_> = domain_facts
        .iter()
        .filter(|&&fid| kb.fact_sort(fid) == member_sort)
        .copied()
        .collect();

    // Should have: Account (Constructor), deposit (Operation)
    assert_eq!(member_facts.len(), 2,
        "banking domain should have 2 member facts");
}

#[test]
fn member_facts_queryable_by_domain() {
    let source = r#"sort Option {
  sort T
  entity none
  entity some(value: T)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let option_term = kb.make_name_term("Option");
    let member_sort = kb.make_name_term("Member");

    // Query by_domain for Option should include member facts
    let domain_facts = kb.by_domain(option_term);
    let member_count = domain_facts
        .iter()
        .filter(|&&fid| kb.fact_sort(fid) == member_sort)
        .count();

    // T (Sort), none (Constructor), some (Constructor) = 3 members
    assert_eq!(member_count, 3,
        "Option should have 3 members (T, none, some)");
}

// ── Mutual reference tests ──────────────────────────────────────

fn check_term_contains(kb: &KnowledgeBase, term: TermId, target: TermId, found: &mut bool) {
    if term == target {
        *found = true;
        return;
    }
    if let Term::Fn { args, .. } = kb.get_term(term) {
        for arg in args.iter() {
            let sub = match arg {
                FnArg::Positional(id) => *id,
                FnArg::Named(_, id) => *id,
            };
            check_term_contains(kb, sub, target, found);
        }
    }
}

#[test]
fn mutual_reference_two_domains() {
    // File 1: domain X references sort from domain Y
    let file_x = r#"domain Geometry
  sort Shape
  entity circle(radius: Int)
  entity rect(w: Int, h: Int)
  operation area(s: Shape) -> Measure
end
"#;
    // File 2: domain Y references sort from domain X
    let file_y = r#"domain Units
  sort Measure
  entity meters(n: Int)
  entity pixels(n: Int)
  operation convert(m: Measure, target: Shape) -> Measure
end
"#;

    let parsed_x = parse::parse(file_x).expect("parse Geometry");
    let parsed_y = parse::parse(file_y).expect("parse Units");

    // Load both files into the same KB — order shouldn't matter for basic loading
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &[&parsed_x, &parsed_y], &NullResolver)
        .expect("load_all failed");

    // Both domains should be registered
    let domain_sort = kb.make_name_term("Domain");
    let domains = kb.by_sort(domain_sort);
    assert_eq!(domains.len(), 2, "should have 2 domains");

    // Geometry's facts should reference Measure (from Units)
    let geometry_term = kb.make_name_term("Geometry");
    let geometry_facts = kb.by_domain(geometry_term);
    assert!(!geometry_facts.is_empty(), "Geometry should have facts");

    // Units' facts should reference Shape (from Geometry)
    let units_term = kb.make_name_term("Units");
    let units_facts = kb.by_domain(units_term);
    assert!(!units_facts.is_empty(), "Units should have facts");

    // Both sorts should exist as type references in operations
    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 2, "should have 2 operations (area, convert)");

    // Verify cross-references: area returns Measure, convert takes Shape
    let measure_term = kb.make_name_term("Measure");
    let shape_term = kb.make_name_term("Shape");

    // area operation is in Geometry domain but references Measure
    let mut area_refs_measure = false;
    for &fid in &geometry_facts {
        let term = kb.fact_term(fid);
        check_term_contains(&kb, term, measure_term, &mut area_refs_measure);
    }
    assert!(area_refs_measure, "Geometry's area should reference Measure");

    // convert operation is in Units domain but references Shape
    let mut convert_refs_shape = false;
    for &fid in &units_facts {
        let term = kb.fact_term(fid);
        check_term_contains(&kb, term, shape_term, &mut convert_refs_shape);
    }
    assert!(convert_refs_shape, "Units' convert should reference Shape");
}

#[test]
fn mutual_reference_load_order_independent() {
    let file_a = r#"sort A {
  entity mkA(ref: B)
}
"#;
    let file_b = r#"sort B {
  entity mkB(ref: A)
}
"#;

    let parsed_a = parse::parse(file_a).expect("parse A");
    let parsed_b = parse::parse(file_b).expect("parse B");

    // Load A then B
    let mut kb1 = KnowledgeBase::new();
    load::load_all(&mut kb1, &[&parsed_a, &parsed_b], &NullResolver)
        .expect("load A,B failed");

    // Load B then A
    let mut kb2 = KnowledgeBase::new();
    load::load_all(&mut kb2, &[&parsed_b, &parsed_a], &NullResolver)
        .expect("load B,A failed");

    // Both should have the same fact counts
    assert_eq!(kb1.fact_count(), kb2.fact_count(),
        "load order should not affect fact count");

    // Both should have the same sort relationships
    let a1 = kb1.make_name_term("A");
    let mka1 = kb1.make_name_term("mkA");
    assert!(kb1.is_subtype(mka1, a1));

    let a2 = kb2.make_name_term("A");
    let mka2 = kb2.make_name_term("mkA");
    assert!(kb2.is_subtype(mka2, a2));
}
