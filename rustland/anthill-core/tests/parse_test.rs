/// Integration tests: parse .anthill source → verify IR structure → load into KB → query.

mod common;

use anthill_core::parse;
use anthill_core::parse::ir::*;
use anthill_core::kb::{KnowledgeBase, SortKind};
use anthill_core::kb::term::{Term, TermId, Literal};
use anthill_core::kb::load::{self, NullResolver};

/// Count elements in a cons-list (cons/nil encoding).
fn count_list_elements(kb: &KnowledgeBase, list_tid: TermId) -> usize {
    let mut count = 0;
    let mut current = list_tid;
    loop {
        match kb.get_term(current) {
            Term::Fn { functor, named_args, .. } => {
                let name = kb.resolve_sym(*functor);
                if name == "nil" {
                    break;
                }
                if name == "cons" {
                    count += 1;
                    match named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "tail") {
                        Some(&(_, t)) => current = t,
                        None => break,
                    }
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
    count
}

use common::{collect_anthill_files, stdlib_dir};

// ── Parsing tests ───────────────────────────────────────────────

#[test]
fn parse_empty_namespace() {
    let source = "namespace banking {\n}\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Namespace(n) => {
            assert_eq!(parsed.symbols.name(n.name.last()), "banking");
            assert!(n.items.is_empty());
        }
        other => panic!("expected Namespace, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_abstract_sort() {
    let source = "sort Scalar = ?\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::AbstractSort(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "Scalar");
            assert!(s.visibility.is_none());
            assert!(matches!(s.definition, TypeExpr::Variable { .. }));
        }
        other => panic!("expected AbstractSort, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_abstract_sort_named_variable() {
    let source = "sort T = ?Element\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::AbstractSort(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "T");
            assert!(s.visibility.is_none());
            match &s.definition {
                TypeExpr::Variable { term_id, .. } => {
                    let term = parsed.terms.get(*term_id);
                    match term {
                        anthill_core::kb::term::Term::Var(vid) => {
                            assert_eq!(parsed.symbols.name(vid.name()), "Element");
                        }
                        other => panic!("expected Var term, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type, got {:?}", other),
            }
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
            assert_eq!(parsed.symbols.name(s.name.last()), "WorkStatus");
            assert_eq!(s.items.len(), 3);
            // Check each entity constructor
            match &s.items[0] {
                Item::Entity(e) => assert_eq!(parsed.symbols.name(e.name.last()), "Draft"),
                other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
            }
            match &s.items[1] {
                Item::Entity(e) => assert_eq!(parsed.symbols.name(e.name.last()), "Open"),
                other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
            }
            match &s.items[2] {
                Item::Entity(e) => {
                    assert_eq!(parsed.symbols.name(e.name.last()), "Claimed");
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
                Term::Fn { functor, pos_args, .. } => {
                    assert_eq!(parsed.symbols.name(*functor), "parent");
                    assert_eq!(pos_args.len(), 2);
                    // Check first arg is "alice"
                    match parsed.terms.get(pos_args[0]) {
                        Term::Const(Literal::String(s)) => assert_eq!(s, "alice"),
                        other => panic!("expected String, got {:?}", other),
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
fn parse_namespace_with_entity_and_operation() {
    let source = r#"namespace banking
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
        Item::Namespace(n) => {
            assert_eq!(parsed.symbols.name(n.name.last()), "banking");
            assert_eq!(n.exports.len(), 3);
            assert_eq!(n.items.len(), 2); // entity + operation

            // Check entity
            match &n.items[0] {
                Item::Entity(e) => {
                    assert_eq!(parsed.symbols.name(e.name.last()), "Account");
                    assert_eq!(e.fields.len(), 2);
                }
                other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
            }

            // Check operation
            match &n.items[1] {
                Item::Operation(o) => {
                    assert_eq!(parsed.symbols.name(o.name.last()), "deposit");
                    assert_eq!(o.params.len(), 2);
                    assert_eq!(o.requires.len(), 1);
                    assert_eq!(o.ensures.len(), 1);
                }
                other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
            }
        }
        other => panic!("expected Namespace, got {:?}", std::mem::discriminant(other)),
    }
}


#[test]
fn parse_line_comment() {
    let source = "-- this is a comment\nsort T = ?\n";
    let parsed = parse::parse(source).expect("parse failed");
    // Comment should be skipped, only the sort should be parsed
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::AbstractSort(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "T");
        }
        other => panic!("expected AbstractSort, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Loading tests ───────────────────────────────────────────────

#[test]
fn load_namespace_into_kb() {
    let source = r#"namespace banking {
  sort AccountId = ?
  sort Money = ?
  entity Account(id: AccountId, balance: Money)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Should have facts: Namespace(banking), Entity(Account)
    assert!(kb.fact_count() >= 2);
}

#[test]
fn load_sort_with_body_registers_entity_of() {
    let source = r#"sort Nat {
  entity zero
  entity succ(pred: Nat)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Find the Nat and zero sort terms (use resolve_qualified_name_term for user-defined names)
    let nat_term = kb.resolve_qualified_name_term("Nat");
    let zero_term = kb.resolve_qualified_name_term("Nat.zero");

    // Check entity-of relationship
    assert!(kb.is_entity_of(zero_term, nat_term), "zero should be entity of Nat");
    assert!(!kb.is_entity_of(nat_term, zero_term), "Nat should not be entity of zero");

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
fn load_banking_namespace() {
    let source = r#"namespace banking
  export Account, Money, deposit

  sort AccountId = ?

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
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Check we have facts of various sorts
    let ns_sort = kb.make_name_term("Namespace");
    assert!(!kb.by_sort(ns_sort).is_empty(), "should have Namespace fact");

    let entity_sort = kb.make_name_term("Entity");
    assert!(!kb.by_sort(entity_sort).is_empty(), "should have Entity fact");

    let op_sort = kb.make_name_term("Operation");
    assert!(!kb.by_sort(op_sort).is_empty(), "should have Operation fact");

    let fact_sort = kb.make_name_term("Fact");
    assert!(!kb.by_sort(fact_sort).is_empty(), "should have Fact fact");

    // Check sort relationship: dollars < Money
    let money_term = kb.resolve_qualified_name_term("banking.Money");
    let dollars_term = kb.resolve_qualified_name_term("banking.Money.dollars");
    assert!(kb.is_entity_of(dollars_term, money_term));
}

#[test]
fn load_workitem_and_query() {
    let source = r#"fact WorkItem(id: "WI-001", description: "Implement feature X", status: Open)
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Check the term has the expected structure: WorkItem(id: "WI-001", ...)
    let wi_sym = kb.intern("WorkItem");
    let workitems = kb.by_functor(wi_sym);
    assert_eq!(workitems.len(), 1, "should have one WorkItem");

    let fid = workitems[0];
    let tid = kb.fact_term(fid);
    match kb.get_term(tid) {
        Term::Fn { functor, named_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "WorkItem");
            assert!(!named_args.is_empty());
            let id_arg = named_args.iter()
                .find(|(k, _)| kb.resolve_sym(*k) == "id")
                .expect("missing 'id' arg");
            match kb.get_term(id_arg.1) {
                Term::Const(Literal::String(s)) => assert_eq!(s, "WI-001"),
                other => panic!("expected String const for id, got {:?}", other),
            }
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
  sort AccountId = ?
  sort Money = ?
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
    let account_term = kb.resolve_qualified_name_term("Account");
    for &fid in &ops {
        assert_eq!(
            kb.fact_domain(fid), account_term,
            "operation should be scoped to the Account sort"
        );
    }

    // Verify OperationInfo terms have "OperationInfo" functor and extract op names from "name" field
    let mut op_names: Vec<String> = Vec::new();
    for &fid in &ops {
        match kb.get_term(kb.fact_term(fid)) {
            Term::Fn { functor, named_args, .. } => {
                assert_eq!(kb.resolve_sym(*functor), "OperationInfo",
                    "operation facts should use OperationInfo functor");
                // Extract the "name" field (a Ref term)
                let name_entry = named_args.iter().find(|(sym, _)| kb.resolve_sym(*sym) == "name");
                assert!(name_entry.is_some(), "OperationInfo should have 'name' field");
                let (_, name_tid) = name_entry.unwrap();
                match kb.get_term(*name_tid) {
                    Term::Ref(sym) => op_names.push(kb.resolve_sym(*sym).to_owned()),
                    other => panic!("expected Ref for name, got {:?}", other),
                }
            }
            other => panic!("expected Fn term for operation, got {:?}", other),
        }
    }
    assert!(op_names.contains(&"deposit".to_owned()), "should have deposit operation");
    assert!(op_names.contains(&"withdraw".to_owned()), "should have withdraw operation");

    // The sort itself should be Defined (has entities) with constructors as entity children
    assert_eq!(kb.sort_kind(account_term), Some(SortKind::Defined));

    let checking_term = kb.resolve_qualified_name_term("Account.checking");
    assert!(kb.is_entity_of(checking_term, account_term),
        "checking should be entity of Account");
    assert_eq!(kb.sort_kind(checking_term), Some(SortKind::Constructor));
}

#[test]
fn load_operation_with_effects() {
    let source = r#"sort Error { sort T = ? entity Error(target: T) }
sort Modify { sort T = ? entity Modify(target: T) }
sort Store {
  entity store
  operation persist(s: Store, fact: Int) -> Int
    effects (Modify[store])
  operation retrieve(s: Store, pattern: Int) -> Int
    effects (Error[store])
  operation process(s: Store, x: Int) -> Int
    effects (Error[store], Modify[store])
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 3, "should have 3 operations");

    // Check each OperationInfo has effects stored as cons-list
    for &fid in &ops {
        let term = kb.get_term(kb.fact_term(fid));
        match term {
            Term::Fn { functor, named_args, .. } => {
                assert_eq!(kb.resolve_sym(*functor), "OperationInfo");
                // Extract operation name from "name" field
                let name_entry = named_args.iter().find(|(sym, _)| kb.resolve_sym(*sym) == "name");
                let name = match name_entry {
                    Some((_, tid)) => match kb.get_term(*tid) {
                        Term::Ref(sym) => kb.resolve_sym(*sym).to_owned(),
                        _ => "?".to_owned(),
                    },
                    None => "?".to_owned(),
                };
                // Find "effects" cons-list
                let effects_entry = named_args.iter().find(|(sym, _)| {
                    kb.resolve_sym(*sym) == "effects"
                });
                assert!(effects_entry.is_some(),
                    "operation '{}' should have 'effects' named arg", name);

                // Count elements in cons-list
                let (_, effects_list_tid) = effects_entry.unwrap();
                let count = count_list_elements(&kb, *effects_list_tid);
                let expected = match name.as_str() {
                    "persist" => 1,
                    "retrieve" => 1,
                    "process" => 2,
                    _ => panic!("unexpected operation: {}", name),
                };
                assert_eq!(count, expected,
                    "operation '{}' should have {} effect(s)", name, expected);
            }
            other => panic!("expected Fn term for operation, got {:?}", other),
        }
    }
}

#[test]
fn load_operation_with_abstract_effect() {
    let source = r#"sort MySort {
  sort E = ?
  operation doSomething(x: Int) -> Int
    effects (E)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 1, "should have 1 operation");

    // Abstract effect E should still be stored in effects list
    let term = kb.get_term(kb.fact_term(ops[0]));
    match term {
        Term::Fn { functor, named_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "OperationInfo");
            let effects_entry = named_args.iter().find(|(sym, _)| {
                kb.resolve_sym(*sym) == "effects"
            });
            assert!(effects_entry.is_some(),
                "OperationInfo should have 'effects' even for abstract effects");
            // Should have 1 effect element (abstract E)
            let (_, effects_list_tid) = effects_entry.unwrap();
            assert_eq!(count_list_elements(&kb, *effects_list_tid), 1,
                "should have 1 abstract effect");
        }
        other => panic!("expected Fn term, got {:?}", other),
    }
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
    let ctor_sym = kb.intern("Constructor");
    for &fid in &members {
        let term = kb.fact_term(fid);
        match kb.get_term(term) {
            Term::Fn { pos_args, .. } => {
                assert_eq!(pos_args.len(), 3);
                // Second arg should be Ident("Constructor")
                assert!(matches!(kb.get_term(pos_args[1]), Term::Ident(s) if *s == ctor_sym));
            }
            other => panic!("expected Fn term, got {:?}", other),
        }
    }
}

#[test]
fn member_facts_for_sort_with_params_and_ops() {
    let source = r#"sort Account
  sort AccountId = ?
  entity checking(id: AccountId, balance: Int)
  entity savings(id: AccountId, balance: Int)
  operation deposit(a: Account, m: Int) -> Account
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let member_sort = kb.make_name_term("Member");
    let account_term = kb.resolve_qualified_name_term("Account");

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
fn member_facts_for_namespace() {
    let source = r#"namespace banking {
  entity Account(id: String, balance: Int)
  operation deposit(a: Account, m: Int) -> Account
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let member_sort = kb.make_name_term("Member");
    let banking_term = kb.resolve_qualified_name_term("banking");

    let ns_facts = kb.by_domain(banking_term);
    let member_facts: Vec<_> = ns_facts
        .iter()
        .filter(|&&fid| kb.fact_sort(fid) == member_sort)
        .copied()
        .collect();

    // Should have: Account (Constructor), deposit (Operation)
    assert_eq!(member_facts.len(), 2,
        "banking namespace should have 2 member facts");
}

#[test]
fn member_facts_queryable_by_domain() {
    let source = r#"sort Option {
  sort T = ?
  entity none
  entity some(value: T)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let option_term = kb.resolve_qualified_name_term("Option");
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

// ── Requires declaration tests ──────────────────────────────────

#[test]
fn parse_sort_with_requires() {
    let source = r#"sort Ordered {
  sort T = ?
  requires Eq[T = T]
  operation gt(a: T, b: T) -> Bool
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "Ordered");
            // Items: AbstractSort(T), RequiresDecl(Eq[T=T]), Operation(gt)
            assert_eq!(s.items.len(), 3);
            match &s.items[1] {
                Item::RequiresDecl(r) => {
                    match &r.type_expr {
                        TypeExpr::Parameterized { name, bindings } => {
                            assert_eq!(parsed.symbols.name(name.last()), "Eq");
                            assert_eq!(bindings.len(), 1);
                            // Named binding: Eq[T = T]
                            let p = bindings[0].param.as_ref().expect("named binding should have param");
                            assert_eq!(parsed.symbols.name(p.last()), "T");
                            match &bindings[0].bound {
                                TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "T"),
                                other => panic!("expected Simple bound, got {:?}", other),
                            }
                        }
                        other => panic!("expected Parameterized type, got {:?}", other),
                    }
                }
                other => panic!("expected RequiresDecl, got {:?}", std::mem::discriminant(other)),
            }
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_sort_with_requires() {
    let source = r#"sort Eq {
  sort T = ?
}

sort Ordered {
  sort T = ?
  requires Eq[T = T]
  operation gt(a: T, b: T) -> Bool
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Check that a Requirement fact exists
    let req_sort = kb.make_name_term("Requirement");
    let reqs = kb.by_sort(req_sort);
    assert_eq!(reqs.len(), 1, "should have 1 Requirement fact");

    // The requirement should be scoped to the Ordered sort
    let ordered_term = kb.resolve_qualified_name_term("Ordered");
    assert_eq!(
        kb.fact_domain(reqs[0]), ordered_term,
        "requirement should be scoped to the Ordered sort"
    );

    // The requirement term should be Requires(sort_ref: Ordered_ref, spec: SortView(Eq(), T=T()))
    let fid = reqs[0];
    let tid = kb.fact_term(fid);
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, named_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "SortRequiresInfo");
            assert_eq!(pos_args.len(), 0, "SortRequiresInfo should use named args, not positional");
            assert_eq!(named_args.len(), 2, "SortRequiresInfo should have 2 named args: sort_ref, spec");
        }
        other => panic!("expected Fn term for Requirement, got {:?}", other),
    }
}

#[test]
fn parse_requires_positional_binding() {
    // `Eq[T]` is a positional binding — T binds to Eq's first param
    let source = r#"sort Ordered {
  sort T = ?
  requires Eq[T]
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            match &s.items[1] {
                Item::RequiresDecl(r) => {
                    match &r.type_expr {
                        TypeExpr::Parameterized { name, bindings } => {
                            assert_eq!(parsed.symbols.name(name.last()), "Eq");
                            assert_eq!(bindings.len(), 1);
                            let b = &bindings[0];
                            // Positional binding: param is None, bound is Simple("T")
                            assert!(b.param.is_none());
                            match &b.bound {
                                TypeExpr::Simple(bound_name) => {
                                    assert_eq!(parsed.symbols.name(bound_name.last()), "T");
                                }
                                other => panic!("expected Simple type, got {:?}", other),
                            }
                        }
                        other => panic!("expected Parameterized type, got {:?}", other),
                    }
                }
                other => panic!("expected RequiresDecl, got {:?}", std::mem::discriminant(other)),
            }
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Mutual reference tests ──────────────────────────────────────

fn check_term_contains(kb: &KnowledgeBase, term: TermId, target: TermId, found: &mut bool) {
    if term == target {
        *found = true;
        return;
    }
    if let Term::Fn { pos_args, named_args, .. } = kb.get_term(term) {
        for &id in pos_args.iter() {
            check_term_contains(kb, id, target, found);
        }
        for &(_, id) in named_args.iter() {
            check_term_contains(kb, id, target, found);
        }
    }
}

#[test]
fn mutual_reference_two_namespaces() {
    // File 1: namespace X references sort from namespace Y (via import)
    let file_x = r#"namespace Geometry
  import Units
  sort Shape {
    entity circle(radius: Int)
    entity rect(w: Int, h: Int)
  }
  operation area(s: Shape) -> Measure
end
"#;
    // File 2: namespace Y references sort from namespace X (via import)
    let file_y = r#"namespace Units
  import Geometry
  sort Measure {
    entity meters(n: Int)
    entity pixels(n: Int)
  }
  operation convert(m: Measure, target: Shape) -> Measure
end
"#;

    let parsed_x = parse::parse(file_x).expect("parse Geometry");
    let parsed_y = parse::parse(file_y).expect("parse Units");

    // Load both files into the same KB — order shouldn't matter for basic loading
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load_all(&mut kb, &[&parsed_x, &parsed_y], &NullResolver)
        .expect("load_all failed");

    // Both namespaces should be registered
    let ns_sort = kb.make_name_term("Namespace");
    let namespaces = kb.by_sort(ns_sort);
    assert_eq!(namespaces.len(), 2, "should have 2 namespaces");

    // Geometry's facts should reference Measure (from Units)
    let geometry_term = kb.resolve_qualified_name_term("Geometry");
    let geometry_facts = kb.by_domain(geometry_term);
    assert!(!geometry_facts.is_empty(), "Geometry should have facts");

    // Units' facts should reference Shape (from Geometry)
    let units_term = kb.resolve_qualified_name_term("Units");
    let units_facts = kb.by_domain(units_term);
    assert!(!units_facts.is_empty(), "Units should have facts");

    // Both sorts should exist as type references in operations
    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 2, "should have 2 operations (area, convert)");

    // Cross-namespace type references resolved via imports
    let measure_term = kb.resolve_qualified_name_term("Units.Measure");
    let shape_term = kb.resolve_qualified_name_term("Geometry.Shape");

    // area operation is in Geometry namespace but references Measure
    let mut area_refs_measure = false;
    for &fid in &geometry_facts {
        let term = kb.fact_term(fid);
        check_term_contains(&kb, term, measure_term, &mut area_refs_measure);
    }
    assert!(area_refs_measure, "Geometry's area should reference Measure");

    // convert operation is in Units namespace but references Shape
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
    let a1 = kb1.resolve_qualified_name_term("A");
    let mka1 = kb1.resolve_qualified_name_term("A.mkA");
    assert!(kb1.is_entity_of(mka1, a1));

    let a2 = kb2.resolve_qualified_name_term("A");
    let mka2 = kb2.resolve_qualified_name_term("A.mkA");
    assert!(kb2.is_entity_of(mka2, a2));
}

// ── Standard library parse tests ────────────────────────────────
//
// These tests discover .anthill files from the stdlib/ directory
// at runtime, so adding new files automatically includes them
// without test changes.

#[test]
fn stdlib_parse_all_files() {
    let dir = stdlib_dir();
    let files = collect_anthill_files(&dir);
    assert!(!files.is_empty(), "no .anthill files found in {}", dir.display());

    let mut failed = Vec::new();
    for path in &files {
        let source = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let rel = path.strip_prefix(&dir).unwrap_or(path);
        match parse::parse(&source) {
            Ok(parsed) => {
                assert!(!parsed.items.is_empty(),
                    "{}: parsed OK but produced no items", rel.display());
            }
            Err(errors) => {
                failed.push(format!("{}: {} error(s): {:?}",
                    rel.display(), errors.len(), errors));
            }
        }
    }

    assert!(failed.is_empty(),
        "stdlib files failed to parse:\n  {}", failed.join("\n  "));
}

#[test]
fn stdlib_load_all_into_kb() {
    let dir = stdlib_dir();
    let files = collect_anthill_files(&dir);
    assert!(!files.is_empty());

    let parsed: Vec<_> = files.iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()))
        })
        .collect();

    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    let load_result = load::load_all(&mut kb, &refs, &NullResolver);

    assert!(kb.fact_count() > 0,
        "KB should contain facts after loading {} stdlib files", files.len());

    if let Err(ref errors) = load_result {
        // Print diagnostics before asserting so they're visible on failure
        let mut unresolved: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        for e in errors {
            if let load::LoadError::UnresolvedName { name, scope_name, .. } = e {
                *unresolved.entry(format!("{name} (in {scope_name})")).or_default() += 1;
            }
        }
        eprintln!("stdlib load: {} errors from {} files:", errors.len(), files.len());
        for (key, count) in &unresolved {
            eprintln!("  {key}: {count}x");
        }
    }
    assert!(load_result.is_ok(),
        "stdlib should load with 0 errors, got {}",
        load_result.as_ref().err().map_or(0, |e| e.len()));
}

#[test]
fn nested_namespace_sees_outer_imports() {
    // A nested `namespace Inner` should see names imported at the
    // enclosing namespace level (List, String, Bool) as well as
    // names defined there (Path).
    let dir = common::testcases_dir().join("nested-namespace-imports");
    let files = common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "expected test files in {}", dir.display());

    // Also load stdlib prelude so that List, String, Bool are available
    let stdlib_dir = common::stdlib_dir();
    let mut all_files = common::collect_anthill_files(&stdlib_dir);
    all_files.extend(files);

    let parsed: Vec<_> = all_files.iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()))
        })
        .collect();

    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    let load_result = load::load_all(&mut kb, &refs, &NullResolver);

    if let Err(ref errors) = load_result {
        for e in errors {
            eprintln!("  error: {e}");
        }
    }
    assert!(load_result.is_ok(),
        "nested namespace should resolve outer imports, got {} errors",
        load_result.as_ref().err().map_or(0, |e| e.len()));
}

#[test]
fn stdlib_import_kinds() {
    // Selective import
    let source = r#"namespace test
  import anthill.prelude.{Option, Nat}
  entity Foo(x: String)
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Namespace(n) => {
            assert_eq!(n.imports.len(), 1);
            match &n.imports[0].kind {
                ImportKind::Selective(names) => assert_eq!(names.len(), 2),
                other => panic!("expected Selective, got {other:?}"),
            }
        }
        _ => panic!("expected Namespace"),
    }

    // Wildcard import
    let source = "namespace test\n  import anthill.prelude.*\n  entity Foo(x: String)\nend\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Namespace(n) => {
            assert_eq!(n.imports.len(), 1);
            assert!(matches!(n.imports[0].kind, ImportKind::Wildcard));
            assert_eq!(n.imports[0].path.segments.len(), 2);
        }
        _ => panic!("expected Namespace"),
    }

    // Plain import
    let source = "namespace test\n  import anthill.prelude.List\n  entity Foo(x: String)\nend\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Namespace(n) => {
            assert_eq!(n.imports.len(), 1);
            assert!(matches!(n.imports[0].kind, ImportKind::Plain));
            assert_eq!(n.imports[0].path.segments.len(), 3);
        }
        _ => panic!("expected Namespace"),
    }
}

// ── Describe declaration tests ──────────────────────────────────

#[test]
fn parse_describe_declaration() {
    let source = "describe Account {< A bank account holding funds >}\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Describe(d) => {
            assert_eq!(parsed.symbols.name(d.target.last()), "Account");
            assert_eq!(d.contents, vec!["A bank account holding funds"]);
        }
        other => panic!("expected Describe, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_abstract_sort_with_description() {
    let source = "sort Money = ? {< Monetary amount >}\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::AbstractSort(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "Money");
            assert!(matches!(s.definition, TypeExpr::Variable { .. }));
            assert_eq!(s.descriptions, vec!["Monetary amount"]);
        }
        other => panic!("expected AbstractSort, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_describe_emits_desc_fact() {
    let source = r#"namespace banking {
  sort Account = ?
  describe Account {< A bank account holding funds >}
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let desc_sort = kb.make_name_term("Description");
    let descs = kb.by_sort(desc_sort);
    assert_eq!(descs.len(), 1, "should have 1 Description fact");

    // Verify the Desc fact structure: Desc(target, text, index)
    let fid = descs[0];
    let tid = kb.fact_term(fid);
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "Description");
            assert_eq!(pos_args.len(), 3);
            // Second arg should be the description text
            match kb.get_term(pos_args[1]) {
                Term::Const(Literal::String(s)) => {
                    assert_eq!(s, "A bank account holding funds");
                }
                other => panic!("expected String constant, got {:?}", other),
            }
            // Third arg should be the index (0)
            match kb.get_term(pos_args[2]) {
                Term::Const(Literal::Int(i)) => {
                    assert_eq!(*i, 0);
                }
                other => panic!("expected Int constant for index, got {:?}", other),
            }
        }
        other => panic!("expected Fn term for Description, got {:?}", other),
    }
}

#[test]
fn load_abstract_sort_description_emits_desc_fact() {
    let source = "sort Money = ? {< Monetary amount >}\n";
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let desc_sort = kb.make_name_term("Description");
    let descs = kb.by_sort(desc_sort);
    assert_eq!(descs.len(), 1, "should have 1 Description fact from inline description");

    let fid = descs[0];
    let tid = kb.fact_term(fid);
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "Description");
            assert_eq!(pos_args.len(), 3);
            match kb.get_term(pos_args[1]) {
                Term::Const(Literal::String(s)) => {
                    assert_eq!(s, "Monetary amount");
                }
                other => panic!("expected String constant, got {:?}", other),
            }
        }
        other => panic!("expected Fn term for Description, got {:?}", other),
    }
}

// ── Variable with inline description tests ──────────────────────

#[test]
fn parse_variable_with_description() {
    let source = "rule test: foo(?x {< the x value >})\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Rule(r) => {
            // Head should be a fn_term foo(?x)
            match &r.head {
                RuleHead::Term(tid) => {
                    match parsed.terms.get(*tid) {
                        Term::Fn { functor, pos_args, .. } => {
                            assert_eq!(parsed.symbols.name(*functor), "foo");
                            assert_eq!(pos_args.len(), 1);
                            // The variable term should have a description
                            assert!(parsed.terms.descriptions.contains_key(&pos_args[0]),
                                "variable should have a description entry");
                            assert_eq!(parsed.terms.descriptions[&pos_args[0]], vec!["the x value"]);
                        }
                        other => panic!("expected Fn term, got {:?}", other),
                    }
                }
                other => panic!("expected Term head, got {:?}", other),
            }
        }
        other => panic!("expected Rule, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_variable_description_emits_fact() {
    let source = "rule test: foo(?x {< the x value >})\n";
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let desc_sort = kb.make_name_term("Description");
    let descs = kb.by_sort(desc_sort);
    assert_eq!(descs.len(), 1, "should have 1 Description fact from variable annotation");

    let fid = descs[0];
    let tid = kb.fact_term(fid);
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "Description");
            assert_eq!(pos_args.len(), 3);
            match kb.get_term(pos_args[1]) {
                Term::Const(Literal::String(s)) => {
                    assert_eq!(s, "the x value");
                }
                other => panic!("expected String constant, got {:?}", other),
            }
        }
        other => panic!("expected Fn term for Description, got {:?}", other),
    }
}

// ── Multiple description blocks ──────────────────────────────────

#[test]
fn parse_describe_multiple_blocks() {
    let source = "describe Account {< A bank account >} {< Holds funds >}\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Describe(d) => {
            assert_eq!(parsed.symbols.name(d.target.last()), "Account");
            assert_eq!(d.contents, vec!["A bank account", "Holds funds"]);
        }
        other => panic!("expected Describe, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_abstract_sort_multiple_descriptions() {
    let source = "sort Money = ? {< Monetary amount >} {< Used in banking >}\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::AbstractSort(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "Money");
            assert_eq!(s.descriptions, vec!["Monetary amount", "Used in banking"]);
        }
        other => panic!("expected AbstractSort, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_sort_with_body_descriptions() {
    let source = r#"{< Tracks work progress >}
sort WorkStatus {
  entity Draft
  entity Open
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "WorkStatus");
            assert_eq!(s.descriptions, vec!["Tracks work progress"]);
            assert_eq!(s.items.len(), 2);
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_describe_multiple_blocks_emits_facts() {
    let source = r#"namespace banking {
  sort Account = ?
  describe Account {< A bank account >} {< Holds funds >}
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let desc_sort = kb.make_name_term("Description");
    let descs = kb.by_sort(desc_sort);
    assert_eq!(descs.len(), 2, "should have 2 Description facts from multi-block describe");

    // Collect description texts
    let mut texts: Vec<String> = descs.iter().map(|fid| {
        let tid = kb.fact_term(*fid);
        match kb.get_term(tid) {
            Term::Fn { pos_args, .. } => {
                match kb.get_term(pos_args[1]) {
                    Term::Const(Literal::String(s)) => s.clone(),
                    other => panic!("expected String, got {:?}", other),
                }
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }).collect();
    texts.sort();
    assert_eq!(texts, vec!["A bank account", "Holds funds"]);
}

#[test]
fn load_abstract_sort_multiple_descriptions_emits_facts() {
    let source = "sort Money = ? {< Monetary amount >} {< Used in banking >}\n";
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let desc_sort = kb.make_name_term("Description");
    let descs = kb.by_sort(desc_sort);
    assert_eq!(descs.len(), 2, "should have 2 Description facts from multi-description abstract sort");
}

#[test]
fn load_sort_with_body_description_emits_fact() {
    let source = r#"{< Tracks work progress >}
sort WorkStatus {
  entity Draft
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let desc_sort = kb.make_name_term("Description");
    let descs = kb.by_sort(desc_sort);
    assert_eq!(descs.len(), 1, "should have 1 Description fact from sort_with_body");

    let fid = descs[0];
    let tid = kb.fact_term(fid);
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "Description");
            match kb.get_term(pos_args[1]) {
                Term::Const(Literal::String(s)) => {
                    assert_eq!(s, "Tracks work progress");
                }
                other => panic!("expected String, got {:?}", other),
            }
        }
        other => panic!("expected Fn, got {:?}", other),
    }
}

#[test]
fn parse_variable_multiple_descriptions() {
    let source = "rule test: foo(?x {< first >} {< second >})\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Rule(r) => {
            match &r.head {
                RuleHead::Term(tid) => {
                    match parsed.terms.get(*tid) {
                        Term::Fn { pos_args, .. } => {
                            let descs = &parsed.terms.descriptions[&pos_args[0]];
                            assert_eq!(descs, &vec!["first", "second"]);
                        }
                        other => panic!("expected Fn, got {:?}", other),
                    }
                }
                other => panic!("expected Term head, got {:?}", other),
            }
        }
        other => panic!("expected Rule, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Variable types in type positions ─────────────────────────────

#[test]
fn parse_operation_with_variable_types() {
    let source = "operation identity(x: ?T) -> ?T\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Operation(o) => {
            assert_eq!(parsed.symbols.name(o.name.last()), "identity");
            assert_eq!(o.params.len(), 1);
            match &o.params[0].ty {
                TypeExpr::Variable { term_id, descriptions } => {
                    assert!(descriptions.is_empty());
                    // Verify it's a named variable (not anonymous)
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => {
                            assert_eq!(parsed.symbols.name(vid.name()), "T");
                        }
                        other => panic!("expected Var, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type, got {:?}", other),
            }
            match &o.return_type {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => {
                            assert_eq!(parsed.symbols.name(vid.name()), "T");
                        }
                        other => panic!("expected Var, got {:?}", other),
                    }
                }
                other => panic!("expected Variable return type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn variable_types_share_scope_in_operation() {
    // ?X in param and return type should share the same VarId
    let source = "operation id(x: ?X) -> ?X\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            let param_tid = match &o.params[0].ty {
                TypeExpr::Variable { term_id, .. } => *term_id,
                _ => panic!("expected Variable"),
            };
            let ret_tid = match &o.return_type {
                TypeExpr::Variable { term_id, .. } => *term_id,
                _ => panic!("expected Variable"),
            };
            // Both should be the same variable (same VarId)
            let param_var = match parsed.terms.get(param_tid) {
                Term::Var(vid) => vid.raw(),
                _ => panic!("expected Var"),
            };
            let ret_var = match parsed.terms.get(ret_tid) {
                Term::Var(vid) => vid.raw(),
                _ => panic!("expected Var"),
            };
            assert_eq!(param_var, ret_var,
                "?X should share identity across param and return type");
        }
        _ => panic!("expected Operation"),
    }
}

#[test]
fn parse_entity_with_variable_field_types() {
    let source = "entity Pair(fst: ?A, snd: ?B)\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Entity(e) => {
            assert_eq!(parsed.symbols.name(e.name.last()), "Pair");
            assert_eq!(e.fields.len(), 2);
            assert!(matches!(e.fields[0].ty, TypeExpr::Variable { .. }));
            assert!(matches!(e.fields[1].ty, TypeExpr::Variable { .. }));
        }
        other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_operation_with_variable_types() {
    let source = r#"sort Funcs {
  operation identity(x: ?T) -> ?T
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 1, "should have 1 Operation fact");
}

// ── Unresolved import / name hard error tests ──────────────────

#[test]
fn unresolved_import_plain_is_hard_error() {
    let source = r#"namespace test
  import nonexistent.path.Foo
  entity Bar(x: String)
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    let result = load::load(&mut kb, &parsed, &NullResolver);
    let errors = result.expect_err("expected load errors for unresolved import");

    let import_errors: Vec<_> = errors.iter().filter(|e| {
        matches!(e, load::LoadError::UnresolvedImport { path, .. } if path == "nonexistent.path.Foo")
    }).collect();
    assert!(!import_errors.is_empty(),
        "should report UnresolvedImport for 'nonexistent.path.Foo', got: {:?}", errors);
}

#[test]
fn unresolved_import_wildcard_is_hard_error() {
    let source = r#"namespace test
  import nonexistent.path.*
  entity Bar(x: String)
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    let result = load::load(&mut kb, &parsed, &NullResolver);
    let errors = result.expect_err("expected load errors for unresolved wildcard import");

    let import_errors: Vec<_> = errors.iter().filter(|e| {
        matches!(e, load::LoadError::UnresolvedImport { path, .. } if path == "nonexistent.path")
    }).collect();
    assert!(!import_errors.is_empty(),
        "should report UnresolvedImport for 'nonexistent.path', got: {:?}", errors);
}

#[test]
fn unresolved_import_selective_is_hard_error() {
    let source = r#"namespace test
  import nonexistent.path.{Foo, Bar}
  entity Baz(x: String)
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    let result = load::load(&mut kb, &parsed, &NullResolver);
    let errors = result.expect_err("expected load errors for unresolved selective import");

    let import_errors: Vec<_> = errors.iter().filter(|e| {
        matches!(e, load::LoadError::UnresolvedImport { .. })
    }).collect();
    assert!(!import_errors.is_empty(),
        "should report UnresolvedImport errors, got: {:?}", errors);
}

#[test]
fn unresolved_name_is_hard_error() {
    let source = r#"sort Foo {
  operation bar(x: Nonexistent) -> Nonexistent
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    let result = load::load(&mut kb, &parsed, &NullResolver);
    let errors = result.expect_err("expected load errors for unresolved type");

    // Should have UnresolvedName errors for "Nonexistent"
    let unresolved: Vec<_> = errors.iter().filter(|e| {
        matches!(e, load::LoadError::UnresolvedName { name, .. } if name == "Nonexistent")
    }).collect();
    assert!(!unresolved.is_empty(),
        "should report UnresolvedName for 'Nonexistent', got: {:?}", errors);

    // Verify span is non-default (the name has a real source location)
    for err in &unresolved {
        if let load::LoadError::UnresolvedName { span, .. } = err {
            assert!(span.end > span.start,
                "span should be non-empty for unresolved name");
        }
    }
}

#[test]
fn all_names_resolved_no_errors() {
    let source = r#"sort Eq {
  sort T = ?
}

sort Ordered {
  sort T = ?
  requires Eq[T = T]
  operation compare(a: T, b: T) -> Int
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("load should succeed with all names resolved");
}

#[test]
fn namespace_scoped_sorts_resolve() {
    // Sorts defined inside a namespace should be visible to siblings
    // via the enclosing scope (no explicit import needed).
    let source = r#"namespace A {
  sort B = ?
  sort C {
    requires B
    operation use_b(x: B) -> B
  }
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("load should succeed: B is visible from C via namespace A");

    // Verify requirement is registered
    let req_sort = kb.make_name_term("Requirement");
    let reqs = kb.by_sort(req_sort);
    assert_eq!(reqs.len(), 1, "should have 1 Requirement (B) for C");
}

// ── Circular requires tests ─────────────────────────────────────

#[test]
fn circular_requires_does_not_panic() {
    let source = r#"
sort A {
  sort T = ?
  requires B[T]
  operation use_b(x: T) -> T
}

sort B {
  sort T = ?
  requires A[T]
  operation use_a(x: T) -> T
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("circular requires should not panic");

    // Both sorts should exist
    let a_term = kb.resolve_qualified_name_term("A");
    let b_term = kb.resolve_qualified_name_term("B");
    assert_ne!(a_term, b_term, "A and B should be distinct sorts");

    // Both should have requirements
    let req_sort = kb.make_name_term("Requirement");
    let reqs = kb.by_sort(req_sort);
    assert_eq!(reqs.len(), 2, "should have 2 requirements (A requires B, B requires A)");
}

// ── Multi-file namespace dedup tests ────────────────────────────

#[test]
fn multi_file_same_namespace_resolution() {
    // Two files both declare `namespace ns`.  Namespace dedup merges them
    // into a single scope so sorts from one file are visible in the other.
    let file1 = r#"namespace ns {
  sort A = ?
}
"#;
    let file2 = r#"namespace ns {
  sort B {
    operation use_a(x: A) -> A
  }
}
"#;

    let parsed1 = parse::parse(file1).expect("parse file1");
    let parsed2 = parse::parse(file2).expect("parse file2");

    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &[&parsed1, &parsed2], &NullResolver)
        .expect("load should succeed: A is visible from B via shared namespace ns");

    // Both sorts should be registered
    let sort_sort = kb.make_name_term("Sort");
    let sorts = kb.by_sort(sort_sort);
    assert!(sorts.len() >= 2, "should have at least 2 sorts (A, B)");

    // The operation in B should reference A
    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 1, "should have 1 operation (use_a)");
}

#[test]
fn multi_file_same_namespace_no_duplicate_facts() {
    let file1 = "namespace ns {\n  sort A = ?\n}\n";
    let file2 = "namespace ns {\n  sort B = ?\n}\n";

    let parsed1 = parse::parse(file1).expect("parse file1");
    let parsed2 = parse::parse(file2).expect("parse file2");

    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &[&parsed1, &parsed2], &NullResolver)
        .expect("load failed");

    let ns_sort = kb.make_name_term("Namespace");
    let ns_facts = kb.by_sort(ns_sort);
    // Two files both declare `namespace ns` — should produce 1 Namespace fact, not 2
    let ns_count = ns_facts.iter().filter(|&&fid| {
        if let Term::Fn { functor, .. } = kb.get_term(kb.fact_term(fid)) {
            kb.resolve_sym(*functor) == "ns"
        } else {
            false
        }
    }).count();
    assert_eq!(ns_count, 1, "namespace ns should have exactly 1 Namespace fact, got {}", ns_count);
}

// ── Dotted name intermediate namespace tests ────────────────────

#[test]
fn dotted_name_creates_intermediate_namespaces() {
    // `sort a.b.C` should create implicit namespaces `a` and `a.b`,
    // and define `C` (short name) in the `a.b` scope.
    let source = r#"sort a.b.C {
  entity mkC
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Check that `a` and `a.b` are registered as Namespace symbols
    assert!(kb.has_qualified_name("a"),
        "implicit namespace 'a' should exist");
    assert!(kb.has_qualified_name("a.b"),
        "implicit namespace 'a.b' should exist");

    // Check that `C` is findable by qualified name
    assert!(kb.has_qualified_name("a.b.C"),
        "sort 'a.b.C' should be registered by qualified name");

    // Check that `C` has short_name "C" (not "a.b.C")
    assert_eq!(kb.qualified_short_name("a.b.C"), Some("C"),
        "sort should have short name 'C'");

    // `C` should be a registered sort with constructor `mkC`
    let c_term = kb.resolve_qualified_name_term("a.b.C");
    assert_eq!(kb.sort_kind(c_term), Some(SortKind::Defined));

    // Entity `mkC` inside sort `a.b.C` gets fully-qualified name
    assert!(kb.has_qualified_name("a.b.C.mkC"),
        "entity mkC inside sort a.b.C should have qualified name 'a.b.C.mkC'");
}

#[test]
fn dotted_siblings_share_scope() {
    // Two dotted names with the same prefix should share the implicit
    // intermediate namespace, making sibling sorts visible to each other.
    let file1 = r#"sort ns.A"#;
    let file2 = r#"sort ns.B {
  operation use_a(x: A) -> A
}
"#;

    let parsed1 = parse::parse(file1).expect("parse file1");
    let parsed2 = parse::parse(file2).expect("parse file2");

    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &[&parsed1, &parsed2], &NullResolver)
        .expect("load should succeed: A and B are siblings in implicit 'ns' scope");

    // Both sorts should be registered
    let sort_sort = kb.make_name_term("Sort");
    let sorts = kb.by_sort(sort_sort);
    assert!(sorts.len() >= 2, "should have at least 2 sorts (A, B)");

    // The operation in B should reference A (resolved via shared ns scope)
    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 1, "should have 1 operation (use_a)");
}

#[test]
fn dotted_namespace_creates_hierarchy() {
    // `namespace a.b.c` should create implicit namespaces `a` and `a.b`.
    let source = r#"namespace a.b.c {
  sort X = ?
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    assert!(kb.has_qualified_name("a"),
        "implicit namespace 'a' should exist");
    assert!(kb.has_qualified_name("a.b"),
        "implicit namespace 'a.b' should exist");
    assert!(kb.has_qualified_name("a.b.c"),
        "explicit namespace 'a.b.c' should exist");

    // X should be defined in the `a.b.c` scope with fully-qualified name
    assert!(kb.has_qualified_name("a.b.c.X"), "sort X should be registered as 'a.b.c.X'");
}

#[test]
fn implicit_and_explicit_namespace_merge() {
    // An implicit namespace from a dotted name and an explicit namespace
    // declaration should merge into the same scope.
    let file1 = r#"sort ns.A"#;
    let file2 = r#"namespace ns {
  sort B {
    operation use_a(x: A) -> A
  }
}
"#;

    let parsed1 = parse::parse(file1).expect("parse file1");
    let parsed2 = parse::parse(file2).expect("parse file2");

    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &[&parsed1, &parsed2], &NullResolver)
        .expect("load should succeed: implicit and explicit 'ns' merge");

    // Both A (from dotted name) and B (from explicit namespace) should exist
    // B is inside namespace ns, so its fully-qualified name is "ns.B"
    assert!(kb.has_qualified_name("ns.A"));
    assert!(kb.has_qualified_name("ns.B"));

    // The operation in B should resolve A via the shared namespace scope
    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    assert_eq!(ops.len(), 1, "should have 1 operation (use_a)");
}

// ── Fully-qualified name tests ──────────────────────────────────

#[test]
fn nested_items_have_qualified_names() {
    // Items defined inside a sort body get fully-qualified names:
    // operation `eq` inside `sort Eq` → qualified_name = "Eq.eq"
    let source = r#"sort Eq {
  sort T = ?
  operation eq(a: T, b: T) -> Bool
  operation neq(a: T, b: T) -> Bool
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Sort Eq at top level
    assert!(kb.has_qualified_name("Eq"),
        "sort Eq should be registered");
    // Type param T inside Eq
    assert!(kb.has_qualified_name("Eq.T"),
        "type param T should have qualified name 'Eq.T'");
    // Operations inside Eq
    assert!(kb.has_qualified_name("Eq.eq"),
        "operation eq should have qualified name 'Eq.eq'");
    assert!(kb.has_qualified_name("Eq.neq"),
        "operation neq should have qualified name 'Eq.neq'");
}

#[test]
fn nested_items_in_dotted_sort_have_qualified_names() {
    // Items inside a dotted sort: `sort anthill.prelude.Eq { operation eq ... }`
    // → qualified_name = "anthill.prelude.Eq.eq"
    let source = r#"sort anthill.prelude.Eq {
  sort T = ?
  operation eq(a: T, b: T) -> Bool
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    assert!(kb.has_qualified_name("anthill.prelude.Eq"),
        "sort should have qualified name 'anthill.prelude.Eq'");
    assert!(kb.has_qualified_name("anthill.prelude.Eq.T"),
        "type param should have qualified name 'anthill.prelude.Eq.T'");
    assert!(kb.has_qualified_name("anthill.prelude.Eq.eq"),
        "operation should have qualified name 'anthill.prelude.Eq.eq'");
}

#[test]
fn nested_items_in_namespace_have_qualified_names() {
    // Entities and sorts inside a namespace get fully-qualified names.
    let source = r#"namespace anthill.reflect {
  sort Term {
    entity Const(value: Int)
    entity Fn(functor: String)
  }
  sort SortInfo = ?
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    assert!(kb.has_qualified_name("anthill.reflect"),
        "namespace should have qualified name 'anthill.reflect'");
    assert!(kb.has_qualified_name("anthill.reflect.Term"),
        "sort Term should have qualified name 'anthill.reflect.Term'");
    assert!(kb.has_qualified_name("anthill.reflect.Term.Const"),
        "entity Const should have qualified name 'anthill.reflect.Term.Const'");
    assert!(kb.has_qualified_name("anthill.reflect.Term.Fn"),
        "entity Fn should have qualified name 'anthill.reflect.Term.Fn'");
    assert!(kb.has_qualified_name("anthill.reflect.SortInfo"),
        "sort SortInfo should have qualified name 'anthill.reflect.SortInfo'");
}

// ── Abstract sort variable preservation tests ────────────────────

#[test]
fn load_abstract_sort_variable_emits_sort_alias() {
    // sort T = ?Element should produce SortAlias(T, ?Element), not SortInfo(T, Abstract)
    let source = "sort T = ?Element\n";
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let sort_sort = kb.make_name_term("Sort");
    let facts = kb.by_sort(sort_sort);
    // Find the SortAlias fact
    let alias_facts: Vec<_> = facts.iter().filter(|fid| {
        let tid = kb.fact_term(**fid);
        matches!(kb.get_term(tid), Term::Fn { functor, .. } if kb.resolve_sym(*functor) == "SortAlias")
    }).collect();
    assert_eq!(alias_facts.len(), 1, "should have 1 SortAlias fact");

    let tid = kb.fact_term(*alias_facts[0]);
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "SortAlias");
            assert_eq!(pos_args.len(), 2);
            // Second arg should be a Var term (the logical variable ?Element)
            match kb.get_term(pos_args[1]) {
                Term::Var(vid) => {
                    assert_eq!(kb.resolve_sym(vid.name()), "Element");
                }
                other => panic!("expected Var term for ?Element, got {:?}", other),
            }
        }
        other => panic!("expected Fn term for SortAlias, got {:?}", other),
    }
}

#[test]
fn load_abstract_sort_anonymous_variable_emits_sort_alias() {
    // sort T = ? should also produce SortAlias with an anonymous Var
    let source = "sort T = ?\n";
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let sort_sort = kb.make_name_term("Sort");
    let facts = kb.by_sort(sort_sort);
    let alias_facts: Vec<_> = facts.iter().filter(|fid| {
        let tid = kb.fact_term(**fid);
        matches!(kb.get_term(tid), Term::Fn { functor, .. } if kb.resolve_sym(*functor) == "SortAlias")
    }).collect();
    assert_eq!(alias_facts.len(), 1, "should have 1 SortAlias fact for anonymous variable");

    let tid = kb.fact_term(*alias_facts[0]);
    match kb.get_term(tid) {
        Term::Fn { pos_args, .. } => {
            assert!(matches!(kb.get_term(pos_args[1]), Term::Var(_)),
                "target should be a Var term");
        }
        other => panic!("expected Fn term, got {:?}", other),
    }
}

#[test]
fn load_abstract_sort_shared_variables() {
    // sort A = ?X and sort B = ?X should share the same VarId in the KB
    let source = "sort A = ?X\nsort B = ?X\n";
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let sort_sort = kb.make_name_term("Sort");
    let facts = kb.by_sort(sort_sort);
    let alias_facts: Vec<_> = facts.iter().filter(|fid| {
        let tid = kb.fact_term(**fid);
        matches!(kb.get_term(tid), Term::Fn { functor, .. } if kb.resolve_sym(*functor) == "SortAlias")
    }).collect();
    assert_eq!(alias_facts.len(), 2, "should have 2 SortAlias facts");

    // Extract the VarIds from both SortAlias targets
    let var_ids: Vec<u32> = alias_facts.iter().map(|fid| {
        let tid = kb.fact_term(**fid);
        match kb.get_term(tid) {
            Term::Fn { pos_args, .. } => {
                match kb.get_term(pos_args[1]) {
                    Term::Var(vid) => vid.raw(),
                    other => panic!("expected Var, got {:?}", other),
                }
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }).collect();
    assert_eq!(var_ids[0], var_ids[1],
        "?X should share the same VarId across both sort definitions");
}

// ── Universal type variable tests ─────────────────────────────────

#[test]
fn parse_entity_with_anonymous_variable_fields() {
    // `entity Foo(x: ?, y: ?)` — each `?` should produce TypeExpr::Variable with distinct VarIds.
    let source = "entity Foo(x: ?, y: ?)\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Entity(e) => {
            assert_eq!(parsed.symbols.name(e.name.last()), "Foo");
            assert_eq!(e.fields.len(), 2);
            // Both fields should be TypeExpr::Variable
            let vid0 = match &e.fields[0].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => vid.raw(),
                        other => panic!("expected Var for field x, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field x, got {:?}", other),
            };
            let vid1 = match &e.fields[1].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => vid.raw(),
                        other => panic!("expected Var for field y, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field y, got {:?}", other),
            };
            assert_ne!(vid0, vid1, "anonymous ? fields should have distinct VarIds");
        }
        other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_entity_with_named_variable_fields_shared() {
    // `entity Pair(a: ?T, b: ?T)` — both `?T` should share the same VarId.
    let source = "entity Pair(a: ?T, b: ?T)\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Entity(e) => {
            assert_eq!(parsed.symbols.name(e.name.last()), "Pair");
            assert_eq!(e.fields.len(), 2);
            let vid0 = match &e.fields[0].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => {
                            assert_eq!(parsed.symbols.name(vid.name()), "T");
                            vid.raw()
                        }
                        other => panic!("expected Var for field a, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field a, got {:?}", other),
            };
            let vid1 = match &e.fields[1].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => {
                            assert_eq!(parsed.symbols.name(vid.name()), "T");
                            vid.raw()
                        }
                        other => panic!("expected Var for field b, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field b, got {:?}", other),
            };
            assert_eq!(vid0, vid1, "named ?T fields should share the same VarId");
        }
        other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_entity_with_distinct_named_variables() {
    // `entity Pair(a: ?A, b: ?B)` — different names should have distinct VarIds.
    let source = "entity Pair(a: ?A, b: ?B)\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Entity(e) => {
            assert_eq!(e.fields.len(), 2);
            let vid0 = match &e.fields[0].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => vid.raw(),
                        other => panic!("expected Var for field a, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field a, got {:?}", other),
            };
            let vid1 = match &e.fields[1].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(vid) => vid.raw(),
                        other => panic!("expected Var for field b, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field b, got {:?}", other),
            };
            assert_ne!(vid0, vid1, "?A and ?B should have distinct VarIds");
        }
        other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Operator tests (Proposal 016) ─────────────────────────────────

use anthill_core::parse::ir::SimpleTermStore;

/// Helper: parse a rule and return the parse-IR term for the head.
fn parse_rule_head_ir(expr: &str) -> (SimpleTermStore, anthill_core::intern::SymbolTable, TermId) {
    let source = format!("rule r: {expr}\n");
    let parsed = parse::parse(&source).expect("parse failed");
    // Extract the head term from the first rule item
    let head_tid = match &parsed.items[0] {
        Item::Rule(r) => match &r.head {
            anthill_core::parse::ir::RuleHead::Term(tid) => *tid,
            _ => panic!("expected rule head term"),
        },
        other => panic!("expected Rule, got {:?}", std::mem::discriminant(other)),
    };
    (parsed.terms, parsed.symbols, head_tid)
}

/// Recursively format a parse-IR term for test assertions.
fn fmt_ir_term(terms: &SimpleTermStore, symbols: &anthill_core::intern::SymbolTable, tid: TermId) -> String {
    match terms.get(tid) {
        Term::Var(vid) => format!("?{}", symbols.name(vid.name())),
        Term::Ident(sym) => symbols.name(*sym).to_string(),
        Term::Ref(sym) => symbols.name(*sym).to_string(),
        Term::Const(Literal::Int(n)) => format!("{n}"),
        Term::Const(Literal::String(s)) => format!("\"{s}\""),
        Term::Fn { functor, pos_args, named_args } => {
            let name = symbols.name(*functor);
            let mut parts: Vec<String> = pos_args.iter()
                .map(|&a| fmt_ir_term(terms, symbols, a))
                .collect();
            for (key, val) in named_args.iter() {
                let key_name = symbols.name(*key);
                let val_str = fmt_ir_term(terms, symbols, *val);
                parts.push(format!("{key_name}: {val_str}"));
            }
            format!("{name}({})", parts.join(", "))
        }
        other => format!("{other:?}"),
    }
}

#[test]
fn parse_multi_operator_chain() {
    // ?a + ?b * ?c → add(?a, mul(?b, ?c)): mul binds tighter than add
    let (terms, symbols, head) = parse_rule_head_ir("?a + ?b * ?c");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "add(?a, mul(?b, ?c))");
}

#[test]
fn parse_left_assoc_add() {
    // ?a + ?b + ?c → add(add(?a, ?b), ?c): left-associative
    let (terms, symbols, head) = parse_rule_head_ir("?a + ?b + ?c");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "add(add(?a, ?b), ?c)");
}

#[test]
fn parse_right_assoc_pow() {
    // ?a ^ ?b ^ ?c → pow(?a, pow(?b, ?c)): right-associative
    let (terms, symbols, head) = parse_rule_head_ir("?a ^ ?b ^ ?c");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "pow(?a, pow(?b, ?c))");
}

#[test]
fn parse_prefix_not() {
    // add(!?a, ?b) → add(not(?a), ?b)
    let (terms, symbols, head) = parse_rule_head_ir("add(!?a, ?b)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "add(not(?a), ?b)");
}

#[test]
fn parse_prefix_in_infix() {
    // !?a + ?b → add(not(?a), ?b): prefix binds tighter
    let (terms, symbols, head) = parse_rule_head_ir("!?a + ?b");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "add(not(?a), ?b)");
}

#[test]
fn parse_new_operators() {
    let (terms, symbols, head) = parse_rule_head_ir("?a | ?b");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "or(?a, ?b)");

    let (terms, symbols, head) = parse_rule_head_ir("?a != ?b");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "neq(?a, ?b)");
}

#[test]
fn parse_ternary_arrow_effect() {
    // ?a -> ?b @ ?c → arrow_effect(?a, ?b, ?c)
    let (terms, symbols, head) = parse_rule_head_ir("?a -> ?b @ ?c");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "arrow_effect(?a, ?b, ?c)");
}

#[test]
fn parse_binary_arrow() {
    // ?a -> ?b (no continuation) → arrow(?a, ?b)
    let (terms, symbols, head) = parse_rule_head_ir("?a -> ?b");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "arrow(?a, ?b)");
}

#[test]
fn parse_existing_infix_unchanged() {
    // Verify backward compatibility: single-operator expressions produce same output
    let (t, s, h) = parse_rule_head_ir("?a + ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "add(?a, ?b)");

    let (t, s, h) = parse_rule_head_ir("?a * ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "mul(?a, ?b)");

    let (t, s, h) = parse_rule_head_ir("?a = ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "eq(?a, ?b)");

    let (t, s, h) = parse_rule_head_ir("?a > ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "gt(?a, ?b)");

    let (t, s, h) = parse_rule_head_ir("?a >= ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "gte(?a, ?b)");

    let (t, s, h) = parse_rule_head_ir("?a < ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "lt(?a, ?b)");

    let (t, s, h) = parse_rule_head_ir("?a <= ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "lte(?a, ?b)");

    let (t, s, h) = parse_rule_head_ir("?a - ?b");
    assert_eq!(fmt_ir_term(&t, &s, h), "sub(?a, ?b)");
}

// ── Set literal tests ─────────────────────────────────────────

#[test]
fn parse_empty_set_literal() {
    // {} → SetLiteral()
    let (terms, symbols, head) = parse_rule_head_ir("{}");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "SetLiteral()");
}

#[test]
fn parse_single_element_set_literal() {
    // {?x} → SetLiteral(?x)
    let (terms, symbols, head) = parse_rule_head_ir("{?x}");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "SetLiteral(?x)");
}

#[test]
fn parse_multi_element_set_literal() {
    // {?a, ?b, ?c} → SetLiteral(?a, ?b, ?c)
    let (terms, symbols, head) = parse_rule_head_ir("{?a, ?b, ?c}");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "SetLiteral(?a, ?b, ?c)");
}

#[test]
fn parse_set_literal_with_integers() {
    // {1, 2, 3} → SetLiteral(1, 2, 3)
    let (terms, symbols, head) = parse_rule_head_ir("{1, 2, 3}");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "SetLiteral(1, 2, 3)");
}

// ── Tuple tests (Proposal 004) ─────────────────────────────────

#[test]
fn parse_unit_tuple() {
    // () → TupleLiteral()
    let (terms, symbols, head) = parse_rule_head_ir("()");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "TupleLiteral()");
}

#[test]
fn parse_positional_tuple() {
    // (1, 2) → TupleLiteral(_1: 1, _2: 2)
    let (terms, symbols, head) = parse_rule_head_ir("(1, 2)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "TupleLiteral(_1: 1, _2: 2)");
}

#[test]
fn parse_named_tuple() {
    // (x: 1, y: 2) → TupleLiteral(x: 1, y: 2)
    let (terms, symbols, head) = parse_rule_head_ir("(x: 1, y: 2)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "TupleLiteral(x: 1, y: 2)");
}

#[test]
fn parse_tuple_variables() {
    // (?a, ?b) → TupleLiteral(_1: ?a, _2: ?b)
    let (terms, symbols, head) = parse_rule_head_ir("(?a, ?b)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "TupleLiteral(_1: ?a, _2: ?b)");
}

#[test]
fn parse_tuple_type_in_operation() {
    let source = "operation foo() -> (Int, String)\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.return_type {
                TypeExpr::Tuple(fields) => {
                    assert_eq!(fields.len(), 2);
                    let name1 = parsed.symbols.name(fields[0].0);
                    let name2 = parsed.symbols.name(fields[1].0);
                    assert_eq!(name1, "_1");
                    assert_eq!(name2, "_2");
                }
                other => panic!("expected Tuple type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_named_tuple_type_in_operation() {
    let source = "operation bar() -> (name: String, age: Int)\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.return_type {
                TypeExpr::Tuple(fields) => {
                    assert_eq!(fields.len(), 2);
                    let name1 = parsed.symbols.name(fields[0].0);
                    let name2 = parsed.symbols.name(fields[1].0);
                    assert_eq!(name1, "name");
                    assert_eq!(name2, "age");
                }
                other => panic!("expected Tuple type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Collection literal tests (Proposal 019) ─────────────────

#[test]
fn parse_empty_collection_literal() {
    let (terms, symbols, head) = parse_rule_head_ir("[]");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "ListLiteral()");
}

#[test]
fn parse_single_element_collection_literal() {
    let (terms, symbols, head) = parse_rule_head_ir("[?x]");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "ListLiteral(?x)");
}

#[test]
fn parse_multi_element_collection_literal() {
    let (terms, symbols, head) = parse_rule_head_ir("[?a, ?b, ?c]");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "ListLiteral(?a, ?b, ?c)");
}

#[test]
fn parse_collection_literal_with_integers() {
    let (terms, symbols, head) = parse_rule_head_ir("[1, 2, 3]");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "ListLiteral(1, 2, 3)");
}

#[test]
fn parse_collection_head_tail() {
    let (terms, symbols, head) = parse_rule_head_ir("[?h | ?t]");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "ListLiteral(?h, tail: ?t)");
}

#[test]
fn parse_collection_multi_head_tail() {
    let (terms, symbols, head) = parse_rule_head_ir("[?a, ?b | ?t]");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "ListLiteral(?a, ?b, tail: ?t)");
}

// ── Field access tests ───────────────────────────────────────

#[test]
fn parse_field_access_variable() {
    // ?x.y → field_access(?x, y)
    let (terms, symbols, head) = parse_rule_head_ir("?x.y");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "field_access(?x, y)");
}

#[test]
fn parse_field_access_chained() {
    // ?x.y.z → field_access(field_access(?x, y), z)
    let (terms, symbols, head) = parse_rule_head_ir("?x.y.z");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "field_access(field_access(?x, y), z)");
}

#[test]
fn parse_field_access_in_fn_arg() {
    // f(?a.b, ?c) → f(field_access(?a, b), ?c)
    let (terms, symbols, head) = parse_rule_head_ir("f(?a.b, ?c)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "f(field_access(?a, b), ?c)");
}

#[test]
fn parse_field_access_in_infix() {
    // ?x.y = ?z → eq(field_access(?x, y), ?z)
    let (terms, symbols, head) = parse_rule_head_ir("?x.y = ?z");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "eq(field_access(?x, y), ?z)");
}

#[test]
fn parse_arrow_type_unary() {
    let source = "operation map(f: (A) -> B) -> C\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.params[0].ty {
                TypeExpr::Arrow { params, return_type, effect } => {
                    assert_eq!(params.len(), 1);
                    match &params[0] {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "A"),
                        other => panic!("expected Simple param, got {:?}", other),
                    }
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "B"),
                        other => panic!("expected Simple return, got {:?}", other),
                    }
                    assert!(effect.is_none());
                }
                other => panic!("expected Arrow type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_arrow_type_named_params() {
    let source = "operation fold(f: (acc: A, elem: B) -> A) -> A\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.params[0].ty {
                TypeExpr::Arrow { params, return_type, effect } => {
                    // Named params (a: A, b: B) — names are discarded, types kept
                    assert_eq!(params.len(), 2);
                    match &params[0] {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "A"),
                        other => panic!("expected Simple param, got {:?}", other),
                    }
                    match &params[1] {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "B"),
                        other => panic!("expected Simple param, got {:?}", other),
                    }
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "A"),
                        other => panic!("expected Simple return, got {:?}", other),
                    }
                    assert!(effect.is_none());
                }
                other => panic!("expected Arrow type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_arrow_type_with_effect() {
    let source = "operation run(f: (A) -> B @ Modifies) -> B\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.params[0].ty {
                TypeExpr::Arrow { params, return_type, effect } => {
                    assert_eq!(params.len(), 1);
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "B"),
                        other => panic!("expected Simple return, got {:?}", other),
                    }
                    let eff = effect.as_ref().expect("expected effect annotation");
                    match eff.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "Modifies"),
                        other => panic!("expected Simple effect, got {:?}", other),
                    }
                }
                other => panic!("expected Arrow type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_arrow_type_nullary() {
    let source = "operation delay(f: () -> A) -> A\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.params[0].ty {
                TypeExpr::Arrow { params, return_type, effect } => {
                    assert_eq!(params.len(), 0);
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "A"),
                        other => panic!("expected Simple return, got {:?}", other),
                    }
                    assert!(effect.is_none());
                }
                other => panic!("expected Arrow type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Ring / Polynom examples with arrow types and infix operators ──

#[test]
fn parse_ring_spec_with_arrow_types() {
    let source = r#"sort Ring
  sort T = ?

  operation add(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T
  operation neg(a: T) -> T
  operation zero() -> T
  operation one() -> T

  rule ?a + zero = ?a
  rule ?a * one = ?a
  rule ?a + neg(?a) = zero
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "Ring");
            let op_count = s.items.iter().filter(|i| matches!(i, Item::Operation(_))).count();
            let rule_count = s.items.iter().filter(|i| matches!(i, Item::Rule(_))).count();
            assert_eq!(op_count, 5, "Ring should have 5 operations");
            assert_eq!(rule_count, 3, "Ring should have 3 rules (laws)");
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_ring_spec_into_kb() {
    let source = r#"sort Ring
  sort T = ?

  operation add(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T
  operation neg(a: T) -> T
  operation zero() -> T
  operation one() -> T

  rule ?a + zero = ?a
  rule ?a * one = ?a
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let ring_term = kb.resolve_qualified_name_term("Ring");
    // Ring is an algebraic spec (no entity constructors), classified as Abstract
    assert_eq!(kb.sort_kind(ring_term), Some(SortKind::Abstract));

    // Ring has sort T + operations — verify it loaded successfully
    assert!(kb.fact_count() > 0, "KB should have facts after loading Ring");
}

#[test]
fn parse_polynom_with_requires_and_arrow_type() {
    let source = r#"sort Polynom
  sort R = ?
  requires Ring[R]

  entity polynom(coefficients: List[R])

  operation eval(p: Polynom[R], x: R) -> R
  operation map_coeffs(p: Polynom[R], f: (R) -> R) -> Polynom[R]
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            assert_eq!(parsed.symbols.name(s.name.last()), "Polynom");

            // Check requires Ring[R] — positional binding
            let req = s.items.iter().find(|i| matches!(i, Item::RequiresDecl(_)));
            assert!(req.is_some(), "should have requires declaration");
            match req.unwrap() {
                Item::RequiresDecl(r) => {
                    match &r.type_expr {
                        TypeExpr::Parameterized { name, bindings } => {
                            assert_eq!(parsed.symbols.name(name.last()), "Ring");
                            assert_eq!(bindings.len(), 1);
                            assert!(bindings[0].param.is_none());
                        }
                        other => panic!("expected Parameterized, got {:?}", other),
                    }
                }
                _ => unreachable!(),
            }

            // Check map_coeffs has arrow type param (R) -> R
            let ops: Vec<_> = s.items.iter().filter_map(|i| match i {
                Item::Operation(o) => Some(o),
                _ => None,
            }).collect();
            let map_op = ops.iter().find(|o| parsed.symbols.name(o.name.last()) == "map_coeffs")
                .expect("should have map_coeffs operation");
            match &map_op.params[1].ty {
                TypeExpr::Arrow { params, return_type, effect } => {
                    assert_eq!(params.len(), 1);
                    assert!(effect.is_none());
                    match &params[0] {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "R"),
                        other => panic!("expected Simple param R, got {:?}", other),
                    }
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "R"),
                        other => panic!("expected Simple return R, got {:?}", other),
                    }
                }
                other => panic!("expected Arrow type, got {:?}", other),
            }
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_polynom_with_ring_requirement() {
    let source = r#"sort List
  sort T = ?
end

sort Ring
  sort T = ?
  operation add(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T
  operation zero() -> T
end

sort Polynom
  sort R = ?
  requires Ring[R]
  entity polynom(coefficients: List[R])
  operation eval(p: Polynom[R], x: R) -> R
end

fact Ring[Int]
fact Polynom[Int]
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let ring_term = kb.resolve_qualified_name_term("Ring");
    let polynom_term = kb.resolve_qualified_name_term("Polynom");
    assert_eq!(kb.sort_kind(ring_term), Some(SortKind::Abstract));
    assert_eq!(kb.sort_kind(polynom_term), Some(SortKind::Defined));

    // Both sorts loaded successfully into the KB
    assert!(kb.fact_count() > 0, "KB should have facts after loading Ring + Polynom");
}

#[test]
fn parse_infix_in_rules_with_ring() {
    let source = r#"sort Ring
  sort T = ?
  operation add(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T

  rule ?a + ?b = ?b + ?a
  rule (?a + ?b) * ?c = ?a * ?c + ?b * ?c
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            let rules: Vec<_> = s.items.iter().filter(|i| matches!(i, Item::Rule(_))).collect();
            assert_eq!(rules.len(), 2, "Ring should have 2 rules (commutativity, distributivity)");
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    }

    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let ring_term = kb.resolve_qualified_name_term("Ring");
    assert_eq!(kb.sort_kind(ring_term), Some(SortKind::Abstract));
}

// ── Expression body tests ──────────────────────────────────────

#[test]
fn parse_operation_with_simple_body() {
    let source = "operation double(x: Int) -> Int = x + x\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Operation(op) => {
            assert_eq!(parsed.symbols.name(op.name.last()), "double");
            assert!(op.body.is_some(), "operation should have a body");
            let body = op.body.unwrap();
            // Body should be an infix term desugared to add(x, x)
            match parsed.terms.get(body) {
                Term::Fn { functor, pos_args, .. } => {
                    assert_eq!(parsed.symbols.name(*functor), "add");
                    assert_eq!(pos_args.len(), 2);
                }
                other => panic!("expected Fn term for body, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_operation_without_body() {
    let source = "operation foo(x: Int) -> Int\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Operation(op) => {
            assert!(op.body.is_none(), "operation without = should have no body");
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_operation_with_match_body() {
    let source = r#"operation length(l: List) -> Int =
  match l
    case nil -> 0
    case cons(_, t) -> 1 + length(t)
"#;
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Operation(op) => {
            assert_eq!(parsed.symbols.name(op.name.last()), "length");
            assert!(op.body.is_some());
            let body = op.body.unwrap();
            match parsed.terms.get(body) {
                Term::Fn { functor, pos_args, .. } => {
                    assert_eq!(parsed.symbols.name(*functor), "match_expr");
                    // pos_args[0] = scrutinee, pos_args[1..] = branches
                    assert_eq!(pos_args.len(), 3, "1 scrutinee + 2 branches");

                    // Check first branch: case nil -> 0
                    match parsed.terms.get(pos_args[1]) {
                        Term::Fn { functor: bf, pos_args: bargs, .. } => {
                            assert_eq!(parsed.symbols.name(*bf), "match_branch");
                            assert_eq!(bargs.len(), 2); // pattern, body
                            // Pattern should be pattern_var(nil)
                            match parsed.terms.get(bargs[0]) {
                                Term::Fn { functor: pf, .. } => {
                                    assert_eq!(parsed.symbols.name(*pf), "pattern_var");
                                }
                                other => panic!("expected pattern_var, got {:?}", other),
                            }
                        }
                        other => panic!("expected match_branch, got {:?}", other),
                    }
                }
                other => panic!("expected match_expr, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_operation_with_if_body() {
    let source = "operation abs(x: Int) -> Int = if x > 0 then x else 0 - x\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            assert!(op.body.is_some());
            let body = op.body.unwrap();
            match parsed.terms.get(body) {
                Term::Fn { functor, pos_args, .. } => {
                    assert_eq!(parsed.symbols.name(*functor), "if_expr");
                    assert_eq!(pos_args.len(), 3); // condition, then, else
                }
                other => panic!("expected if_expr, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_operation_with_let_body() {
    let source = r#"operation f(a: Int, b: Int) -> Int =
  let a2 = a * a
  let b2 = b * b
  a2 + b2
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            assert!(op.body.is_some());
            let body = op.body.unwrap();
            // Outer let_chain
            match parsed.terms.get(body) {
                Term::Fn { functor, pos_args, .. } => {
                    assert_eq!(parsed.symbols.name(*functor), "let_expr");
                    assert_eq!(pos_args.len(), 3); // pattern, value, body
                    // Inner body should be another let_chain
                    match parsed.terms.get(pos_args[2]) {
                        Term::Fn { functor: inner_f, pos_args: inner_args, .. } => {
                            assert_eq!(parsed.symbols.name(*inner_f), "let_expr");
                            assert_eq!(inner_args.len(), 3);
                        }
                        other => panic!("expected inner let_expr, got {:?}", other),
                    }
                }
                other => panic!("expected let_expr, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_operation_with_lambda_body() {
    let source = "operation make_adder(x: Int) -> Fun = lambda y -> x + y\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            assert!(op.body.is_some());
            let body = op.body.unwrap();
            match parsed.terms.get(body) {
                Term::Fn { functor, pos_args, .. } => {
                    assert_eq!(parsed.symbols.name(*functor), "lambda");
                    assert_eq!(pos_args.len(), 2); // param pattern, body
                    // Param should be pattern_var(y)
                    match parsed.terms.get(pos_args[0]) {
                        Term::Fn { functor: pf, pos_args: pargs, .. } => {
                            assert_eq!(parsed.symbols.name(*pf), "pattern_var");
                            assert_eq!(pargs.len(), 1);
                            match parsed.terms.get(pargs[0]) {
                                Term::Ident(sym) => {
                                    assert_eq!(parsed.symbols.name(*sym), "y");
                                }
                                other => panic!("expected Ident(y), got {:?}", other),
                            }
                        }
                        other => panic!("expected pattern_var, got {:?}", other),
                    }
                }
                other => panic!("expected lambda, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_pattern_wildcard() {
    let source = r#"operation f(x: T) -> Int =
  match x
    case _ -> 0
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            let body = op.body.unwrap();
            match parsed.terms.get(body) {
                Term::Fn { pos_args, .. } => {
                    // Branch pattern should be pattern_wildcard
                    let branch = parsed.terms.get(pos_args[1]);
                    match branch {
                        Term::Fn { pos_args: bargs, .. } => {
                            match parsed.terms.get(bargs[0]) {
                                Term::Fn { functor, pos_args: wargs, .. } => {
                                    assert_eq!(parsed.symbols.name(*functor), "pattern_wildcard");
                                    assert!(wargs.is_empty());
                                }
                                other => panic!("expected pattern_wildcard, got {:?}", other),
                            }
                        }
                        other => panic!("expected match_branch, got {:?}", other),
                    }
                }
                other => panic!("expected match_expr, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_pattern_constructor() {
    let source = r#"operation f(x: T) -> Int =
  match x
    case cons(h, t) -> 1
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            let body = op.body.unwrap();
            match parsed.terms.get(body) {
                Term::Fn { pos_args, .. } => {
                    let branch = parsed.terms.get(pos_args[1]);
                    match branch {
                        Term::Fn { pos_args: bargs, .. } => {
                            // Pattern = pattern_constructor(Ident(cons), pattern_var(h), pattern_var(t))
                            match parsed.terms.get(bargs[0]) {
                                Term::Fn { functor, pos_args: cargs, .. } => {
                                    assert_eq!(parsed.symbols.name(*functor), "pattern_constructor");
                                    assert_eq!(cargs.len(), 3); // name + 2 sub-patterns
                                    // First arg is the constructor name
                                    match parsed.terms.get(cargs[0]) {
                                        Term::Ident(sym) => {
                                            assert_eq!(parsed.symbols.name(*sym), "cons");
                                        }
                                        other => panic!("expected Ident(cons), got {:?}", other),
                                    }
                                }
                                other => panic!("expected pattern_constructor, got {:?}", other),
                            }
                        }
                        other => panic!("expected match_branch, got {:?}", other),
                    }
                }
                other => panic!("expected match_expr, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_pattern_literal() {
    let source = r#"operation f(n: Int) -> String =
  match n
    case 0 -> "zero"
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            let body = op.body.unwrap();
            match parsed.terms.get(body) {
                Term::Fn { pos_args, .. } => {
                    let branch = parsed.terms.get(pos_args[1]);
                    match branch {
                        Term::Fn { pos_args: bargs, .. } => {
                            match parsed.terms.get(bargs[0]) {
                                Term::Fn { functor, pos_args: largs, .. } => {
                                    assert_eq!(parsed.symbols.name(*functor), "pattern_literal");
                                    assert_eq!(largs.len(), 1);
                                    match parsed.terms.get(largs[0]) {
                                        Term::Const(Literal::Int(0)) => {}
                                        other => panic!("expected Int(0), got {:?}", other),
                                    }
                                }
                                other => panic!("expected pattern_literal, got {:?}", other),
                            }
                        }
                        other => panic!("expected match_branch, got {:?}", other),
                    }
                }
                other => panic!("expected match_expr, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_operation_body_with_clauses() {
    let source = r#"operation safe_div(a: Int, b: Int) -> Int
  requires b != 0
  = a / b
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            assert_eq!(op.requires.len(), 1, "should have one requires clause");
            assert!(op.body.is_some(), "should have a body");
            match parsed.terms.get(op.body.unwrap()) {
                Term::Fn { functor, .. } => {
                    assert_eq!(parsed.symbols.name(*functor), "div");
                }
                other => panic!("expected div Fn, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn parse_operation_body_in_block() {
    let source = r#"sort Math
  operation
    double(x: Int) -> Int = x + x
    triple(x: Int) -> Int = x + x + x
  end
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::SortWithBody(s) => {
            match &s.items[0] {
                Item::OperationBlock(ob) => {
                    assert_eq!(ob.entries.len(), 2);
                    assert!(ob.entries[0].body.is_some());
                    assert!(ob.entries[1].body.is_some());
                    // First op body is add(x, x)
                    match parsed.terms.get(ob.entries[0].body.unwrap()) {
                        Term::Fn { functor, .. } => {
                            assert_eq!(parsed.symbols.name(*functor), "add");
                        }
                        other => panic!("expected add, got {:?}", other),
                    }
                }
                other => panic!("expected OperationBlock, got {:?}", std::mem::discriminant(other)),
            }
        }
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    }
}

// ── Expression body loading tests ───────────────────────────────
//
// These tests parse operations with expression bodies, load them
// (together with the stdlib), and verify the KB contains properly
// structured Expr/Pattern entity terms.

/// Helper: load stdlib + extra source into a KB. Returns the KB.
fn load_with_stdlib(extra_source: &str) -> KnowledgeBase {
    let dir = stdlib_dir();
    let files = collect_anthill_files(&dir);
    let mut all_parsed: Vec<_> = files.iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()))
        })
        .collect();
    let extra = parse::parse(extra_source).expect("parse extra source failed");
    all_parsed.push(extra);

    let refs: Vec<_> = all_parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load_all(&mut kb, &refs, &NullResolver)
        .expect("load failed");

    kb
}

/// Helper: find the named arg value in a Fn term.
/// Helper: if term is a Handle(Occurrence, id), dereference to the occurrence's structural term.
/// Otherwise return the term as-is.
fn deref_occ(kb: &KnowledgeBase, term_id: TermId) -> TermId {
    use anthill_core::kb::term::HandleKind;
    match kb.get_term(term_id) {
        Term::Const(anthill_core::kb::term::Literal::Handle(HandleKind::Occurrence, id)) => {
            let occ_id = anthill_core::kb::occurrence::OccurrenceId::from_raw(*id);
            kb.occurrence_store().term(occ_id)
        }
        _ => term_id,
    }
}

fn get_named_arg<'a>(kb: &'a KnowledgeBase, term_id: TermId, field: &str) -> Option<TermId> {
    match kb.get_term(term_id) {
        Term::Fn { named_args, .. } => {
            named_args.iter()
                .find(|(sym, _)| kb.resolve_sym(*sym) == field)
                .map(|&(_, tid)| tid)
        }
        _ => None,
    }
}

/// Helper: get functor name of a Fn term.
fn functor_name(kb: &KnowledgeBase, term_id: TermId) -> String {
    match kb.get_term(term_id) {
        Term::Fn { functor, .. } => kb.resolve_sym(*functor).to_owned(),
        _ => format!("{:?}", kb.get_term(term_id)),
    }
}

/// Helper: unwrap some(value) → value, panicking if not some.
fn unwrap_some(kb: &KnowledgeBase, term_id: TermId) -> TermId {
    match kb.get_term(term_id) {
        Term::Fn { functor, named_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "some",
                "expected some(...), got {}", functor_name(kb, term_id));
            named_args.iter()
                .find(|(sym, _)| kb.resolve_sym(*sym) == "value")
                .map(|&(_, tid)| tid)
                .expect("some() should have a value field")
        }
        other => panic!("expected some(Fn), got {:?}", other),
    }
}

/// Helper: assert a term is none().
fn assert_none(kb: &KnowledgeBase, term_id: TermId) {
    match kb.get_term(term_id) {
        Term::Fn { functor, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "none",
                "expected none(), got {}", functor_name(kb, term_id));
        }
        other => panic!("expected none(), got {:?}", other),
    }
}

/// Helper: get the first element of a cons-list.
fn list_head(kb: &KnowledgeBase, list_tid: TermId) -> Option<TermId> {
    match kb.get_term(list_tid) {
        Term::Fn { functor, named_args, .. } if kb.resolve_sym(*functor) == "cons" => {
            named_args.iter()
                .find(|(sym, _)| kb.resolve_sym(*sym) == "head")
                .map(|&(_, tid)| tid)
        }
        _ => None,
    }
}

/// Helper: find an OperationInfo by qualified name substring from op facts.
/// Uses `contains` to match qualified names like "test.expr.max".
fn find_op_info(kb: &mut KnowledgeBase, qualified_substr: &str) -> TermId {
    let op_sort = kb.make_name_term("Operation");
    let ops = kb.by_sort(op_sort);
    for &fid in &ops {
        let tid = kb.fact_term(fid);
        if let Some(name_tid) = get_named_arg(kb, tid, "name") {
            if let Term::Ref(sym) = kb.get_term(name_tid) {
                let qname = kb.qualified_name_of(*sym);
                if qname.contains(qualified_substr) {
                    return tid;
                }
            }
        }
    }
    panic!("OperationInfo matching '{}' not found", qualified_substr);
}

#[test]
fn load_operation_with_if_body() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  operation max(a: Int, b: Int) -> Int =
    if gt(a, b) then a else b
end
"#);

    let op_info = find_op_info(&mut kb, "test.expr.max");

    // body should be some(ExprOccurrence handle → if_expr(...))
    let body_opt = get_named_arg(&kb, op_info, "body").expect("body field missing");
    let body_handle = unwrap_some(&kb, body_opt);
    let body = deref_occ(&kb, body_handle);
    assert_eq!(functor_name(&kb, body), "if_expr");

    // cond should be ExprOccurrence handle → apply(fn: gt, args: [a, b])
    let cond_handle = get_named_arg(&kb, body, "cond").expect("cond missing");
    let cond = deref_occ(&kb, cond_handle);
    assert_eq!(functor_name(&kb, cond), "apply");

    // then_branch and else_branch should be ExprOccurrence handles → var_ref
    let then_handle = get_named_arg(&kb, body, "then_branch").expect("then_branch missing");
    assert_eq!(functor_name(&kb, deref_occ(&kb, then_handle)), "var_ref");
    let else_handle = get_named_arg(&kb, body, "else_branch").expect("else_branch missing");
    assert_eq!(functor_name(&kb, deref_occ(&kb, else_handle)), "var_ref");
}

#[test]
fn load_operation_with_match_body() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  sort Nat
    entity zero
    entity succ(pred: Nat)
    operation is_zero(n: Nat) -> Bool =
      match n
        case zero() -> true
        case succ(_) -> false
  end
end
"#);

    let op_info = find_op_info(&mut kb, "test.expr.Nat.is_zero");

    // body should be some(ExprOccurrence handle → match_expr(...))
    let body_opt = get_named_arg(&kb, op_info, "body").expect("body field missing");
    let body = deref_occ(&kb, unwrap_some(&kb, body_opt));
    assert_eq!(functor_name(&kb, body), "match_expr");

    // scrutinee should be ExprOccurrence handle → var_ref(name: n)
    let scrutinee = deref_occ(&kb, get_named_arg(&kb, body, "scrutinee").expect("scrutinee missing"));
    assert_eq!(functor_name(&kb, scrutinee), "var_ref");

    // branches should be a 2-element list
    let branches = get_named_arg(&kb, body, "branches").expect("branches missing");
    assert_eq!(count_list_elements(&kb, branches), 2);

    // First branch: pattern = constructor_pattern(zero), body = bool_lit(true)
    let branch1 = list_head(&kb, branches).expect("first branch missing");
    assert_eq!(functor_name(&kb, branch1), "MatchBranch");
    let pat1 = get_named_arg(&kb, branch1, "pattern").expect("pattern missing");
    assert_eq!(functor_name(&kb, pat1), "constructor_pattern");
    let body1 = deref_occ(&kb, get_named_arg(&kb, branch1, "body").expect("body missing"));
    assert_eq!(functor_name(&kb, body1), "bool_lit");

    // Guard should be none
    let guard1 = get_named_arg(&kb, branch1, "guard").expect("guard missing");
    assert_none(&kb, guard1);
}

#[test]
fn load_operation_with_let_body() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  operation double(x: Int) -> Int =
    let y = x
    add(y, y)
end
"#);

    let op_info = find_op_info(&mut kb, "test.expr.double");
    let body_opt = get_named_arg(&kb, op_info, "body").expect("body field missing");
    let body = deref_occ(&kb, unwrap_some(&kb, body_opt));
    assert_eq!(functor_name(&kb, body), "let_expr");

    // pattern should be var_pattern (not ExprOccurrence — it's a Pattern)
    let pattern = get_named_arg(&kb, body, "pattern").expect("pattern missing");
    assert_eq!(functor_name(&kb, pattern), "var_pattern");

    // value should be ExprOccurrence handle → var_ref (x)
    let value = deref_occ(&kb, get_named_arg(&kb, body, "value").expect("value missing"));
    assert_eq!(functor_name(&kb, value), "var_ref");

    // body should be ExprOccurrence handle → apply (add)
    let inner_body = deref_occ(&kb, get_named_arg(&kb, body, "body").expect("inner body missing"));
    assert_eq!(functor_name(&kb, inner_body), "apply");
}

#[test]
fn load_operation_with_lambda_body() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  operation make_inc() -> Int =
    lambda x -> add(x, 1)
end
"#);

    let op_info = find_op_info(&mut kb, "test.expr.make_inc");
    let body_opt = get_named_arg(&kb, op_info, "body").expect("body field missing");
    let body = deref_occ(&kb, unwrap_some(&kb, body_opt));
    assert_eq!(functor_name(&kb, body), "lambda");

    // param should be var_pattern (Pattern, not ExprOccurrence)
    let param = get_named_arg(&kb, body, "param").expect("param missing");
    assert_eq!(functor_name(&kb, param), "var_pattern");

    // body should be ExprOccurrence handle → apply (add)
    let lambda_body = deref_occ(&kb, get_named_arg(&kb, body, "body").expect("lambda body missing"));
    assert_eq!(functor_name(&kb, lambda_body), "apply");

    // add should have 2 args
    let args = get_named_arg(&kb, lambda_body, "args").expect("args missing");
    assert_eq!(count_list_elements(&kb, args), 2);
}

#[test]
fn load_operation_without_body() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  operation abstract_op(x: Int) -> Int
end
"#);

    let op_info = find_op_info(&mut kb, "test.expr.abstract_op");
    let body_opt = get_named_arg(&kb, op_info, "body").expect("body field missing");
    assert_none(&kb, body_opt);
}

#[test]
fn load_operation_impl_fact_emitted() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  operation incr(x: Int) -> Int =
    add(x, 1)
end
"#);

    // Check OperationImpl fact was emitted
    let impl_sort = kb.make_name_term("OperationImpl");
    let impls = kb.by_sort(impl_sort);
    // Find the one for "incr"
    let mut found = false;
    for &fid in &impls {
        let tid = kb.fact_term(fid);
        if let Some(op_tid) = get_named_arg(&kb, tid, "operation") {
            if let Term::Ref(sym) = kb.get_term(op_tid) {
                if kb.qualified_name_of(*sym).contains("test.expr.incr") {
                    found = true;
                    // body should be apply(fn: add, args: [x, 1])
                    let body = get_named_arg(&kb, tid, "body").expect("body missing");
                    assert_eq!(functor_name(&kb, body), "apply");
                    // params should be a 1-element list [x]
                    let params = get_named_arg(&kb, tid, "params").expect("params missing");
                    assert_eq!(count_list_elements(&kb, params), 1);
                }
            }
        }
    }
    assert!(found, "OperationImpl for 'incr' not found");
}

// ── Occurrence infrastructure tests ─────────────────────────────

#[test]
fn parse_records_term_spans() {
    let source = "operation double(x: Int) -> Int = x + x\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(op) => {
            let body = op.body.unwrap();
            assert!(
                parsed.terms.spans.contains_key(&body),
                "expression body should have a span recorded"
            );
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_operation_body_creates_occurrences() {
    let source = r#"
sort Math {
  operation double(x: Int) -> Int = add(x, x)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    assert!(
        !kb.occurrence_store().is_empty(),
        "OccurrenceStore should have occurrences from expression body"
    );
}

#[test]
fn load_if_expr_creates_occurrences() {
    let source = r#"
sort Math {
  operation abs(x: Int) -> Int = if gt(x, 0) then x else sub(0, x)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let occ_count = kb.occurrence_store().len();
    assert!(
        occ_count >= 3,
        "expected at least 3 occurrences from if expression, got {}",
        occ_count,
    );
}

#[test]
fn occurrence_has_owner_symbol() {
    let source = r#"
sort Math {
  operation double(x: Int) -> Int = add(x, x)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let store = kb.occurrence_store();
    let has_owner = (0..store.len())
        .any(|i| {
            let occ = anthill_core::kb::occurrence::OccurrenceId::from_raw(i as u32);
            store.owner(occ).is_some()
        });
    assert!(has_owner, "at least one occurrence should have an owner symbol");
}

#[test]
fn occurrences_indexed_by_functor() {
    let source = r#"
sort Math {
  operation abs(x: Int) -> Int = if gt(x, 0) then x else sub(0, x)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // The if_expr functor should be indexed in the OccurrenceStore
    let if_expr_sym = kb.try_resolve_symbol("anthill.reflect.Expr.if_expr")
        .expect("if_expr symbol should exist");
    let occurrences = kb.occurrence_store().by_functor(if_expr_sym);
    assert!(
        !occurrences.is_empty(),
        "if_expr should be indexed by functor in OccurrenceStore"
    );
}

#[test]
fn resolve_finds_occurrence_candidates() {
    let source = r#"
sort Math {
  operation double(x: Int) -> Int = add(x, x)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Build a query pattern: apply(fn: ?f, args: ?a)
    let apply_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply")
        .expect("apply symbol should exist");
    let fn_key = kb.intern("fn");
    let args_key = kb.intern("args");
    let f_sym = kb.intern("f");
    let a_sym = kb.intern("a");
    let f_var = kb.fresh_var(f_sym);
    let a_var = kb.fresh_var(a_sym);
    let f_term = kb.alloc(Term::Var(f_var));
    let a_term = kb.alloc(Term::Var(a_var));

    use smallvec::SmallVec;
    let pattern = kb.alloc(Term::Fn {
        functor: apply_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(fn_key, f_term), (args_key, a_term)]),
    });

    // Resolve the pattern — should find occurrence candidates
    let solutions = kb.resolve(&[pattern], &Default::default());
    assert!(
        !solutions.is_empty(),
        "resolver should find apply(...) occurrence from expression body"
    );
}
