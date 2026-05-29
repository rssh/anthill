/// Integration tests: parse .anthill source → verify IR structure → load into KB → query.


use anthill_core::parse;
use anthill_core::parse::ir::*;
use anthill_core::kb::{KnowledgeBase, SortKind};
use anthill_core::kb::term::{Term, TermId, Literal, Var};
use anthill_core::kb::load::{self, NullResolver};

use crate::common::{collect_anthill_files, stdlib_dir};

fn first_operation(parsed: &ParsedFile) -> &Operation {
    match &parsed.items[0] {
        Item::Operation(o) => o,
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

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
fn parse_literal_in_type_arg_is_denoted() {
    // WI-302: a literal standing in a type-argument position (`Vector[Int, 3]`)
    // is value-in-type → the converter emits `TypeExpr::Denoted` for the `3`.
    let source = "entity E(v: Vector[Int, 3])\n";
    let parsed = parse::parse(source).expect("parse failed");
    let entity = match &parsed.items[0] {
        Item::Entity(e) => e,
        other => panic!("expected Entity, got {:?}", std::mem::discriminant(other)),
    };
    let bindings = match &entity.fields[0].ty {
        TypeExpr::Parameterized { bindings, .. } => bindings,
        other => panic!("expected Parameterized field type, got {other:?}"),
    };
    assert!(
        bindings.iter().any(|b| matches!(b.bound, TypeExpr::Denoted(_))),
        "expected a Denoted binding for the literal `3`, got {bindings:?}"
    );
}

#[test]
fn load_literal_type_arg_in_body_no_reentrancy_panic() {
    // WI-302 regression: a value-in-type literal as a call type-arg inside an
    // operation body (`g[3](x)`) lowers via `type_expr_to_term`'s Denoted arm,
    // which runs *inside* the `convert_expr_term` body walk. Lowering it must
    // NOT re-enter `convert_expr_term` (it is not re-entrant). Loading must not
    // panic (an Err for unrelated resolution reasons is acceptable).
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let src = "operation g[n](x: Int) -> Int\noperation f(x: Int) -> Int = g[3](x)\n";
    let parsed = parse::parse(src).expect("parse failed");
    let _ = load::load(&mut kb, &parsed, &NullResolver);
}

#[test]
fn modify_name_arg_denotes_by_resolution_kind() {
    // Intended semantics for a NAME `c` in a type-argument position `Modify[c]`,
    // decided by what `c` resolves to (load-time, scope-aware / SymbolKind):
    //   c -> a PARAMETER or RESULT (a VALUE) ........ denoted(var_ref(c))
    //   c -> an OPERATION (value-producing; WI-313) . denoted(var_ref(c))
    //   c -> an ENTITY (a TYPE; §6.3) ............... sort_ref(c)   (NOT denoted)
    //   c -> a SORT (a TYPE) ........................ sort_ref(c)   (NOT denoted)
    //   c -> unresolved ............................. load error
    // The split is value vs type. An entity is sugar for a single-constructor
    // sort (kernel-language §6.3), so its bare name is a TYPE; the ambient-KB
    // accessor `kb` is properly a zero-arg OPERATION (value-producing) — that is
    // the value-in-type case WI-313 was really about, not the entity.
    // (Assumes `Modify` is in scope from the prelude effects.)
    fn contains_functor(kb: &KnowledgeBase, t: TermId, name: &str) -> bool {
        match kb.get_term(t) {
            Term::Fn { functor, pos_args, named_args } => {
                kb.resolve_sym(*functor) == name
                    || pos_args.iter().any(|&a| contains_functor(kb, a, name))
                    || named_args.iter().any(|(_, v)| contains_functor(kb, *v, name))
            }
            _ => false,
        }
    }
    // Self-contained: define a local `Modify` sort (with a type param) and
    // return `Int` (which the prelude resolves); only the `[c]`/`[C]`/`[nope]`
    // argument varies across the three cases.
    const MODIFY: &str = "sort Modify\n  sort T = ?\nend\n";
    fn effects_of_f(src: &str) -> Result<(KnowledgeBase, Vec<TermId>), String> {
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        let full = format!("{MODIFY}{src}");
        let parsed = parse::parse(&full).map_err(|e| format!("parse: {e:?}"))?;
        load::load(&mut kb, &parsed, &NullResolver).map_err(|e| format!("load: {e:?}"))?;
        let sym = kb.try_resolve_symbol("f").ok_or("operation `f` not found")?;
        let rec = anthill_core::kb::op_info::lookup_operation_info(&kb, sym)
            .ok_or("no OperationInfo for `f`")?;
        Ok((kb, rec.effects))
    }

    // (1) c is a PARAMETER (a value) -> denoted
    let (kb, eff) = effects_of_f("operation f(c: Int) -> Int effects Modify[c]\n")
        .expect("parameter case should load");
    assert!(
        eff.iter().any(|&e| contains_functor(&kb, e, "denoted")),
        "Modify[c] with c a parameter should denote, effects={eff:?}",
    );

    // (1b) kb is an ENTITY -> NOT denoted (sort_ref). A standalone entity is
    // sugar for a single-constructor sort (§6.3), so its bare name is a TYPE.
    // WI-313: entities are NOT value-in-type (this was the original mis-modeling).
    let (kbe, effe) = effects_of_f("sort KB\n  entity kb\nend\noperation f() -> Int effects Modify[kb]\n")
        .expect("entity case should load");
    assert!(
        effe.iter().all(|&e| !contains_functor(&kbe, e, "denoted")),
        "Modify[kb] with kb an entity should be sort_ref (NOT denoted), effects={effe:?}",
    );

    // (1c) kb is a zero-arg OPERATION (value-producing, like reflect's ambient-KB
    // accessor) -> denoted. This is the value-in-type case WI-313 was really
    // about: `kb()` yields a value, so a reference to it in a type slot denotes.
    let (kbo, effo) = effects_of_f("operation kb() -> Int\noperation f() -> Int effects Modify[kb]\n")
        .expect("operation case should load");
    assert!(
        effo.iter().any(|&e| contains_functor(&kbo, e, "denoted")),
        "Modify[kb] with kb a zero-arg operation should denote, effects={effo:?}",
    );

    // (2) C is a SORT (a type) -> NOT denoted (sort_ref)
    let (kb2, eff2) = effects_of_f("sort C = ?\noperation f() -> Int effects Modify[C]\n")
        .expect("sort case should load");
    assert!(
        eff2.iter().all(|&e| !contains_functor(&kb2, e, "denoted")),
        "Modify[C] with C a sort should NOT denote, effects={eff2:?}",
    );

    // (3) name does not resolve -> load error
    assert!(
        effects_of_f("operation f() -> Int effects Modify[nope]\n").is_err(),
        "Modify[nope] with `nope` unresolved should be a load error",
    );
}

#[test]
fn modify_value_param_in_effects_is_denoted() {
    // WI-302: `effects Modify[c]` where `c` is a value-parameter → the inner
    // binding lowers to `denoted(value: Ref(c))`, NOT `sort_ref(c)`, so it
    // reads as a value indexing the Modify effect (proposal 027.1 / 011).
    let mut kb = load_with_stdlib(r#"
namespace test.wi302
  import anthill.prelude.{Cell, Int}

  operation set_cell(c: Cell[V = Int], value: Int) -> Cell[V = Int]
    effects Modify[c]
end
"#);

    let op_info = find_op_info(&mut kb, "test.wi302.set_cell");
    let effects_list = get_named_arg(&kb, op_info, "effects").expect("effects arg");
    let effects = cons_list_to_vec(&kb, effects_list);
    assert_eq!(effects.len(), 1, "expected one effect (Modify[c])");

    // effects[0] = parameterized(base: sort_ref(Modify), bindings: [TypeBinding{..}])
    let bindings_list = get_named_arg(&kb, effects[0], "bindings").expect("bindings");
    let bindings = cons_list_to_vec(&kb, bindings_list);
    assert_eq!(bindings.len(), 1, "Modify[c] has one binding");

    // The binding value must be `denoted(value: Ref(c))`, not `sort_ref(c)`.
    let value = get_named_arg(&kb, bindings[0], "value").expect("binding value");
    match kb.get_term(value) {
        Term::Fn { functor, named_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "denoted",
                "value-param `c` in Modify[c] must lower to denoted, got `{}`",
                kb.resolve_sym(*functor));
            let inner = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "value")
                .map(|(_, v)| *v)
                .expect("denoted.value field");
            match kb.get_term(inner) {
                Term::Ref(s) => assert_eq!(kb.resolve_sym(*s), "c",
                    "denoted should carry Ref(c)"),
                other => panic!("expected Ref(c) inside denoted, got {other:?}"),
            }
        }
        other => panic!("expected denoted Fn for value-param binding, got {other:?}"),
    }
}

#[test]
fn qualified_parameterized_type_parses_and_loads() {
    // WI-311: a fully-qualified sort name WITH parameters
    // (`anthill.prelude.List[T = Int]`) parses as a Parameterized type whose
    // name keeps all qualified segments, and resolves/loads against stdlib.
    let src = r#"
namespace test.wi311
  import anthill.prelude.{Int}
  entity Box(items: anthill.prelude.List[T = Int])
end
"#;
    let parsed = parse::parse(src).expect("parse failed");
    let ns = match &parsed.items[0] {
        Item::Namespace(n) => n,
        other => panic!("expected Namespace, got {:?}", std::mem::discriminant(other)),
    };
    let entity = ns.items.iter().find_map(|it| match it {
        Item::Entity(e) => Some(e),
        _ => None,
    }).expect("entity Box");
    match &entity.fields[0].ty {
        TypeExpr::Parameterized { name, bindings } => {
            let segs: Vec<String> = name.segments.iter()
                .map(|s| parsed.symbols.name(*s).to_string())
                .collect();
            assert_eq!(segs, vec!["anthill", "prelude", "List"],
                "qualified application base must keep all segments, got {segs:?}");
            assert_eq!(bindings.len(), 1, "expected one binding (T = Int)");
        }
        other => panic!("expected Parameterized field type, got {other:?}"),
    }

    // Compiles right: the qualified name + parameters resolve against stdlib
    // (load_with_stdlib panics on any load error).
    let _kb = load_with_stdlib(src);
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
                        anthill_core::kb::term::Term::Var(Var::Global(vid)) => {
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
    assert_eq!(kb.sort_kind(nat_term), Some(SortKind::Sort));
    assert_eq!(kb.sort_kind(zero_term), None); // entities aren't sorts

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
    assert_eq!(kb.sort_kind(account_term), Some(SortKind::Sort));

    let checking_term = kb.resolve_qualified_name_term("Account.checking");
    assert!(kb.is_entity_of(checking_term, account_term),
        "checking should be entity of Account");
    assert_eq!(kb.sort_kind(checking_term), None); // entities aren't sorts
}

#[test]
fn load_operation_with_effects() {
    let source = r#"sort Error { sort T = ? entity Error(target: T) }
sort Modify { sort T = ? entity Modify(target: T) }
sort Store {
  entity store
  operation persist(s: Store, fact: Int) -> Int
    effects Modify[store]
  operation retrieve(s: Store, pattern: Int) -> Int
    effects Error[store]
  operation process(s: Store, x: Int) -> Int
    effects {Error[store], Modify[store]}
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
                let count = cons_list_to_vec(&kb, *effects_list_tid).len();
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
    effects E
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
            assert_eq!(cons_list_to_vec(&kb, *effects_list_tid).len(), 1,
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

    // Cross-namespace type references resolved via imports.
    // Types are now sort_ref(name: Ref(sym)) — look for the Ref(sym) form.
    let measure_sym = kb.resolve_symbol("Units.Measure");
    let measure_ref = kb.alloc(Term::Ref(measure_sym));
    let shape_sym = kb.resolve_symbol("Geometry.Shape");
    let shape_ref = kb.alloc(Term::Ref(shape_sym));

    // area operation is in Geometry namespace but references Measure
    let mut area_refs_measure = false;
    for &fid in &geometry_facts {
        let term = kb.fact_term(fid);
        check_term_contains(&kb, term, measure_ref, &mut area_refs_measure);
    }
    assert!(area_refs_measure, "Geometry's area should reference Measure");

    // convert operation is in Units namespace but references Shape
    let mut convert_refs_shape = false;
    for &fid in &units_facts {
        let term = kb.fact_term(fid);
        check_term_contains(&kb, term, shape_ref, &mut convert_refs_shape);
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
    let dir = crate::common::testcases_dir().join("nested-namespace-imports");
    let files = crate::common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "expected test files in {}", dir.display());

    // Also load stdlib prelude so that List, String, Bool are available
    let stdlib_dir = crate::common::stdlib_dir();
    let mut all_files = crate::common::collect_anthill_files(&stdlib_dir);
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
    let source = "sort Money = ? {< Monetary amount >}?\n";
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
    let source = "sort Money = ? {< Monetary amount >}?\n";
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
    let source = "rule test: foo(?x {< the x value >}?)\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert_eq!(parsed.items.len(), 1);
    match &parsed.items[0] {
        Item::Rule(r) => {
            // Head should be a fn_term foo(?x). Single-head rule.
            assert_eq!(r.heads.len(), 1, "expected single head");
            match &r.heads[0] {
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
    let source = "rule test: foo(?x {< the x value >}?)\n";
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
    let source = "sort Money = ? {< Monetary amount >} {< Used in banking >}?\n";
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
    let source = "sort Money = ? {< Monetary amount >} {< Used in banking >}?\n";
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
    let source = "rule test: foo(?x {< first >} {< second >}?)\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Rule(r) => {
            assert_eq!(r.heads.len(), 1, "expected single head");
            match &r.heads[0] {
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
                        Term::Var(Var::Global(vid)) => {
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
                        Term::Var(Var::Global(vid)) => {
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
                Term::Var(Var::Global(vid)) => vid.raw(),
                _ => panic!("expected Var"),
            };
            let ret_var = match parsed.terms.get(ret_tid) {
                Term::Var(Var::Global(vid)) => vid.raw(),
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
fn selective_import_finds_enum_entity_by_short_name() {
    // An enum entity lives in the enum's sort scope, so its qualified
    // name is `<ns>.<Sort>.<entity>`, not `<ns>.<entity>`. A selective
    // import like `import <ns>.{entity}` must still find it via the
    // nested-scope fallback.
    let source = r#"namespace test.parse
  export Result, ok, err
  enum Result
    entity ok(value: String)
    entity err(reason: String)
  end
end

namespace test.client
  import test.parse.{ok, err, Result}
  entity Use(r: Result)
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    let result = load::load(&mut kb, &parsed, &NullResolver);

    if let Err(errors) = &result {
        let import_errors: Vec<_> = errors.iter()
            .filter(|e| matches!(e, load::LoadError::UnresolvedImport { .. }))
            .collect();
        assert!(import_errors.is_empty(),
            "selective import of enum entities should resolve; got: {:?}", import_errors);
    }
    // Loaded successfully, or only had errors unrelated to this import.

    // Confirm both enum entities resolve from test.client's scope.
    for short in &["ok", "err"] {
        let qname = format!("test.parse.Result.{short}");
        let sym = kb.try_resolve_symbol(&qname);
        assert!(sym.is_some(), "{qname} should be defined");
    }
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
    assert_eq!(kb.sort_kind(c_term), Some(SortKind::Sort));

    // Entity `mkC` inside sort `a.b.C` gets fully-qualified name
    assert!(kb.has_qualified_name("a.b.C.mkC"),
        "entity mkC inside sort a.b.C should have qualified name 'a.b.C.mkC'");
}

#[test]
fn dotted_siblings_share_scope() {
    // Two dotted names with the same prefix should share the implicit
    // intermediate namespace, making sibling sorts visible to each other.
    let file1 = r#"sort ns.A end"#;
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
    let file1 = r#"sort ns.A end"#;
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
                Term::Var(Var::Global(vid)) => {
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
                    Term::Var(Var::Global(vid)) => vid.raw(),
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
                        Term::Var(Var::Global(vid)) => vid.raw(),
                        other => panic!("expected Var for field x, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field x, got {:?}", other),
            };
            let vid1 = match &e.fields[1].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(Var::Global(vid)) => vid.raw(),
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
                        Term::Var(Var::Global(vid)) => {
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
                        Term::Var(Var::Global(vid)) => {
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
                        Term::Var(Var::Global(vid)) => vid.raw(),
                        other => panic!("expected Var for field a, got {:?}", other),
                    }
                }
                other => panic!("expected Variable type for field a, got {:?}", other),
            };
            let vid1 = match &e.fields[1].ty {
                TypeExpr::Variable { term_id, .. } => {
                    match parsed.terms.get(*term_id) {
                        Term::Var(Var::Global(vid)) => vid.raw(),
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
        Item::Rule(r) => {
            assert_eq!(r.heads.len(), 1, "expected single head");
            match &r.heads[0] {
                anthill_core::parse::ir::RuleHead::Term(tid) => *tid,
                _ => panic!("expected rule head term"),
            }
        },
        other => panic!("expected Rule, got {:?}", std::mem::discriminant(other)),
    };
    (parsed.terms, parsed.symbols, head_tid)
}

/// Recursively format a parse-IR term for test assertions.
fn fmt_ir_term(terms: &SimpleTermStore, symbols: &anthill_core::intern::SymbolTable, tid: TermId) -> String {
    match terms.get(tid) {
        Term::Var(Var::Global(vid)) => format!("?{}", symbols.name(vid.name())),
        Term::Var(Var::DeBruijn(n)) => format!("?#{n}"),
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
    // WI-278: a value (variable) receiver routes to dot_apply, not the
    // field_access builtin. ?x.y → dot_apply(?x, y)
    let (terms, symbols, head) = parse_rule_head_ir("?x.y");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "dot_apply(?x, y)");
}

#[test]
fn parse_field_access_chained() {
    // ?x.y.z → dot_apply(dot_apply(?x, y), z)
    let (terms, symbols, head) = parse_rule_head_ir("?x.y.z");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "dot_apply(dot_apply(?x, y), z)");
}

#[test]
fn parse_field_access_in_fn_arg() {
    // f(?a.b, ?c) → f(dot_apply(?a, b), ?c)
    let (terms, symbols, head) = parse_rule_head_ir("f(?a.b, ?c)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "f(dot_apply(?a, b), ?c)");
}

#[test]
fn parse_field_access_in_infix() {
    // ?x.y = ?z → eq(dot_apply(?x, y), ?z)
    let (terms, symbols, head) = parse_rule_head_ir("?x.y = ?z");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "eq(dot_apply(?x, y), ?z)");
}

#[test]
fn parse_dot_method_call_preserves_receiver() {
    // WI-278: `?x.m(?a)` parses as a method call; the receiver (formerly
    // dropped by collect_field_access_segments) is the first arg of
    // dot_apply, then the name, then the call args.
    let (terms, symbols, head) = parse_rule_head_ir("?x.m(?a)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "dot_apply(?x, m, ?a)");
}

#[test]
fn parse_dot_method_call_chained() {
    // ?xs.map(?f).filter(?p) → nested dot_apply, receivers intact.
    let (terms, symbols, head) = parse_rule_head_ir("?xs.map(?f).filter(?p)");
    assert_eq!(
        fmt_ir_term(&terms, &symbols, head),
        "dot_apply(dot_apply(?xs, map, ?f), filter, ?p)",
    );
}

#[test]
fn parse_dot_static_call_still_flattens() {
    // `Foo.bar(?a)` — name (non-value) receiver keeps qualified-name
    // flattening: a normal call `Foo.bar(?a)`, not a dot_apply.
    let (terms, symbols, head) = parse_rule_head_ir("Foo.bar(?a)");
    assert_eq!(fmt_ir_term(&terms, &symbols, head), "Foo.bar(?a)");
}

#[test]
fn parse_field_access_in_operation_body() {
    // `p.fst` after `=` must parse as field_access, not be eaten by
    // the qualified-name lookahead.
    let source = "namespace t\n  sort Pair\n    entity P(fst: Int, snd: Int)\n  end\n  operation get_fst(p: Pair) -> Int =\n    p.fst\nend\n";
    let parsed = parse::parse(source).expect("parse failed");
    fn find_op(items: &[Item]) -> Option<&Operation> {
        for i in items {
            match i {
                Item::Operation(o) => return Some(o),
                Item::Namespace(n) => if let Some(o) = find_op(&n.items) { return Some(o); },
                Item::SortWithBody(s) => if let Some(o) = find_op(&s.items) { return Some(o); },
                _ => {}
            }
        }
        None
    }
    let op = find_op(&parsed.items).expect("expected operation item");
    let body = op.body.expect("operation should have a body");
    assert_eq!(
        fmt_ir_term(&parsed.terms, &parsed.symbols, body),
        "field_access(p, fst)",
    );
}

#[test]
fn parse_arrow_type_unary() {
    let source = "operation map(f: (A) -> B) -> C\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.params[0].ty {
                TypeExpr::Arrow { params, return_type, effects } => {
                    assert_eq!(params.len(), 1);
                    match &params[0] {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "A"),
                        other => panic!("expected Simple param, got {:?}", other),
                    }
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "B"),
                        other => panic!("expected Simple return, got {:?}", other),
                    }
                    assert!(effects.is_empty());
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
                TypeExpr::Arrow { params, return_type, effects } => {
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
                    assert!(effects.is_empty());
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
                TypeExpr::Arrow { params, return_type, effects } => {
                    assert_eq!(params.len(), 1);
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "B"),
                        other => panic!("expected Simple return, got {:?}", other),
                    }
                    assert_eq!(effects.len(), 1, "expected exactly one effect");
                    match &effects[0] {
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
fn parse_arrow_type_with_effect_set() {
    let source = "operation run(f: (A) -> B @ {Modifies, Reads}) -> B\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.params[0].ty {
                TypeExpr::Arrow { effects, .. } => {
                    assert_eq!(effects.len(), 2, "expected braced effect set of 2");
                    let names: Vec<&str> = effects.iter().map(|e| match e {
                        TypeExpr::Simple(n) => parsed.symbols.name(n.last()),
                        other => panic!("expected Simple effect, got {:?}", other),
                    }).collect();
                    assert_eq!(names, vec!["Modifies", "Reads"]);
                }
                other => panic!("expected Arrow type, got {:?}", other),
            }
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

/// End-to-end: parse an operation whose parameter is an arrow type with
/// a 2-effect set, load into KB, and verify the resulting arrow term
/// carries the WI-307 v1a canonical `effects_rows(EffectExpression)`
/// payload: a right-folded `merge(present(l₁), merge(present(l₂),
/// empty_row))` chain whose labels are the two effect functors.
#[test]
fn load_arrow_type_with_effect_set_canonical_row() {
    let source = r#"sort Modifies { sort T = ? entity Modifies(target: T) }
sort Reads { sort T = ? entity Reads(target: T) }
sort Host {
  sort A = ?
  sort B = ?
  entity host
  operation run(f: (A) -> B @ {Modifies[host], Reads[host]}) -> B
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // Drill OperationInfo for `run` to find parameter `f`'s arrow type
    // — that's where the effect set lands.
    let run_op = find_operation_info(&mut kb, "run");
    let params_list = named_arg(&kb, run_op, "params");
    let params = cons_list_to_vec(&kb, params_list);
    let arrow_term = named_arg(&kb, params[0], "type_name");

    let functor_name = match kb.get_term(arrow_term) {
        Term::Fn { functor, .. } => kb.resolve_sym(*functor).to_owned(),
        other => panic!("expected arrow Fn, got {:?}", other),
    };
    assert_eq!(functor_name, "arrow",
        "arrow-effect term should be built via prelude Type.arrow");

    // WI-307 v1a: the effects field is `effects_rows(effects_expr: <EX>)`,
    // not a List. Walk the wrapper down to the EffectExpression payload.
    let effects_field = named_arg(&kb, arrow_term, "effects");
    let er_functor = match kb.get_term(effects_field) {
        Term::Fn { functor, .. } => kb.resolve_sym(*functor).to_owned(),
        other => panic!("expected effects_rows Fn, got {:?}", other),
    };
    assert_eq!(er_functor, "effects_rows",
        "arrow.effects should be wrapped in the effects_rows Type entity");

    // Walk the canonical right-folded `merge(present(l), merge(...,
    // empty_row))` chain and collect the present-label types.
    let expr = named_arg(&kb, effects_field, "effects_expr");
    let mut labels: Vec<anthill_core::kb::term::TermId> = Vec::new();
    let mut node = expr;
    loop {
        let (functor, args) = match kb.get_term(node) {
            Term::Fn { functor, named_args, .. } => {
                (kb.resolve_sym(*functor).to_owned(), named_args.clone())
            }
            other => panic!("expected EffectExpression Fn, got {:?}", other),
        };
        match functor.as_str() {
            "empty_row" => break,
            "present" => {
                labels.push(named_arg(&kb, node, "label"));
                break;
            }
            "merge" => {
                let left = args.iter()
                    .find(|(s, _)| kb.resolve_sym(*s) == "left")
                    .map(|(_, v)| *v).expect("merge.left");
                if let Term::Fn { functor: lf, .. } = kb.get_term(left) {
                    if kb.resolve_sym(*lf) == "present" {
                        labels.push(named_arg(&kb, left, "label"));
                    }
                }
                let right = args.iter()
                    .find(|(s, _)| kb.resolve_sym(*s) == "right")
                    .map(|(_, v)| *v).expect("merge.right");
                node = right;
            }
            other => panic!("unexpected EffectExpression head `{}`", other),
        }
    }
    assert_eq!(labels.len(), 2, "row should carry two present labels");

    // Each `Modifies[host]` lowers to `parameterized(base: sort_ref(name:
    // Ref(Modifies)), bindings: cons(...))`, so drill base → name. The
    // canonical-form sort orders labels by `type_display_name`, so the
    // order here is alphabetical (`Modifies` before `Reads`).
    let names: Vec<String> = labels.iter().map(|&effect| {
        let base = named_arg(&kb, effect, "base");
        let name_tid = named_arg(&kb, base, "name");
        match kb.get_term(name_tid) {
            Term::Ref(sym) => kb.resolve_sym(*sym).to_owned(),
            other => panic!("expected Ref for sort_ref.name, got {:?}", other),
        }
    }).collect();
    assert_eq!(names, vec!["Modifies".to_owned(), "Reads".to_owned()],
        "effect bases should be Modifies, Reads in canonical (alphabetic) order");

    // Printer regression: the arrow's pretty-print must still mention
    // every effect base name regardless of how `effects` is shaped.
    let printer = anthill_core::persistence::print::TermPrinter::new(&kb);
    let printed = printer.print_term(arrow_term);
    assert!(printed.contains("Modifies") && printed.contains("Reads"),
        "printer output should mention both effect bases; got `{}`", printed);
    assert!(printed.contains("effects"),
        "printer output should mention the effects field; got `{}`", printed);
}

// ── WI-327 EffectExpression surface grammar ─────────────────────────────
//
// Adds `+E` (explicit presence sugar), `-E` (absence / lacks-constraint),
// and `merge(E1, …, En)` (sugar for braced set form) to the effects
// surface grammar (proposal 045 §3, §Phase 2). The bare `E` form keeps
// its meaning; `+E` lowers identically; `-E` produces an `absent(E)`
// EffectExpression atom; `merge(...)` flattens like a braced set.

/// WI-327: `+E` parses and is structurally identical to bare `E`.
#[test]
fn parse_effect_presence_lowers_like_bare() {
    let preamble = r#"
sort Modify
  sort T = ?
  entity Modify(target: T)
end
sort Host
  entity host
"#;
    let source_bare = format!("{preamble}\n  operation foo() -> Int effects Modify[host]\nend\n");
    let source_plus = format!("{preamble}\n  operation foo() -> Int effects +Modify[host]\nend\n");
    let parsed_bare = parse::parse(&source_bare).expect("bare parse failed");
    let parsed_plus = parse::parse(&source_plus).expect("`+E` parse failed");

    let mut kb_bare = KnowledgeBase::new();
    load::register_prelude(&mut kb_bare);
    load::load(&mut kb_bare, &parsed_bare, &NullResolver).expect("bare load failed");

    let mut kb_plus = KnowledgeBase::new();
    load::register_prelude(&mut kb_plus);
    load::load(&mut kb_plus, &parsed_plus, &NullResolver).expect("`+E` load failed");

    // Build the canonical effects rows from the same input set in both
    // KBs; they should match the post-load operation's effects.
    let kb_sym_bare = find_operation_info(&mut kb_bare, "foo");
    let kb_sym_plus = find_operation_info(&mut kb_plus, "foo");

    let eff_bare = named_arg(&kb_bare, kb_sym_bare, "effects");
    let eff_plus = named_arg(&kb_plus, kb_sym_plus, "effects");

    // Cross-KB structural equivalence (TermIds aren't comparable across
    // KBs, so check the head functor is `cons` and the head label name
    // matches).
    fn first_label_name(kb: &KnowledgeBase, eff_list: anthill_core::kb::term::TermId) -> String {
        // OperationInfo.effects is still a cons-list at the reflect-side
        // (the canonical effects_rows lives in the arrow.effects path).
        match kb.get_term(eff_list) {
            Term::Fn { functor, named_args, .. } if kb.resolve_sym(*functor) == "cons" => {
                let head = named_args.iter()
                    .find(|(s, _)| kb.resolve_sym(*s) == "head")
                    .map(|(_, v)| *v).expect("cons.head");
                // head is the effect term — parameterized(Modify, [c = ...]) etc.
                let base = named_arg(kb, head, "base");
                let name_tid = named_arg(kb, base, "name");
                match kb.get_term(name_tid) {
                    Term::Ref(sym) => kb.resolve_sym(*sym).to_owned(),
                    _ => "?".to_owned(),
                }
            }
            _ => "?".to_owned(),
        }
    }

    let name_bare = first_label_name(&kb_bare, eff_bare);
    let name_plus = first_label_name(&kb_plus, eff_plus);
    assert_eq!(name_bare, name_plus,
        "`effects +E` should lower identically to `effects E`");
    assert_eq!(name_bare, "Modify",
        "expected the effect to be Modify; got `{}`", name_bare);
}

/// WI-327: `-E` parses and lowers to an `absent(E)` atom inside the
/// canonical effects_rows.
#[test]
fn parse_effect_absence_lowers_to_absent_atom() {
    let source = r#"
sort Error
  entity Error
end
sort Host
  entity host
  operation foo() -> Int effects -Error
end
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    // The reflect-side effects list still uses cons. Walk it and verify
    // the head element is an `absent(...)` EffectExpression atom.
    let foo_op = find_operation_info(&mut kb, "foo");
    let eff_list = named_arg(&kb, foo_op, "effects");
    let head = match kb.get_term(eff_list) {
        Term::Fn { functor, named_args, .. } if kb.resolve_sym(*functor) == "cons" => {
            named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "head")
                .map(|(_, v)| *v).expect("cons.head")
        }
        other => panic!("expected cons head, got {:?}", other),
    };
    let head_functor = match kb.get_term(head) {
        Term::Fn { functor, .. } => kb.resolve_sym(*functor).to_owned(),
        other => panic!("expected Fn head, got {:?}", other),
    };
    assert_eq!(head_functor, "absent",
        "`-E` should lower to an `absent(...)` atom; got `{}`", head_functor);
}

/// WI-327: `merge(E1, E2)` flattens identically to the braced-set form.
#[test]
fn parse_effect_merge_lowers_like_braced_set() {
    let preamble = r#"
sort Modify
  sort T = ?
  entity Modify(target: T)
end
sort Reads
  sort T = ?
  entity Reads(target: T)
end
sort Host
  entity host
"#;
    let source_merge = format!("{preamble}\n  operation foo() -> Int effects merge(Modify[host], Reads[host])\nend\n");
    let source_braced = format!("{preamble}\n  operation foo() -> Int effects {{Modify[host], Reads[host]}}\nend\n");
    let parsed_merge = parse::parse(&source_merge).expect("merge parse failed");
    let parsed_braced = parse::parse(&source_braced).expect("braced parse failed");

    let mut kb_merge = KnowledgeBase::new();
    load::register_prelude(&mut kb_merge);
    load::load(&mut kb_merge, &parsed_merge, &NullResolver).expect("merge load failed");

    let mut kb_braced = KnowledgeBase::new();
    load::register_prelude(&mut kb_braced);
    load::load(&mut kb_braced, &parsed_braced, &NullResolver).expect("braced load failed");

    // Count cons cells in both effects lists — should be 2 each.
    fn count_cons(kb: &KnowledgeBase, tid: anthill_core::kb::term::TermId) -> usize {
        let mut node = tid;
        let mut n = 0;
        loop {
            match kb.get_term(node) {
                Term::Fn { functor, named_args, .. } if kb.resolve_sym(*functor) == "cons" => {
                    n += 1;
                    let tail = named_args.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "tail")
                        .map(|(_, v)| *v).expect("cons.tail");
                    node = tail;
                }
                _ => return n,
            }
        }
    }

    let op_merge = find_operation_info(&mut kb_merge, "foo");
    let op_braced = find_operation_info(&mut kb_braced, "foo");
    let eff_merge = named_arg(&kb_merge, op_merge, "effects");
    let eff_braced = named_arg(&kb_braced, op_braced, "effects");

    assert_eq!(count_cons(&kb_merge, eff_merge), 2,
        "merge(E1, E2) should flatten to 2 effects");
    assert_eq!(count_cons(&kb_braced, eff_braced), 2,
        "braced {{E1, E2}} should produce 2 effects");
}

#[test]
fn parse_arrow_type_nullary() {
    let source = "operation delay(f: () -> A) -> A\n";
    let parsed = parse::parse(source).expect("parse failed");
    match &parsed.items[0] {
        Item::Operation(o) => {
            match &o.params[0].ty {
                TypeExpr::Arrow { params, return_type, effects } => {
                    assert_eq!(params.len(), 0);
                    match return_type.as_ref() {
                        TypeExpr::Simple(n) => assert_eq!(parsed.symbols.name(n.last()), "A"),
                        other => panic!("expected Simple return, got {:?}", other),
                    }
                    assert!(effects.is_empty());
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
    assert_eq!(kb.sort_kind(ring_term), Some(SortKind::Sort));

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
                TypeExpr::Arrow { params, return_type, effects } => {
                    assert_eq!(params.len(), 1);
                    assert!(effects.is_empty());
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
    assert_eq!(kb.sort_kind(ring_term), Some(SortKind::Sort));
    assert_eq!(kb.sort_kind(polynom_term), Some(SortKind::Sort));

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
    assert_eq!(kb.sort_kind(ring_term), Some(SortKind::Sort));
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
                    assert_eq!(parsed.symbols.name(*functor), "lambda_expr");
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


/// Helper (WI-305): the operation body is no longer a fact field — it lives in
/// the `op_body_node` side-table. Given an OperationInfo / OperationImpl term,
/// read its `name`/`operation` symbol and fetch the body occurrence. `None` for
/// body-less ops. Inspect the body via its `Expr` variant — control-flow forms
/// (If/Let/Match/Lambda) and `VarRef` leaves have no goal-term shape.
fn op_body_occ(
    kb: &KnowledgeBase,
    info_term: TermId,
    name_field: &str,
) -> Option<std::rc::Rc<anthill_core::kb::node_occurrence::NodeOccurrence>> {
    let name_tid = get_named_arg(kb, info_term, name_field)?;
    let op_sym = match kb.get_term(name_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        _ => return None,
    };
    kb.op_body_node(op_sym).cloned()
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

    use anthill_core::kb::node_occurrence::Expr;
    let op_info = find_op_info(&mut kb, "test.expr.max");

    // body now lives in the op_body_node side-table (WI-305) → Expr::If
    let body = op_body_occ(&kb, op_info, "name").expect("op body missing");
    match body.as_expr() {
        Some(Expr::If { condition, then_branch, else_branch }) => {
            // condition is an Apply (gt(a, b))
            assert!(matches!(condition.as_expr(), Some(Expr::Apply { .. })),
                "condition should be an apply, got {:?}", condition.as_expr());
            // both branches are var references (Expr::VarRef / Expr::Var)
            assert!(matches!(then_branch.as_expr(), Some(Expr::VarRef { .. } | Expr::Var(_))),
                "then_branch should be a var ref, got {:?}", then_branch.as_expr());
            assert!(matches!(else_branch.as_expr(), Some(Expr::VarRef { .. } | Expr::Var(_))),
                "else_branch should be a var ref, got {:?}", else_branch.as_expr());
        }
        other => panic!("expected If, got {other:?}"),
    }
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

    use anthill_core::kb::node_occurrence::Expr;
    let op_info = find_op_info(&mut kb, "test.expr.Nat.is_zero");

    // body now lives in the op_body_node side-table (WI-305) → Expr::Match
    let body = op_body_occ(&kb, op_info, "name").expect("op body missing");
    match body.as_expr() {
        Some(Expr::Match { scrutinee, branches }) => {
            // scrutinee is a var ref (n)
            assert!(matches!(scrutinee.as_expr(), Some(Expr::VarRef { .. } | Expr::Var(_))),
                "scrutinee should be a var ref, got {:?}", scrutinee.as_expr());
            assert_eq!(branches.len(), 2, "two branches");

            // First branch: pattern = constructor_pattern(zero), body = bool literal
            // WI-318: branch.pattern is now a Pattern-kind occurrence.
            let branch1 = &branches[0];
            use anthill_core::kb::node_occurrence::Pattern;
            assert!(
                matches!(branch1.pattern.as_pattern(), Some(Pattern::Constructor { .. })),
                "branch pattern should be a Constructor pattern, got {:?}", branch1.pattern.as_pattern(),
            );
            assert!(matches!(branch1.body.as_expr(), Some(Expr::Const(_))),
                "branch body should be a bool literal, got {:?}", branch1.body.as_expr());
            // Guard should be none
            assert!(branch1.guard.is_none(), "branch guard should be none");
        }
        other => panic!("expected Match, got {other:?}"),
    }
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

    use anthill_core::kb::node_occurrence::Expr;
    let op_info = find_op_info(&mut kb, "test.expr.double");
    let body = op_body_occ(&kb, op_info, "name").expect("op body missing");
    match body.as_expr() {
        Some(Expr::Let { pattern, value, body: inner_body, .. }) => {
            // WI-318: pattern is now a Pattern-kind occurrence.
            use anthill_core::kb::node_occurrence::Pattern;
            assert!(
                matches!(pattern.as_pattern(), Some(Pattern::Var { .. })),
                "let pattern should be a Var pattern, got {:?}", pattern.as_pattern(),
            );
            // value is a var ref (x)
            assert!(matches!(value.as_expr(), Some(Expr::VarRef { .. } | Expr::Var(_))),
                "value should be a var ref, got {:?}", value.as_expr());
            // inner body is an Apply (add(y, y))
            assert!(matches!(inner_body.as_expr(), Some(Expr::Apply { .. })),
                "inner body should be an apply, got {:?}", inner_body.as_expr());
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn load_operation_with_lambda_body() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  import anthill.prelude.{Function, Int}
  operation make_inc() -> Function[Int, Int] =
    lambda x -> add(x, 1)
end
"#);

    use anthill_core::kb::node_occurrence::Expr;
    let op_info = find_op_info(&mut kb, "test.expr.make_inc");
    let body = op_body_occ(&kb, op_info, "name").expect("op body missing");
    match body.as_expr() {
        Some(Expr::Lambda { param, body: lambda_body }) => {
            // WI-318: param is now a Pattern-kind Rc<NodeOccurrence>.
            use anthill_core::kb::node_occurrence::Pattern;
            assert!(
                matches!(param.as_pattern(), Some(Pattern::Var { .. })),
                "lambda param is a Pattern::Var, got {:?}", param.as_pattern(),
            );
            // lambda body is an Apply (add(x, 1)) with 2 positional args
            match lambda_body.as_expr() {
                Some(Expr::Apply { pos_args, .. }) => {
                    assert_eq!(pos_args.len(), 2, "add should have 2 args");
                }
                other => panic!("lambda body should be an apply, got {other:?}"),
            }
        }
        other => panic!("expected Lambda, got {other:?}"),
    }
}

#[test]
fn parse_tuple_literal_with_lambda_element() {
    // Regression: a lambda may be a tuple element — `(lambda x -> x, 5)` —
    // since `tuple_literal` shares the `_fn_arg` grammar rule. The
    // converter must visit the element as an ExprBody (like fn_term /
    // dot_apply args); otherwise it records "unexpected term node:
    // lambda_expr" and `parse` returns Err. Tested at the parse layer
    // because the loader rewrites the parse-IR `TupleLiteral` into a
    // reflect `constructor` expr.
    let source = "operation pair() -> T = (lambda x -> x, 5)\n";
    let parsed = parse::parse(source).expect("parse failed");
    let op = match &parsed.items[0] {
        Item::Operation(op) => op,
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    };
    let body = op.body.expect("body missing");
    let named = match parsed.terms.get(body) {
        Term::Fn { functor, named_args, .. } => {
            assert_eq!(parsed.symbols.name(*functor), "TupleLiteral");
            named_args.clone()
        }
        other => panic!("expected TupleLiteral, got {:?}", other),
    };
    // The lambda element survived conversion (not dropped, not errored).
    let has_lambda = named.iter().any(|(_, v)| matches!(
        parsed.terms.get(*v),
        Term::Fn { functor, .. } if parsed.symbols.name(*functor) == "lambda_expr"
    ));
    assert!(has_lambda, "lambda element should be preserved in the tuple, got {named:?}");
}

#[test]
fn load_operation_without_body() {
    let mut kb = load_with_stdlib(r#"
namespace test.expr
  operation abstract_op(x: Int) -> Int
end
"#);

    let op_info = find_op_info(&mut kb, "test.expr.abstract_op");
    // No body field anymore (WI-305); a body-less op has no op_body_node entry.
    assert!(op_body_occ(&kb, op_info, "name").is_none(),
        "declaration-only op should have no body occurrence");
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
        let op_sym = get_named_arg(&kb, tid, "operation")
            .and_then(|op_tid| match kb.get_term(op_tid) {
                Term::Ref(sym) | Term::Ident(sym) => Some(*sym),
                _ => None,
            });
        if let Some(op_sym) = op_sym {
            {
                if kb.qualified_name_of(op_sym).contains("test.expr.incr") {
                    found = true;
                    // params should be a 1-element list [x]
                    let params = get_named_arg(&kb, tid, "params").expect("params missing");
                    assert_eq!(cons_list_to_vec(&kb, params).len(), 1);
                    // body is no longer a fact field (WI-305) — read it from the
                    // op_body_node side-table via the OperationImpl `operation`.
                    use anthill_core::kb::node_occurrence::Expr;
                    let body = op_body_occ(&kb, tid, "operation").expect("op body missing");
                    assert!(matches!(body.as_expr(), Some(Expr::Apply { .. })),
                        "op body should be an apply, got {:?}", body.as_expr());
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
            let span = parsed.terms.span(body);
            assert!(
                span.end > span.start,
                "expression body span should cover a non-empty source range; got {:?}",
                span,
            );
        }
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn load_operation_body_creates_node_occurrence() {
    // WI-251 — operation bodies are now `Rc<NodeOccurrence>` trees
    // keyed in `kb.op_bodies`. Verifying the loader populates them
    // is the post-migration analogue of the old occurrence-store
    // population checks.
    let source = r#"
sort Math {
  operation double(x: Int) -> Int = add(x, x)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let double_sym = kb.try_resolve_symbol("Math.double")
        .or_else(|| kb.try_resolve_symbol("double"))
        .expect("double operation should be resolved");
    assert!(
        kb.op_body_node(double_sym).is_some(),
        "kb.op_body_node should be populated for `double`"
    );
}

#[test]
fn load_dot_method_call_materializes_dot_apply() {
    // WI-278 end-to-end: a value-receiver method call in an op body loads
    // (converter `dot_apply` parse term → loader reflect re-encode →
    // materialize) into `Expr::DotApply` with the receiver + args preserved.
    use anthill_core::kb::node_occurrence::Expr;
    let source = r#"
sort Math {
  operation f(x: Int) -> Int = ?xs.g(?a)
}
"#;
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let f_sym = kb.try_resolve_symbol("Math.f")
        .or_else(|| kb.try_resolve_symbol("f"))
        .expect("f operation should be resolved");
    let body = kb.op_body_node(f_sym).expect("op body present");
    match body.as_expr() {
        Some(Expr::DotApply { name, pos_args, named_args, .. }) => {
            assert_eq!(kb.resolve_sym(*name), "g", "method name");
            assert_eq!(pos_args.len(), 1, "one positional arg (?a)");
            assert!(named_args.is_empty());
        }
        other => panic!("expected DotApply, got {other:?}"),
    }
}

#[test]
fn incorrect_program_error_includes_line_number() {
    // Entity with a field of unknown type — should produce an error pointing to line 2.
    let source = "sort Shapes {\n  entity Box(width: Nonexistent)\n}\n";
    //            line 1              line 2                          line 3
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    let result = load::load(&mut kb, &parsed, &NullResolver);
    let errors = result.expect_err("expected load errors for unresolved type");

    let unresolved: Vec<_> = errors.iter().filter(|e| {
        matches!(e, load::LoadError::UnresolvedName { name, .. } if name == "Nonexistent")
    }).collect();
    assert!(!unresolved.is_empty(),
        "should report UnresolvedName for 'Nonexistent', got: {:?}", errors);

    // Verify format_with_source produces "line:col: ..." with correct line
    let formatted = unresolved[0].format_with_source(source);
    assert!(formatted.starts_with("2:"),
        "error should point to line 2, got: {}", formatted);
    assert!(formatted.contains("Nonexistent"),
        "error should mention the unresolved name, got: {}", formatted);
}

// ── Regression: descriptions with unicode and embedded keywords ────
//
// Real-world anthill-todo descriptions accumulate em-dashes, Greek
// letters, section / multiplication signs, embedded code-like snippets
// (`kb.epoch()`), and quoted text that itself contains `status: Open`.
// The parser must tolerate all of this inside a string literal.

#[test]
fn parse_workitem_description_with_unicode_punctuation() {
    // em-dash, Greek alpha, multiplication sign, section sign — all
    // common in design docs and work-item descriptions.
    let source = r#"fact WorkItem(
  id: "WI-177",
  description: "KB mutation epoch — bridge between live KB mutations and the existing proof cache (proposal 030 phase α: prove.rs:70). state_hash recomputed FROM SCRATCH per record, O(visited × kb_size). See examples/github-todo/docs/anthill-migration.md §6.",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;
    let parsed = parse::parse(source)
        .expect("WorkItem fact with unicode punctuation must parse");
    assert_eq!(parsed.items.len(), 1);
    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("load of unicode-description WorkItem must succeed");
}

#[test]
fn parse_description_containing_status_open_substring() {
    // A description literally containing the substring `status: Open`
    // — the kind of body that appears when the work item itself
    // explains a status-update flow. The parser must keep this inside
    // the string; downstream text-surgery (the `update_status_in_source`
    // path in anthill-todo) bears the burden of finding the *real*
    // status field and not the one in the quoted description, but the
    // parser side is straightforward — the closing `"` always wins.
    let source = r#"fact WorkItem(
  id: "WI-X",
  description: "asserts a WorkItem(id: \"X\", status: Open), retracts it, asserts WorkItem(id: \"X\", status: Claimed(...))",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;
    let parsed = parse::parse(source)
        .expect("description with literal `status: Open` substring must parse");
    assert_eq!(parsed.items.len(), 1);

    let mut kb = KnowledgeBase::new();
    load::load(&mut kb, &parsed, &NullResolver).expect("load");

    // Sanity: the description's String literal carries the embedded
    // `status: Open` verbatim; the *fact's* status field is just `Open`.
    let wi_sym = kb.intern("WorkItem");
    let rules = kb.by_functor(wi_sym);
    assert_eq!(rules.len(), 1);
    let head = kb.rule_head(rules[0]);
    let Term::Fn { named_args, .. } = kb.get_term(head) else {
        panic!("WorkItem head should be Fn");
    };
    let desc = named_args
        .iter()
        .find(|(s, _)| kb.resolve_sym(*s) == "description")
        .map(|(_, t)| *t)
        .expect("description named arg present");
    let Term::Const(Literal::String(desc_str)) = kb.get_term(desc) else {
        panic!("description must be a String const");
    };
    assert!(
        desc_str.contains(r#"status: Open"#),
        "description should retain the literal `status: Open` substring"
    );
    assert!(
        desc_str.contains(r#"WorkItem(id: "X""#),
        "description should retain the embedded WorkItem reference"
    );
}

#[test]
fn parse_handles_multiple_facts_with_long_unicode_descriptions() {
    // Multiple WorkItems back-to-back with WI-177-shaped descriptions —
    // the file shape `anthill-todo` accumulates over time. Tree-sitter
    // recovery must not let one fact's content leak into the next.
    let source = "\
fact WorkItem(\n  id: \"WI-A\",\n  description: \"em-dash — and § here\",\n  acceptance: [ToolPasses(\"cargo-test\")],\n  depends_on: [],\n  status: Open)\n\n\
fact WorkItem(\n  id: \"WI-B\",\n  description: \"Greek α and × multiplication, plus quoted \\\"X\\\"\",\n  acceptance: [ToolPasses(\"cargo-test\")],\n  depends_on: [],\n  status: Open)\n\n\
fact WorkItem(\n  id: \"WI-C\",\n  description: \"plain ASCII, no surprises\",\n  acceptance: [ToolPasses(\"cargo-test\")],\n  depends_on: [],\n  status: Open)\n";
    let parsed = parse::parse(source).expect("three-fact unicode source must parse");
    assert_eq!(parsed.items.len(), 3);
}

// ── Operation type parameters ────────────────────────────────────

#[test]
fn parse_operation_with_single_type_param() {
    let parsed = parse::parse("operation identity[T](x: T) -> T\n").expect("parse failed");
    let op = first_operation(&parsed);
    assert_eq!(op.type_params.len(), 1);
    assert_eq!(parsed.symbols.name(op.type_params[0].name), "T");
    assert!(op.type_params[0].default.is_none());
}

#[test]
fn parse_operation_with_multiple_type_params() {
    let parsed = parse::parse("operation pair[A, B](a: A, b: B) -> Pair\n").expect("parse failed");
    let op = first_operation(&parsed);
    let names: Vec<_> = op.type_params.iter().map(|p| parsed.symbols.name(p.name)).collect();
    assert_eq!(names, vec!["A", "B"]);
    assert!(op.type_params.iter().all(|p| p.default.is_none()));
}

#[test]
fn parse_operation_type_param_with_default() {
    let parsed = parse::parse("operation defaulted[T = Int](x: T) -> T\n").expect("parse failed");
    let op = first_operation(&parsed);
    assert_eq!(op.type_params.len(), 1);
    assert_eq!(parsed.symbols.name(op.type_params[0].name), "T");
    match &op.type_params[0].default {
        Some(TypeExpr::Simple(name)) => {
            assert_eq!(parsed.symbols.name(name.last()), "Int");
        }
        other => panic!("expected Simple(Int) default, got {:?}", other),
    }
}

#[test]
fn parse_operation_without_type_params_unchanged() {
    let parsed = parse::parse("operation length(l: List) -> Int\n").expect("parse failed");
    let op = first_operation(&parsed);
    assert!(op.type_params.is_empty());
}

#[test]
fn parse_operation_entry_carries_type_params() {
    let source = "sort S\n  operation map[A, B](xs: List, f: F) -> List\nend\n";
    let parsed = parse::parse(source).expect("parse failed");
    let sort = match &parsed.items[0] {
        Item::SortWithBody(s) => s,
        other => panic!("expected SortWithBody, got {:?}", std::mem::discriminant(other)),
    };
    let op = match &sort.items[0] {
        Item::Operation(o) => o,
        other => panic!("expected Operation, got {:?}", std::mem::discriminant(other)),
    };
    let names: Vec<_> = op.type_params.iter().map(|p| parsed.symbols.name(p.name)).collect();
    assert_eq!(names, vec!["A", "B"]);
}

/// WI-271: walk the SimpleTermStore for `Term::ParseAux(SortBindings)`
/// nodes — these encode call-site `[A = Int, ...]` type-args. Returns
/// every bindings list found, in allocation order.
fn collect_parse_type_args(parsed: &ParsedFile) -> Vec<Vec<SortBinding>> {
    parsed.terms.iter()
        .filter_map(|(_, t)| match t {
            Term::ParseAux(aux) => match aux.as_ref() {
                ParseAux::SortBindings(bindings) => Some(bindings.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

#[test]
fn parse_typed_call_site_records_type_args() {
    let source = "sort S\n  rule r(?t) :- term_as_entity[WorkItem](?t)\nend\n";
    let parsed = parse::parse(source).expect("parse failed");

    let typed_calls = collect_parse_type_args(&parsed);
    assert_eq!(typed_calls.len(), 1, "expected exactly one typed call site");

    let bindings = &typed_calls[0];
    assert_eq!(bindings.len(), 1, "expected one type binding");
    // Positional binding `[WorkItem]` — param=None, bound is the Simple type.
    assert!(bindings[0].param.is_none());
    match &bindings[0].bound {
        TypeExpr::Simple(name) => assert_eq!(parsed.symbols.name(name.last()), "WorkItem"),
        other => panic!("expected Simple(WorkItem) binding, got {:?}", other),
    }
}

#[test]
fn parse_named_typed_call_site_records_binding_param() {
    let source = "sort S\n  rule r(?t) :- term_as_entity[E = WorkItem](?t)\nend\n";
    let parsed = parse::parse(source).expect("parse failed");

    let typed_calls = collect_parse_type_args(&parsed);
    let bindings = typed_calls.first().expect("expected one typed call site");
    assert_eq!(bindings.len(), 1);
    let p = bindings[0].param.as_ref().expect("expected named binding");
    assert_eq!(parsed.symbols.name(p.last()), "E");
}

#[test]
fn parse_untyped_call_site_records_no_type_args() {
    let source = "sort S\n  rule r(?t) :- term_as_entity(?t)\nend\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert!(
        collect_parse_type_args(&parsed).is_empty(),
        "untyped call sites must not record ParseAux(SortBindings) nodes"
    );
}

#[test]
fn parse_sort_companion_call_no_op_type_args() {
    // Map[K = String, V = Int].empty() is a sort companion (proposal 035),
    // NOT an operation-level typed call. The bindings live on the inner
    // instantiation_term that is the *object* of the field_access; the
    // outer fn_term's name is the field_access (`empty`), so no ParseAux
    // SortBindings should be allocated for the fn_term TermId.
    let source = "sort S\n  rule r() :- Map[K = String, V = Int].empty()\nend\n";
    let parsed = parse::parse(source).expect("parse failed");
    assert!(
        collect_parse_type_args(&parsed).is_empty(),
        "sort companion call must not register operation-level type-args"
    );
}

// ── Loading: operation type parameters bind to logical variables ────

/// Find the loaded OperationInfo fact whose `name` field references the
/// given short name. Returns the OperationInfo's term id.
fn find_operation_info(kb: &mut KnowledgeBase, short_name: &str) -> TermId {
    let op_sort = kb.make_name_term("Operation");
    let fid = kb.by_sort(op_sort).into_iter().find(|&fid| {
        match kb.get_term(kb.fact_term(fid)) {
            Term::Fn { named_args, .. } => named_args.iter().any(|(s, t)| {
                kb.resolve_sym(*s) == "name"
                    && matches!(kb.get_term(*t), Term::Ref(sym) if kb.resolve_sym(*sym) == short_name)
            }),
            _ => false,
        }
    }).unwrap_or_else(|| panic!("no OperationInfo for `{}`", short_name));
    kb.fact_term(fid)
}

fn named_arg(kb: &KnowledgeBase, term: TermId, key: &str) -> TermId {
    match kb.get_term(term) {
        Term::Fn { named_args, .. } => named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == key)
            .map(|(_, t)| *t)
            .unwrap_or_else(|| panic!("missing named arg `{}`", key)),
        other => panic!("named_arg on non-Fn: {:?}", other),
    }
}

fn cons_list_to_vec(kb: &KnowledgeBase, mut list: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    loop {
        match kb.get_term(list) {
            Term::Fn { functor, named_args, .. } if kb.resolve_sym(*functor) == "cons" => {
                let h = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "head")
                    .map(|(_, t)| *t).expect("cons head");
                let t = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "tail")
                    .map(|(_, t)| *t).expect("cons tail");
                out.push(h);
                list = t;
            }
            _ => break,
        }
    }
    out
}

/// Panic unless `term` is a `Term::Var(Global(_))`; returns its raw VarId.
fn assert_var_id(kb: &KnowledgeBase, term: TermId) -> u32 {
    match kb.get_term(term) {
        Term::Var(Var::Global(vid)) => vid.raw(),
        other => panic!("expected Term::Var(Global), got {:?}", other),
    }
}

#[test]
fn load_op_type_param_resolves_bare_name_to_var() {
    let parsed = parse::parse("operation identity[T](x: T) -> T\n").expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_info = find_operation_info(&mut kb, "identity");
    let return_type = named_arg(&kb, op_info, "return_type");
    assert_var_id(&kb, return_type);
}

#[test]
fn load_op_type_param_shares_var_across_param_and_return() {
    // Bare-name references to a declared type param share a VarId
    // throughout the operation.
    let parsed = parse::parse(
        "operation identity[A](x: A) -> A\n"
    ).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_info = find_operation_info(&mut kb, "identity");
    let params_list = named_arg(&kb, op_info, "params");
    let params = cons_list_to_vec(&kb, params_list);
    assert_eq!(params.len(), 1);

    let param_x_type = named_arg(&kb, params[0], "type_name");
    let return_type = named_arg(&kb, op_info, "return_type");

    let vid_param = assert_var_id(&kb, param_x_type);
    let vid_return = assert_var_id(&kb, return_type);
    assert_eq!(vid_param, vid_return,
        "two bare-name references to `A` must share a VarId");
}

#[test]
fn load_op_distinct_type_params_get_distinct_vars() {
    let parsed = parse::parse(
        "operation pair[A, B](a: A, b: B) -> A\n"
    ).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_info = find_operation_info(&mut kb, "pair");
    let params_list = named_arg(&kb, op_info, "params");
    let params = cons_list_to_vec(&kb, params_list);
    let vid_a = assert_var_id(&kb, named_arg(&kb, params[0], "type_name"));
    let vid_b = assert_var_id(&kb, named_arg(&kb, params[1], "type_name"));
    assert_ne!(vid_a, vid_b);
}

#[test]
fn load_op_type_param_shares_var_into_parameterized_return() {
    // Use a locally-defined parameterized sort `Box` so the test is
    // self-contained — no stdlib import dependency.
    let source = "\
sort Box
  sort T = ?
end
operation just[A](x: A) -> Box[A]
";
    let parsed = parse::parse(source).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_info = find_operation_info(&mut kb, "just");
    let params_list = named_arg(&kb, op_info, "params");
    let params = cons_list_to_vec(&kb, params_list);
    let vid_param = assert_var_id(&kb, named_arg(&kb, params[0], "type_name"));

    let return_type = named_arg(&kb, op_info, "return_type");
    let bindings_list = named_arg(&kb, return_type, "bindings");
    let bindings = cons_list_to_vec(&kb, bindings_list);
    assert_eq!(bindings.len(), 1);
    let bound_value = named_arg(&kb, bindings[0], "value");
    let vid_return = assert_var_id(&kb, bound_value);

    assert_eq!(vid_param, vid_return,
        "`A` in param and `A` inside Box[A] must share a VarId");
}

#[test]
fn load_op_without_type_params_unaffected() {
    let parsed = parse::parse("operation length(x: Int) -> Int\n").expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::load(&mut kb, &parsed, &NullResolver).expect("load failed");

    let op_info = find_operation_info(&mut kb, "length");
    let return_type = named_arg(&kb, op_info, "return_type");
    assert!(!matches!(kb.get_term(return_type), Term::Var(_)));
}

#[test]
fn user_written_dot_apply_token_does_not_panic() {
    // `dot_apply` is not a reserved name, and `convert_term` (the
    // rule/fact/query term path, distinct from the converter's op-body
    // path) sees user-typed tokens. The WI-278 dot_apply re-encode must
    // match ONLY the converter form `dot_apply(receiver, Ident(name), …)`
    // (>= 2 positional args, Ident name); a user-written `dot_apply(?x)`
    // with < 2 positional args must fall through to generic conversion,
    // not index `pos_args[1]` and panic the loader. Regression for the
    // arity/Ident guard in convert_term.
    let src = r#"
namespace test.dot_apply_guard
  rule r(?x) :- dot_apply(?x)
end
"#;
    let parsed = parse::parse(src).expect("parse failed");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    // Pre-fix this panicked with index-out-of-bounds in convert_term.
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("load should succeed (1-arg dot_apply falls through, no panic)");
}
