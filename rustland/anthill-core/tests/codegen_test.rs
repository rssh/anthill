/// Integration tests: parse .anthill source → generate_rust → verify output.

use anthill_core::parse;
use anthill_core::codegen::generate_rust;

fn gen(source: &str) -> String {
    let parsed = parse::parse(source).unwrap_or_else(|e| {
        panic!("parse failed: {e:?}\nsource:\n{source}")
    });
    generate_rust(&parsed)
}

// ── Test 1: Entity with fields → struct ──────────────────────────

#[test]
fn entity_with_fields_to_struct() {
    let out = gen(r#"entity Account(id: String, balance: Int)"#);
    assert!(out.contains("struct Account {"), "output:\n{out}");
    assert!(out.contains("pub id: String"), "output:\n{out}");
    assert!(out.contains("pub balance: i64"), "output:\n{out}");
}

// ── Test 2: Unit entity → unit struct ────────────────────────────

#[test]
fn unit_entity_to_unit_struct() {
    let out = gen("entity Marker");
    assert!(out.contains("struct Marker;"), "output:\n{out}");
}

// ── Test 3: Sort with constructors → enum ────────────────────────

#[test]
fn sort_with_constructors_to_enum() {
    let out = gen(r#"sort WorkStatus {
  entity Draft
  entity Open
  entity Claimed(agent: String, since: String)
}
"#);
    assert!(out.contains("enum WorkStatus {"), "output:\n{out}");
    assert!(out.contains("Draft,"), "output:\n{out}");
    assert!(out.contains("Open,"), "output:\n{out}");
    assert!(out.contains("Claimed {"), "output:\n{out}");
    assert!(out.contains("agent: String,"), "output:\n{out}");
    assert!(out.contains("since: String,"), "output:\n{out}");
}

// ── Test 4: Sort with ops → trait ────────────────────────────────

#[test]
fn sort_with_ops_to_trait() {
    let out = gen(r#"sort Eq {
  sort T
  operation eq(a: T, b: T) -> Bool
  operation neq(a: T, b: T) -> Bool
}
"#);
    assert!(out.contains("trait Eq {"), "output:\n{out}");
    assert!(out.contains("fn eq(&self"), "output:\n{out}");
    assert!(out.contains("fn neq(&self"), "output:\n{out}");
}

// ── Test 5: Type param → Self collapse ───────────────────────────

#[test]
fn self_collapse_heuristic() {
    let out = gen(r#"sort Eq {
  sort T
  operation eq(a: T, b: T) -> Bool
}
"#);
    // Should collapse T to Self
    assert!(out.contains("&self"), "should have &self: {out}");
    assert!(out.contains("&Self"), "should have &Self param: {out}");
    // Should NOT have <T> on the trait
    assert!(!out.contains("trait Eq<T>"), "should not have generic: {out}");
}

// ── Test 6: requires → supertrait ────────────────────────────────

#[test]
fn requires_to_supertrait() {
    let out = gen(r#"sort Ordered {
  sort T
  requires Eq{T = T}
  operation compare(a: T, b: T) -> Int
}
"#);
    assert!(out.contains("trait Ordered: Eq {"), "output:\n{out}");
}

// ── Test 7: fact inside sort → supertrait ────────────────────────

#[test]
fn fact_inside_sort_to_supertrait() {
    let out = gen(r#"sort QueryableStore {
  fact Store
  operation retrieve(store: QueryableStore, pattern: Term) -> List{T = Term}
    effects (Reads(store))
}
"#);
    assert!(out.contains("trait QueryableStore: Store {"), "output:\n{out}");
}

// ── Test 8: Effects: Modifies → &mut self + Result ───────────────

#[test]
fn effects_modifies_to_mut_self_result() {
    let out = gen(r#"sort Store {
  operation persist(store: Store, fact: Term, meta: Meta) -> FactId
    effects (Modifies(store))
}
"#);
    assert!(out.contains("fn persist(&mut self"), "output:\n{out}");
    assert!(out.contains("Result<"), "output:\n{out}");
}

// ── Test 9: Effects: Reads → &self + Result ──────────────────────

#[test]
fn effects_reads_to_self_result() {
    let out = gen(r#"sort QueryableStore {
  operation retrieve(store: QueryableStore, pattern: Term) -> List{T = Term}
    effects (Reads(store))
}
"#);
    assert!(out.contains("fn retrieve(&self"), "output:\n{out}");
    assert!(out.contains("Result<"), "output:\n{out}");
}

// ── Test 10: Effects: Emits → callback param ─────────────────────

#[test]
fn effects_emits_to_callback() {
    let out = gen(r#"sort Processor {
  operation process(p: Processor) -> Bool
    effects (Emits(AuditEvent))
}
"#);
    assert!(out.contains("on_event: impl FnMut(AuditEvent)"), "output:\n{out}");
}

// ── Test 11: Prelude type mappings ───────────────────────────────

#[test]
fn prelude_type_mappings() {
    let out = gen(r#"entity Data(
  count: Int,
  ratio: Float,
  flag: Bool,
  items: List{T = Int},
  maybe: Option{T = String}
)
"#);
    assert!(out.contains("i64"), "should have i64: {out}");
    assert!(out.contains("f64"), "should have f64: {out}");
    assert!(out.contains("bool"), "should have bool: {out}");
    assert!(out.contains("Vec<i64>"), "should have Vec<i64>: {out}");
    assert!(out.contains("Option<String>"), "should have Option<String>: {out}");
}

// ── Test 12: Recursive field → Box ───────────────────────────────

#[test]
fn recursive_field_to_box() {
    let out = gen(r#"sort List {
  sort T
  entity Nil
  entity Cons(head: T, tail: List)
}
"#);
    assert!(out.contains("enum List<T>"), "output:\n{out}");
    assert!(out.contains("Nil,"), "output:\n{out}");
    assert!(out.contains("Box<List<T>>"), "should box recursive field: {out}");
}

// ── Test 13: Namespace → mod + use ───────────────────────────────

#[test]
fn namespace_to_mod_with_use() {
    let out = gen(r#"namespace banking
  import anthill.prelude.{List, Option}
  entity Account(id: String, balance: Int)
end
"#);
    assert!(out.contains("pub mod banking {"), "output:\n{out}");
    assert!(out.contains("use "), "should have use statement: {out}");
    assert!(out.contains("List"), "should import List: {out}");
    assert!(out.contains("Option"), "should import Option: {out}");
}

// ── Test 14: Namespace fact → impl marker comment ────────────────

#[test]
fn namespace_fact_to_impl_marker() {
    let out = gen(r#"namespace anthill.persistence.filesystem
  import anthill.persistence.{BulkStore}
  entity FileStore(root: String, convention: String)
  fact BulkStore
end
"#);
    assert!(out.contains("// impl BulkStore for FileStore"), "output:\n{out}");
}

// ── Test 15: Rules → test stubs ──────────────────────────────────

#[test]
fn rules_to_test_stubs() {
    let out = gen(r#"sort Eq {
  sort T
  operation eq(a: T, b: T) -> Bool
  rule reflexive: eq(?a, ?a)
}
"#);
    assert!(out.contains("#[cfg(test)]"), "output:\n{out}");
    assert!(out.contains("#[test]"), "output:\n{out}");
    assert!(out.contains("fn prop_reflexive"), "output:\n{out}");
}

// ── Test 16: Constraint → check fn ───────────────────────────────

#[test]
fn constraint_to_check_fn() {
    let out = gen(r#"constraint non_negative: gte(balance(?a), zero_val)"#);
    assert!(out.contains("fn check_non_negative"), "output:\n{out}");
    assert!(out.contains("todo!"), "output:\n{out}");
}

// ── Test 17: Full: persistence store.anthill ─────────────────────

#[test]
fn full_persistence_store_hierarchy() {
    let source = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../stdlib/anthill/persistence/store.anthill")
    ).expect("read store.anthill");

    let out = gen(&source);

    assert!(out.contains("mod persistence"), "should have mod persistence: {out}");

    // Abstract sorts → unit structs (opaque types)
    assert!(out.contains("struct Store;"), "should have struct Store: {out}");
    assert!(out.contains("struct QueryableStore;"), "should have struct QueryableStore: {out}");
    assert!(out.contains("struct BulkStore;"), "should have struct BulkStore: {out}");

    // All operations as free functions
    assert!(out.contains("fn persist("), "should have persist: {out}");
    assert!(out.contains("fn retract("), "should have retract: {out}");
    assert!(out.contains("fn flush("), "should have flush: {out}");
    assert!(out.contains("fn retrieve("), "should have retrieve: {out}");
    assert!(out.contains("fn pull("), "should have pull: {out}");
    assert!(out.contains("fn route("), "should have route: {out}");
}

// ── Test 18: Abstract sort at namespace level → unit struct ──────

#[test]
fn abstract_sort_in_namespace_to_unit_struct() {
    let out = gen(r#"namespace reflect
  sort Term
  sort FactId
  operation reify(t: Term) -> Term
end
"#);
    assert!(out.contains("struct Term;"), "should emit unit struct for Term: {out}");
    assert!(out.contains("struct FactId;"), "should emit unit struct for FactId: {out}");
    // reify should be a free function, not a trait method
    assert!(out.contains("fn reify("), "should have reify as free fn: {out}");
    assert!(!out.contains("trait Term"), "Term should not be a trait: {out}");
}

// ── Test 19: Enum variant names → PascalCase ─────────────────────

#[test]
fn enum_variant_pascal_case() {
    let out = gen(r#"sort Strategy {
  entity stage0
  entity by_namespace
  entity flat
}
"#);
    assert!(out.contains("Stage0,"), "should have Stage0 variant: {out}");
    assert!(out.contains("ByNamespace,"), "should have ByNamespace variant: {out}");
    assert!(out.contains("Flat,"), "should have Flat variant: {out}");
}

// ── Test 20: Fact-entity association only preceding entity ────────

#[test]
fn fact_associates_only_preceding_entity() {
    let out = gen(r#"namespace store
  entity SqlStore(url: String)
  entity QueryBinding(pattern: String)
  entity ColumnDef(name: String)
  fact QueryableStore
end
"#);
    // Should only associate with ColumnDef (immediately preceding entity)
    assert!(out.contains("// impl QueryableStore for ColumnDef"), "output:\n{out}");
    assert!(!out.contains("// impl QueryableStore for SqlStore"), "should not associate with SqlStore: {out}");
    assert!(!out.contains("// impl QueryableStore for QueryBinding"), "should not associate with QueryBinding: {out}");
}
