/// Integration tests: parse .anthill source → generate_rust → verify output.

use anthill_core::parse;
use anthill_core::codegen::generate_rust;

fn gen(source: &str) -> String {
    let parsed = parse::parse(source).unwrap_or_else(|e| {
        panic!("parse failed: {e:?}\nsource:\n{source}")
    });
    generate_rust(&parsed).unwrap_or_else(|e| {
        panic!("codegen failed: {e:?}\nsource:\n{source}")
    })
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
  sort T = ?
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
  sort T = ?
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
  sort T = ?
  requires Eq[T = T]
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
  operation retrieve(store: QueryableStore, pattern: Term) -> List[T = Term]
}
"#);
    assert!(out.contains("trait QueryableStore: Store {"), "output:\n{out}");
}

// ── Test 8: Effects: Modify → &mut self (no Result without Error) ─

#[test]
fn effects_modifies_to_mut_self_result() {
    // Modify alone → &mut self, no Result wrapping
    let out = gen(r#"sort Store {
  operation persist(store: Store, fact: Term, meta: Meta) -> FactId
    effects (Modify[store])
}
"#);
    assert!(out.contains("fn persist(&mut self"), "output:\n{out}");
    assert!(!out.contains("Result<"), "Modify without Error should not wrap in Result:\n{out}");

    // Modify + Error → &mut self + Result
    let out2 = gen(r#"sort Store {
  operation persist(store: Store, fact: Term, meta: Meta) -> FactId
    effects (Modify[store], Error)
}
"#);
    assert!(out2.contains("fn persist(&mut self"), "output:\n{out2}");
    assert!(out2.contains("Result<FactId, Error>"), "output:\n{out2}");
}

// ── Test 9: Effects: Error alone → &self + Result ────────────────

#[test]
fn effects_reads_to_self_result() {
    // No effects → &self, no Result
    let out = gen(r#"sort QueryableStore {
  operation retrieve(store: QueryableStore, pattern: Term) -> List[T = Term]
}
"#);
    assert!(out.contains("fn retrieve(&self"), "output:\n{out}");
    assert!(!out.contains("Result<"), "No effects should not wrap in Result:\n{out}");

    // Error alone → &self + Result
    let out2 = gen(r#"sort QueryableStore {
  operation retrieve(store: QueryableStore, pattern: Term) -> List[T = Term]
    effects (Error)
}
"#);
    assert!(out2.contains("fn retrieve(&self"), "output:\n{out2}");
    assert!(out2.contains("Result<Vec<Term>, Error>"), "output:\n{out2}");
}

// ── Test 10: Prelude type mappings ───────────────────────────────

#[test]
fn prelude_type_mappings() {
    let out = gen(r#"entity Data(
  count: Int,
  ratio: Float,
  flag: Bool,
  items: List[T = Int],
  maybe: Option[T = String]
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
  sort T = ?
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
  sort T = ?
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

    // Three-trait hierarchy
    assert!(out.contains("trait Store"), "should have trait Store: {out}");
    assert!(out.contains("trait QueryableStore: Store"), "should have QueryableStore: Store: {out}");
    assert!(out.contains("trait BulkStore: Store"), "should have BulkStore: Store: {out}");

    // Store should have persist, retract, flush
    assert!(out.contains("fn persist("), "should have persist: {out}");
    assert!(out.contains("fn retract("), "should have retract: {out}");
    assert!(out.contains("fn flush("), "should have flush: {out}");

    // QueryableStore should have retrieve
    assert!(out.contains("fn retrieve("), "should have retrieve: {out}");

    // BulkStore should have pull
    assert!(out.contains("fn pull("), "should have pull: {out}");

    // route should be a free function
    assert!(out.contains("fn route("), "should have route: {out}");
}

// ── Test 18: Abstract sort at namespace level → unit struct ──────

#[test]
fn abstract_sort_in_namespace_to_unit_struct() {
    let out = gen(r#"namespace reflect
  sort Term = ?
  sort FactId = ?
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

// ── Test 21: Fact with bindings → supertrait ─────────────────────

#[test]
fn fact_with_bindings_to_supertrait() {
    let out = gen(r#"sort Stream {
  sort S = ?
  sort E = ?
  fact Streamable[T = S]
  operation head(s: S) -> Option[T = S]
}
"#);
    assert!(out.contains("Streamable"), "should have supertrait Streamable: {out}");
}

// ── Test 22: Enum type param NOT collapsed to self ───────────────

#[test]
fn enum_type_param_not_self() {
    let out = gen(r#"sort LogicalStream {
  sort T = ?
  entity Empty
  operation pure(x: T) -> LogicalStream
}
"#);
    // pure should NOT get &self — T is a type param, not the sort itself
    assert!(out.contains("fn pure(x: T) -> Self"), "pure should have (x: T) -> Self, not &self: {out}");
    assert!(!out.contains("fn pure(&self"), "pure should NOT have &self: {out}");
}

// ── Test 23: Trait self in return with multi type params ─────────

#[test]
fn trait_self_in_return_multi_param() {
    let out = gen(r#"sort Stream {
  sort S = ?
  sort E = ?
  operation tail(s: Stream) -> Stream
}
"#);
    // With 2 type params, collapse_self is false, but sort-name → Self still works
    assert!(out.contains("fn tail(&self) -> Self"), "should have tail(&self) -> Self: {out}");
}

// ── Test 24: Enum self in return type ────────────────────────────

#[test]
fn enum_self_in_return() {
    let out = gen(r#"sort LogicalStream {
  sort T = ?
  entity Empty
  operation mplus(a: LogicalStream, b: LogicalStream) -> LogicalStream
}
"#);
    assert!(out.contains("-> Self"), "return type should be Self: {out}");
}

// ── Test 25: Abstract effect parameter → Result<R, E> ────────────

#[test]
fn abstract_effect_parameter_to_result() {
    // sort E = ? used in effects (E) → Result<R, E>
    let out = gen(r#"sort Stream {
  sort T = ?
  sort E = ?
  operation head(s: Stream) -> Option[T = T]
    effects (E)
  operation isEmpty(s: Stream) -> Bool
}
"#);
    // head has effects (E) → Result wrapping with abstract E
    assert!(out.contains("fn head(&self) -> Result<Option<T>, E>"), "should wrap in Result<..., E>: {out}");
    // isEmpty has no effects → no Result
    assert!(out.contains("fn is_empty(&self) -> bool"), "no effects should not wrap: {out}");
    assert!(!out.contains("is_empty(&self) -> Result"), "no effects should not wrap: {out}");
}
