//! WI-20260902-JB6RS — A CONSTRUCTOR'S TYPE AND ITS INSTANCE ARE TWO TERMS.
//!
//! A constructor is a sort in its own right (kernel-language.md §6.3), so its one
//! declaration has two readings, and a name is read by its context (§4.4, *A name has a
//! reading in each context*): in a type context a constructor is its TYPE, named by the
//! declaration's type face; in a data context it is its INSTANCE; and its type written as
//! data takes the bracket, `red[]`. These rows drive the type face where it is minted —
//! a bracket in a clause, in a query, in an operation body — and read it back through
//! matching and evaluation — for every constructor: one nested in a sort, an eponymous
//! one, a free-standing one.
//!
//! BACKED OUT, each part alone (measured):
//!  * `KnowledgeBase::type_context_face` minting nothing (returning its argument): every
//!    row fails — the type and the instance are one term again.
//!  * the clause bracket's face (`Loader::convert_term_inner`, the `is_type_app` block):
//!    `a_bracket_in_a_clause_is_the_type` fails — `held(red[])` stores the instance.
//!  * the query bracket's face (`convert_query_term_expecting`):
//!    `a_bracket_in_a_query_is_the_type` fails.
//!  * the body type value's face (`bare_type_value_occ` and the bracket frames):
//!    `a_bracket_in_an_operation_body_is_the_type` fails.
use crate::common::{interp_for, load_errors_of, load_kb_with, query_pattern_term, query_unary};
use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::Term;

const SRC: &str = r#"
namespace test.jb6rs.face
  import anthill.prelude.{Int64, Bool, Type}
  enum Colour
    entity red
    entity green(v: Int64)
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  fact held(red[])
  fact inst(red)
  fact boxed(Box[V = red])
  rule typeFindsType(1) :- held(red[])
  rule instanceFindsType(1) :- held(red)
  rule typeFindsInstance(1) :- inst(red[])
  rule instanceFindsInstance(1) :- inst(red)
  rule bareBindingIsTheType(1) :- boxed(Box[V = red[]])
  operation theType() -> Type = red[]
  operation theInstance() -> Colour = red
end
"#;

fn answers(kb: &mut anthill_core::kb::KnowledgeBase, rule: &str) -> usize {
    query_unary(kb, &format!("test.jb6rs.face.{rule}")).len()
}

/// A bracket in a fact, a rule head or a rule body is the TYPE, and a fact over the type
/// and a fact over the instance answer only their own spelling. A bare constructor named
/// as a bracket's BINDING is the type too: `Box[V = red]` is `Box[V = red[]]`.
#[test]
fn a_bracket_in_a_clause_is_the_type() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "typeFindsType"), 1, "`red[]` finds the type");
    assert_eq!(answers(&mut kb, "instanceFindsType"), 0, "`red` does not find the type");
    assert_eq!(answers(&mut kb, "typeFindsInstance"), 0, "`red[]` does not find the instance");
    assert_eq!(answers(&mut kb, "instanceFindsInstance"), 1, "`red` finds the instance");
    assert_eq!(answers(&mut kb, "bareBindingIsTheType"), 1, "a binding is read in a type context");
}

/// A query reads a bracket as a clause does, so the type a fact holds is found by
/// writing the type, and not by writing the instance.
#[test]
fn a_bracket_in_a_query_is_the_type() {
    let mut kb = load_kb_with(SRC);
    let config = ResolveConfig {
        max_solutions: 4,
        ..ResolveConfig::default()
    };
    let by_type = query_pattern_term(&mut kb, "test.jb6rs.face.held(test.jb6rs.face.Colour.red[])");
    assert_eq!(kb.resolve(&[by_type], &config).len(), 1, "the query `held(red[])`");
    let by_instance = query_pattern_term(&mut kb, "test.jb6rs.face.held(test.jb6rs.face.Colour.red)");
    assert!(kb.resolve(&[by_instance], &config).is_empty(), "the query `held(red)`");
}

/// An operation body's `red[]` evaluates to the TYPE — the term every type producer builds
/// for the constructor (`make_sort_ref`, which names it by its type face) — and its bare
/// `red` to the instance, which is not that term.
#[test]
fn a_bracket_in_an_operation_body_is_the_type() {
    let mut interp = interp_for(SRC);
    let red = interp
        .kb()
        .try_resolve_symbol("test.jb6rs.face.Colour.red")
        .expect("red resolves");
    let the_type = interp.kb_mut().make_sort_ref(red);
    match interp.call("test.jb6rs.face.theType", &[]).expect("theType runs") {
        Value::Term { id, .. } => {
            assert_eq!(id, the_type, "`red[]` is the type every producer builds");
            assert!(
                matches!(interp.kb().get_term(id), Term::Ref(s) if s.is_type_face() && s.plain() == red),
                "and that type names `red` by its type face, not by the instance's symbol"
            );
        }
        other => panic!("expected the type as a term, got {other:?}"),
    }
    let instance = interp.call("test.jb6rs.face.theInstance", &[]).expect("theInstance runs");
    assert!(
        !matches!(instance, Value::Term { id, .. } if id == the_type),
        "`red` is the instance, not the type: {instance:?}"
    );
}

const BRACKETS: &str = r#"
namespace test.jb6rs.brackets
  import anthill.prelude.{Int64, String}
  sort Pair
    sort L = ?
    sort R = ?
    entity left(l: L)
    entity both(l: L, r: R)
  end
  fact pairTy(Pair.both[Int64, String])
  fact sortTy(Int64[])
  rule namedFindsPositional(1) :- pairTy(Pair.both[L = Int64, R = String])
  rule bareFindsEmpty(1) :- sortTy(Int64)
end
"#;

/// A constructor's bracket binds its SORT's parameters, in a clause as in a body: the
/// positional and the named spelling of one variant type are one term, and a key the sort
/// does not declare is refused. And a bracket that binds nothing is the bare type —
/// `Int64[]` is `Int64`, in a clause and in a query.
///
/// BACKED OUT (measured): the type-argument owner falling back to the sort-only gate, in
/// the clause, the rule body or the query, or the query's entity desugar run over a
/// bracket — the spelling assertions fail (the positional and the named stay two terms;
/// `Zork` loads). The `Int64[]` assertions pass either way BY DESIGN: a sort's nullary
/// `Fn{Int64}` and its `Ref(Int64)` are still two terms until the gate in `alloc` goes,
/// but the matcher reads them as one head, so the empty bracket is found by the bare name
/// already — the rows pin that it stays so.
#[test]
fn a_constructors_bracket_binds_its_sorts_parameters() {
    let mut kb = load_kb_with(BRACKETS);
    let answers = |kb: &mut anthill_core::kb::KnowledgeBase, rule: &str| {
        query_unary(kb, &format!("test.jb6rs.brackets.{rule}")).len()
    };
    assert_eq!(answers(&mut kb, "namedFindsPositional"), 1, "`both[Int64, String]` is `both[L = Int64, R = String]`");
    assert_eq!(answers(&mut kb, "bareFindsEmpty"), 1, "`Int64[]` is `Int64` in a clause");
    let config = ResolveConfig {
        max_solutions: 4,
        ..ResolveConfig::default()
    };
    let by_bare = query_pattern_term(&mut kb, "test.jb6rs.brackets.sortTy(anthill.prelude.Int64)");
    assert_eq!(kb.resolve(&[by_bare], &config).len(), 1, "and in a query");
    let by_empty = query_pattern_term(&mut kb, "test.jb6rs.brackets.sortTy(anthill.prelude.Int64[])");
    assert_eq!(kb.resolve(&[by_empty], &config).len(), 1, "a query's `Int64[]` is `Int64`");
    let by_positional = query_pattern_term(
        &mut kb,
        "test.jb6rs.brackets.pairTy(test.jb6rs.brackets.Pair.both[anthill.prelude.Int64, anthill.prelude.String])",
    );
    assert_eq!(kb.resolve(&[by_positional], &config).len(), 1, "a query's positional bracket is the named one");
    let errs = load_errors_of(
        "namespace test.jb6rs.zork\n  import anthill.prelude.Int64\n  sort Pair\n    sort L = ?\n    \
         entity left(l: L)\n  end\n  fact held(Pair.left[Zork = Int64])\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("has no type parameter named 'Zork'")),
        "a key `Pair` does not declare is refused in a clause: {errs:?}"
    );
}

const EPONYMOUS: &str = r#"
namespace test.jb6rs.epon
  import anthill.prelude.Int64
  sort Foo
    sort X = ?
    entity Foo(X: X)
  end
  entity Baz
  fact held(Foo[X = Int64])
  fact heldBaz(Baz[])
  rule typeFindsType(1) :- held(Foo[X = Int64])
  rule instanceFindsType(1) :- held(Foo(X: ?v))
  rule bazTypeFindsType(1) :- heldBaz(Baz[])
  rule bazInstanceFindsType(1) :- heldBaz(Baz())
end
"#;

/// An eponymous or free-standing entity — one name that is both a sort and its
/// constructor — has a type face too, so its TYPE and its INSTANCE are two terms. The
/// collision measured at the start of WI-20260902-JB6RS: over `entity Foo(X: X)`, whose
/// field is labelled like its sort's parameter, `fact held(Foo[X = Int64])` was found by
/// the instance pattern `held(Foo(X: ?v))`; and over a fieldless `entity Baz`, `Baz[]`
/// and `Baz()` were one term.
///
/// BACKED OUT (`type_context_face` minting for nested constructors only): both instance
/// rows answer 1. The four readers that compare a symbol read off a type against a
/// declaration, each made to read the declaration when this population got its faces,
/// are driven by the suites that found them, each failing ALONE when its `.plain()` is
/// backed out (measured):
///  * `subtype::variant_at_its_sort` — the widen never reaches the owner and recurses:
///    `wi1056_rule_body_type_check_test::all_four_spellings_of_one_type_conform_alike`
///    overflows its stack;
///  * `load::find_operation_in_sort` — a member of an eponymous sort is not found by dot
///    dispatch: three rows of `wi979` (`both_orders_dispatch_the_secondary_entrys_member`,
///    `both_orders_record_the_same_categories`,
///    `neither_order_defines_a_phantom_nested_constructor`);
///  * `KnowledgeBase::sort_has_constructors` — `wi_f8pyz_spec_clause_alias_test::
///    the_reflect_view_named_as_a_spec_is_refused_as_a_data_sort`, and for a nested face
///    `kb::jb6rs_type_face_reads_the_declaration_tests`;
///  * cpp-gen `collect_type_refs` — the data band loses an edge and emits a struct before
///    the one it holds: `namespace_traits_test::data_band_chains_three_levels`.
#[test]
fn an_eponymous_or_free_standing_entitys_type_is_not_its_instance() {
    let mut kb = load_kb_with(EPONYMOUS);
    let answers = |kb: &mut anthill_core::kb::KnowledgeBase, rule: &str| {
        query_unary(kb, &format!("test.jb6rs.epon.{rule}")).len()
    };
    assert_eq!(answers(&mut kb, "typeFindsType"), 1);
    assert_eq!(answers(&mut kb, "instanceFindsType"), 0, "the instance pattern does not find the type");
    assert_eq!(answers(&mut kb, "bazTypeFindsType"), 1);
    assert_eq!(answers(&mut kb, "bazInstanceFindsType"), 0, "`Baz()` does not find `Baz[]`");
}

const BY_TYPE: &str = r#"
namespace test.jb6rs.bytype
  import anthill.prelude.{Int64, List, Type, Bool}
  import anthill.reflect.{SortInfo, is_modifiable}
  import anthill.reflect.KB.{kb, facts_of, stored_facts_of}
  import anthill.reflect.typing.{extract_sort_ref}
  entity Item(n: Int64)
  fact Item(n: 1)
  fact Item(n: 2)
  sort Foo
    sort X = ?
    entity Foo(X: X)
  end
  enum Colour
    entity red
    entity green(v: Int64)
  end
  operation itemModifiable() -> Bool = is_modifiable(Item)
  operation itemTypeModifiable() -> Bool = is_modifiable(Item[])
  operation variantModifiable() -> Bool = is_modifiable(red[])
  operation byName() -> Int64 = List.length(facts_of(kb(), Item))
  operation byType() -> Int64 = List.length(facts_of(kb(), Item[]))
  operation storedByType() -> Int64 = List.length(stored_facts_of(kb(), Item[]))
  operation bareType() -> Type = Item
  operation bracketType() -> Type = Item[]
  rule faceNamesItsSort(1) :- extract_sort_ref(Foo[X = Int64], ?n), SortInfo(name: ?n)
end
"#;

/// A reader handed an entity's TYPE reads the declaration it names, so the face a type
/// carries reaches the entity's rows: `facts_of(kb(), Item[])` lists the `Item` facts as
/// `facts_of(kb(), Item)` does, and `stored_facts_of` alike; `extract_sort_ref` answers
/// the sort's NAME, so a carrier written `Foo[X = Int64]` joins `SortInfo(name: Foo)`. And
/// an operation body's bare `Item`, still read as the type until the reading of a bare
/// name flips, is the term `Item[]` is — one type, one term. `is_modifiable` asks of a
/// type, and an entity's — its own sort's, or a nested variant's — is one.
///
/// BACKED OUT, each alone (measured): `type_value_decl` answering the face
/// (`value_functor`) — `byType` and `storedByType` answer 0, in silence, and with the bare
/// name below also faced, so does `byName`; `extract_sort_ref` keeping the face —
/// `faceNamesItsSort` answers 0; the bare free-standing name built as the plain
/// `Ref(Item)` in `reduce_var` — `bareType` and `bracketType` are two terms;
/// `is_modifiable`'s sort test comparing the face against its own owner — the three
/// `is_modifiable` calls are refused as data.
#[test]
fn a_reader_handed_an_entitys_type_reads_its_declaration() {
    let mut interp = interp_for(BY_TYPE);
    let count = |interp: &mut anthill_core::eval::Interpreter, op: &str| match interp
        .call(&format!("test.jb6rs.bytype.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op} runs: {e:?}"))
    {
        Value::Int(n) => n,
        other => panic!("{op}: expected an Int64, got {other:?}"),
    };
    assert_eq!(count(&mut interp, "byName"), 2, "the bare name lists the facts");
    assert_eq!(count(&mut interp, "byType"), 2, "`Item[]` lists the facts");
    assert_eq!(count(&mut interp, "storedByType"), 2, "and `stored_facts_of` alike");
    for op in ["itemModifiable", "itemTypeModifiable", "variantModifiable"] {
        match interp.call(&format!("test.jb6rs.bytype.{op}"), &[]) {
            Ok(Value::Bool(false)) => {}
            other => panic!("{op}: `is_modifiable` reads an entity's type, which holds no cell: {other:?}"),
        }
    }
    let term_of = |interp: &mut anthill_core::eval::Interpreter, op: &str| match interp
        .call(&format!("test.jb6rs.bytype.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op} runs: {e:?}"))
    {
        Value::Term { id, .. } => id,
        other => panic!("{op}: expected the type as a term, got {other:?}"),
    };
    assert_eq!(
        term_of(&mut interp, "bareType"),
        term_of(&mut interp, "bracketType"),
        "an operation body's bare `Item` is the type `Item[]` is"
    );
    let mut kb = load_kb_with(BY_TYPE);
    assert_eq!(
        query_unary(&mut kb, "test.jb6rs.bytype.faceNamesItsSort").len(),
        1,
        "`extract_sort_ref(Foo[X = Int64])` names the sort `SortInfo` records"
    );
}
