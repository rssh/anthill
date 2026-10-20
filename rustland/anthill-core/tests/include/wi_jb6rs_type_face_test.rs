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
/// `Fn{Int64}` and its `Ref(Int64)` are one term since the gate in `alloc` went (step 6),
/// and before it the matcher read them as one head — the rows pin that it stays so.
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
  operation itemTypeModifiable() -> Bool = is_modifiable(Item[])
  operation variantModifiable() -> Bool = is_modifiable(red[])
  operation byType() -> Int64 = List.length(facts_of(kb(), Item[]))
  operation storedByType() -> Int64 = List.length(stored_facts_of(kb(), Item[]))
  operation bracketType() -> Type = Item[]
  rule faceNamesItsSort(1) :- extract_sort_ref(Foo[X = Int64], ?n), SortInfo(name: ?n)
end
"#;

/// A reader handed an entity's TYPE reads the declaration it names, so the face a type
/// carries reaches the entity's rows: `facts_of(kb(), Item[])` lists the `Item` facts, and
/// `stored_facts_of` alike; `extract_sort_ref` answers the sort's NAME, so a carrier
/// written `Foo[X = Int64]` joins `SortInfo(name: Foo)`. `Item[]` in an operation body is
/// the term every type producer builds. `is_modifiable` asks of a type, and an entity's —
/// its own sort's, or a nested variant's — is one.
///
/// BACKED OUT, each alone (measured): `type_value_decl` answering the face
/// (`value_functor`) — `byType` and `storedByType` answer 0, in silence; `extract_sort_ref`
/// keeping the face — `faceNamesItsSort` answers 0; `is_modifiable`'s sort test comparing
/// the face against its own owner — the two `is_modifiable` calls are refused as data.
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
    assert_eq!(count(&mut interp, "byType"), 2, "`Item[]` lists the facts");
    assert_eq!(count(&mut interp, "storedByType"), 2, "and `stored_facts_of` alike");
    for op in ["itemTypeModifiable", "variantModifiable"] {
        match interp.call(&format!("test.jb6rs.bytype.{op}"), &[]) {
            Ok(Value::Bool(false)) => {}
            other => panic!("{op}: `is_modifiable` reads an entity's type, which holds no cell: {other:?}"),
        }
    }
    let item = interp
        .kb()
        .try_resolve_symbol("test.jb6rs.bytype.Item")
        .expect("Item resolves");
    let the_type = interp.kb_mut().make_sort_ref(item);
    match interp.call("test.jb6rs.bytype.bracketType", &[]).expect("bracketType runs") {
        Value::Term { id, .. } => assert_eq!(id, the_type, "`Item[]` is the type every producer builds"),
        other => panic!("expected the type as a term, got {other:?}"),
    }
    let mut kb = load_kb_with(BY_TYPE);
    assert_eq!(
        query_unary(&mut kb, "test.jb6rs.bytype.faceNamesItsSort").len(),
        1,
        "`extract_sort_ref(Foo[X = Int64])` names the sort `SortInfo` records"
    );
}

const READING: &str = r#"
namespace test.jb6rs.reading
  import anthill.prelude.{Int64, Type, Option}
  import anthill.reflect.{Term}
  enum Colour
    entity red
    entity green(v: Int64)
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  entity account(id: Int64, name: Int64)
  entity Baz
  entity Item(n: Int64)
  entity TypeBox(t: Type)
  entity holdsQ(pattern: Term)
  sort Solo
    entity Solo
  end
  entity Cfg(x: Option[T = Int64])
  entity ListLiteral
  fact holdsQ(pattern: account)
  fact p(account(id: 1, name: 2))
  fact heldAcct(account)
  fact boxed(Box[V = red])
  fact boxedItem(Box[V = Item])
  fact heldT(Item[])
  fact TypeBox(t: Item[])
  rule bareFindsInstance(1) :- p(account)
  rule bindsInstance(?t) :- ?t <=> account
  rule bareBindingInBody(1) :- boxed(Box[V = red])
  rule fieldedBindingIsTheType(1) :- boxedItem(Box[V = Item[]])
  rule quotedMatches(1) :- holdsQ(pattern: account)
  rule bareIsNotTheType(1) :- heldT(Item)
  rule bracketIsTheType(1) :- heldT(Item[])
  rule typedFieldHoldsTheType(1) :- TypeBox(t: Item[])
  operation bazInstance() -> Baz = Baz
  operation bazApplied() -> Baz = Baz()
  operation bazType() -> Type = Baz[]
  operation soloInstance() -> Solo = Solo
  operation cfgInstance() -> Cfg = Cfg
end
"#;

/// A BARE constructor name in a DATA context is its INSTANCE (kernel-language.md §4.4): in
/// a clause's data slot `p(account)` is `p(account())`, the pattern with every field
/// fresh — so `?t <=> account` binds that pattern, which a ground `account(…)` unifies —
/// and in an operation body `Baz` is `Baz()`. Its TYPE is written `Item[]`, and the two
/// never meet: `heldT(Item[])` is not found by `heldT(Item)`. A bracket's BINDING is a
/// type context in a rule body as in a clause, so `:- boxed(Box[V = red])` finds the fact
/// that wrote it so. And an entity's type in a `Type` field is a type, with no field filled
/// (an instance there, `TypeBox(t: Item(n: ?))`, the typer refuses).
///
/// BACKED OUT, each part alone (measured), this row fails — at the assertion the part is
/// for — under every one of them:
///  * the canon making an entity's nullary application its bare name, or its reflect-form
///    exemption read by last segment (`is_reflect_form_functor`): the store rows;
///  * the clause converter's data-slot reading (`Loader::bare_name_term`), or its bracket
///    gate: `heldAcct`, `fieldedBindingIsTheType` (and `wi_vnwaw`'s data-slot row);
///  * the rule-body walk's data-slot reading (`body_data_slot_name`): its instance arm —
///    `bindsInstance` (and `wi_czj2n` F, `wi_vnwaw`); its type arm — `bareBindingInBody`;
///    its quoted-field gate — `quotedMatches`;
///  * the query walk's (`query_data_slot_name`), or its bracket gate: the query rows;
///  * the typer's and eval's bare constructor arms asking `is_constructor_symbol`, eval's
///    sort arm reading an eponymous entity as its type, its nullary gate counting fields
///    rather than non-`Option` fields: the operation-body rows;
///  * the clause bracket's entity fill: the module does not load (`TypeBox(t: Item[])` is
///    "expected Type, got Item").
/// `bareFindsInstance` passes either way BY DESIGN — the goal is matched by head, and the
/// reference heads as the application does — and is the control that the fact is found.
#[test]
fn a_bare_constructor_in_a_data_context_is_its_instance() {
    let mut kb = load_kb_with(READING);
    let answers = |kb: &mut anthill_core::kb::KnowledgeBase, rule: &str| {
        query_unary(kb, &format!("test.jb6rs.reading.{rule}")).len()
    };
    assert_eq!(answers(&mut kb, "bareFindsInstance"), 1, "`p(account)` is `p(account())`");
    assert_eq!(answers(&mut kb, "bareBindingInBody"), 1, "a body's bracket binding is the type");
    assert_eq!(answers(&mut kb, "bareIsNotTheType"), 0, "the bare name is not the type");
    assert_eq!(answers(&mut kb, "bracketIsTheType"), 1, "`Item[]` is");
    assert_eq!(answers(&mut kb, "typedFieldHoldsTheType"), 1, "a `Type` field holds the type");
    assert_eq!(
        answers(&mut kb, "fieldedBindingIsTheType"),
        1,
        "a fielded entity as a clause's bracket binding is its type, not its pattern"
    );
    assert_eq!(
        answers(&mut kb, "quotedMatches"),
        1,
        "a quoted `Term` field keeps the name as written in the goal as in the fact"
    );
    let config = ResolveConfig {
        max_solutions: 4,
        ..ResolveConfig::default()
    };
    let ground = query_pattern_term(
        &mut kb,
        "test.jb6rs.reading.bindsInstance(test.jb6rs.reading.account(id: 3, name: 4))",
    );
    assert_eq!(
        kb.resolve(&[ground], &config).len(),
        1,
        "`?t <=> account` binds the all-fields-fresh pattern, which a ground account unifies"
    );
    for (pattern, want, what) in [
        (
            "test.jb6rs.reading.heldAcct(test.jb6rs.reading.account(id: 9, name: 9))",
            1,
            "a fact's `heldAcct(account)` holds the pattern, which any account unifies",
        ),
        (
            "test.jb6rs.reading.p(test.jb6rs.reading.account)",
            1,
            "a query's `p(account)` is `p(account())`",
        ),
        (
            "test.jb6rs.reading.boxedItem(test.jb6rs.reading.Box[V = test.jb6rs.reading.Item])",
            1,
            "a query's bracket binding is the type",
        ),
    ] {
        let goal = query_pattern_term(&mut kb, pattern);
        assert_eq!(kb.resolve(&[goal], &config).len(), want, "{what}");
    }
    // A fieldless constructor's two spellings are ONE TERM — the canon in the store.
    let baz_sym = kb
        .try_resolve_symbol("test.jb6rs.reading.Baz")
        .expect("Baz resolves");
    let applied = kb.alloc(Term::Fn {
        functor: baz_sym,
        pos_args: Default::default(),
        named_args: Default::default(),
    });
    assert_eq!(applied, kb.alloc(Term::Ref(baz_sym)), "`Baz()` and `Baz` are one term");
    // A user's own entity named like a reflect form is an ordinary entity.
    let own = kb
        .try_resolve_symbol("test.jb6rs.reading.ListLiteral")
        .expect("the user's ListLiteral resolves");
    let own_applied = kb.alloc(Term::Fn {
        functor: own,
        pos_args: Default::default(),
        named_args: Default::default(),
    });
    assert_eq!(own_applied, kb.alloc(Term::Ref(own)), "a user's `ListLiteral()` is its bare name");

    let mut interp = interp_for(READING);
    let baz = interp
        .kb()
        .try_resolve_symbol("test.jb6rs.reading.Baz")
        .expect("Baz resolves");
    let head_of = |interp: &mut anthill_core::eval::Interpreter, op: &str| {
        let v = interp
            .call(&format!("test.jb6rs.reading.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op} runs: {e:?}"));
        anthill_core::eval::value_functor(interp.kb(), &v).unwrap_or_else(|| panic!("{op}: {v:?}"))
    };
    assert_eq!(head_of(&mut interp, "bazInstance"), baz, "an operation body's `Baz` is the instance");
    assert_eq!(head_of(&mut interp, "bazApplied"), baz, "as `Baz()` is");
    let ty = head_of(&mut interp, "bazType");
    assert!(ty.is_type_face() && ty.plain() == baz, "`Baz[]` is the type: {ty:?}");
    let solo = interp
        .kb()
        .try_resolve_symbol("test.jb6rs.reading.Solo")
        .expect("Solo resolves");
    assert_eq!(head_of(&mut interp, "soloInstance"), solo, "an eponymous entity's bare name is its instance");
    let cfg = interp
        .kb()
        .try_resolve_symbol("test.jb6rs.reading.Cfg")
        .expect("Cfg resolves");
    assert_eq!(
        head_of(&mut interp, "cfgInstance"),
        cfg,
        "an entity whose every field is an `Option` is built bare, its fields `none`"
    );
}

/// The bare name of a constructor that takes fields, in an operation body, is an
/// INCOMPLETE construction, refused as `Item()` is — it is no longer the type, which is
/// `Item[]`. The step that made the type the bracket's moved every `facts_of(kb(), X)` of
/// this repository to `X[]`; this is what an unmoved one meets.
///
/// BACKED OUT, each alone (measured), this row fails: the refusal itself; its own load
/// error class (rendered as a field's type mismatch); the typer's bare constructor arm
/// asking `is_constructor_symbol`. A positional argument read as covering the field at its
/// own index fails the mixed control here and thirteen rows of `wi_t2470` / `wi_1f0qp`;
/// the refusal returned alone, ahead of the supplied fields' own mismatches, fails
/// `wi_akkwf`'s marker-call row.
#[test]
fn a_bare_fielded_entity_in_an_operation_body_is_refused() {
    let errs = load_errors_of(
        "namespace test.jb6rs.refused\n  import anthill.prelude.{Int64, Type}\n  \
         entity Item(n: Int64)\n  operation ty() -> Type = Item\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("`Item` is constructed without its field `n`")),
        "the bare `Item` is refused as the construction it is: {errs:?}"
    );
    let unrendered = crate::common::unrendered_load_errors_of(
        "namespace test.jb6rs.refused\n  import anthill.prelude.{Int64, Type}\n  \
         entity Item(n: Int64)\n  operation ty() -> Type = Item\nend\n",
    );
    assert!(
        unrendered.iter().any(|e| matches!(
            e.peel(),
            anthill_core::kb::load::LoadError::IncompleteConstruction { ctor, missing, .. }
                if ctor == "Item" && missing == &["n".to_string()]
        )),
        "its own class, naming the constructor and the field: {unrendered:?}"
    );
    let applied = load_errors_of(
        "namespace test.jb6rs.refused\n  import anthill.prelude.{Int64, Type}\n  \
         entity Item(n: Int64)\n  operation ty() -> Type = Item()\nend\n",
    );
    assert_eq!(errs, applied, "as its applied spelling is, with the same diagnostic");
    // The control: a positional argument takes the field no name took, so a MIXED
    // construction supplies every field and loads.
    load_kb_with(
        "namespace test.jb6rs.mixed\n  import anthill.prelude.Int64\n  \
         entity two(a: Int64, b: Int64)\n  operation mk() -> two = two(1, a: 2)\nend\n",
    );
}

/// `kind` reports a constructor's TYPE as a sort and its instance as the entity, in the
/// interpreter's operation and in the resolver's builtin, which read one table
/// (`KnowledgeBase::reflect_kind`). The typed surface hands `kind` a `Symbol`, and refuses
/// a `Type` there; a face reaches it from a host call and from an untyped goal.
///
/// BACKED OUT (`reflect_kind` answering `kind_of`, which does not see the face): both
/// type rows report `Entity`. The instance rows pass either way BY DESIGN.
#[test]
fn kind_reports_a_type_face_as_a_sort() {
    let mut interp = interp_for(SRC);
    let red = interp
        .kb()
        .try_resolve_symbol("test.jb6rs.face.Colour.red")
        .expect("red resolves");
    let the_type = interp.kb_mut().make_sort_ref(red);
    let the_instance = interp.kb_mut().alloc(Term::Ref(red));
    let kind_of = |interp: &mut anthill_core::eval::Interpreter, t| match interp
        .call("anthill.reflect.kind", &[Value::term(t)])
        .expect("kind runs")
    {
        Value::Str(s) => s,
        other => panic!("kind answers a String, got {other:?}"),
    };
    assert_eq!(kind_of(&mut interp, the_type), "Sort", "the type `red[]` is a sort");
    assert_eq!(kind_of(&mut interp, the_instance), "Entity", "the instance `red` is the entity");

    let mut kb = load_kb_with(SRC);
    let config = ResolveConfig {
        max_solutions: 4,
        ..ResolveConfig::default()
    };
    for (pattern, want) in [
        ("anthill.reflect.kind(test.jb6rs.face.Colour.red[], \"Sort\")", 1),
        ("anthill.reflect.kind(test.jb6rs.face.Colour.red[], \"Entity\")", 0),
        ("anthill.reflect.kind(test.jb6rs.face.Colour.red, \"Entity\")", 1),
    ] {
        let goal = query_pattern_term(&mut kb, pattern);
        assert_eq!(kb.resolve(&[goal], &config).len(), want, "the resolver's builtin: {pattern}");
    }
}

const STORED_DECLS: &str = r#"
  import anthill.prelude.{Int64, Type, List, Option}
  entity Item(n: Int64)
  entity Bare
  sort Foo
    sort X = ?
    entity Foo(X: X)
  end
  entity TypeHolder(t: Type, ts: List[T = Type])
  entity BoundHolder(t: Type)
"#;

/// A type written as data survives the JSON store: the writer spells an entity's type by
/// its qualified name, and the reader, under a field declared `Type`, builds the type that
/// name denotes — so the reloaded fact is found by the bracket and is the fact it was. A
/// sort's type (`Int64`) is read back the same way. A type WITH bindings has no flat form
/// and is refused at the writer, loudly, rather than written as the instance it would
/// reload as.
///
/// A string naming no type under such a field is refused, not read as a string.
///
/// BACKED OUT, each alone (measured), this row fails: the reader's `Type` arm, or its
/// refusal of a name that is no type; the writer's arm qualifying a type, or asking
/// `Option.none` before it (`none[]` became JSON `null`), or its refusal of a type with
/// bindings; the clause bracket's entity fill (the fixture does not load); the fact-field
/// check's type-face arm; and `bare_entity_slots`' face guard, which keeps the reload's
/// `Item[]` from being expanded into a pattern.
#[test]
fn a_type_in_the_json_store_reads_back_as_the_type() {
    use anthill_core::persistence::term_ser;
    let mut kb = load_kb_with(&format!(
        "namespace test.jb6rs.stored{STORED_DECLS}  fact TypeHolder(t: Item[], ts: [Bare[], Int64, Option.none[]])\nend\n"
    ));
    let holder = kb
        .try_resolve_symbol("test.jb6rs.stored.TypeHolder")
        .expect("TypeHolder resolves");
    let rids = kb.rules_by_functor(holder);
    let json = term_ser::serialize_json(&kb, "test.jb6rs.stored.TypeHolder", &rids).expect("serializes");
    assert!(
        json.contains("\"test.jb6rs.stored.Item\""),
        "the type is written by its qualified name: {json}"
    );
    let mut reloaded = load_kb_with(&format!("namespace test.jb6rs.stored{STORED_DECLS}end\n"));
    let domain = reloaded.intern("test.jb6rs.stored");
    term_ser::load_json(&mut reloaded, &json, domain).expect("loads back");
    let config = ResolveConfig {
        max_solutions: 4,
        ..ResolveConfig::default()
    };
    let goal = query_pattern_term(
        &mut reloaded,
        "test.jb6rs.stored.TypeHolder(t: test.jb6rs.stored.Item[], \
         ts: [test.jb6rs.stored.Bare[], anthill.prelude.Int64, anthill.prelude.Option.none[]])",
    );
    assert_eq!(reloaded.resolve(&[goal], &config).len(), 1, "the reloaded fact is the one written: {json}");

    let unknown = term_ser::load_json(
        &mut reloaded,
        r#"{ "meta": { "entity": "test.jb6rs.stored.TypeHolder" },
             "data": { "t": "no.such.Sort", "ts": [] } }"#,
        domain,
    );
    assert!(
        matches!(&unknown, Err(errs) if errs.iter().any(|e| format!("{e:?}").contains("names no sort"))),
        "a `Type` field naming no type is refused, not read as a string: {unknown:?}"
    );

    let mut bound = load_kb_with(&format!(
        "namespace test.jb6rs.boundstored{STORED_DECLS}  fact BoundHolder(t: Foo[X = Int64])\nend\n"
    ));
    let holder = bound
        .try_resolve_symbol("test.jb6rs.boundstored.BoundHolder")
        .expect("BoundHolder resolves");
    let rids = bound.rules_by_functor(holder);
    let refused = term_ser::serialize_json(&bound, "test.jb6rs.boundstored.BoundHolder", &rids);
    assert!(
        matches!(&refused, Err(e) if format!("{e:?}").contains("cannot be represented")),
        "a type with bindings is refused at the writer: {refused:?}"
    );
}

/// A field declared at a DATA sort holds its instances, and the typer refuses anything
/// else there, in a fact as in a body: an instance of another sort — a free-standing
/// entity's `Alpha()` too, the one term with its bare name since the two spellings were
/// made one — and a TYPE written as data (`red[]`). A `Type` field holds the type.
///
/// BACKED OUT, each alone (measured): the fact-field check's `Ref` arm asking
/// `is_constructor_symbol` — `c: Alpha()` loads (and `wi830`'s role row with it); its
/// type-face arm — `c: red[]` loads; its advice where a type is declared — the message
/// does not say `Alpha[]`.
#[test]
fn a_data_field_refuses_a_type_and_a_foreign_instance() {
    let errs = load_errors_of(
        "namespace test.jb6rs.fields\n  import anthill.prelude.Type\n  enum Colour\n    \
         entity red\n    entity green\n  end\n  entity Alpha\n  entity Holder(c: Colour)\n  \
         entity TypeBox(t: Type)\n  fact Holder(c: Alpha())\n  fact Holder(c: red[])\n  \
         fact TypeBox(t: red[])\n  fact TypeBox(t: Alpha())\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("Holder.c") && e.contains("got Alpha")),
        "an instance of another sort: {errs:?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("Holder.c") && e.contains("got Type (red[])")),
        "a type written as data: {errs:?}"
    );
    assert_eq!(
        errs.iter().filter(|e| e.contains("TypeBox")).count(),
        1,
        "a `Type` field holds the type, and refuses only the instance: {errs:?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("TypeBox.t") && e.contains("TYPE is written `Alpha[]`")),
        "an instance where a type is declared is told how the type is written: {errs:?}"
    );
}

const SORT_APPS: &str = r#"
namespace test.jb6rs.sortapp
  import anthill.prelude.{Int64, Eq, List}
  sort Shape
    entity circle(r: Int64)
  end
  fact holds(Shape[])
  fact Eq[T = Int64]
  fact listy(List[T = Int64])
  rule bareFindsBracket(1) :- holds(Shape)
  rule bracketFindsBracket(1) :- holds(Shape[])
  rule eqByBracket(?q) :- Eq[T = ?q]
end
"#;

/// A sort with no constructor of its name has ONE reading, its type: its bare name and its
/// empty bracket are one term (`Shape` is `Shape[]`, the canon in `alloc` exempting no sort
/// since step 6), and its PARENTHESIZED spelling names nothing to apply — `Shape()` and
/// `Eq(T: ?q)` are refused in a clause and in a query, where they used to be the type
/// silently (`Eq(T: ?q)` answered from `fact Eq[T = Int64]`). A sort that is also an
/// operation is applied as the operation. And its type, printed as data, takes the bracket
/// — `List[T = Int64]` — which reloads as itself where `List(T: Int64)` would be refused.
///
/// BACKED OUT, each alone (measured), this row fails: the canon keeping a sort's nullary
/// `Fn` (and five rows that pin the one term: `map_arena`, `execute`, `wi1028`,
/// `term_view`, `wi_n3w68`); the clause refusal (and `wi_s8jyf`, `wi_q0093`), the rule-body
/// walk's, or the query's; the query's quoted-field gate; `names_only_a_type` counting an
/// operation's name (the `Both` control is refused); the printer's type arm, or the parse
/// side's written bracket. The clause refusal's `Off` gate fails `wi_5g28a` (an operation
/// body's application is the typer's to refuse, and was reported twice). The single
/// report passes either way BY DESIGN — measured, no rule-body argument reached the
/// refusal twice, so the record that would have deduplicated it was not kept.
#[test]
fn a_sort_has_one_reading_and_names_nothing_to_apply() {
    use anthill_core::persistence::print;
    let mut kb = load_kb_with(SORT_APPS);
    let answers = |kb: &mut anthill_core::kb::KnowledgeBase, rule: &str| {
        query_unary(kb, &format!("test.jb6rs.sortapp.{rule}")).len()
    };
    assert_eq!(answers(&mut kb, "bareFindsBracket"), 1, "`Shape` is `Shape[]`");
    assert_eq!(answers(&mut kb, "bracketFindsBracket"), 1);
    assert_eq!(answers(&mut kb, "eqByBracket"), 1, "the bracket goal answers from the fact");
    let shape = kb
        .try_resolve_symbol("test.jb6rs.sortapp.Shape")
        .expect("Shape resolves");
    let applied = kb.alloc(Term::Fn {
        functor: shape,
        pos_args: Default::default(),
        named_args: Default::default(),
    });
    assert_eq!(applied, kb.alloc(Term::Ref(shape)), "one term in the store");

    let refused = |decl: &str| {
        load_errors_of(&format!(
            "namespace test.jb6rs.sortapp2\n  import anthill.prelude.{{Int64, Eq}}\n  \
             sort Shape\n    entity circle(r: Int64)\n  end\n  fact holds(Shape[])\n  \
             fact Eq[T = Int64]\n  {decl}\nend\n"
        ))
    };
    for (decl, sort) in [
        ("rule viaParens(?q) :- Eq(T: ?q)", "Eq"),
        ("rule shapeNullary(1) :- holds(Shape())", "Shape"),
        ("fact holds2(Shape())", "Shape"),
    ] {
        let errs = refused(decl);
        assert_eq!(
            errs.iter().filter(|e| e.contains(&format!("`{sort}(…)` is an application"))).count(),
            1,
            "`{decl}` is refused, once: {errs:?}"
        );
    }
    // Inside a field declared `Term` the pattern is QUOTED, as written, in the fact and in
    // the query that searches for it alike.
    let mut quoted = load_kb_with(
        "namespace test.jb6rs.quoted\n  import anthill.prelude.{Int64, Eq}\n  \
         import anthill.reflect.{Term}\n  entity holdsQ(pattern: Term)\n  \
         fact holdsQ(pattern: Eq(T: 1))\nend\n",
    );
    let quoted_query =
        anthill_core::parse::parse("fact test.jb6rs.quoted.holdsQ(pattern: anthill.prelude.Eq(T: 1))")
            .expect("parses");
    let quoted_scan: Vec<String> = anthill_core::kb::load::scan_query_definitions(&mut quoted, &[&quoted_query])
        .iter()
        .map(|e| e.to_string())
        .collect();
    assert!(quoted_scan.is_empty(), "a quoted field is not judged in a query: {quoted_scan:?}");
    let config = ResolveConfig {
        max_solutions: 4,
        ..ResolveConfig::default()
    };
    let by_bracket = query_pattern_term(&mut kb, "anthill.prelude.Eq[T = ?q]");
    assert_eq!(kb.resolve(&[by_bracket], &config).len(), 1, "the query's bracket answers");
    // The query's own scan refuses its parentheses (the CLI's `--pattern` path).
    let parsed = anthill_core::parse::parse("fact anthill.prelude.Eq(T: ?q)").expect("parses");
    let scanned: Vec<String> = anthill_core::kb::load::scan_query_definitions(&mut kb, &[&parsed])
        .iter()
        .map(|e| e.to_string())
        .collect();
    assert!(
        scanned.iter().any(|e| e.contains("`Eq(…)` is an application")),
        "the query's parentheses are refused: {scanned:?}"
    );
    // A sort that is also an operation is applied as the operation: not refused.
    let mut with_op = load_kb_with(
        "namespace test.jb6rs.sortop\n  import anthill.prelude.Int64\n  sort Both\n    \
         entity mk(x: Int64)\n  end\n  operation Both(n: Int64) -> Int64 = n\n  \
         rule viaOp(?v) :- ?v <=> Both(3)\nend\n",
    );
    assert_eq!(query_unary(&mut with_op, "test.jb6rs.sortop.viaOp").len(), 1, "the operation answers");

    // The type, printed as data, takes the bracket and reloads as itself.
    let listy = kb
        .try_resolve_symbol("test.jb6rs.sortapp.listy")
        .expect("listy resolves");
    let rid = kb.rules_by_functor(listy)[0];
    let printed = print::print_fact(&kb, kb.rule_head(rid), None);
    assert!(printed.contains("List[T = Int64]"), "printed with the bracket: {printed}");
    // The parse side, with no kind table, prints a WRITTEN bracket as one.
    let parsed = anthill_core::parse::parse("fact holds(Eq[T = Int64])").expect("parses");
    let fact = parsed
        .items
        .iter()
        .find_map(|item| match item {
            anthill_core::parse::ir::Item::Fact(fact) => Some(fact.term),
            _ => None,
        })
        .expect("a fact");
    let printed = print::print_fact(&parsed, fact, None);
    assert!(printed.contains("Eq[T = Int64]"), "the parse side keeps the bracket: {printed}");
}
