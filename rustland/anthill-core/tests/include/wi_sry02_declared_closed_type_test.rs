//! WI-20261126-SRY02 — a declared type at an application, as a type the KB holds:
//! `term_ser::DeclaredType::closed_type`. A caller that reaches a constructor's field at an
//! application through `DataShape::fields` (WI-20261125-CMQJ4) compares the field's type with
//! a type it holds by `views_structurally_equal`, as the KB compares types everywhere else —
//! not by `TypeShape`s (a second definition of type equality) nor by display names.
//!
//! Each row DRIVES the reading from outside the crate: it reaches a field at an application,
//! closes its type, and compares it with the type the loader gives where the same type is
//! WRITTEN (a field or an operation's parameter spelled with the arguments substituted).
//!
//! CONTROLS, MEASURED 2026-11-27 one at a time on a binary of this file and the codec's suites
//! alone (`wi_cmqj4_declared_type_shape_test`, `wi_wc18y_value_codec_test`,
//! `wi_scpw9_set_map_spec_values_test`, `wi_9wvt7_review7_test`, `wi_jb6rs_type_face_test`,
//! `declared_field_type_readers_test`, `wi926_eponymous_entity_test`: 82 rows), each a change
//! to `closed_type`'s walk in `term_ser.rs`; every row not named passed under each:
//! - (A) The method made the codec's private reading it replaced (the substitution through a
//!   type application's bindings only, the type returned as it is wherever its place binds
//!   nothing): `a_tuple_naming_a_parameter_closes` FAILS (`t` refused as `UnboundParameter`
//!   named by the whole tuple, `(a: ?_, n: Int64)`, though its place binds `A`),
//!   `a_function_type_naming_a_parameter_is_refused` the same way,
//!   `a_parameter_free_at_depth_is_refused_by_name` FAILS (the written `Cell[T = A]` handed in
//!   comes back with `A` in it), and `a_form_the_substitution_…` FAILS (`P.Key` comes back as
//!   `P.Key`). The four rows of the ticket PASS BY DESIGN: they are what the private reading
//!   already did, and this change makes it public.
//! - (B) The substitution taken out (an application or a tuple returned as `resolve` leaves
//!   it): `a_field_at_an_application_is_the_type_written_there` FAILS at `Holder.c`
//!   (`Cell[T = A]` against the written `Cell[T = Bool]`), `a_parameter_nothing_binds_…` at
//!   the bare `Holder`'s `c`, the tuple row, the free-at-depth row, `a_form_the_substitution_…`
//!   at `ks: Cell[T = P.Key]`, and the codec's
//!   `a_spec_value_in_a_generic_place_is_read_at_its_bindings` (the place a spec value is read
//!   at). `value` at `Cell[T = Int64]` and at the bare `Cell` PASS BY DESIGN: a parameter
//!   standing alone is read by `resolve`, which `shape` reads by too.
//! - (C) Every form that holds a variable rebuilt, the first cut of this change (`/code-review`
//!   found it): `a_function_type_naming_a_parameter_is_refused` FAILS (rebuilt, not refused) and
//!   `a_form_the_substitution_…` FAILS (`P.Key` names `P` by its name, holds no variable, and
//!   came back as `P.Key`).
//! - (D) An application or a tuple rebuilt though none of its children changed:
//!   `a_type_that_names_no_parameter_comes_back_as_it_is` FAILS (an entity value where the
//!   declared term was).
//! Backing the whole change out removes the public method, and this file does not compile.
use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::op_info::lookup_operation_info;
use anthill_core::kb::term::TermId;
use anthill_core::kb::term_view::views_structurally_equal;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::term_ser::{self, DeclaredType, TypeShape, ValueProblem};

use crate::common::load_kb_with;

const DECLS: &str = r#"
namespace test.sr
  import anthill.prelude.{Int64, Bool, String}

  sort Cell[T]
    entity Cell(value: T)
  end
  sort Holder[A]
    entity Holder(c: Cell[T = A], t: (a: A, n: Int64), n: Int64, f: (x: A) -> Int64, g: (x: Int64) -> Int64, mk: MemStore.Key)
  end
  sort Held[T]
    entity Held(value: T, at: Int64)
  end

  sort Storage
    sort C = ?
    sort Key = ?
    operation get(s: C, k: Key) -> Int64
  end
  sort MemStore
    provides Storage[C = MemStore, Key = String]
    entity memStore
    operation get(s: MemStore, k: String) -> Int64 = 0
  end
  sort Wrapper
    sort P = ?
    requires Storage[C = P]
    entity wrapper(provider: P, k: P.Key, ks: Cell[T = P.Key])
  end

  entity Written(cb: Cell[T = Bool], ci: Cell[T = Int64], h: Holder[A = Bool], t: (a: Bool, n: Int64),
                 w: Wrapper[P = MemStore], ms: MemStore)

  operation observe(now: Int64, held: Held[T = Int64]) -> Bool = true
end
"#;

fn sym(kb: &KnowledgeBase, name: &str) -> Symbol {
    kb.try_resolve_symbol(name).unwrap_or_else(|| panic!("`{name}` resolves"))
}

/// The declared type of `entity.field`, as the loader gives it for the field as written.
fn field_type(kb: &KnowledgeBase, entity: &str, field: &str) -> Value {
    kb.entity_field_types(sym(kb, entity))
        .expect("declared fields")
        .iter()
        .find(|(f, _)| kb.local_name_of(*f) == field)
        .map(|(_, t)| t.clone())
        .unwrap_or_else(|| panic!("`{entity}` declares `{field}`"))
}

/// The declared type of `op`'s parameter `param`, as the loader gives it.
fn param_type(kb: &KnowledgeBase, op: &str, param: &str) -> Value {
    lookup_operation_info(kb, sym(kb, op))
        .unwrap_or_else(|| panic!("`{op}` is declared"))
        .params
        .into_iter()
        .find(|(p, _)| kb.local_name_of(*p) == param)
        .map(|(_, t)| t)
        .unwrap_or_else(|| panic!("`{op}` declares `{param}`"))
}

/// The type a text names, as a data file's `meta.entity` is read.
fn ty(kb: &mut KnowledgeBase, text: &str) -> TermId {
    term_ser::type_from_text(kb, text).unwrap_or_else(|e| panic!("`{text}`: {e}"))
}

/// The field `name` of the one constructor of the data type `ty`, at the type.
fn field_at(kb: &KnowledgeBase, ty: &DeclaredType, name: &str) -> DeclaredType {
    let TypeShape::Data(data) = ty.shape(kb).unwrap_or_else(|p| panic!("a data type: {p}")) else {
        panic!("a data type")
    };
    let [ctor] = data.constructors() else {
        panic!("one constructor, found {:?}", data.constructors())
    };
    data.fields(kb, *ctor)
        .unwrap_or_else(|p| panic!("fields: {p}"))
        .into_iter()
        .find(|(f, _)| kb.local_name_of(*f) == name)
        .map(|(_, t)| t)
        .unwrap_or_else(|| panic!("a field `{name}`"))
}

fn closed(kb: &KnowledgeBase, ty: &DeclaredType) -> Value {
    ty.closed_type(kb)
        .unwrap_or_else(|p| panic!("`{}` closes: {p}", ty.display_name(kb)))
}

#[test]
fn a_field_at_an_application_is_the_type_written_there() {
    let kb = load_kb_with(DECLS);
    // (1) `Cell`'s `value: T` at `Cell[T = Int64]` is the loader's `Int64`: the ticket's
    // scenario, a field of `Held[T = Int64]` reached through an operation's signature beside
    // a parameter `now: Int64`, and the same reading at a field's type.
    let now = param_type(&kb, "test.sr.observe", "now");
    let held = DeclaredType::closed(&param_type(&kb, "test.sr.observe", "held"));
    let value = closed(&kb, &field_at(&kb, &held, "value"));
    assert!(views_structurally_equal(&kb, &value, &now), "`Held.value` at `Held[T = Int64]` is `now`'s type");
    let at = closed(&kb, &field_at(&kb, &held, "at"));
    assert!(views_structurally_equal(&kb, &at, &now), "`Held.at`, written `Int64`, is `now`'s type");
    let cell = DeclaredType::closed(&field_type(&kb, "test.sr.Written", "ci"));
    let value = closed(&kb, &field_at(&kb, &cell, "value"));
    assert!(views_structurally_equal(&kb, &value, &now), "`Cell.value` at `Cell[T = Int64]`");
    // Not equal to another type: the comparison is not vacuous.
    let bool_cell = DeclaredType::closed(&field_type(&kb, "test.sr.Written", "cb"));
    let bool_value = closed(&kb, &field_at(&kb, &bool_cell, "value"));
    assert!(!views_structurally_equal(&kb, &bool_value, &now), "`Cell.value` at `Cell[T = Bool]` is not `Int64`");

    // (2) `Holder`'s `c: Cell[T = A]` at `Holder[A = Bool]` is the loader's `Cell[T = Bool]`.
    // FAILS with the substitution taken out.
    let holder = DeclaredType::closed(&field_type(&kb, "test.sr.Written", "h"));
    let c = closed(&kb, &field_at(&kb, &holder, "c"));
    let written = field_type(&kb, "test.sr.Written", "cb");
    assert!(
        views_structurally_equal(&kb, &c, &written),
        "`Holder.c` at `Holder[A = Bool]` is the written `Cell[T = Bool]`"
    );
    assert!(
        !views_structurally_equal(&kb, &c, &field_type(&kb, "test.sr.Written", "ci")),
        "and not `Cell[T = Int64]`"
    );
}

/// The one value on its one carrier: the same hash-consed term, or the same occurrence. A
/// field's type rides a term, or under `ANTHILL_TEST_NODE_CARRIER=1` the occurrence of the
/// alias written there; "as it is" means either, unrebuilt.
fn same_carrier(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Term { id: x, .. }, Value::Term { id: y, .. }) => x == y,
        (Value::Node(x), Value::Node(y)) => Rc::ptr_eq(x, y),
        _ => false,
    }
}

#[test]
fn a_type_that_names_no_parameter_comes_back_as_it_is() {
    let kb = load_kb_with(DECLS);
    // (3) `Holder.n: Int64` at `Holder[A = Bool]`: the place binds `A`, the type names none of
    // it, and the type is the declared one on its carrier.
    let holder = DeclaredType::closed(&field_type(&kb, "test.sr.Written", "h"));
    let declared = field_type(&kb, "test.sr.Holder", "n");
    let n = closed(&kb, &field_at(&kb, &holder, "n"));
    assert!(same_carrier(&n, &declared), "`n` is the declared `Int64` itself, found {n:?}");
    // A function type, and a projection off a sort, that name none of it. The projection's
    // member is a parameter of the spec it projects (`Storage.Key`): only a projection's
    // SUBJECT names a parameter of a place.
    for f in ["g", "mk"] {
        let declared = field_type(&kb, "test.sr.Holder", f);
        let back = closed(&kb, &field_at(&kb, &holder, f));
        assert!(same_carrier(&back, &declared), "`{f}` is the declared type itself, found {back:?}");
    }
    // A type handed in closed, at a place that binds nothing.
    let cb = field_type(&kb, "test.sr.Written", "cb");
    let back = closed(&kb, &DeclaredType::closed(&cb));
    assert!(same_carrier(&back, &cb), "`Cell[T = Bool]` comes back as it is, found {back:?}");
}

#[test]
fn a_parameter_nothing_binds_is_refused_by_name() {
    let mut kb = load_kb_with(DECLS);
    // (4) `Cell` with `T` neither written nor defaulted: `value` is refused, by `T`.
    let bare = DeclaredType::closed(&ty(&mut kb, "test.sr.Cell"));
    assert_eq!(
        field_at(&kb, &bare, "value").closed_type(&kb).expect_err("T is open"),
        ValueProblem::UnboundParameter { name: "T".into() }
    );
    // At depth: `Holder.c: Cell[T = A]` at a bare `Holder` is refused by `A` at `c` itself,
    // where `shape` refuses it only once a walk reaches `c`'s `value`.
    let bare = DeclaredType::closed(&ty(&mut kb, "test.sr.Holder"));
    assert_eq!(
        field_at(&kb, &bare, "c").closed_type(&kb).expect_err("A is open"),
        ValueProblem::UnboundParameter { name: "A".into() }
    );
}

#[test]
fn a_parameter_free_at_depth_is_refused_by_name() {
    let kb = load_kb_with(DECLS);
    // The field type as WRITTEN (`Cell[T = A]`, in `Holder`'s parameter), handed in for the
    // type at an application: `A` is free in it, and refused by the parameter's name. FAILS
    // under the private reading, which returned a type handed in closed as it was.
    let as_written = DeclaredType::closed(&field_type(&kb, "test.sr.Holder", "c"));
    assert_eq!(
        as_written.closed_type(&kb).expect_err("A is free"),
        ValueProblem::UnboundParameter { name: "A".into() }
    );
}

#[test]
fn a_tuple_naming_a_parameter_closes() {
    let kb = load_kb_with(DECLS);
    // `Holder.t: (a: A, n: Int64)` at `Holder[A = Bool]` is the written `(a: Bool, n: Int64)`.
    // FAILS under the private reading (refused as an unbound parameter, though `A` is bound)
    // and with the substitution taken out.
    let holder = DeclaredType::closed(&field_type(&kb, "test.sr.Written", "h"));
    let t = closed(&kb, &field_at(&kb, &holder, "t"));
    assert!(
        views_structurally_equal(&kb, &t, &field_type(&kb, "test.sr.Written", "t")),
        "`Holder.t` at `Holder[A = Bool]` is the written `(a: Bool, n: Int64)`"
    );
}

#[test]
fn a_form_the_substitution_does_not_go_through_is_refused_where_it_names_a_parameter() {
    let kb = load_kb_with(DECLS);
    // `Wrapper.k: P.Key` at `Wrapper[P = MemStore]`: the projection names `P` by its name,
    // and substituted in it would be a projection off `MemStore` that is not the term the
    // loader writes for `MemStore.Key`. Refused, as `shape` refuses it — at the field and
    // inside an application (`ks: Cell[T = P.Key]`) — where it used to come back as `P.Key`.
    // FAILS under the private reading and under the first cut of this change (both returned
    // `P.Key`, unequal to everything the caller holds).
    let wrapper = DeclaredType::closed(&field_type(&kb, "test.sr.Written", "w"));
    assert_eq!(
        field_at(&kb, &wrapper, "k").closed_type(&kb).expect_err("P.Key is not substituted in"),
        ValueProblem::NoDataSpelling
    );
    assert_eq!(field_at(&kb, &wrapper, "k").shape(&kb).expect_err("shape agrees"), ValueProblem::NoDataSpelling);
    assert_eq!(
        field_at(&kb, &wrapper, "ks").closed_type(&kb).expect_err("nor inside an application"),
        ValueProblem::NoDataSpelling
    );
    // The parameter itself, standing alone, is substituted.
    let provider = closed(&kb, &field_at(&kb, &wrapper, "provider"));
    assert!(views_structurally_equal(&kb, &provider, &field_type(&kb, "test.sr.Written", "ms")), "`provider` is `MemStore`");
}

#[test]
fn a_function_type_naming_a_parameter_is_refused() {
    let kb = load_kb_with(DECLS);
    // `Holder.f: (x: A) -> Int64` at `Holder[A = Bool]`: not substituted in, as `P.Key` is
    // not. FAILS under the first cut of this change, which rebuilt it, and under the private
    // reading, which refused it as an unbound parameter named by the whole function type.
    let holder = DeclaredType::closed(&field_type(&kb, "test.sr.Written", "h"));
    assert_eq!(
        field_at(&kb, &holder, "f").closed_type(&kb).expect_err("a function type is not substituted in"),
        ValueProblem::NoDataSpelling
    );
}
