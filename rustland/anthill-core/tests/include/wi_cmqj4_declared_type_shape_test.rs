//! WI-20261125-CMQJ4 — a constructor's field types at an application of its sort, read through
//! the codec's own walk, made public: `term_ser::DeclaredType::shape` and
//! `term_ser::DataShape::fields`. A caller that walks a value at its declared type as the codec
//! does (a value generator, a differ) reads a field's type there with the sort's parameters
//! substituted, defaults applied, and an outer place's bindings kept — the reading the codec
//! decodes and encodes by, not a second copy of it.
//!
//! Each row DRIVES the reading from outside the crate: it reads a type's constructor, its
//! fields, and each field's shape, and asserts what the field is at the application. The last
//! row builds a value of each type from nothing but what the reading reports, and the codec
//! encodes it and decodes it back to the same term.
//!
//! CONTROLS, MEASURED 2026-11-25 one at a time on a binary of this file and the codec's own
//! suite (`wi_wc18y_value_codec_test`) alone, each a change to the rule's one copy in
//! `term_ser.rs`; every row not named passed under each:
//! - `sort_env`'s positional match taken out: `a_positional_binding_reads_by_position` and the
//!   round trip FAIL, at the type whose arguments carry positional labels (`a` is
//!   `UnboundParameter { name: "A" }`). Its two other spellings PASS BY DESIGN: the loader names
//!   a positional application's arguments by parameter (`Pair[A = Int64, B = String]`), so a
//!   lowered type never reaches the positional match.
//! - `sort_env`'s default branch taken out (every unwritten parameter open):
//!   `a_parameter_left_to_its_default_reads_at_the_default` and the round trip FAIL, at the bare
//!   face (`v` is `UnboundParameter { name: "T" }`). The spelling through `type_from_text`
//!   PASSES BY DESIGN: its lowering writes the default into the type.
//! - `DataShape::fields` handing out each field with no bindings: every row here that reads a
//!   field at an application FAILS (`UnboundParameter { name: "T" }`, `c` shown `Cell[T = ?_]`),
//!   and two rows of the codec's suite with them. The refusal by name PASSES BY DESIGN: a
//!   free canonical variable is named by its parameter, bound or not.
//! - `sort_env` binding a written parameter with no bindings of its place
//!   (`DeclaredType::closed(v)` for `ty.within(v)`): `a_nested_binding_reads_in_its_outer_place`
//!   and the round trip (through `Uses.h`) FAIL (`c.value` is `UnboundParameter { name: "A" }`).
//! Backing the whole change out removes the public reading, and this file does not compile.
use anthill_core::eval::Value;
use anthill_core::intern::{positional_label, Symbol};
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::term_ser::{self, CodecOptions, DeclaredType, TypeShape, ValueProblem};
use smallvec::SmallVec;

use crate::common::load_kb_with;

const DECLS: &str = r#"
namespace test.cm
  import anthill.prelude.{Option, List, Int64, String, Bool}

  sort Cell[T]
    entity Cell(value: T)
  end
  sort Box
    sort T = ? default Int64
    entity Box(v: T)
  end
  sort Pair[A, B]
    entity Pair(a: A, b: B)
  end
  sort Holder[A]
    entity Holder(c: Cell[T = A], cs: List[T = Cell[T = A]], o: Option[T = A])
  end
  sort Two { entity One(n: Int64)  entity Other }

  entity Uses(p: Pair[Int64, String], h: Holder[A = Bool])
end
"#;

fn sym(kb: &KnowledgeBase, name: &str) -> Symbol {
    kb.try_resolve_symbol(name).unwrap_or_else(|| panic!("`{name}` resolves"))
}

/// The type a text names, as a data file's `meta.entity` is read.
fn ty(kb: &mut KnowledgeBase, text: &str) -> TermId {
    term_ser::type_from_text(kb, text).unwrap_or_else(|e| panic!("`{text}`: {e}"))
}

/// The declared type of `entity.field`, as written in the declaration.
fn field_type(kb: &KnowledgeBase, entity: &str, field: &str) -> Value {
    let e = sym(kb, entity);
    kb.entity_field_types(e)
        .expect("declared fields")
        .iter()
        .find(|(f, _)| kb.local_name_of(*f) == field)
        .map(|(_, t)| t.clone())
        .unwrap_or_else(|| panic!("`{entity}` declares `{field}`"))
}

/// The one constructor of a data type, and its fields at the type, by name.
fn only_ctor_fields(kb: &KnowledgeBase, ty: &DeclaredType) -> (Symbol, Vec<(String, DeclaredType)>) {
    let TypeShape::Data(data) = ty.shape(kb).unwrap_or_else(|p| panic!("a data type: {p}")) else {
        panic!("a data type")
    };
    let [ctor] = data.constructors() else {
        panic!("one constructor, found {:?}", data.constructors())
    };
    let fields = data
        .fields(kb, *ctor)
        .unwrap_or_else(|p| panic!("fields: {p}"))
        .into_iter()
        .map(|(f, t)| (kb.local_name_of(f).to_owned(), t))
        .collect();
    (*ctor, fields)
}

fn field<'a>(fields: &'a [(String, DeclaredType)], name: &str) -> &'a DeclaredType {
    fields
        .iter()
        .find(|(f, _)| f == name)
        .map(|(_, t)| t)
        .unwrap_or_else(|| panic!("a field `{name}`"))
}

/// `Pair[_1 = Int64, _2 = String]`: a type term whose arguments carry positional labels, as a
/// host may build one. The loader never writes it (it names the arguments by parameter), so it
/// is the spelling that reaches the reading's positional match.
fn pair_by_position(kb: &mut KnowledgeBase) -> TermId {
    let int = ty(kb, "anthill.prelude.Int64");
    let string = ty(kb, "anthill.prelude.String");
    let face = kb.type_face_of(sym(kb, "test.cm.Pair"));
    let first = kb.intern(&positional_label(0));
    let second = kb.intern(&positional_label(1));
    kb.alloc(Term::Fn {
        functor: face,
        pos_args: SmallVec::new(),
        named_args: smallvec::smallvec![(first, int), (second, string)],
    })
}

/// The shape a field reads as, by name: the primitive, or the sort's qualified name.
fn shape_name(kb: &KnowledgeBase, ty: &DeclaredType) -> Result<String, ValueProblem> {
    Ok(match ty.shape(kb)? {
        TypeShape::String => "String".into(),
        TypeShape::Int64 => "Int64".into(),
        TypeShape::Float => "Float".into(),
        TypeShape::BigInt => "BigInt".into(),
        TypeShape::Bool => "Bool".into(),
        TypeShape::Type => "Type".into(),
        TypeShape::Option(inner) => format!("Option[{}]", shape_name(kb, &inner)?),
        TypeShape::List(elem) => format!("List[{}]", shape_name(kb, &elem)?),
        TypeShape::Set(elem) => format!("Set[{}]", shape_name(kb, &elem)?),
        TypeShape::Map { key, value } => format!("Map[{}, {}]", shape_name(kb, &key)?, shape_name(kb, &value)?),
        TypeShape::Tuple(_) => "tuple".into(),
        TypeShape::Data(data) => kb.qualified_name_of(data.sort()).to_owned(),
    })
}

#[test]
fn an_application_reads_its_constructors_fields_at_its_bindings() {
    let mut kb = load_kb_with(DECLS);
    let cell = ty(&mut kb, "test.cm.Cell[T = anthill.prelude.Int64]");
    let (ctor, fields) = only_ctor_fields(&kb, &DeclaredType::closed(&cell));
    assert_eq!(kb.qualified_name_of(ctor), "test.cm.Cell");
    // As written, the field is the sort's parameter; at the application, `Int64`.
    assert!(
        matches!(field_type(&kb, "test.cm.Cell", "value").head(&kb), ViewHead::Var(_)),
        "`entity_field_types` gives `value` in `Cell`'s parameter"
    );
    assert_eq!(shape_name(&kb, field(&fields, "value")), Ok("Int64".into()));
    assert_eq!(field(&fields, "value").display_name(&kb), "Int64");
}

#[test]
fn a_parameter_left_to_its_default_reads_at_the_default() {
    let mut kb = load_kb_with(DECLS);
    // The bare face, as a data file names a row's constructor: the default is applied by the
    // reading itself. FAILS with the default branch backed out.
    let face = Value::SymbolRef(kb.type_face_of(sym(&kb, "test.cm.Box")));
    let (_, fields) = only_ctor_fields(&kb, &DeclaredType::closed(&face));
    assert_eq!(shape_name(&kb, field(&fields, "v")), Ok("Int64".into()), "`Box` at its face");
    // The text `Box`, lowered as a declaration's type is: the default is written into the type.
    // Passes either way by design.
    let lowered = ty(&mut kb, "test.cm.Box");
    let (_, fields) = only_ctor_fields(&kb, &DeclaredType::closed(&lowered));
    assert_eq!(shape_name(&kb, field(&fields, "v")), Ok("Int64".into()), "`Box` from its text");
}

#[test]
fn a_positional_binding_reads_by_position() {
    let mut kb = load_kb_with(DECLS);
    // FAILS with the positional match backed out.
    let by_position = pair_by_position(&mut kb);
    // Lowered: the loader names the arguments by parameter. Pass either way by design.
    let written = ty(&mut kb, "test.cm.Pair[anthill.prelude.Int64, anthill.prelude.String]");
    let declared = field_type(&kb, "test.cm.Uses", "p");
    for (what, pair) in [
        ("by position", DeclaredType::closed(&by_position)),
        ("from its text", DeclaredType::closed(&written)),
        ("as a field's type", DeclaredType::closed(&declared)),
    ] {
        let (_, fields) = only_ctor_fields(&kb, &pair);
        assert_eq!(shape_name(&kb, field(&fields, "a")), Ok("Int64".into()), "`a` {what}");
        assert_eq!(shape_name(&kb, field(&fields, "b")), Ok("String".into()), "`b` {what}");
    }
}

#[test]
fn a_nested_binding_reads_in_its_outer_place() {
    let kb = load_kb_with(DECLS);
    // `Uses.h: Holder[A = Bool]`; `Holder.c: Cell[T = A]` names `Holder`'s parameter, so
    // `c.value` is `Bool` — at a field, inside a `List`, and inside an `Option`.
    let holder = DeclaredType::closed(&field_type(&kb, "test.cm.Uses", "h"));
    let (_, fields) = only_ctor_fields(&kb, &holder);
    let c = field(&fields, "c");
    assert_eq!(c.display_name(&kb), "Cell[T = Bool]");
    let (_, cell_fields) = only_ctor_fields(&kb, c);
    assert_eq!(shape_name(&kb, field(&cell_fields, "value")), Ok("Bool".into()));
    let TypeShape::List(elem) = field(&fields, "cs").shape(&kb).expect("cs") else {
        panic!("`cs` is a List")
    };
    let (_, elem_fields) = only_ctor_fields(&kb, &elem);
    assert_eq!(shape_name(&kb, field(&elem_fields, "value")), Ok("Bool".into()), "`cs`'s element's `value`");
    assert_eq!(shape_name(&kb, field(&fields, "o")), Ok("Option[Bool]".into()));
}

#[test]
fn an_unwritten_parameter_with_no_default_is_refused_by_name() {
    let mut kb = load_kb_with(DECLS);
    // The type reads, and its constructor and fields with it; the field that names the open
    // parameter is refused where it is read, by the parameter's name.
    let bare = ty(&mut kb, "test.cm.Cell");
    let (_, fields) = only_ctor_fields(&kb, &DeclaredType::closed(&bare));
    assert_eq!(
        field(&fields, "value").shape(&kb).expect_err("T is open"),
        ValueProblem::UnboundParameter { name: "T".into() }
    );
    // The field type as WRITTEN, handed in for the type at an application, is refused by the
    // parameter's name too: its variable is anonymous, and the reading names what it stands for.
    let as_written = DeclaredType::closed(&field_type(&kb, "test.cm.Cell", "value"));
    assert_eq!(as_written.shape(&kb).expect_err("T is free"), ValueProblem::UnboundParameter { name: "T".into() });
    assert_eq!(as_written.display_name(&kb), "T", "shown by the parameter's name, not `?_`");
    // A constructor named by its type face is the constructor.
    let cell_face = kb.type_face_of(sym(&kb, "test.cm.Cell"));
    let TypeShape::Data(cell) = DeclaredType::closed(&bare).shape(&kb).expect("Cell") else {
        panic!("a data type")
    };
    assert_eq!(cell.fields(&kb, cell_face).expect("the face names `Cell`").len(), 1);
    // A constructor that is not one of the type's is refused, not read at the type's bindings.
    let TypeShape::Data(two) = DeclaredType::closed(&ty(&mut kb, "test.cm.Two")).shape(&kb).expect("Two") else {
        panic!("a data type")
    };
    assert_eq!(two.constructors().len(), 2, "`Two` has two constructors");
    assert_eq!(
        two.fields(&kb, sym(&kb, "test.cm.Cell")).expect_err("not Two's"),
        ValueProblem::UnknownConstructor {
            name: "test.cm.Cell".into(),
            sort: "test.cm.Two".into(),
        }
    );
}

/// A value of `ty` built from nothing but what the reading reports: the first constructor of
/// a data type, each field a value of its reported type. Built as the decoder builds one (a
/// nullary constructor its `Ref`, any other its fields in declared order), so the round trip
/// is a hash-consed identity.
fn sample(kb: &mut KnowledgeBase, ty: &DeclaredType) -> TermId {
    let shape = ty.shape(kb).unwrap_or_else(|p| panic!("`{}`: {p}", ty.display_name(kb)));
    match shape {
        TypeShape::Int64 => kb.alloc(Term::Const(Literal::Int(7))),
        TypeShape::String => kb.alloc(Term::Const(Literal::String("s".into()))),
        TypeShape::Bool => kb.alloc(Term::Const(Literal::Bool(true))),
        TypeShape::Option(inner) => {
            let v = sample(kb, &inner);
            let some = sym(kb, "anthill.prelude.Option.some");
            let value = kb.entity_field_names(some).expect("`some`'s field")[0];
            kb.make_entity_term(some, SmallVec::new(), SmallVec::from_elem((value, v), 1))
        }
        TypeShape::List(elem) => {
            let items = [sample(kb, &elem), sample(kb, &elem)];
            kb.build_list(&items)
        }
        TypeShape::Data(data) => {
            let ctor = data.constructors()[0];
            let fields = data.fields(kb, ctor).unwrap_or_else(|p| panic!("fields: {p}"));
            let named: SmallVec<[(Symbol, TermId); 2]> = fields.iter().map(|(f, t)| (*f, sample(kb, t))).collect();
            if named.is_empty() {
                kb.alloc(Term::Ref(ctor))
            } else {
                kb.make_entity_term(ctor, SmallVec::new(), named)
            }
        }
        other => panic!("no sample of {other:?}"),
    }
}

#[test]
fn a_value_built_from_the_reported_field_types_decodes_to_itself() {
    let mut kb = load_kb_with(DECLS);
    let face = Value::SymbolRef(kb.type_face_of(sym(&kb, "test.cm.Box")));
    let by_position = Value::term(pair_by_position(&mut kb));
    let types: Vec<(String, Value)> = vec![
        ("Cell[T = Int64]".into(), Value::term(ty(&mut kb, "test.cm.Cell[T = anthill.prelude.Int64]"))),
        ("Box at its face".into(), face),
        ("Box from its text".into(), Value::term(ty(&mut kb, "test.cm.Box"))),
        ("Pair[Int64, String]".into(), Value::term(ty(&mut kb, "test.cm.Pair[anthill.prelude.Int64, anthill.prelude.String]"))),
        ("Pair[_1 = Int64, _2 = String]".into(), by_position),
        ("Uses".into(), Value::term(ty(&mut kb, "test.cm.Uses"))),
    ];
    for (what, top) in types {
        let value = sample(&mut kb, &DeclaredType::closed(&top));
        let json = term_ser::encode_value(&kb, &value, &top, CodecOptions::default())
            .unwrap_or_else(|e| panic!("{what}: the codec writes the sample: {e}"));
        let back = term_ser::decode_value(&mut kb, &json, &top, CodecOptions::default())
            .unwrap_or_else(|e| panic!("{what}: the codec reads {json} back: {e}"));
        assert_eq!(back, value, "{what}: {json} decodes to the sample");
    }
}
