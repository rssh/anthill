//! WI-20261122-WC18Y — proposal 021's mapping as a public pair over `TermView`: ONE value at a
//! declared type, decoded (`term_ser::decode_value`) and encoded (`term_ser::encode_value`),
//! with a data file as one use of it (`load_json` / `serialize_json` rebuilt on the pair).
//!
//! Each row DRIVES the pair: it decodes or encodes a value at a type the KB declares, and
//! asserts the term (against the fact the same source writes, by hash-consed identity) or the
//! JSON bytes. The back-outs at each row were MEASURED, one at a time, on a binary of this
//! file alone. The rows the ticket asks to be measured against the code before it are at the
//! file level, since that code had no public pair; they were run against `term_ser.rs` at
//! e25f0b734 (see `a_data_file_is_one_use_of_the_pair`).
use anthill_core::eval::{HostValue, Value};
use anthill_core::kb::op_info::lookup_operation_info;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::term_view::TermView;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::term_ser::{
    self, BigIntSpelling, CodecOptions, EntityTags, JsonPath, PathStep, SerError, TagNames,
    ValueError, ValueProblem, WiderTuple,
};

use crate::common::{interp_for, load_kb_with};

const DECLS: &str = r#"
namespace test.wc
  import anthill.prelude.{Option, List, Int64, String, Float, BigInt, Bool, Type}
  import anthill.prelude.Option.{some, none}

  sort Status { entity Open  entity Closed }
  entity P(id: Int64, name: String)
  entity Point(x: Int64, y: Int64)
  sort Move { entity Moved(to: Point)  entity Stay }
  sort Acceptance {
    entity ToolPasses(tool: String)
    entity Verified(at: String, by: String)
  }
  sort Box {
    sort T = ? default Int64
    entity Box(items: List[T = T], first: Option[T = T])
  }
  sort Mix { entity Mix(x: Int64)  entity Other }
  sort Bag {
    sort T = ?
    entity Bag(v: T, first: Option[T = T])
  }
  const limit: Int64 = 3
  entity Late(zz: Int64, aa: Int64)
  entity Nest(o: Option[T = Option[T = Int64]])
  entity S(ps: List[T = P], at: Point, st: Status, acc: List[T = Acceptance],
           note: Option[T = String], opts: List[T = Option[T = Int64]], big: BigInt,
           f: Float, flag: Bool, bx: Box[T = String], ty: Type, mv: Move)

  fact S(ps: [P(id: 1, name: "a"), P(id: 2, name: "b")], at: Point(x: 1, y: 2), st: Open,
         acc: [ToolPasses(tool: "cargo-test"), Verified(at: "2027-03-15", by: "rs")],
         note: some("hi"), opts: [some(1), none, some(3)],
         big: 123456789012345678901234567890n, f: 3.0, flag: true,
         bx: Box(items: ["a"], first: none), ty: Box[T = String],
         mv: Moved(to: Point(x: 5, y: 6)))

  entity H(p: (state: Status, n: Int64))
  fact H(p: (n: 3, state: Open))
  entity Wide(p: (state: Status, n: Int64))
  fact Wide(p: (state: Open, n: 3, extra: 1))

  operation place(s: S, n: Int64) -> (state: S, n: Int64) = (state: s, n: n)
  operation pair(n: Int64) -> (Int64, String) = (n, "x")
  operation narrow() -> (a: Int64) = (b: 2, a: 1)
  operation mk(n: Int64) -> (p: P, pt: Point, k: Int64) =
    (p: P(id: n, name: "x"), pt: Point(x: n, y: 2), k: n)
end
"#;

fn kb() -> KnowledgeBase {
    load_kb_with(DECLS)
}

fn sym(kb: &KnowledgeBase, name: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(name).unwrap_or_else(|| panic!("`{name}` resolves"))
}

/// The declared type of `entity.field`.
fn field_type(kb: &KnowledgeBase, entity: &str, field: &str) -> Value {
    let e = sym(kb, entity);
    kb.entity_field_types(e)
        .expect("declared fields")
        .iter()
        .find(|(f, _)| kb.local_name_of(*f) == field)
        .map(|(_, t)| t.clone())
        .unwrap_or_else(|| panic!("`{entity}` declares `{field}`"))
}

/// The value the source fact of `S` holds in `field`.
fn source_field(kb: &KnowledgeBase, field: &str) -> TermId {
    let s = sym(kb, "test.wc.S");
    let rids = kb.rules_by_functor(s);
    assert_eq!(rids.len(), 1, "one source fact of S");
    let head = kb.rule_head(rids[0]);
    head.named_field(kb, field)
        .and_then(|v| v.as_term_id())
        .unwrap_or_else(|| panic!("the fact holds `{field}`"))
}

fn result_type(kb: &KnowledgeBase, op: &str) -> Value {
    lookup_operation_info(kb, sym(kb, op)).expect("operation info").return_type
}

fn text(json: &serde_json::Value) -> String {
    serde_json::to_string(json).expect("JSON text")
}

fn opts() -> CodecOptions {
    CodecOptions::default()
}

/// Every field of the source fact of `S`, encoded at its declared type with the default
/// options, is the JSON 021 states for it, and decodes back to the SAME term (hash-consed
/// identity with the fact's own field). Covers: a list of multi-field entities, a nested
/// entity, an enum value, a constructor with fields and the single-field shorthand, Option in
/// a field and in a list, BigInt past `i64`, a Float, a generic entity at its argument, a
/// `Type` value, and the writer's shorthand rule over a field that is itself an entity.
///
/// FAILS when backed out (measured): the writer leaving an entity type's own constructor
/// untagged under the default options (`ps`, `at`, `bx` lose their tag; four other rows fail
/// with it); the shorthand guard (`mv` is written `{"Moved":{"Point":…}}`, which reads back as
/// `Moved`'s fields and is refused `UnknownField`); the parameter environment (`bx.items` is
/// refused `UnboundParameter T`). Each also fails `a_data_file_is_one_use_of_the_pair`.
#[test]
fn every_field_round_trips_at_its_declared_type() {
    let mut kb = kb();
    let rows: &[(&str, &str)] = &[
        ("ps", r#"[{"P":{"id":1,"name":"a"}},{"P":{"id":2,"name":"b"}}]"#),
        ("at", r#"{"Point":{"x":1,"y":2}}"#),
        ("st", r#""Open""#),
        ("acc", r#"[{"ToolPasses":"cargo-test"},{"Verified":{"at":"2027-03-15","by":"rs"}}]"#),
        ("note", r#""hi""#),
        ("opts", "[1,null,3]"),
        ("big", r#""123456789012345678901234567890""#),
        ("f", "3.0"),
        ("flag", "true"),
        ("bx", r#"{"Box":{"items":["a"]}}"#),
        ("ty", r#""test.wc.Box[T = anthill.prelude.String]""#),
        ("mv", r#"{"Moved":{"to":{"Point":{"x":5,"y":6}}}}"#),
    ];
    for (field, want) in rows {
        let ty = field_type(&kb, "test.wc.S", field);
        let value = source_field(&kb, field);
        let json = term_ser::encode_value(&kb, &value, &ty, opts())
            .unwrap_or_else(|e| panic!("`{field}` encodes: {e}"));
        assert_eq!(text(&json), *want, "`{field}` is written as 021 states");
        let back = term_ser::decode_value(&mut kb, &json, &ty, opts())
            .unwrap_or_else(|e| panic!("`{field}` decodes: {e}"));
        assert_eq!(back, value, "`{field}` reads back as the fact's own term");
    }
}

/// A `Type` value is the type's qualified text, and the text reads back as the type a
/// declaration writes: the fact's `ty: Box[T = String]` and the field type `bx: Box[T =
/// String]` are one term, and `type_to_text` / `type_from_text` are inverse on it.
#[test]
fn a_type_is_its_text_and_reads_back_as_the_declared_type() {
    let mut kb = kb();
    // The declared type on whatever carrier it rides (an occurrence under
    // ANTHILL_TEST_NODE_CARRIER=1): its text, read back, is the type the fact's data slot holds.
    let declared = field_type(&kb, "test.wc.S", "bx");
    let text = term_ser::type_to_text(&kb, &declared).expect("a type has a text");
    assert_eq!(text, "test.wc.Box[T = anthill.prelude.String]");
    let read = term_ser::type_from_text(&mut kb, &text).expect("reads back");
    assert_eq!(read, source_field(&kb, "ty"), "the annotation, its text and the data slot are one type");

    // An unwritten parameter takes its default where the text is read, as in a declaration.
    let bare = term_ser::type_from_text(&mut kb, "test.wc.Box").expect("bare Box");
    let int = term_ser::type_from_text(&mut kb, "test.wc.Box[T = anthill.prelude.Int64]").expect("Box[T = Int64]");
    assert_eq!(bare, int, "`Box` is `Box[T = Int64]`");

    // A tuple type has a text too.
    let tuple = result_type(&kb, "test.wc.place");
    let tuple_text = term_ser::type_to_text(&kb, &tuple).expect("tuple text");
    assert_eq!(tuple_text, "(state: test.wc.S, n: anthill.prelude.Int64)");
    let read = term_ser::type_from_text(&mut kb, &tuple_text).expect("tuple reads back");
    assert_eq!(term_ser::type_to_text(&kb, &read).unwrap(), tuple_text);

    for (text, problem) in [
        ("no.such.Sort", "UnknownName"),
        ("anthill.prelude.Int64 const x: anthill.prelude.Int64", "NotAType"),
        // A top-level import is no item: FAILS when backed out (measured), read as `Int64`.
        ("anthill.prelude.Int64\nimport test.wc.{P}", "NotAType"),
        ("anthill.prelude.List[T = ?x]", "Variable"),
        ("?x", "Variable"),
    ] {
        let err = term_ser::type_from_text(&mut kb, text).expect_err(text);
        assert!(format!("{:?}", err.problem).starts_with(problem), "`{text}`: {err}");
    }

    // A name that is a value, or a namespace, is no type: refused as an annotation naming it
    // is, so the decoder takes no `Type` value the writer would refuse to write back.
    // FAILS when backed out (measured): without the annotation's refusal `test.wc.limit` reads
    // as a type.
    for text in ["test.wc.limit", "test.wc"] {
        let err = term_ser::type_from_text(&mut kb, text).expect_err(text);
        assert!(matches!(err.problem, ValueProblem::NotAType { .. }), "`{text}`: {err}");
    }

    // Reading a type asserts nothing: an inline description in the text is no
    // `DescriptionInfo`. FAILS when backed out (measured): one more fact.
    let descriptions = |kb: &KnowledgeBase| kb.rules_by_functor(sym(kb, "anthill.reflect.DescriptionInfo")).len();
    let before = descriptions(&kb);
    let err = term_ser::type_from_text(&mut kb, "(a: ?x {< a note >}?)").expect_err("a variable");
    assert_eq!(err.problem, ValueProblem::Variable);
    assert_eq!(descriptions(&kb), before, "no description is asserted");

    // The writer refuses what the reader refuses: a namespace or a const at `Type` is no type.
    // FAILS when backed out (measured): both are written as their names.
    let ty_field = field_type(&kb, "test.wc.S", "ty");
    for name in ["test.wc", "test.wc.limit"] {
        let r = kb.alloc(Term::Ref(sym(&kb, name)));
        let err = term_ser::encode_value(&kb, &r, &ty_field, opts()).expect_err(name);
        assert!(matches!(err.problem, ValueProblem::WrongShape { .. }), "`{name}`: {err}");
    }

    // A text read per call banks no source per call.
    // FAILS when backed out (measured): a source per call, 100 more.
    let before = kb.source_count();
    for _ in 0..100 {
        term_ser::type_from_text(&mut kb, "test.wc.P").unwrap();
    }
    assert!(kb.source_count() <= before + 1, "{before} -> {}", kb.source_count());

    // An anonymous `?` binding leaves the parameter open, as in a declaration: the text is
    // the bare `List`, a type, and a value at it has no reading.
    let open = term_ser::type_from_text(&mut kb, "anthill.prelude.List[T = ?]").expect("the bare List");
    assert_eq!(open, term_ser::type_from_text(&mut kb, "anthill.prelude.List").unwrap());
    let err = term_ser::decode_value(&mut kb, &serde_json::json!([]), &open, opts()).expect_err("T is open");
    assert_eq!(err.problem, ValueProblem::UnboundParameter { name: "T".into() });
}

/// A labelled tuple — an operation's declared result — is an object keyed by its labels in the
/// VALUE's order, which is its identity (kernel §4.5; decided with the user, 2026-11-23); a
/// positional one an array; a wider tuple value is written at the declared labels, or refused
/// with `WiderTuple::Refuse`.
///
/// FAILS when backed out (measured): writing a labelled tuple in its type's order, or reading
/// it in its type's order (the reordered value comes back as another, and in the file row
/// below the source fact reloads as a second one); the projection to the declared labels
/// (`narrow` writes its `b` too); the array spelling of a positional tuple (`pair` is written `{"_1":…}`); the
/// `Float` reading of an integral number (`"f":3` reads as the Int64 3, which `f: Float`
/// refuses to write back); `preserve_order` (the keys come out sorted).
#[test]
fn tuples_by_their_declared_labels() {
    let mut interp = interp_for(DECLS);
    let place_ty = result_type(interp.kb(), "test.wc.place");
    let json: serde_json::Value = serde_json::from_str(
        r#"{"state":{"S":{"ps":[],"at":{"Point":{"x":1,"y":2}},"st":"Closed","acc":[],
            "opts":[],"big":7,"f":3,"flag":false,"bx":{"Box":{"items":[]}},
            "ty":"anthill.prelude.Int64","mv":"Stay"}},"n":3}"#,
    )
    .unwrap();
    let kb = interp.kb_mut();
    let term = term_ser::decode_value(kb, &json, &place_ty, opts()).expect("the tuple decodes");
    let again = term_ser::encode_value(kb, &term, &place_ty, opts()).expect("and encodes");
    assert_eq!(
        text(&again),
        r#"{"state":{"S":{"ps":[],"at":{"Point":{"x":1,"y":2}},"st":"Closed","acc":[],"opts":[],"big":7,"f":3.0,"flag":false,"bx":{"Box":{"items":[]}},"ty":"anthill.prelude.Int64","mv":"Stay"}},"n":3}"#,
        "a labelled tuple is its labels in the type's order; `3` under Float is the Float 3.0"
    );

    let pair = interp.call("test.wc.pair", &HostValue::all(&[Value::Int(4)])).expect("pair runs").value;
    let pair_ty = result_type(interp.kb(), "test.wc.pair");
    let pair_json = term_ser::encode_value(interp.kb(), &pair, &pair_ty, opts()).expect("pair encodes");
    assert_eq!(text(&pair_json), r#"[4,"x"]"#, "a positional tuple is an array");
    let back = term_ser::decode_value(interp.kb_mut(), &pair_json, &pair_ty, opts()).expect("pair decodes");
    assert_eq!(
        text(&term_ser::encode_value(interp.kb(), &back, &pair_ty, opts()).unwrap()),
        r#"[4,"x"]"#
    );
    // In another order than the type's: written, and read back, in its own.
    let reordered: serde_json::Value = serde_json::from_str(
        r#"{"n":3,"state":{"S":{"ps":[],"at":{"Point":{"x":1,"y":2}},"st":"Closed","acc":[],"opts":[],"big":7,"f":3.0,"flag":false,"bx":{"Box":{"items":[]}},"ty":"anthill.prelude.Int64","mv":"Stay"}}}"#,
    )
    .unwrap();
    let kb = interp.kb_mut();
    let t = term_ser::decode_value(kb, &reordered, &place_ty, opts()).expect("decodes");
    assert_ne!(t, term, "another order is another tuple");
    assert_eq!(text(&term_ser::encode_value(kb, &t, &place_ty, opts()).unwrap()), text(&reordered));

    let short: serde_json::Value = serde_json::from_str("[4]").unwrap();
    let err = term_ser::decode_value(interp.kb_mut(), &short, &pair_ty, opts()).expect_err("too short");
    assert_eq!(err.problem, ValueProblem::MissingField { name: "_2".into() });

    let narrow = interp.call("test.wc.narrow", &HostValue::all(&[])).expect("narrow runs").value;
    let narrow_ty = result_type(interp.kb(), "test.wc.narrow");
    let projected = term_ser::encode_value(interp.kb(), &narrow, &narrow_ty, opts()).expect("projected");
    assert_eq!(text(&projected), r#"{"a":1}"#, "a wider tuple is written at the declared labels");
    let refuse = CodecOptions {
        wider_tuple: WiderTuple::Refuse,
        ..opts()
    };
    let err = term_ser::encode_value(interp.kb(), &narrow, &narrow_ty, refuse).expect_err("refused");
    assert_eq!(err.problem, ValueProblem::WiderThanDeclared { labels: vec!["b".into()] });
}

/// One term encodes to the same bytes on every carrier: the `Value` an operation returned
/// (a `Value::Tuple` of `Value::Entity`s) and the `TermId` of the same term.
///
/// FAILS when backed out (measured): `preserve_order`, against the expected bytes (both
/// carriers then agree on sorted keys, so the equality alone would not catch it).
#[test]
fn a_value_and_its_term_encode_to_the_same_bytes() {
    let mut interp = interp_for(DECLS);
    let v = interp.call("test.wc.mk", &HostValue::all(&[Value::Int(9)])).expect("mk runs").value;
    assert!(matches!(v, Value::Tuple { .. }), "the interpreter's own carrier: {v:?}");
    let ty = result_type(interp.kb(), "test.wc.mk");
    let from_value = term_ser::encode_value(interp.kb(), &v, &ty, opts()).expect("the Value encodes");
    let term = interp.kb_mut().alloc_from_value(&v).expect("the Value lowers");
    let from_term = term_ser::encode_value(interp.kb(), &term, &ty, opts()).expect("the term encodes");
    assert_eq!(text(&from_value), text(&from_term));
    assert_eq!(
        text(&from_value),
        r#"{"p":{"P":{"id":9,"name":"x"}},"pt":{"Point":{"x":9,"y":2}},"k":9}"#
    );
}

/// Variables are an option, off by default: then `"?x"` is the string `"?x"` and no escape is
/// read; with them on `"?x"` is a variable (under `Option`, the present value's), and `\`
/// escapes a literal one, both ways.
///
/// FAILS when backed out (measured): the option gate (`"?x"` decodes to a variable with the
/// defaults). The old code had no reading of one value in which `"?x"` is the string: its
/// data files have variables on, as they still do.
#[test]
fn variables_are_an_option() {
    let mut kb = kb();
    let string = field_type(&kb, "test.wc.P", "name");
    let note = field_type(&kb, "test.wc.S", "note");
    let q: serde_json::Value = serde_json::json!("?x");
    let off = term_ser::decode_value(&mut kb, &q, &string, opts()).expect("off");
    assert_eq!(kb.get_term(off), &Term::Const(Literal::String("?x".into())));
    let escaped = term_ser::decode_value(&mut kb, &serde_json::json!("\\?x"), &string, opts()).expect("off");
    assert_eq!(kb.get_term(escaped), &Term::Const(Literal::String("\\?x".into())), "no escape is read");

    let on = CodecOptions::data_file();
    let var = term_ser::decode_value(&mut kb, &q, &string, on).expect("on");
    assert!(matches!(kb.get_term(var), Term::Var(_)), "a variable");
    let some_var = term_ser::decode_value(&mut kb, &q, &note, on).expect("on, at Option");
    let printed = anthill_core::persistence::print::TermPrinter::new(&kb).print_term(some_var);
    assert!(printed.starts_with("some("), "`?x` at Option is some(?x): {printed}");
    let err = term_ser::encode_value(&kb, &var, &string, opts()).expect_err("a variable with variables off");
    assert_eq!(err.problem, ValueProblem::Variable);
    assert_eq!(text(&term_ser::encode_value(&kb, &var, &string, on).unwrap()), r#""?x""#);

    // One value is one scope: two variables that share a name are written apart, one variable
    // twice is written alike, and an anonymous one is named where it occurs twice.
    // FAILS when backed out (measured): `["?x","?x","?x"]` for two variables, read back as one.
    let tags = term_ser::type_from_text(&mut kb, "anthill.prelude.List[T = anthill.prelude.String]").unwrap();
    let x = kb.intern("x");
    let anon = kb.intern("_");
    let var = |kb: &mut KnowledgeBase, name| {
        let v = kb.fresh_var(name);
        kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(v)))
    };
    let (x1, x2, a1, a2) = (var(&mut kb, x), var(&mut kb, x), var(&mut kb, anon), var(&mut kb, anon));
    for (items, written) in [
        (vec![x1, x2, x1], r#"["?x","?x_2","?x"]"#),
        (vec![a1, a2], r#"["?","?"]"#),
        (vec![a1, a1], r#"["?_","?_"]"#),
    ] {
        let list = kb.build_list(&items);
        let json = term_ser::encode_value(&kb, &list, &tags, on).unwrap();
        assert_eq!(text(&json), written);
        let back = term_ser::decode_value(&mut kb, &json, &tags, on).unwrap();
        let again = term_ser::encode_value(&kb, &back, &tags, on).unwrap();
        assert_eq!(text(&again), written, "the variables read back as they were apart");
    }

    for literal in ["?x", "\\?x"] {
        let lit = kb.alloc(Term::Const(Literal::String(literal.into())));
        let json = term_ser::encode_value(&kb, &lit, &string, on).unwrap();
        assert_eq!(json.as_str(), Some(format!("\\{literal}").as_str()), "escaped once");
        assert_eq!(term_ser::decode_value(&mut kb, &json, &string, on).unwrap(), lit, "and read back exact");
    }
}

/// Numbers follow the declared type, and an error names the JSON path and the type.
///
/// FAILS when backed out (measured): the `Float` arm's reading of an integral number as the
/// Float (`3` becomes the Int64 3, a different term from the source's `3.0`). `3.5` under
/// Int64 is refused by `as_i64` answering `None` for a number written with a fraction or an
/// exponent; the old code read it as a Float and loaded the row (measured, see below).
#[test]
fn numbers_follow_the_declared_type() {
    let mut kb = kb();
    let int = field_type(&kb, "test.wc.P", "id");
    let float = field_type(&kb, "test.wc.S", "f");
    let three = term_ser::decode_value(&mut kb, &serde_json::json!(3), &float, opts()).unwrap();
    assert_eq!(three, source_field(&kb, "f"), "`3` under Float is the source's `3.0`");
    for (json, problem) in [("3.5", "NotAnInteger"), ("3.0", "NotAnInteger"), ("1e3", "NotAnInteger"), ("9223372036854775808", "OutOfRange"), ("-9223372036854775809", "OutOfRange"), ("\"3\"", "WrongShape")] {
        let json: serde_json::Value = serde_json::from_str(json).unwrap();
        let err = term_ser::decode_value(&mut kb, &json, &int, opts()).expect_err("refused");
        assert!(format!("{:?}", err.problem).starts_with(problem), "{json}: {err}");
    }

    // The path and the type, deep in a value.
    let s = term_ser::type_from_text(&mut kb, "test.wc.S").unwrap();
    let bad: serde_json::Value = serde_json::from_str(
        r#"{"S":{"ps":[{"P":{"id":1,"name":"a"}},{"P":{"id":3.5,"name":"b"}}]}}"#,
    )
    .unwrap();
    let err = term_ser::decode_value(&mut kb, &bad, &s, opts()).expect_err("3.5 under Int64");
    assert_eq!(err.to_string(), "$.S.ps[1].P.id: expected Int64, found 3.5, which is not written as an integer");
    assert_eq!(
        err.path.steps(),
        &[
            PathStep::Key("S".into()),
            PathStep::Key("ps".into()),
            PathStep::Index(1),
            PathStep::Key("P".into()),
            PathStep::Key("id".into())
        ]
    );
    let _: &JsonPath = &err.path;

    // BigInt: a number in range, digits past it; both read; a rounded integer refused.
    let big = field_type(&kb, "test.wc.S", "big");
    let small = term_ser::decode_value(&mut kb, &serde_json::json!(7), &big, opts()).unwrap();
    assert_eq!(text(&term_ser::encode_value(&kb, &small, &big, opts()).unwrap()), "7");
    let digits = CodecOptions {
        big_int: BigIntSpelling::AlwaysDigits,
        ..opts()
    };
    assert_eq!(text(&term_ser::encode_value(&kb, &small, &big, digits).unwrap()), r#""7""#);
    assert_eq!(term_ser::decode_value(&mut kb, &serde_json::json!("7"), &big, opts()).unwrap(), small);
    let rounded: serde_json::Value = serde_json::from_str("123456789012345678901234567890").unwrap();
    let err = term_ser::decode_value(&mut kb, &rounded, &big, opts()).expect_err("past u64, unquoted");
    assert!(matches!(err.problem, ValueProblem::OutOfRange { .. }), "{err}");
}

/// Every constructed value carries its tag: the untagged nested entity the ticket measured
/// stays refused, now naming the tag; a one-field shorthand is read by the payload's shape.
#[test]
fn constructed_values_carry_their_tag() {
    let mut kb = kb();
    let ps = field_type(&kb, "test.wc.S", "ps");
    let untagged: serde_json::Value = serde_json::from_str(r#"[{"id":1,"name":"a"}]"#).unwrap();
    let err = term_ser::decode_value(&mut kb, &untagged, &ps, opts()).expect_err("untagged");
    assert_eq!(
        err.problem,
        ValueProblem::NotTagged {
            found: "an object of 2 keys".into(),
            tags: vec!["P".into()]
        },
        "{err}"
    );
    assert_eq!(err.to_string(), "$[0]: expected P, found an object of 2 keys, where a constructed value is its constructor's tag (P)");

    let acc = field_type(&kb, "test.wc.S", "acc");
    for (json, problem) in [
        (r#"[{"Verified":"2027"}]"#, ValueProblem::NotOneField { constructor: "Verified".into(), fields: 2 }),
        (r#"["ToolPasses"]"#, ValueProblem::NotOneField { constructor: "ToolPasses".into(), fields: 1 }),
        (r#"["Verified"]"#, ValueProblem::NotOneField { constructor: "Verified".into(), fields: 2 }),
        (r#"["Opne"]"#, ValueProblem::UnknownConstructor { name: "Opne".into(), sort: "test.wc.Acceptance".into() }),
        (r#"[{"ToolPasses":{"tol":"x"}}]"#, ValueProblem::UnknownField { name: "tol".into() }),
        (r#"[{"Verified":{"at":"x"}}]"#, ValueProblem::MissingField { name: "by".into() }),
    ] {
        let json: serde_json::Value = serde_json::from_str(json).unwrap();
        let err = term_ser::decode_value(&mut kb, &json, &acc, opts()).expect_err("refused");
        assert_eq!(err.problem, problem, "{json}");
    }

    let err = term_ser::decode_value(&mut kb, &serde_json::json!(["ToolPasses"]), &acc, opts()).unwrap_err();
    assert!(err.to_string().ends_with("declares one field, so its payload is the object of its fields or its one field's value"), "{err}");

    // A value holds its constructor's fields and no others: an extra argument is refused, not
    // dropped. FAILS when backed out (measured): `P` is written without `extra`.
    let p_ty = term_ser::type_from_text(&mut kb, "test.wc.P").unwrap();
    let p = sym(&kb, "test.wc.P");
    let (id, name, extra) = (kb.intern("id"), kb.intern("name"), kb.intern("extra"));
    let (one, a) = (kb.alloc(Term::Const(Literal::Int(1))), kb.alloc(Term::Const(Literal::String("a".into()))));
    let wide = kb.alloc(Term::Fn {
        functor: p,
        pos_args: Default::default(),
        named_args: smallvec::smallvec![(id, one), (name, a), (extra, one)],
    });
    let err = term_ser::encode_value(&kb, &wide, &p_ty, opts()).expect_err("an extra argument");
    assert_eq!(err.problem, ValueProblem::UnknownField { name: "extra".into() });

    // A sort whose eponymous constructor has a sibling: the value is tagged either way. A
    // payload is read by its shape, so the fields object and the shorthand are one value, and
    // the writer writes the shorthand: the one field's encoding is not an object.
    let mix = term_ser::type_from_text(&mut kb, "test.wc.Mix").unwrap();
    for (json, written) in [(r#"{"Mix":{"x":3}}"#, r#"{"Mix":3}"#), (r#"{"Mix":3}"#, r#"{"Mix":3}"#), (r#""Other""#, r#""Other""#)] {
        let j: serde_json::Value = serde_json::from_str(json).unwrap();
        let t = term_ser::decode_value(&mut kb, &j, &mix, opts()).unwrap_or_else(|e| panic!("{json}: {e}"));
        assert_eq!(text(&term_ser::encode_value(&kb, &t, &mix, opts()).unwrap()), written);
    }

    // An absent field whose type has no reading keeps its own problem: at `Bag` with no `T`,
    // the parameter, not "a required field is absent".
    // FAILS when backed out (measured): `MissingField { name: "v" }`.
    let bag = term_ser::type_from_text(&mut kb, "test.wc.Bag").unwrap();
    let err = term_ser::decode_value(&mut kb, &serde_json::json!({"Bag": {}}), &bag, opts()).expect_err("T is open");
    assert_eq!(err.problem, ValueProblem::UnboundParameter { name: "T".into() }, "{err}");
    assert_eq!(err.to_string(), "$.Bag.v: expected T, type parameter `T` is bound neither by the type nor by a default");

    // `some(none())` has no spelling; `null` is the outer none. A variable standing for a whole
    // inner Option has none either, read or written. FAILS when backed out (measured): read
    // as `some(?x)`, which the writer refuses.
    let nest = field_type(&kb, "test.wc.Nest", "o");
    let err = term_ser::decode_value(&mut kb, &serde_json::json!("?x"), &nest, CodecOptions::data_file())
        .expect_err("?x for an inner Option");
    assert_eq!(err.problem, ValueProblem::Variable);
    let none = term_ser::decode_value(&mut kb, &serde_json::Value::Null, &nest, opts()).unwrap();
    assert_eq!(text(&term_ser::encode_value(&kb, &none, &nest, opts()).unwrap()), "null");
    let inner_none = term_ser::type_from_text(&mut kb, "anthill.prelude.Option[T = anthill.prelude.Int64]").unwrap();
    let n = term_ser::decode_value(&mut kb, &serde_json::Value::Null, &inner_none, opts()).unwrap();
    let some_none = {
        let some = sym(&kb, "anthill.prelude.Option.some");
        let value = kb.entity_field_names(some).unwrap()[0];
        kb.make_entity_term(some, Default::default(), smallvec::smallvec![(value, n)])
    };
    let err = term_ser::encode_value(&kb, &some_none, &nest, opts()).expect_err("some(none())");
    assert!(matches!(err.problem, ValueProblem::Unrepresentable { .. }), "{err}");
}

/// A type's text is read on behalf of NO file: a file-scoped import of the query source
/// scanned last does not reach it, so one text reads one way whatever was scanned before.
///
/// FAILS when backed out (measured): with the asking file left as the query's, `P` resolves
/// through the query's `import test.wc.{P}`.
#[test]
fn a_type_text_reads_at_global_on_behalf_of_no_file() {
    use anthill_core::kb::load;
    let mut kb = kb();
    let query = anthill_core::parse::parse("import test.wc.{P}\nfact P(id: 1, name: \"a\")\n").expect("parse");
    let ids = load::register_sources(&mut kb, &[&query]);
    let errors = load::scan_definitions_with_sources(
        &mut kb,
        &[&query],
        &ids,
        load::ImportAttribution::PerFile,
        load::SourceRole::Query,
    );
    assert!(errors.is_empty(), "{errors:?}");
    kb.set_asking_file(ids.first().copied());
    let err = term_ser::type_from_text(&mut kb, "P").expect_err("`P` is no name at <global>");
    assert_eq!(err.problem, ValueProblem::UnknownName { name: "P".into() });
    assert_eq!(kb.set_asking_file(None), ids.first().copied(), "the asking file is restored");
}

/// The options that change a spelling: an entity type's own constructor untagged, tags by
/// qualified name. The reader takes only the chosen spelling.
///
/// FAILS when backed out (measured): the writer ignoring `OmitAtEntityType` (`ps` keeps its
/// tags); `Qualified` written as the short name; the runtime-account refusal on the untagged
/// path (the account decodes).
#[test]
fn options_choose_the_spelling() {
    let mut kb = kb();
    let ps = field_type(&kb, "test.wc.S", "ps");
    let value = source_field(&kb, "ps");
    let omit = CodecOptions {
        entity_tags: EntityTags::OmitAtEntityType,
        ..opts()
    };
    let json = term_ser::encode_value(&kb, &value, &ps, omit).unwrap();
    assert_eq!(text(&json), r#"[{"id":1,"name":"a"},{"id":2,"name":"b"}]"#);
    assert_eq!(term_ser::decode_value(&mut kb, &json, &ps, omit).unwrap(), value);
    assert!(term_ser::decode_value(&mut kb, &json, &ps, opts()).is_err(), "the default reads tags only");

    // The runtime's accounts are refused untagged as tagged. FAILS when backed out (measured):
    // the account decodes at its constructor's own type.
    let account = term_ser::type_from_text(&mut kb, "anthill.reflect.LoadFailed.load_failed").unwrap();
    let err = term_ser::decode_value(&mut kb, &serde_json::json!({"diagnostics": []}), &account, omit)
        .expect_err("an account");
    assert!(matches!(err.problem, ValueProblem::RuntimeAccount { .. }), "{err}");

    // A sort's value is tagged still under OmitAtEntityType.
    let st = field_type(&kb, "test.wc.S", "st");
    let open = source_field(&kb, "st");
    assert_eq!(text(&term_ser::encode_value(&kb, &open, &st, omit).unwrap()), r#""Open""#);

    let qualified = CodecOptions {
        tag_names: TagNames::Qualified,
        ..opts()
    };
    let acc = field_type(&kb, "test.wc.S", "acc");
    let acc_value = source_field(&kb, "acc");
    let json = term_ser::encode_value(&kb, &acc_value, &acc, qualified).unwrap();
    assert_eq!(
        text(&json),
        r#"[{"test.wc.Acceptance.ToolPasses":"cargo-test"},{"test.wc.Acceptance.Verified":{"at":"2027-03-15","by":"rs"}}]"#
    );
    assert_eq!(term_ser::decode_value(&mut kb, &json, &acc, qualified).unwrap(), acc_value);
}

/// Keys are in DECLARED order, whatever order the names were interned in or the JSON wrote.
///
/// FAILS when backed out (measured): `preserve_order` off in anthill-core's Cargo.toml —
/// `{"Late":{"aa":2,"zz":1}}`.
#[test]
fn keys_in_declared_order() {
    let mut kb = kb();
    let late = term_ser::type_from_text(&mut kb, "test.wc.Late").unwrap();
    let json: serde_json::Value = serde_json::from_str(r#"{"Late":{"aa":2,"zz":1}}"#).unwrap();
    let t = term_ser::decode_value(&mut kb, &json, &late, opts()).unwrap();
    assert_eq!(text(&term_ser::encode_value(&kb, &t, &late, opts()).unwrap()), r#"{"Late":{"zz":1,"aa":2}}"#);
}

/// A type with no data spelling is refused at both ends, naming the type.
///
/// FAILS when backed out (measured): a sort with no constructors read as a data sort (the
/// refusal is then `WrongShape`, a shape no value could have).
#[test]
fn a_type_with_no_data_spelling_is_refused() {
    let mut kb = kb();
    for text_ty in ["anthill.prelude.Map[K = anthill.prelude.Int64, V = anthill.prelude.Int64]", "(anthill.prelude.Int64) -> anthill.prelude.Int64"] {
        let ty = term_ser::type_from_text(&mut kb, text_ty).unwrap_or_else(|e| panic!("{text_ty}: {e}"));
        let err = term_ser::decode_value(&mut kb, &serde_json::json!([]), &ty, opts()).expect_err(text_ty);
        assert_eq!(err.problem, ValueProblem::NoDataSpelling, "{err}");
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let err = term_ser::encode_value(&kb, &one, &ty, opts()).expect_err(text_ty);
        assert_eq!(err.problem, ValueProblem::NoDataSpelling, "{err}");
    }
}

// ── The data file, rebuilt on the pair ─────────────────────────

/// The three MEASURED faults of the ticket, at the file: a nested entity, a number under Float,
/// and an escaped `?` string; and a generic entity named by `meta.entity` with its argument.
///
/// MEASURED AGAINST THE OLD CODE (e25f0b734, its `load_json` / `serialize_json` on this
/// fixture): the writer wrote `ps` and `at` untagged, as `{"id": 1, "name": "a"}`, and its own
/// file failed to load back (`inline object with multiple keys must be inside a data entry`);
/// `"f": 3` loaded a SECOND fact, distinct from the source's (the Int64 3); a bracket in
/// `meta.entity` was `unknown entity`; and `"id": 3.5` under Int64 loaded, as a Float.
#[test]
fn a_data_file_is_one_use_of_the_pair() {
    let mut kb = kb();
    let domain = kb.intern("wc.data");
    let s = sym(&kb, "test.wc.S");
    let source = kb.rules_by_functor(s);
    let json = term_ser::serialize_json(&kb, "test.wc.S", &source).expect("the source fact is written");
    let mut fresh = kb_without_facts();
    let d = fresh.intern("wc.data");
    assert_eq!(term_ser::load_json(&mut fresh, &json, d).expect("and read back"), 1);
    let reloaded = fresh.rules_by_functor(sym(&fresh, "test.wc.S"));
    let again = term_ser::serialize_json(&fresh, "test.wc.S", &reloaded).unwrap();
    assert_eq!(json, again, "the file round-trips byte for byte");

    // A tuple in another order than its field's type is written in its own and reloads as
    // the SAME fact; one wider than its type is refused by the file writer, not projected.
    // FAILS when backed out (measured): written in the type's order, a second fact; with
    // the file writer projecting, `extra` is dropped and the write succeeds.
    let h = sym(&kb, "test.wc.H");
    let h_rows = kb.rules_by_functor(h);
    let h_json = term_ser::serialize_json(&kb, "test.wc.H", &h_rows).unwrap();
    assert!(h_json.contains("\"n\": 3,\n      \"state\": \"Open\""), "{h_json}");
    assert_eq!(term_ser::load_json(&mut kb, &h_json, domain).unwrap(), 1);
    let heads: std::collections::HashSet<_> = kb.rules_by_functor(h).iter().map(|r| kb.rule_head(*r)).collect();
    assert_eq!(heads.len(), 1, "the reloaded fact is the source's");
    let wide = kb.rules_by_functor(sym(&kb, "test.wc.Wide"));
    let err = term_ser::serialize_json(&kb, "test.wc.Wide", &wide).expect_err("a wider tuple");
    assert!(
        matches!(&err, SerError::Row { error: ValueError { problem: ValueProblem::WiderThanDeclared { labels }, .. }, .. } if labels == &["extra"]),
        "{err}"
    );

    // `3` under Float loads as the Float, so the reloaded fact IS the source's.
    let edited = json.replace("\"f\": 3.0", "\"f\": 3");
    assert_ne!(edited, json, "the fixture writes f");
    assert_eq!(term_ser::load_json(&mut kb, &edited, domain).unwrap(), 1);
    let after = kb.rules_by_functor(s);
    assert!(after.iter().all(|r| kb.rule_head(*r) == kb.rule_head(source[0])), "one fact, written twice");

    // A generic entity, named with its argument.
    let boxes = r#"{"meta":{"entity":"test.wc.Box[T = anthill.prelude.String]"},"data":{"items":["a","b"]}}"#;
    assert_eq!(term_ser::load_json(&mut kb, boxes, domain).expect("Box[T = String] rows"), 1);
    let bad = r#"{"meta":{"entity":"test.wc.Box[T = anthill.prelude.String]"},"data":[{"items":["a"]},{"items":[1]}]}"#;
    let errs = term_ser::load_json(&mut kb, bad, domain).expect_err("an Int64 under T = String");
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].to_string(), "data[1].items[0]: expected String, found 1");
    let ty = term_ser::type_from_text(&mut kb, "test.wc.Box[T = anthill.prelude.String]").unwrap();
    let rows = kb.rules_by_functor(sym(&kb, "test.wc.Box"));
    let written = term_ser::serialize_json_at(&kb, &ty, &rows).expect("written at its type");
    assert!(written.contains(r#""entity": "test.wc.Box[T = anthill.prelude.String]""#), "{written}");
    assert!(matches!(
        term_ser::serialize_json(&kb, "test.wc.Box[T = anthill.prelude.String]", &rows),
        Err(SerError::Format(_))
    ));

    // A number under Int64 that is not written as an integer, and the untagged nested entity,
    // are refused at their place in the row.
    let int35 = r#"{"meta":{"entity":"test.wc.P"},"data":{"id":3.5,"name":"a"}}"#;
    let errs = term_ser::load_json(&mut kb, int35, domain).expect_err("3.5 under Int64");
    assert_eq!(errs[0].to_string(), "data.id: expected Int64, found 3.5, which is not written as an integer");
    let mut untagged: serde_json::Value = serde_json::from_str(&json).unwrap();
    untagged["data"]["ps"][0] = serde_json::json!({ "id": 1, "name": "a" });
    let errs = term_ser::load_json(&mut kb, &untagged.to_string(), domain).expect_err("an untagged nested entity");
    assert_eq!(
        errs[0].to_string(),
        "data.ps[0]: expected P, found an object of 2 keys, where a constructed value is its constructor's tag (P)"
    );

    // TOML's `nan` has no JSON value: refused where it is written, as an error of its row
    // beside the other rows', not read as `null` and not aborting the file.
    // FAILS when backed out to the old `null` (measured): the refusal is then
    // `expected Int64, found null`, and under an `Option` field the row would load.
    let nan = "[meta]\nentity = \"test.wc.Late\"\n\n[[data]]\nzz = 1\naa = nan\n\n[[data]]\nzz = \"x\"\naa = 2\n";
    let errs = term_ser::load_toml(&mut kb, nan, domain).expect_err("nan");
    let errs: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
    assert_eq!(
        errs,
        [
            "data[0].aa: expected Int64, the TOML float `nan` has no spelling",
            r#"data[1].zz: expected Int64, found "x""#
        ]
    );

    // A row of a `data` object is `data`, not an index the file does not hold.
    let one = r#"{"meta":{"entity":"test.wc.P"},"data":{"id":"x","name":"a"}}"#;
    let errs = term_ser::load_json(&mut kb, one, domain).expect_err("a string under Int64");
    assert_eq!(errs[0].to_string(), r#"data.id: expected Int64, found "x""#);

    // A row's error names the row.
    let missing = r#"{"meta":{"entity":"test.wc.P"},"data":[{"id":1,"name":"a"},{"id":2}]}"#;
    let errs = term_ser::load_json(&mut kb, missing, domain).expect_err("a missing field");
    assert!(
        matches!(&errs[..], [SerError::Row { index: Some(1), error: ValueError { problem: ValueProblem::MissingField { name }, .. } }] if name == "name"),
        "{errs:?}"
    );
}

fn kb_without_facts() -> KnowledgeBase {
    let start = DECLS.find("  fact S(").expect("the fact");
    let end = DECLS[start..].find("\n\n").map(|e| start + e).expect("its end");
    load_kb_with(&format!("{}{}", &DECLS[..start], &DECLS[end..]))
}
