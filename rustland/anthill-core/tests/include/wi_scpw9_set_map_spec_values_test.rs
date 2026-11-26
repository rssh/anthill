//! WI-20261125-SCPW9 — spellings, through `term_ser::decode_value` / `encode_value`, for a `Set`,
//! a `Map`, and a value at a sort with abstract values (a spec its providers' values are values
//! of, proposal 073 §2). Before this ticket each was refused `NoDataSpelling` at both ends
//! (measured on 8ed4765f3 through anthill-traces' test binary).
//!
//! - A set is the array of its elements, read as the `insert` / `empty` chain a fact writes and
//!   written in one order, each element once.
//! - A map is the array of its `[key, value]` entries, read as the `put` / `empty` chain a fact
//!   writes; written from that chain or from a running map's handle, in the order of its keys.
//! - A value at `Sp` (providers `Car`, `Van`) is tagged by its constructor among the providers';
//!   read as `Instance(dict, value)`, the pair an operation body builds and a call takes (decided
//!   with the user 2026-11-25), and as the provider's value alone in a data file, which is how a
//!   source fact holds it.
//!
//! Each row drives the pair and asserts the term (by hash-consed identity with the one a fact or
//! an operation body builds) or the bytes; the spec rows also run an operation on what was read.
//! The back-outs at each row were MEASURED, one at a time, on a binary of this file and the
//! codec's two other suites (`wi_wc18y_value_codec_test`, `wi_cmqj4_declared_type_shape_test`),
//! which pass under every one of them.
use anthill_core::eval::{HostValue, Interpreter, Value};
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::term_view::TermView;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::term_ser::{
    self, CodecOptions, DeclaredType, SpecValues, TagNames, TypeShape, ValueError, ValueProblem,
};
use smallvec::SmallVec;

use crate::common::interp_for;

const SRC: &str = r#"
namespace test.sc
  import anthill.prelude.{Set, Map, List, Int64, String}

  entity P(id: Int64, name: String)

  entity Ints(s: Set[T = Int64])
  fact Ints(s: Set.insert(Set.insert(Set.insert(Set.empty(), 2), 10), 1))
  entity Again(s: Set[T = Int64])
  fact Again(s: Set.insert(Set.insert(Set.insert(Set.insert(Set.empty(), 1), 10), 2), 1))
  entity Ps(s: Set[T = P])
  fact Ps(s: Set.insert(Set.insert(Set.empty(), P(id: 2, name: "b")), P(id: 1, name: "a")))

  entity Prices(m: Map[K = String, V = Int64])
  fact Prices(m: Map.put(Map.put(Map.empty(), "b", 2), "a", 1))
  entity Shadowed(m: Map[K = String, V = Int64])
  fact Shadowed(m: Map.put(Map.put(Map.empty(), "a", 1), "a", 3))
  operation prices() -> Map[K = String, V = Int64] = Map.put(Map.put(Map.empty(), "b", 2), "a", 1)
  operation shadowed() -> Map[K = String, V = Int64] = Map.put(Map.put(Map.empty(), "a", 1), "a", 3)
  operation byP() -> Map[K = P, V = Int64] =
    Map.put(Map.put(Map.empty(), P(id: 2, name: "b"), 20), P(id: 1, name: "a"), 10)

  sort Sp
    operation size(s: Sp) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp
    operation size(c: Car) -> Int64 = 40
  end
  sort Van
    entity van(n: Int64)
    provides Sp
    operation size(c: Van) -> Int64 = 2
  end
  entity Fleet(xs: List[T = Sp])
  fact Fleet(xs: [car(n: 1), van(n: 2)])
  operation total(xs: List[T = Sp]) -> Int64 = List.foldLeft(xs, 0, lambda (acc, c) -> acc + Sp.size(c))
  operation fleet() -> Fleet = Fleet(xs: [car(n: 1), van(n: 2)])
  operation fleetTotal(f: Fleet) -> Int64 = total(f.xs)
  operation one(x: Sp) -> Int64 = Sp.size(x)

  -- Two providers whose constructors share a short name.
  sort Sq
    operation w(s: Sq) -> Int64
  end
  sort Bus
    entity mk(n: Int64)
    provides Sq
    operation w(b: Bus) -> Int64 = 1
  end
  sort Tram
    entity mk(n: Int64)
    provides Sq
    operation w(t: Tram) -> Int64 = 2
  end
  operation weight(x: Sq) -> Int64 = Sq.w(x)

  -- A spec two providers provide at two applications.
  sort Sk
    sort T = ?
    operation k(s: Sk) -> Int64
  end
  sort Cart
    entity cart(n: Int64)
    provides Sk[T = Int64]
    operation k(c: Cart) -> Int64 = 3
  end
  sort Bike
    entity bike(n: Int64)
    provides Sk[T = String]
    operation k(b: Bike) -> Int64 = 5
  end

  -- A provider whose provision binds the spec through its own parameter, at its default.
  sort Gen
    sort T = ? default String
    entity gen(v: T)
    provides Sk[T = T]
    operation k(g: Self) -> Int64 = 7
  end

  -- A spec applied at a parameter of the sort whose field it types.
  sort Rack
    sort A = ?
    entity rack(x: Sk[T = A])
  end

  -- A spec no sort with constructors provides.
  sort Lonely
    operation f(s: Lonely) -> Int64
  end
end
"#;

fn interp() -> Interpreter {
    interp_for(SRC)
}

fn sym(kb: &KnowledgeBase, name: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(name).unwrap_or_else(|| panic!("`{name}` resolves"))
}

/// The declared type of `entity`'s one field `field`.
fn field_type(kb: &KnowledgeBase, entity: &str, field: &str) -> Value {
    let e = sym(kb, entity);
    kb.entity_field_types(e)
        .expect("declared fields")
        .iter()
        .find(|(f, _)| kb.local_name_of(*f) == field)
        .map(|(_, t)| t.clone())
        .unwrap_or_else(|| panic!("`{entity}` declares `{field}`"))
}

/// The value the one source fact of `entity` holds in `field`.
fn fact_field(kb: &KnowledgeBase, entity: &str, field: &str) -> TermId {
    let rids = kb.rules_by_functor(sym(kb, entity));
    assert_eq!(rids.len(), 1, "one source fact of {entity}");
    kb.rule_head(rids[0])
        .named_field(kb, field)
        .and_then(|v| v.as_term_id())
        .unwrap_or_else(|| panic!("the fact of {entity} holds `{field}`"))
}

fn ty(kb: &mut KnowledgeBase, text: &str) -> TermId {
    term_ser::type_from_text(kb, text).unwrap_or_else(|e| panic!("`{text}`: {e}"))
}

fn json(text: &str) -> serde_json::Value {
    serde_json::from_str(text).unwrap_or_else(|e| panic!("`{text}`: {e}"))
}

fn text(json: &serde_json::Value) -> String {
    serde_json::to_string(json).expect("JSON text")
}

fn opts() -> CodecOptions {
    CodecOptions::default()
}

fn decode_err(kb: &mut KnowledgeBase, value: &str, at: &impl TermView, opts: CodecOptions) -> ValueError {
    term_ser::decode_value(kb, &json(value), at, opts).expect_err(value)
}

// ── Set ─────────────────────────────────────────────────────────

/// A set is the array of its elements: `[2, 10, 1]` reads as the very term the fact
/// `Ints(s: Set.insert(Set.insert(Set.insert(Set.empty(), 2), 10), 1))` holds (each element
/// inserted in the array's order), and the set is written in one order whatever order it was
/// built in or how often an element was inserted: the fact, a set read in another order, and a
/// set that inserts `1` twice (`Again`) are each `[1,2,10]` — by value, not by text (`10` after
/// `2`) — every time.
///
/// FAILS when backed out (measured): the `Set` shape (`NoDataSpelling` at both ends); the
/// writer's order; the writer's dedup (`Again`'s `1` is written twice); ordering by the text of
/// the spellings instead of `json_order` (`10` before `2`).
#[test]
fn a_set_is_the_array_of_its_elements() {
    let mut interp = interp();
    let kb = interp.kb_mut();
    let set_ty = field_type(kb, "test.sc.Ints", "s");
    let source = fact_field(kb, "test.sc.Ints", "s");
    let read = term_ser::decode_value(kb, &json("[2, 10, 1]"), &set_ty, opts()).expect("the set decodes");
    assert_eq!(read, source, "`[2, 10, 1]` is the fact's own `insert` chain");

    let other = term_ser::decode_value(kb, &json("[1, 2, 10]"), &set_ty, opts()).expect("another order decodes");
    assert_ne!(other, source, "another order is another chain");
    let again = fact_field(kb, "test.sc.Again", "s");
    for (what, set) in [("the fact", source), ("another order", other), ("`1` inserted twice", again)] {
        for _ in 0..2 {
            let written = term_ser::encode_value(kb, &set, &set_ty, opts()).unwrap_or_else(|e| panic!("{what}: {e}"));
            assert_eq!(text(&written), "[1,2,10]", "{what} is written in one order, each element once");
        }
    }
}

/// A set of entities is the array of their tagged spellings, read as the fact's chain and
/// written in the order of those spellings (`P(id: 1, …)` before `P(id: 2, …)`).
///
/// FAILS when backed out (measured): the `Set` shape; the writer's order.
#[test]
fn a_set_of_entities() {
    let mut interp = interp();
    let kb = interp.kb_mut();
    let set_ty = field_type(kb, "test.sc.Ps", "s");
    let source = fact_field(kb, "test.sc.Ps", "s");
    let written = term_ser::encode_value(kb, &source, &set_ty, opts()).expect("the set encodes");
    assert_eq!(
        text(&written),
        r#"[{"P":{"id":1,"name":"a"}},{"P":{"id":2,"name":"b"}}]"#
    );
    let in_fact_order = json(r#"[{"P":{"id":2,"name":"b"}},{"P":{"id":1,"name":"a"}}]"#);
    let read = term_ser::decode_value(kb, &in_fact_order, &set_ty, opts()).expect("decodes");
    assert_eq!(read, source, "read in the fact's order, the fact's own term");
    let back = term_ser::decode_value(kb, &written, &set_ty, opts()).expect("the written set decodes");
    assert_eq!(text(&term_ser::encode_value(kb, &back, &set_ty, opts()).unwrap()), text(&written));
}

/// What a set refuses: an element written twice (the same term, however it is spelled: the
/// single-field shorthand is the same `P`), not an array, an element of another type, and a
/// set with a variable tail.
///
/// FAILS when backed out (measured): the repeated-element check (`[1, 2, 1]` decodes); the `Set`
/// shape.
#[test]
fn what_a_set_refuses() {
    let mut interp = interp();
    let kb = interp.kb_mut();
    let ints = field_type(kb, "test.sc.Ints", "s");
    let err = decode_err(kb, "[1, 2, 1]", &ints, opts());
    assert_eq!(err.problem, ValueProblem::RepeatedElement { first: 0 }, "{err}");
    assert_eq!(err.path.to_string(), "$[2]", "{err}");
    assert_eq!(
        err.to_string(),
        "$[2]: expected Set[T = Int64], found the element written at index 0 again; a set holds an element once"
    );

    let ps = field_type(kb, "test.sc.Ps", "s");
    let err = decode_err(kb, r#"[{"P":{"id":1,"name":"a"}},{"P":{"name":"a","id":1}}]"#, &ps, opts());
    assert_eq!(err.problem, ValueProblem::RepeatedElement { first: 0 }, "{err}");

    let err = decode_err(kb, r#"{"a": 1}"#, &ints, opts());
    assert!(matches!(err.problem, ValueProblem::WrongShape { .. }), "{err}");
    let err = decode_err(kb, r#"[1, "x"]"#, &ints, opts());
    assert_eq!(err.path.to_string(), "$[1]", "{err}");
    assert_eq!(err.expected, "Int64", "{err}");

    // `insert(?s, 1)`: no array holds its unknown rest.
    let insert = sym(kb, "anthill.prelude.Set.insert");
    let s = kb.intern("s");
    let var = kb.fresh_var(s);
    let rest = kb.alloc(Term::Var(Var::Global(var)));
    let one = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(1)));
    let open = kb.alloc(Term::Fn {
        functor: insert,
        pos_args: SmallVec::from_slice(&[rest, one]),
        named_args: SmallVec::new(),
    });
    let err = term_ser::encode_value(kb, &open, &ints, opts()).expect_err("a variable tail");
    assert_eq!(
        err.problem,
        ValueProblem::Unrepresentable {
            what: "a set with a variable tail".into()
        }
    );
}

// ── Map ─────────────────────────────────────────────────────────

/// A map is the array of its `[key, value]` entries: `[["b", 2], ["a", 1]]` reads as the fact
/// `Prices(m: Map.put(Map.put(Map.empty(), "b", 2), "a", 1))`'s own `put` chain, and is written
/// in the order of its keys. A running map, a host handle with no term, is written the same as
/// its chain, from the handle alone (it carries its own arena: no interpreter is passed). A later
/// `put` of a key shadows an earlier one, in the chain and in the running map alike.
///
/// FAILS when backed out (measured): the `Map` shape (`NoDataSpelling` at both ends); the
/// handle's reading (the running map is no `put` chain); the chain's shadowing (`Shadowed`
/// writes `a` twice); the writer's order (the map read back from its own text, built in another
/// order, is written in that order).
#[test]
fn a_map_is_the_array_of_its_entries() {
    let mut interp = interp();
    let map_ty = field_type(interp.kb(), "test.sc.Prices", "m");
    let kb = interp.kb_mut();
    let source = fact_field(kb, "test.sc.Prices", "m");
    let read = term_ser::decode_value(kb, &json(r#"[["b", 2], ["a", 1]]"#), &map_ty, opts()).expect("decodes");
    assert_eq!(read, source, "the entries in the array's order are the fact's own `put` chain");
    let written = term_ser::encode_value(kb, &source, &map_ty, opts()).expect("the chain encodes");
    assert_eq!(text(&written), r#"[["a",1],["b",2]]"#);
    let back = term_ser::decode_value(kb, &written, &map_ty, opts()).expect("the written map decodes");
    assert_eq!(text(&term_ser::encode_value(kb, &back, &map_ty, opts()).unwrap()), text(&written));

    let running = interp.call("test.sc.prices", &[]).expect("prices runs").value;
    assert!(matches!(running, Value::Map(_)), "a running map is a handle: {running:?}");
    let from_handle = term_ser::encode_value(interp.kb(), &running, &map_ty, opts()).expect("the handle encodes");
    assert_eq!(text(&from_handle), text(&written), "a running map is written as its chain is");

    let shadowed_ty = field_type(interp.kb(), "test.sc.Shadowed", "m");
    let chain = fact_field(interp.kb(), "test.sc.Shadowed", "m");
    let from_chain = term_ser::encode_value(interp.kb(), &chain, &shadowed_ty, opts()).expect("encodes");
    assert_eq!(text(&from_chain), r#"[["a",3]]"#, "the later `put` of `a` shadows the earlier");
    let running = interp.call("test.sc.shadowed", &[]).expect("shadowed runs").value;
    let from_handle = term_ser::encode_value(interp.kb(), &running, &shadowed_ty, opts()).expect("encodes");
    assert_eq!(text(&from_handle), r#"[["a",3]]"#);
}

/// What a map refuses: a key written twice (its value would be the array's order alone), an
/// entry that is not `[key, value]`, a value of another type at its place in the entry, and an
/// object — one spelling, keys strings or not.
///
/// FAILS when backed out (measured): the repeated-key check (`[["a", 1], ["a", 2]]` decodes); the
/// `Map` shape.
#[test]
fn what_a_map_refuses() {
    let mut interp = interp();
    let map_ty = field_type(interp.kb(), "test.sc.Prices", "m");
    let kb = interp.kb_mut();
    let err = decode_err(kb, r#"[["a", 1], ["a", 2]]"#, &map_ty, opts());
    assert_eq!(err.problem, ValueProblem::RepeatedKey { first: 0 }, "{err}");
    assert_eq!(
        err.to_string(),
        "$[1]: expected Map[K = String, V = Int64], found the key of the entry at index 0 again; a map holds a key once"
    );
    let err = decode_err(kb, r#"[["a"]]"#, &map_ty, opts());
    assert_eq!(err.problem, ValueProblem::NotAnEntry { found: "an array of 1 elements".into() }, "{err}");
    assert_eq!(err.path.to_string(), "$[0]");
    let err = decode_err(kb, r#"[["a", "x"]]"#, &map_ty, opts());
    assert_eq!(err.path.to_string(), "$[0][1]", "{err}");
    assert_eq!(err.expected, "Int64", "{err}");
    let err = decode_err(kb, r#"{"a": 1}"#, &map_ty, opts());
    assert!(matches!(err.problem, ValueProblem::WrongShape { .. }), "{err}");
}

// ── A value at a sort with abstract values ──────────────────────

/// `{"car": {"n": 1}}` at `Sp` is `car(n: 1)` paired with `Car`'s dictionary, the very term an
/// operation body builds (the lowered value of `fleet()`, element by element), and a call takes
/// it: `one` answers 40 on it, and `fleetTotal` 42 on a `Fleet` read whole. Read with
/// `SpecValues::Plain` it is the provider's value alone, which a call refuses at the abstract
/// sort — the control. Written back, as the running pair and as the source fact's plain value
/// alike, it is the provider's value tagged by its constructor (`{"car":1}`, 021's single-field
/// shorthand, which reads back as the same).
///
/// FAILS when backed out (measured): the abstract sort's shape (`NoDataSpelling` at both ends);
/// the pairing (`one` and `fleetTotal` are refused "holds no instance", and the identity with
/// `fleet()`'s value fails); the writer opening the pair (the running `Fleet` is refused
/// `UnknownConstructor` `Instance`).
#[test]
fn a_spec_value_is_its_providers_value_paired_with_its_dictionary() {
    let mut interp = interp();
    let sp = ty(interp.kb_mut(), "test.sc.Sp");
    let car = term_ser::decode_value(interp.kb_mut(), &json(r#"{"car": {"n": 1}}"#), &sp, opts()).expect("decodes");
    // At its declared type: a bare pair is read at its carrier's type by a host call
    // (`Interpreter::call`), as the value it carries.
    let at_sp = |v: TermId| HostValue::typed(Value::term(v), Value::term(sp));
    let answer = interp.call("test.sc.one", &[at_sp(car)]).expect("`one` runs on it");
    assert_eq!(answer.value.literal_int64(interp.kb()), Some(40));
    let written = term_ser::encode_value(interp.kb(), &car, &sp, opts()).expect("the pair encodes");
    assert_eq!(text(&written), r#"{"car":1}"#);

    let fleet_ty = ty(interp.kb_mut(), "test.sc.Fleet");
    let built = interp.call("test.sc.fleet", &[]).expect("fleet runs").value;
    let built_term = interp.kb_mut().alloc_from_value(&built).expect("a fleet lowers");
    let read = term_ser::decode_value(
        interp.kb_mut(),
        &json(r#"{"Fleet": [{"car": {"n": 1}}, {"van": {"n": 2}}]}"#),
        &fleet_ty,
        opts(),
    )
    .expect("a fleet decodes");
    assert_eq!(read, built_term, "the term an operation body builds, its elements paired");
    let total = interp.call("test.sc.fleetTotal", &HostValue::all(&[Value::term(read)])).expect("runs");
    assert_eq!(total.value.literal_int64(interp.kb()), Some(42));

    let want = r#"{"Fleet":[{"car":1},{"van":2}]}"#;
    let from_running = term_ser::encode_value(interp.kb(), &built, &fleet_ty, opts()).expect("the running fleet encodes");
    assert_eq!(text(&from_running), want);
    let fact = interp.kb().rule_head(interp.kb().rules_by_functor(sym(interp.kb(), "test.sc.Fleet"))[0]);
    let from_fact = term_ser::encode_value(interp.kb(), &fact, &fleet_ty, opts()).expect("the fact encodes");
    assert_eq!(text(&from_fact), want, "the fact's plain values are written as the pairs are");

    // The control: the provider's value alone is no value a call at `Sp` takes.
    let plain = CodecOptions {
        spec_values: SpecValues::Plain,
        ..opts()
    };
    let bare = term_ser::decode_value(interp.kb_mut(), &json(r#"{"car": {"n": 1}}"#), &sp, plain).expect("decodes");
    assert_ne!(bare, car);
    let refused = interp.call("test.sc.one", &[at_sp(bare)]).expect_err("no instance");
    assert!(format!("{refused:?}").contains("holds no instance"), "{refused:?}");
}

/// A data file reads a value at an abstract sort as the provider's value alone
/// (`CodecOptions::data_file`), which is how the source fact holds it: the file the source fact
/// is written to reads back as that fact's own term, and the pair is no fact of it.
///
/// FAILS when backed out (measured): `data_file`'s `SpecValues::Plain` (the row reads back as
/// the pairs, another term than the source fact's); the abstract sort's shape; the pairing (the
/// defaults then read the plain value too).
#[test]
fn a_data_file_reads_a_spec_value_as_a_source_fact_holds_it() {
    let mut interp = interp();
    let kb = interp.kb_mut();
    let fleet = sym(kb, "test.sc.Fleet");
    let source = kb.rules_by_functor(fleet);
    let file = term_ser::serialize_json(kb, "test.sc.Fleet", &source).expect("the fact is written");
    let row: serde_json::Value = serde_json::from_str::<serde_json::Value>(&file).unwrap()["data"].clone();
    assert_eq!(text(&row), r#"{"xs":[{"car":1},{"van":2}]}"#);
    let xs_ty = field_type(kb, "test.sc.Fleet", "xs");
    let read = term_ser::decode_value(kb, &row["xs"], &xs_ty, CodecOptions::data_file()).expect("decodes");
    assert_eq!(read, fact_field(kb, "test.sc.Fleet", "xs"), "the source fact's own plain values");
    let paired = term_ser::decode_value(kb, &row["xs"], &xs_ty, opts()).expect("decodes");
    assert_ne!(paired, read, "with the defaults the elements are pairs");

    // Loaded beside the source fact, the row is that fact again, not another.
    let domain = kb.intern("scpw9.data");
    let loaded = term_ser::load_json(kb, &file, domain).expect("the file loads");
    assert_eq!(loaded, 1);
    let heads: Vec<TermId> = kb.rules_by_functor(fleet).iter().map(|r| kb.rule_head(*r)).collect();
    assert!(heads.iter().all(|h| *h == heads[0]), "one fact, read back as itself: {heads:?}");
}

/// What a value at an abstract sort refuses, by name: a tag no provider's constructor has; a
/// short tag two providers' constructors share (`Bus.mk`, `Tram.mk`), at both ends, which their
/// qualified names tell apart; a provider of the sort at another application (`Bike provides
/// Sk[T = String]` is no `Sk[T = Int64]`, though its provision answers for `Sk`), at both ends;
/// one whose provision binds through its own parameter, refused where its dictionary is built;
/// and a spec no sort with constructors provides, which has no spelling at all.
///
/// FAILS when backed out (measured): the reader's ambiguity check (`{"mk": 1}` reads as one of
/// the two); the writer's (`Tram.mk(n: 2)` is written `{"mk":2}`); the providers read at the
/// type's bindings (`typing::provider_admitted_at`: `bike` is read and written at `Sk[T =
/// Int64]`); the place's own type before the dictionary (`gen` at `Sk[T = Int64]` is paired with
/// `Gen`'s `Sk[T = String]` instance, in `typing::instance_dictionary_of_read_value`); the
/// abstract sort's shape; the pairing (the `weight` call is refused "holds no instance"); the
/// writer opening the pair.
#[test]
fn what_a_spec_value_refuses() {
    let mut interp = interp();
    let kb = interp.kb_mut();
    let sp = ty(kb, "test.sc.Sp");
    let err = decode_err(kb, r#"{"truck": {"n": 1}}"#, &sp, opts());
    assert_eq!(
        err.problem,
        ValueProblem::UnknownConstructor {
            name: "truck".into(),
            sort: "test.sc.Sp".into()
        },
        "{err}"
    );
    let five = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(5)));
    let err = term_ser::encode_value(kb, &five, &sp, opts()).expect_err("an Int64 at Sp");
    assert!(matches!(err.problem, ValueProblem::WrongShape { .. }), "{err}");

    let sq = ty(kb, "test.sc.Sq");
    let shared = ValueProblem::AmbiguousTag {
        tag: "mk".into(),
        constructors: vec!["test.sc.Bus.mk".into(), "test.sc.Tram.mk".into()],
    };
    let err = decode_err(kb, r#"{"mk": 1}"#, &sq, opts());
    assert_eq!(err.problem, shared, "{err}");
    assert_eq!(
        err.to_string(),
        "$: expected Sq, 'mk' names 2 constructors (test.sc.Bus.mk, test.sc.Tram.mk), so a value \
         tagged so has no one reading; tag them by their qualified names (TagNames::Qualified)"
    );
    let qualified = CodecOptions {
        tag_names: TagNames::Qualified,
        ..opts()
    };
    let tram = term_ser::decode_value(kb, &json(r#"{"test.sc.Tram.mk": 2}"#), &sq, qualified).expect("decodes");
    let err = term_ser::encode_value(kb, &tram, &sq, opts()).expect_err("an ambiguous short tag");
    assert_eq!(err.problem, shared, "{err}");
    let written = term_ser::encode_value(kb, &tram, &sq, qualified).expect("qualified");
    assert_eq!(text(&written), r#"{"test.sc.Tram.mk":2}"#);
    let weight = interp
        .call("test.sc.weight", &[HostValue::typed(Value::term(tram), Value::term(sq))])
        .expect("runs");
    assert_eq!(weight.value.literal_int64(interp.kb()), Some(2), "the pair is Tram's");

    // A provider at another application is no constructor of the type, at both ends.
    let kb = interp.kb_mut();
    let sk_int = ty(kb, "test.sc.Sk[T = anthill.prelude.Int64]");
    let sk_string = ty(kb, "test.sc.Sk[T = anthill.prelude.String]");
    term_ser::decode_value(kb, &json(r#"{"cart": 1}"#), &sk_int, opts()).expect("`Cart` provides `Sk[T = Int64]`");
    let not_here = ValueProblem::UnknownConstructor {
        name: "bike".into(),
        sort: "test.sc.Sk".into(),
    };
    let err = decode_err(kb, r#"{"bike": 1}"#, &sk_int, opts());
    assert_eq!(err.problem, not_here, "{err}");
    let bike = term_ser::decode_value(kb, &json(r#"{"bike": 1}"#), &sk_string, opts()).expect("at its own");
    let err = term_ser::encode_value(kb, &bike, &sk_int, opts()).expect_err("written at another application");
    assert_eq!(
        err.problem,
        ValueProblem::UnknownConstructor {
            name: "test.sc.Bike.bike".into(),
            sort: "test.sc.Sk".into()
        },
        "{err}"
    );
    // A provision through the provider's own parameter admits any application on its face; the
    // provider's type at the value (`Gen[T = String]`, its field read at `T`'s default) decides, by
    // resolution.
    term_ser::decode_value(kb, &json(r#"{"gen": "x"}"#), &sk_string, opts()).expect("`Gen` is an `Sk[T = String]`");
    let err = decode_err(kb, r#"{"gen": "x"}"#, &sk_int, opts());
    assert!(
        matches!(&err.problem, ValueProblem::NoInstance { reason } if reason.contains("it is no")),
        "{err}"
    );

    let lonely = ty(kb, "test.sc.Lonely");
    let err = decode_err(kb, r#"{"x": 1}"#, &lonely, opts());
    assert_eq!(err.problem, ValueProblem::NoDataSpelling, "{err}");
    let err = term_ser::encode_value(kb, &five, &lonely, opts()).expect_err("Lonely");
    assert_eq!(err.problem, ValueProblem::NoDataSpelling, "{err}");
}

/// A value at an abstract sort applied at a parameter of its place (`rack(x: Sk[T = A])`) is
/// paired with the dictionary at the place's binding: at `Rack[A = Int64]` a `cart` (`Cart
/// provides Sk[T = Int64]`) and not a `bike`, at `Rack[A = String]` the other way round. And a
/// walker reads the providers as the codec does, through `DeclaredType::shape`: `Sp`'s
/// constructors are `car` and `van`, each with its provider, where a data sort's have none.
///
/// FAILS when backed out (measured): the place's bindings substituted into the type the
/// dictionary is built at (`closed_type` answering the field's type as written, `Sk[T = A]`:
/// `gen` is paired at `Rack[A = Int64]`); the providers read at the type's bindings (`bike` is
/// read at `Rack[A = Int64]`, `cart` at `Rack[A = String]`).
#[test]
fn a_spec_value_in_a_generic_place_is_read_at_its_bindings() {
    let mut interp = interp();
    let kb = interp.kb_mut();
    let at_int = ty(kb, "test.sc.Rack[A = anthill.prelude.Int64]");
    let at_string = ty(kb, "test.sc.Rack[A = anthill.prelude.String]");
    let cart = r#"{"rack": {"x": {"cart": 1}}}"#;
    let bike = r#"{"rack": {"x": {"bike": 1}}}"#;
    for (place, fits, misfit) in [(at_int, cart, bike), (at_string, bike, cart)] {
        let read = term_ser::decode_value(kb, &json(fits), &place, opts()).unwrap_or_else(|e| panic!("{fits}: {e}"));
        // `rack`'s one field is written as an object, so in full; `cart`'s as a number, so short.
        let written = term_ser::encode_value(kb, &read, &place, opts()).expect("encodes");
        assert_eq!(text(&written), text(&json(fits)), "written back as it was read");
        let err = decode_err(kb, misfit, &place, opts());
        assert!(matches!(&err.problem, ValueProblem::UnknownConstructor { .. }), "{misfit}: {err}");
        assert_eq!(err.path.to_string(), "$.rack.x", "{err}");
    }
    // `Gen provides Sk[T = T]` is admitted at both on its face; the dictionary, built at the
    // place's own binding, takes it at `String` alone.
    let gen = r#"{"rack": {"x": {"gen": "x"}}}"#;
    term_ser::decode_value(kb, &json(gen), &at_string, opts()).expect("a `Gen[T = String]` at `Sk[T = String]`");
    let err = decode_err(kb, gen, &at_int, opts());
    assert!(
        matches!(&err.problem, ValueProblem::NoInstance { reason } if reason.contains("it is no")),
        "{err}"
    );

    let qn = |kb: &KnowledgeBase, s: anthill_core::intern::Symbol| kb.qualified_name_of(s).to_owned();
    let sp = ty(kb, "test.sc.Sp");
    let TypeShape::Data(data) = DeclaredType::closed(&sp).shape(kb).expect("Sp has a shape") else {
        panic!("a sort with abstract values reads as data")
    };
    let read: Vec<(String, Option<String>)> =
        data.constructors().iter().map(|c| (qn(kb, *c), data.provider(*c).map(|p| qn(kb, p)))).collect();
    let want = [("test.sc.Car.car", Some("test.sc.Car")), ("test.sc.Van.van", Some("test.sc.Van"))];
    assert_eq!(
        read,
        want.map(|(c, p)| (c.to_owned(), p.map(str::to_owned))),
        "the providers' constructors, each with its provider"
    );
    let fleet = ty(kb, "test.sc.Fleet");
    let TypeShape::Data(data) = DeclaredType::closed(&fleet).shape(kb).expect("Fleet") else {
        panic!("an entity reads as data")
    };
    assert_eq!(data.provider(data.constructors()[0]), None, "a data sort's constructor has no provider");
}

/// A map keyed by entities, a running one: its keys are the structures they were put under, read
/// back off the handle and written tagged, in the order of their spellings.
///
/// FAILS when backed out (measured): the handle's reading; the writer's order.
#[test]
fn a_running_map_keyed_by_entities() {
    let mut interp = interp();
    let running = interp.call("test.sc.byP", &[]).expect("byP runs").value;
    let ty = term_ser::type_from_text(interp.kb_mut(), "anthill.prelude.Map[K = test.sc.P, V = anthill.prelude.Int64]")
        .expect("the map's type");
    let written = term_ser::encode_value(interp.kb(), &running, &ty, opts()).expect("the handle encodes");
    let want = r#"[[{"P":{"id":1,"name":"a"}},10],[{"P":{"id":2,"name":"b"}},20]]"#;
    assert_eq!(text(&written), want);
    let kb = interp.kb_mut();
    let chain = term_ser::decode_value(kb, &written, &ty, opts()).expect("decodes");
    assert_eq!(text(&term_ser::encode_value(kb, &chain, &ty, opts()).unwrap()), want, "and its chain alike");
}

/// A data file holds a set and a map as the value's chain was built
/// (`CollectionOrder::AsBuilt`, decided with the user 2026-11-25), so each fact reads back as
/// itself — TOML as JSON: arrays, an entry an array of two, an element inserted twice (`Again`)
/// and a key put twice (`Shadowed`) written each time. The canonical text of the same set is
/// another chain, and the canonical reader refuses the repeats.
///
/// FAILS when backed out (measured): `data_file`'s `AsBuilt` (`Ints` and `Prices` reload as
/// other facts, `Again` and `Shadowed` too); the `Set` shape; the `Map` shape.
#[test]
fn a_data_file_holds_sets_and_maps_as_they_were_built() {
    let mut interp = interp();
    let kb = interp.kb_mut();
    for (entity, row) in [
        ("test.sc.Ints", r#"{"s":[2,10,1]}"#),
        ("test.sc.Again", r#"{"s":[1,10,2,1]}"#),
        ("test.sc.Prices", r#"{"m":[["b",2],["a",1]]}"#),
        ("test.sc.Shadowed", r#"{"m":[["a",1],["a",3]]}"#),
    ] {
        let functor = sym(kb, entity);
        let source = kb.rules_by_functor(functor);
        let json_file = term_ser::serialize_json(kb, entity, &source).unwrap_or_else(|e| panic!("{entity}: {e}"));
        let written = serde_json::from_str::<serde_json::Value>(&json_file).unwrap()["data"].clone();
        assert_eq!(text(&written), row, "{entity} as built");
        let toml_file = term_ser::serialize_toml(kb, entity, &source).unwrap_or_else(|e| panic!("{entity}: {e}"));
        for (load, file) in [
            (term_ser::load_json as fn(&mut KnowledgeBase, &str, _) -> _, &json_file),
            (term_ser::load_toml, &toml_file),
        ] {
            let domain = kb.intern("scpw9.data");
            let loaded = load(kb, file, domain).unwrap_or_else(|e| {
                panic!("{entity}: {}\n{file}", e.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("; "))
            });
            assert_eq!(loaded, 1, "{file}");
            let heads: Vec<TermId> = kb.rules_by_functor(functor).iter().map(|r| kb.rule_head(*r)).collect();
            assert!(heads.iter().all(|h| *h == heads[0]), "{entity} reads back as itself:\n{file}");
        }
    }
    let ints = field_type(kb, "test.sc.Again", "s");
    let err = decode_err(kb, "[1, 10, 2, 1]", &ints, opts());
    assert_eq!(err.problem, ValueProblem::RepeatedElement { first: 0 }, "the canonical reader refuses it");
}
