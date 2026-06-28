//! WI-173 — surface pretty-printing for TYPE terms in `TermPrinter::write_term`.
//!
//! A hash-consed type term (an operation signature's param/return type, a
//! type-valued fact field, codegen output) used to fall through to the generic
//! `name(arg: val, …)` Fn form — `Arrow(param: Int64, result: Bool, effects:
//! EffectsRows(effects_expr: empty_row))` instead of `(Int64) -> Bool`. The
//! printer now renders the distinct `TypeExtractor.*` functors in surface syntax:
//! arrow `(A) -> B @ {E}`, named tuple `(a: T, …)`, bare sort `S`, and — in type
//! context (a child of a type) — the parameterized `S[k = v]`.
//!
//! NOTE (WI-361 limitation): a STANDALONE bare parameterized type reached via
//! generic `write_term` (e.g. a `FieldInfo.type_name` that is just `List[T=Int]`,
//! with no enclosing type wrapper) stays the data form `List(T: Int64)` — a
//! `Fn{S, named}` is structurally identical to a data term, so `write_term`
//! cannot tell them apart without type context. Inside a type (`(List[T=Int]) ->
//! Bool`) the parameterized form IS recovered, as the arrow case below shows.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn fresh_kb() -> KnowledgeBase {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    kb
}

#[test]
fn arrow_pure_prints_surface() {
    let mut kb = fresh_kb();
    let int = kb.make_sort_ref_by_name("Int64");
    let b = kb.make_sort_ref_by_name("Bool");
    let arrow = kb.make_arrow_type(int, b, &[]);
    assert_eq!(TermPrinter::new(&kb).print_term(arrow), "(Int64) -> Bool");
}

#[test]
fn arrow_single_effect_prints_unbraced() {
    let mut kb = fresh_kb();
    let int = kb.make_sort_ref_by_name("Int64");
    let b = kb.make_sort_ref_by_name("Bool");
    let eff = kb.make_sort_ref_by_name("Error");
    let arrow = kb.make_arrow_type(int, b, &[eff]);
    assert_eq!(TermPrinter::new(&kb).print_term(arrow), "(Int64) -> Bool @ Error");
}

#[test]
fn arrow_effect_set_prints_braced() {
    let mut kb = fresh_kb();
    let int = kb.make_sort_ref_by_name("Int64");
    let b = kb.make_sort_ref_by_name("Bool");
    // Two distinct effect labels → a braced, canonically-sorted set.
    let e1 = kb.make_sort_ref_by_name("Aeff");
    let e2 = kb.make_sort_ref_by_name("Beff");
    let arrow = kb.make_arrow_type(int, b, &[e1, e2]);
    assert_eq!(
        TermPrinter::new(&kb).print_term(arrow),
        "(Int64) -> Bool @ {Aeff, Beff}",
    );
}

#[test]
fn named_tuple_prints_surface() {
    let mut kb = fresh_kb();
    let int = kb.make_sort_ref_by_name("Int64");
    let b = kb.make_sort_ref_by_name("Bool");
    let a_sym = kb.intern("a");
    let bb_sym = kb.intern("b");
    let nt = kb.make_named_tuple_type(&[(a_sym, int), (bb_sym, b)]);
    assert_eq!(TermPrinter::new(&kb).print_term(nt), "(a: Int64, b: Bool)");
}

#[test]
fn positional_tuple_prints_unlabelled() {
    let mut kb = fresh_kb();
    let int = kb.make_sort_ref_by_name("Int64");
    let b = kb.make_sort_ref_by_name("Bool");
    let f1 = kb.intern("_1");
    let f2 = kb.intern("_2");
    let nt = kb.make_named_tuple_type(&[(f1, int), (f2, b)]);
    assert_eq!(TermPrinter::new(&kb).print_term(nt), "(Int64, Bool)");
}

#[test]
fn nested_parameterized_in_arrow_recovers_bracket_form() {
    let mut kb = fresh_kb();
    let int = kb.make_sort_ref_by_name("Int64");
    let b = kb.make_sort_ref_by_name("Bool");
    let list = kb.make_sort_ref_by_name("List");
    let t_sym = kb.intern("T");
    let list_int = kb.make_parameterized_type(list, &[(t_sym, int)]);
    // Inside the arrow (a known type context) the parameterized param recovers
    // its `[T = Int64]` bracket form, not the data `List(T: Int64)`.
    let arrow = kb.make_arrow_type(list_int, b, &[]);
    assert_eq!(
        TermPrinter::new(&kb).print_term(arrow),
        "(List[T = Int64]) -> Bool",
    );
}

#[test]
fn multi_param_arrow_param_not_double_wrapped() {
    let mut kb = fresh_kb();
    let int = kb.make_sort_ref_by_name("Int64");
    let b = kb.make_sort_ref_by_name("Bool");
    let x = kb.intern("x");
    let y = kb.intern("y");
    let params = kb.make_named_tuple_type(&[(x, int), (y, b)]);
    let arrow = kb.make_arrow_type(params, b, &[]);
    // The named-tuple param uses its own parens directly — no `((x: …))`.
    assert_eq!(
        TermPrinter::new(&kb).print_term(arrow),
        "(x: Int64, y: Bool) -> Bool",
    );
}

/// A real loaded operation signature: the callback param's arrow type, read back
/// from its `OperationInfo` and printed, is the surface form — not the cons-list
/// blob. The ticket's driver case (an operation signature round-tripping).
#[test]
fn loaded_arrow_signature_prints_surface() {
    use anthill_core::eval::Value;
    let src = r#"
namespace wi173.rt
  import anthill.prelude.{Int64, Bool}
  operation apply_cb(g: (Int64) -> Bool) -> Bool = g(0)
end
"#;
    let mut kb = fresh_kb();
    let parsed = parse::parse(src).expect("parse");
    load::load_all(&mut kb, &[&parsed], &NullResolver).expect("load");
    let op_sym = kb.resolve_symbol("wi173.rt.apply_cb");
    let info = anthill_core::kb::op_info::lookup_operation_info(&kb, op_sym)
        .expect("OperationInfo for apply_cb");
    let g_sym = kb.resolve_symbol("wi173.rt.apply_cb.g");
    let (_, g_ty) = info
        .params
        .iter()
        .find(|(s, _)| *s == g_sym)
        .expect("param g present");
    let printed = match g_ty {
        Value::Term { id: t, .. } => TermPrinter::new(&kb).print_term(*t),
        other => panic!("expected a ground arrow type for g, got {other:?}"),
    };
    assert_eq!(
        printed, "(Int64) -> Bool",
        "a loaded callback param's arrow type must print as surface syntax, not the \
         `Arrow(param: …, effects: EffectsRows(…))` blob",
    );
}
