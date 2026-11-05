//! WI-20260823-53W12 — proposal 055 umbrella B: a type written in a clause's term is the
//! type value it denotes, and a declared column takes it as an operation's parameter takes
//! an argument (`docs/design/055-implementation.md` §7).
//!
//! THE RULE. A type written as data — a sort's name, bare or applied, a constructor's type
//! face, a sort's parameter, a structural type written as a bracket's entry — is a value of
//! `Type`, in a fact, a rule's head and a rule's body alike:
//!
//!   fact held(t: Box[V = Int64], n: 1)       a field declared `Type` takes it
//!   fact num(i: Box)                          a field declared `Int64` refuses it
//!   fact wrap(inner: named(s: Box, n: 5))     so does a field of a construction in it
//!   rule w(?n) :- held(t: Box[V = (Int64, String)], n: ?n)    a structural entry in a goal
//!   rule nm2(Box[V = ?v]) <=> idt(?v) @[simp]                  a variable bound to an entry
//!
//! And a bracket on an operation or a relation binds its type parameters, never its arguments
//! (proposal 060 §2.1: a rule is an operation; decided with the user 2026-11-02): written
//! alone — `mine[1, 2]`, `is_entity_of[Colour, Colour]`, `two[1, 2]`, a head `fact myrel[T =
//! Red]` — it is refused wherever it stands. It was read as the argument list.
//!
//! BEFORE. The fact and rule-head check read a type's head as the sort of a value and found
//! none, so every field took it: `fact num(i: Box)` loaded beside `entity num(i: Int64)`,
//! where the same goal in a rule body was refused. The rule-body walk and the `@[simp]`
//! splice built a structural entry from its term, a construction in the type
//! meta-language, and the typer refused its leaves as "a defect in the walk that built
//! this occurrence".
//!
//! CONTROLS — each part backed out on its own, in one build (temporary switches):
//!   the fact and rule-head field check (`check_type_value_against_field`) — FAIL:
//!     a_type_in_a_field_of_another_type_is_refused (its bare, applied, two face,
//!       parameter and rule-head rows)
//!     a_type_in_a_field_of_another_type_is_quoted
//!   the field of a construction inside a clause (`argument_fits_field`'s arm) — FAIL:
//!     a_type_in_a_field_of_another_type_is_refused (its two nested rows)
//!   both together — FAIL, in addition: its list and option rows. Each part reaches them
//!     alone: the field check through the list's and the option's parameter, the clause
//!     walk through the `cons` and `some` constructions they are stored as.
//!   the rule-body entry (`Loader::lower_entry_type_aux_occ` materializing the term) — FAIL:
//!     a_structural_entry_in_a_goal_meets_a_declared_column
//!   a type typing its position as a literal does (`constrain_arg`'s arm) — FAIL:
//!     a_list_of_types_is_a_list_at_type, and
//!     `wi_drgcp_precondition_goal_spelling_test::a_list_in_a_goal_is_written_as_its_literal`
//!     (with the field check on, its fact `among([Untrusted[], Public[]])`)
//!   the splice of a bound entry (`subst_var_leaf`'s structural arm) — FAIL:
//!     a_simp_binder_takes_a_structural_entry_as_its_type
//!   a `TypeExtractor` construction read as a type written as data (the predicate widened to
//!     every `TypeExtractor` constructor) — FAIL:
//!     a_type_extractor_construction_is_its_instance
//!   the spec's note left out of the fact's refusal — FAIL:
//!     a_type_at_a_spec_field_is_told_the_spec_is_over_its_parameter
//!   the bracket on a callable (`Loader::refuse_bracket_on_a_callable`) — FAIL:
//!     a_bracket_alone_on_a_callable_is_refused, and the head rows
//!     `wi_c7anm_head_parameter_column_test::{a_bracketed_head_is_refused_in_both_spellings,
//!     a_bracketed_head_with_a_positional_argument_is_refused_not_a_panic}` and
//!     `wi_s8jyf_provision_spelling_test::an_unresolved_bracketed_head_is_refused`; its head
//!     case alone — FAIL: those three; its operation-body site alone — FAIL:
//!     a_bracket_alone_on_a_callable_is_refused (its operation rows); the query scan's —
//!     FAIL: a_bracket_alone_on_a_callable_is_refused_in_a_query.
//!   the head judged by its kinds as any other name (a qualified head is minted with none)
//!     — FAIL: a_bracket_on_a_const_and_a_qualified_head_are_refused; a non-callable name
//!     let through — FAIL: the same row; the operation body typed after its bracket's
//!     refusal — FAIL: a_bracket_alone_on_a_callable_is_refused (a second report); the head
//!     wording keyed on a top-level term rather than the clause's head node — FAIL: the
//!     same row (its constraint goal is reported twice).
//!   UNDRIVEN, measured: the splice arm narrowed to the three forms an entry is written as.
//!     Widened to every `TypeExtractor` constructor, no row moves, and a fact's
//!     `TypeVar(name: Int64)` read into a variable and handed to an operation answers alike
//!     either way; the narrowing keeps a `TypeExtractor` value from being typed `Type`.
//!   PASS UNDER EACH, by design — they are the fences:
//!     the_type_columns_take_the_type — a field at `Type`, `Term`, `List[T = Type]`,
//!       `Option[T = Type]` or a type parameter, and the variable-bearing goal on it.
//!     the_rule_body_goal_was_refused_already — the operation-body typer reads the goal's
//!       `TypeValue` node.
//!     a_call_and_a_type_keep_their_brackets — a call's arguments in parentheses, an
//!       operation call's bracket before them, a sort's and a constructor's bracket.
//!     the_heads_advice_loads — the two declarations the head's refusal advises.
//!     a_sort_parameter_in_a_rule_body_is_the_parameter — a sort's goal (proposal 062) is
//!       where the parameter is substituted, driven by
//!       wi_t70a2_sort_goal_test::the_parameter_is_substituted_by_its_type; here it is the
//!       parameter.
//!
//! The 060 forms the ticket names are driven where they are owned: a `requires` clause's
//! requirement edge by `wi_p7vp4_rule_body_requirements_test`, a rule body's `require[…]`
//! dictionary by `wi_qhdgc_require_spec_logical_variable_test`.

use anthill_core::eval::Value;
use anthill_core::kb::term_view::{views_structurally_equal, TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_errors_of, load_kb_with, query_unary};

/// `test.<ns>`: `Box` to apply, a nominal enum and a free-standing entity for their type
/// faces, `idt` to hand a type value through, `decl` declaring `declared`, and `body`.
fn source(ns: &str, declared: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Type, Bool, String, Int64, List, Option, Eq}}
  import anthill.reflect.Term
  sort Box
    sort V = ?
  end
  enum Colour
    entity red
  end
  entity Leaf(name: String)
  entity named(s: String, n: Int64)
  entity num(i: Int64)
  entity wrap(inner: named)
  entity held(t: Type, n: Int64)
  operation idt(t: Type) -> Type = t
  operation decl({declared}) -> Int64 = 0
{body}
end
"#
    )
}

/// The answers of `test.<ns>.r(?x)`. Every one must be definite.
fn answers(kb: &mut KnowledgeBase, ns: &str) -> Vec<Value> {
    query_unary(kb, &format!("test.{ns}.r"))
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "{ns}: a conditional answer, {v:?}");
            v
        })
        .collect()
}

/// The integers `r` answers in `body`.
fn ints(ns: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&source(ns, "x: Int64", body));
    let mut got: Vec<i64> = answers(&mut kb, ns)
        .into_iter()
        .map(|v| match v {
            Value::Int(n) => n,
            other => panic!("{ns}: expected an Int64, got {other:?}"),
        })
        .collect();
    got.sort();
    got
}

/// The type `decl`'s parameter `i` is declared with.
fn declared(kb: &KnowledgeBase, ns: &str, i: usize) -> Value {
    let op = kb
        .try_resolve_symbol(&format!("test.{ns}.decl"))
        .unwrap_or_else(|| panic!("{ns}: `decl` does not resolve"));
    anthill_core::kb::op_info::lookup_operation_info(kb, op)
        .unwrap_or_else(|| panic!("{ns}: `decl` has no signature"))
        .params[i]
        .1
        .clone()
}

/// The refusals of `body`, which must not load.
fn refusals(ns: &str, body: &str) -> Vec<String> {
    let errs = load_errors_of(&source(ns, "x: Int64", body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    errs
}

/// A type in a field declared at another type is refused, wherever the field is: a fact's,
/// a rule head's, a construction's inside either, a list's element, an `Option`'s.
#[test]
fn a_type_in_a_field_of_another_type_is_refused() {
    for (ns, body, said) in [
        ("w53bare", "  fact num(i: Box)", "num.i (entity-field): expected Int64, got Type (Box)"),
        (
            "w53applied",
            "  fact named(s: Box[V = Int64], n: 1)",
            "named.s (entity-field): expected String, got Type (Box[V = Int64])",
        ),
        (
            "w53face",
            "  fact named(s: red[], n: 1)",
            "named.s (entity-field): expected String, got Type (red[])",
        ),
        (
            "w53entityface",
            "  fact named(s: Leaf[], n: 1)",
            "named.s (entity-field): expected String, got Type (Leaf[])",
        ),
        (
            "w53param",
            "  enum Text\n    sort Trust = ?\n    entity text(raw: String)\n    fact num(i: Trust)\n  end",
            "num.i (entity-field): expected Int64, got Type (Trust)",
        ),
        (
            "w53head",
            "  rule named(s: Box, n: 1) :- true",
            "named.s (entity-field): expected String, got Type (Box)",
        ),
        (
            "w53nestedfact",
            "  fact wrap(inner: named(s: Box, n: 1))",
            "named.s (entity-field): expected String, got Type (Box)",
        ),
        (
            "w53nestedhead",
            "  rule wrap(inner: named(s: Box[V = String], n: 1)) :- true",
            "named.s (entity-field): expected String, got Type (Box[V = String])",
        ),
        (
            "w53list",
            "  entity listy(xs: List[T = String])\n  fact listy(xs: [Box])",
            "expected String, got Type (Box)",
        ),
        (
            "w53option",
            "  entity opt(o: Option[T = Int64])\n  fact opt(o: Box)",
            "expected Int64, got Type (Box)",
        ),
    ] {
        let errs = refusals(ns, body);
        assert!(
            errs.iter().any(|e| e.contains(said)),
            "{ns}: expected a refusal saying `{said}`, got {errs:?}"
        );
        assert_eq!(errs.len(), 1, "{ns}: one refusal, got {errs:?}");
    }
}

/// The refusal says which type was written, and where: the fact's own line.
#[test]
fn a_type_in_a_field_of_another_type_is_quoted() {
    let fact = "  fact named(s: Box[V = Box[V = Int64]], n: 1)";
    let errs = refusals("w53quoted", fact);
    assert_eq!(errs.len(), 1, "{errs:?}");
    let line = source("w53quoted", "x: Int64", fact)
        .lines()
        .position(|l| l == fact)
        .expect("the fact's line")
        + 1;
    assert!(
        errs[0].contains(&format!("{line}:8:"))
            && errs[0].contains("got Type (Box[V = Box[V = Int64]])"),
        "{errs:?}"
    );
}

/// At a field typed by a spec over its parameter, the refusal says why a provider's value is
/// no value of the spec, as the operation body's does.
#[test]
fn a_type_at_a_spec_field_is_told_the_spec_is_over_its_parameter() {
    let errs = refusals(
        "w53specfield",
        "  import anthill.prelude.PartialEq\n  entity e(x: PartialEq)\n  fact e(x: Box)",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        errs[0].contains("e.x (entity-field): expected PartialEq, got Type (Box) — ")
            && errs[0].contains("is a spec over its parameter `T`"),
        "{errs:?}"
    );
}

/// A `TypeExtractor` construction written in a clause is its constructor's instance, as any
/// constructor's is, and a field declared `TypeExtractor` takes it: a type written as data is
/// headed by a name that denotes only a type, and a structural type reaches a clause's term
/// only as a bracket's entry.
#[test]
fn a_type_extractor_construction_is_its_instance() {
    assert_eq!(
        ints(
            "w53extractor",
            "  import anthill.prelude.TypeExtractor\n  \
             import anthill.prelude.TypeExtractor.{Nothing, TypeVar}\n  \
             entity rec(x: TypeExtractor, n: Int64)\n  entity wrapped(r: rec)\n  \
             fact rec(x: Nothing, n: 1)\n  fact wrapped(r: rec(x: TypeVar(name: Int64), n: 2))\n  \
             rule r(?n) :- rec(x: Nothing, n: ?n)\n  rule r(?n) :- wrapped(r: rec(x: ?, n: ?n))",
        ),
        [1, 2]
    );
}

/// A field declared `Type`, `Term`, a list or an option of `Type`, or a type parameter takes
/// a type, and a goal finds it — the goal that writes a variable inside the type too.
#[test]
fn the_type_columns_take_the_type() {
    assert_eq!(
        ints(
            "w53typecol",
            "  fact held(t: Box, n: 1)\n  fact held(t: Box[V = Int64], n: 2)\n  \
             fact held(t: red[], n: 3)\n  fact held(t: Leaf[], n: 4)\n  \
             rule held(t: Box[V = String], n: 5) :- true\n  rule r(?n) :- held(t: ?, n: ?n)",
        ),
        [1, 2, 3, 4, 5]
    );
    assert_eq!(
        ints(
            "w53typecolgoal",
            "  fact held(t: Box[V = Int64], n: 2)\n  fact held(t: Box[V = String], n: 5)\n  \
             rule r(?n) :- held(t: Box[V = Int64], n: ?n)",
        ),
        [2]
    );
    // The variable inside the type binds what the fact holds there.
    let body = "  fact held(t: Box[V = Int64], n: 2)\n  rule r(?v) :- held(t: Box[V = ?v], n: ?)";
    let mut kb = load_kb_with(&source("w53typecolvar", "x: Int64, y: String", body));
    let got = answers(&mut kb, "w53typecolvar");
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        views_structurally_equal(&kb, &got[0], &declared(&kb, "w53typecolvar", 0)),
        "{got:?}"
    );
    assert!(
        !views_structurally_equal(&kb, &got[0], &declared(&kb, "w53typecolvar", 1)),
        "{got:?}"
    );
    assert_eq!(
        ints(
            "w53othercols",
            "  entity rawt(t: Term, n: Int64)\n  entity tlisty(xs: List[T = Type], n: Int64)\n  \
             entity opt(o: Option[T = Type], n: Int64)\n  sort Gen\n    sort T = ?\n    \
             entity gbox(v: T, n: Int64)\n  end\n  fact rawt(t: Box, n: 1)\n  \
             fact tlisty(xs: [Box, Int64], n: 2)\n  fact opt(o: Box, n: 3)\n  \
             fact gbox(v: Box[V = Int64], n: 4)\n  \
             rule r(?n) :- rawt(t: Box, n: ?n)\n  rule r(?n) :- tlisty(xs: [Box, Int64], n: ?n)\n  \
             rule r(?n) :- opt(o: Box, n: ?n)\n  rule r(?n) :- gbox(v: Box[V = Int64], n: ?n)",
        ),
        [1, 2, 3, 4]
    );
}

/// A list of types written as data is a list at `Type`: each element types the list's
/// element as `Type`, as a literal types it at its sort, and an element of another type
/// beside it is refused for it. Before, a constructor's type face was read as the
/// constructor: `[red[], 3]` was refused as `expected Colour`, and `[red[], red]`, a type
/// beside an instance, loaded.
#[test]
fn a_list_of_types_is_a_list_at_type() {
    assert_eq!(
        ints(
            "w53typelist",
            "  fact among([red[], Leaf[], Box])\n  rule r(1) :- among([red[], Leaf[], Box])",
        ),
        [1]
    );
    for (ns, list, said) in [
        (
            "w53typelistint",
            "[red[], 3]",
            "cons.head (entity-field): expected Type, got Int64",
        ),
        (
            "w53typelistinst",
            "[red[], red]",
            "cons.head (entity-field): expected Type, got Colour",
        ),
        (
            "w53instlisttype",
            "[red, red[]]",
            "cons.head (entity-field): expected Colour, got Type (red[])",
        ),
    ] {
        let errs = refusals(ns, &format!("  fact among({list})"));
        assert!(
            errs.iter().any(|e| e.contains(said)),
            "{ns}: expected `{said}`, got {errs:?}"
        );
        assert_eq!(errs.len(), 1, "{ns}: one refusal, got {errs:?}");
    }
}

/// The fence: in a rule body the goal is typed as an operation body is, which read the
/// goal's `TypeValue` node before this change.
#[test]
fn the_rule_body_goal_was_refused_already() {
    let errs = refusals(
        "w53bodygoal",
        "  rule r(?n) :- named(s: Box[V = Int64], n: ?n)",
    );
    assert!(
        errs.iter()
            .any(|e| e
                .contains("named.s (entity-field): expected String, got Type (Box[V = Int64])")),
        "{errs:?}"
    );
}

/// A tuple type and an arrow type written as a bracket's entry, in a rule body's goal on a
/// declared `Type` column, are the types the fact holds.
#[test]
fn a_structural_entry_in_a_goal_meets_a_declared_column() {
    for (ns, entry) in [
        ("w53goaltuple", "(Int64, String)"),
        ("w53goalnamed", "(a: Int64, b: Int64)"),
        ("w53goalarrow", "(Int64) -> Int64"),
    ] {
        let body = format!(
            "  fact held(t: Box[V = {entry}], n: 7)\n  fact held(t: Box[V = Bool], n: 8)\n  \
             rule r(?n) :- held(t: Box[V = {entry}], n: ?n)"
        );
        assert_eq!(ints(ns, &body), [7], "{ns}");
    }
}

/// A `@[simp]` rule whose left-hand side binds a variable to a structural entry hands its
/// right-hand side that type, as an operation body would; an effect row too.
#[test]
fn a_simp_binder_takes_a_structural_entry_as_its_type() {
    for (ns, entry) in [
        ("w53simparrow", "(Int64) -> Int64"),
        ("w53simptuple", "(Int64, String)"),
        ("w53simprow", "{}"),
    ] {
        let declared_params = format!("x: Box[V = {entry}], y: Box[V = Bool]");
        let body = format!(
            "  operation nm2(t: Type) -> Type\n  rule nm2(Box[V = ?v]) <=> idt(Box[V = ?v]) @[simp]\n  \
             operation go() -> Type = nm2(Box[V = {entry}])\n  rule r(?t) :- ?t <=> go()"
        );
        let mut kb = load_kb_with(&source(ns, &declared_params, &body));
        let got = answers(&mut kb, ns);
        assert_eq!(got.len(), 1, "{ns}: {got:?}");
        assert!(
            views_structurally_equal(&kb, &got[0], &declared(&kb, ns, 0)),
            "{ns}: {got:?}"
        );
        assert!(
            !views_structurally_equal(&kb, &got[0], &declared(&kb, ns, 1)),
            "{ns}: {got:?}"
        );
    }
    // The variable itself: the entry, as the type it is.
    for (ns, entry, other) in [
        ("w53simpvararrow", "(Int64) -> Int64", "(Int64) -> Bool"),
        (
            "w53simpvartuple",
            "(a: Int64, b: Int64)",
            "(a: Int64, b: Bool)",
        ),
    ] {
        let body = format!(
            "  operation nm2(t: Type) -> Type\n  rule nm2(Box[V = ?v]) <=> idt(?v) @[simp]\n  \
             operation go() -> Type = nm2(Box[V = {entry}])\n  rule r(?t) :- ?t <=> go()"
        );
        let mut kb = load_kb_with(&source(ns, &format!("x: {entry}, y: {other}"), &body));
        let got = answers(&mut kb, ns);
        assert_eq!(got.len(), 1, "{ns}: {got:?}");
        assert!(
            views_structurally_equal(&kb, &got[0], &declared(&kb, ns, 0)),
            "{ns}: {got:?}"
        );
        assert!(
            !views_structurally_equal(&kb, &got[0], &declared(&kb, ns, 1)),
            "{ns}: {got:?}"
        );
    }
    // An effect row, compared through `Eb`'s bracket, its one type position.
    let body = "  sort Eb\n    sort E = ?\n  end\n  operation nm2(t: Type) -> Type\n  \
                rule nm2(Box[V = ?v]) <=> idt(Eb[E = ?v]) @[simp]\n  \
                operation go() -> Type = nm2(Box[V = {}])\n  rule r(?t) :- ?t <=> go()";
    let ns = "w53simpvarrow";
    let mut kb = load_kb_with(&source(ns, "x: Eb[E = {}], y: Eb[E = {Int64}]", body));
    let got = answers(&mut kb, ns);
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        views_structurally_equal(&kb, &got[0], &declared(&kb, ns, 0)),
        "{got:?}"
    );
    assert!(
        !views_structurally_equal(&kb, &got[0], &declared(&kb, ns, 1)),
        "{got:?}"
    );
}

/// In a rule body inside a sort, the sort's parameter is the parameter, rigid: nothing
/// substitutes it, so `is_entity_of(Trust, TrustLevel)` holds of no instance there, where
/// the same goal over an entity of the sort holds. A sort's `requires` goal is where it is
/// substituted per instance (`wi_t70a2_sort_goal_test`).
#[test]
fn a_sort_parameter_in_a_rule_body_is_the_parameter() {
    let body = "  import anthill.reflect.typing.is_entity_of\n  enum TrustLevel\n    entity Public\n  end\n  \
                enum Text\n    sort Trust = ?\n    entity text(raw: String)\n    \
                rule param(?t) :- ?t <=> Trust\n    rule guard(1) :- is_entity_of(Trust, TrustLevel)\n  end\n  \
                rule r(?n) :- Text.guard(?n)\n  rule r(2) :- is_entity_of(Public, TrustLevel)";
    let ns = "w53param062";
    let mut kb = load_kb_with(&source(ns, "x: Int64", body));
    let got = query_unary(&mut kb, &format!("test.{ns}.Text.param"));
    assert_eq!(got.len(), 1, "{got:?}");
    let named = match got[0].0.head(&kb) {
        ViewHead::Functor {
            functor,
            pos_arity: 0,
            named_arity: 0,
        } => kb.qualified_name_of(functor).to_string(),
        other => panic!("expected the parameter's name, got {other:?}"),
    };
    assert_eq!(named, format!("test.{ns}.Text.Trust"));
    assert_eq!(ints(ns, body), [2]);
}

// ── A bracket on a callable (proposal 060 §2.1) ─────────────────────────────────────────

/// `mine`, a relation; `two`, an operation; `idf`, an operation with a type parameter; and a
/// fact-only relation.
const CALLABLES: &str = "  import anthill.reflect.typing.is_entity_of\n  \
                         rule mine(?a, ?b) :- ?a <=> 1, ?b <=> 2\n  fact holdsF(1)\n  \
                         operation two(a: Int64, b: Int64) -> Int64 = a + b\n  \
                         operation idf[A](x: A) -> A = x\n";

/// A rule is an operation, and a bracket on either binds its type parameters, never its
/// arguments: written alone it is refused wherever it stands. Before, it was read as the
/// argument list — `mine[1, 2]` answered as `mine(1, 2)`, `two[1, 2]` loaded as `two(1, 2)`,
/// and `is_entity_of[Red, Red]` asked `is_entity_of(Red, Red)`.
#[test]
fn a_bracket_alone_on_a_callable_is_refused() {
    for (ns, body, name) in [
        ("w53brgoal", "  rule r(1) :- mine[1, 2]", "mine"),
        ("w53brnot", "  rule r(1) :- not(mine[1, 2])", "mine"),
        ("w53brvalue", "  rule r(?x) :- ?x <=> mine[1, 2]", "mine"),
        ("w53brdata", "  fact holds(mine[1, 2])", "mine"),
        ("w53brfact", "  rule r(1) :- holdsF[1]", "holdsF"),
        (
            "w53brentityof",
            "  rule r(1) :- is_entity_of[Colour, Colour]",
            "is_entity_of",
        ),
        ("w53bropargs", "  operation h() -> Int64 = two[1, 2]", "two"),
        (
            "w53broptype",
            "  operation h() -> Int64 = two[Int64]",
            "two",
        ),
        (
            "w53bropparam",
            "  operation h() -> Type = idf[Int64]",
            "idf",
        ),
        (
            "w53brconstraint",
            "  constraint c: mine[1, 2] :- true",
            "mine",
        ),
    ] {
        let errs = refusals(ns, &format!("{CALLABLES}{body}"));
        let said = format!(
            "`{name}[…]` is a bracket on an operation or a relation, which binds its type \
             parameters and is read only before a call's arguments, `{name}[…](…)` — \
             `{name}[…]()` where none is written; the arguments are written in parentheses, \
             `{name}(…)`"
        );
        // One refusal: the operation body is not typed after it (the misread call's return
        // mismatch is not added), and a constraint's goal is no clause head.
        assert_eq!(errs.len(), 1, "{ns}: one refusal, got {errs:?}");
        assert!(
            errs[0].contains(&said),
            "{ns}: expected the bracket's refusal, got {errs:?}"
        );
    }
}

/// A bracket on a name that is no type and no callable — a const — writes type arguments it
/// does not take; and a clause's head is refused for its bracket however it is spelled,
/// qualified too, where the head declares the relation.
#[test]
fn a_bracket_on_a_const_and_a_qualified_head_are_refused() {
    let errs = refusals(
        "w53brconst",
        "  const seven: Int64 = 7\n  fact holds(seven[1])",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        errs[0].contains("`seven[…]` writes type arguments of `seven`, which takes none"),
        "{errs:?}"
    );
    let errs = refusals(
        "w53brqualified",
        "  fact test.w53brqualified.myrel[T = Colour]",
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        errs[0].contains("declares the relation `test.w53brqualified.myrel` with a bracket"),
        "{errs:?}"
    );
}

/// The head's advice is a program that loads: a column, and a type parameter with its bound.
#[test]
fn the_heads_advice_loads() {
    assert_eq!(
        ints(
            "w53bradvice",
            "  fact myrel(T: Colour)\n  fact seedc(red)\n  \
             rule myrel2[T](?x: T) :- Eq[T], seedc(?x)\n  \
             rule r(1) :- myrel(T: Colour)\n  rule r(2) :- myrel2(red)",
        ),
        [1, 2]
    );
}

/// A query pattern is refused the same way, before it is converted.
#[test]
fn a_bracket_alone_on_a_callable_is_refused_in_a_query() {
    let mut kb = load_kb_with(&source("w53brquery", "x: Int64", CALLABLES));
    let parsed = anthill_core::parse::parse("fact test.w53brquery.mine[1, 2]").expect("parse");
    let errs: Vec<String> = anthill_core::kb::load::scan_query_definitions(&mut kb, &[&parsed])
        .iter()
        .map(|e| e.to_string())
        .collect();
    assert!(
        errs.iter()
            .any(|e| e.contains("`mine[…]` is a bracket on an operation or a relation")),
        "{errs:?}"
    );
}

/// The fences: a call's arguments in parentheses, a call's bracket in an operation body
/// before its arguments, and a bracket on a sort or a constructor, which is its type.
#[test]
fn a_call_and_a_type_keep_their_brackets() {
    assert_eq!(
        ints(
            "w53brcall",
            &format!(
                "{CALLABLES}  operation h() -> Int64 = two(1, 2) + idf[A = Int64](3)\n  \
                 rule r(?n) :- mine(?n, 2)\n  rule r(?n) :- ?n <=> h()"
            ),
        ),
        [1, 6]
    );
    assert_eq!(
        ints(
            "w53brtype",
            "  fact held(t: Box[V = Int64], n: 1)\n  fact held(t: red[], n: 2)\n  \
             rule r(?n) :- held(t: Box[V = Int64], n: ?n)\n  rule r(?n) :- held(t: red[], n: ?n)",
        ),
        [1, 2]
    );
}
