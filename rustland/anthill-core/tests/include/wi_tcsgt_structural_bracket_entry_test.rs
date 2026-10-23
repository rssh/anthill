//! WI-20261012-TCSGT — a structural type written as an entry of a bracket in a term is the
//! type it is (proposal 055 §2: an entry of a nominal type's bracket is a type position).
//!
//! THE RULE. A tuple type, an arrow type and an effect row have no term shape, and each is
//! one type value wherever the bracket that holds it is written:
//!
//!   idt(Box[V = (Int64) -> Int64])            an argument at a `Type` parameter
//!   let t = Box[V = (a: Int64, b: Int64)]     a `let`, and `t.tag()` on it
//!   operation ty() -> Type = Box[V = () -> Int64]
//!   (Box[V = (Int64, String)]).tag()          a receiver, as `Box[V = (Int64, String)].tag()`
//!   Box[V = Box[V = (Int64) -> Int64]]        one bracket down
//!   fact holds(Box[V = (Int64) -> Int64])     a fact, a rule's head, a goal
//!
//! Before, the converter read such an entry as a name spelled with its text
//! (`unresolved name '(Int64) -> Int64'`), and a positional one was `unexpected term
//! node: arrow_type`.
//!
//! WHAT A ROW ASSERTS. `decl` declares a parameter with the row's text in a TYPE position,
//! and a row's answer is compared with that declared type through the view, on whichever
//! carrier each rides — so a row says the bracket is the type the same text is in a
//! signature, and not only that it loaded. A receiver row calls `keep(x: V) -> V`, which
//! takes a value of the entry's type and refuses any other.
//!
//! EVERY ROW HAS ITS OWN SOURCE, in a namespace of its own.
//!
//! CONTROLS — measured against this module, `wi1106_parametric_data_sort_test`,
//! `wi_51w18_require_spec_type_args_test` and `wi_qhdgc_require_spec_logical_variable_test`,
//! each piece backed out on its own. No row of `wi366_value_in_type_facts_test`,
//! `wi_a3fy2_rule_body_type_receiver_test`, `wi_papx0_dot_receiver_split_test`,
//! `wi_rxt6s_dotted_sort_type_value_test`, the WAHB6, N31XX and 5G28A modules moves under
//! any of them.
//!
//!   the converter's arm (`convert_type_value` sending a tuple type and an arrow type to
//!   its default arm, a name spelled with the text) — FAIL:
//!     an_argument_is_the_type_its_text_is_in_a_signature
//!     a_let_binds_the_type
//!     a_result_is_the_type
//!     one_bracket_down_is_the_type
//!     a_positional_entry_is_the_named_one
//!     a_positional_entry_in_a_clauses_term_is_the_named_one
//!     a_parenthesized_receiver_in_an_operation_body_answers_as_its_companion_call
//!     a_parenthesized_receiver_in_a_rule_body_answers_as_its_companion_call
//!     a_fact_is_matched_by_a_goal
//!     a_rule_head_holds_the_type
//!     a_variable_inside_the_entry_binds
//!     the_three_walks_build_one_value
//!     an_entry_under_a_rules_let_and_if_is_the_type
//!     a_match_arm_is_unfolded_past_the_entry
//!     a_type_parameter_inside_the_entry_is_refused
//!     a_value_inside_the_entry_is_refused
//!     a_name_inside_the_entry_is_reported_as_itself
//!     a_lone_parenthesized_type_is_no_type (its entry row)
//!     an_entry_is_no_spec_instance
//!     a_parameter_named_like_a_bracket_channel_takes_an_entry
//!     a_query_pattern_refuses_the_entry_by_name
//!   and `wi1106…::a_binding_that_resolved_to_nothing_is_refused_not_filed`.
//!   the top-level positional route (`convert_instantiation_term` handing a tuple type, an
//!   arrow type and a row to `convert_term`) — FAIL:
//!     a_positional_entry_is_the_named_one
//!     a_positional_entry_in_a_clauses_term_is_the_named_one
//!     an_effect_row_entry_is_its_row (its positional row)
//!     an_entry_is_no_spec_instance
//!     a_query_pattern_refuses_the_entry_by_name (its positional pattern)
//!   and `wi_51w18…::a_positional_effect_row_keeps_its_slot_too`.
//!   the operation body's node (the entry materialized from its term, as the effect row
//!   was, in place of `Loader::entry_type_value_occ`) — FAIL:
//!     an_argument_is_the_type_its_text_is_in_a_signature
//!     a_let_binds_the_type
//!     a_result_is_the_type
//!     one_bracket_down_is_the_type
//!     a_positional_entry_is_the_named_one
//!     a_parenthesized_receiver_in_an_operation_body_answers_as_its_companion_call
//!     a_parenthesized_receiver_in_a_rule_body_answers_as_its_companion_call
//!     the_three_walks_build_one_value
//!     an_entry_under_a_rules_let_and_if_is_the_type
//!     a_match_arm_is_unfolded_past_the_entry
//!     a_type_parameter_inside_the_entry_is_refused
//!     a_parameter_named_like_a_bracket_channel_takes_an_entry
//!     an_effect_row_entry_is_its_row (its operation-body and receiver rows)
//!   the denoted type's reader (`type_denoted_by_occurrence` without its arm for a carried
//!   value) — FAIL:
//!     a_let_binds_the_type (its dot rows)
//!     a_parenthesized_receiver_in_an_operation_body_answers_as_its_companion_call
//!     a_parenthesized_receiver_in_a_rule_body_answers_as_its_companion_call
//!     a_type_parameter_inside_the_entry_is_refused (its receiver rows)
//!     an_effect_row_entry_is_its_row (its receiver rows)
//!   the unfold's arm (`anf_flatten` declining a carried term) — FAIL:
//!     a_match_arm_is_unfolded_past_the_entry
//!   the closing walk's arm (`node_to_debruijn` leaving a carried term's variables) — FAIL:
//!     an_entry_under_a_rules_let_and_if_is_the_type (its variable row)
//!   the printer's writer (a carried value that is no term printed `<spliced>`) — FAIL:
//!     an_entry_under_a_rules_let_and_if_is_the_type (its variable row)
//!   and, with its scalar arm alone taken out, `persistence::print`'s
//!   `a_carried_entity_prints_its_arguments`.
//!   the refusal (`open_structural_entry` answering `None` always) — FAIL:
//!     a_type_parameter_inside_the_entry_is_refused
//!   its reading of a projection off a value (`open_name_in_type` without that arm) — FAIL:
//!     a_type_parameter_inside_the_entry_is_refused (its projection row)
//!   `require[…]`'s refusal of an entry as its whole argument — FAIL, by the sentence
//!   missing; with the rule-body walk's own arm for an entry taken out as well, by a panic:
//!     an_entry_is_no_spec_instance
//!   `require[…]` admitting a row only as a binding (every entry lowered there) — FAIL:
//!     an_entry_is_no_spec_instance
//!   and `wi_51w18…::a_binding_that_is_not_a_name_at_all_is_reported`,
//!   `wi_qhdgc…::a_tuple_type_stays_refused`.
//!   the drop rule naming an entry by its text — FAIL:
//!     an_entry_is_no_spec_instance
//!   and `wi_qhdgc…::a_tuple_type_stays_refused`.
//!   the row's arm on `require[…]`'s positional loop — FAIL:
//!     `wi_51w18…::a_positional_effect_row_keeps_its_slot_too`
//!   the receiver sweep, and the query scan's two channels, keyed by the payload's kind
//!   (either put back to "any parse-only payload under that key") — FAIL:
//!     a_parameter_named_like_a_bracket_channel_takes_an_entry
//!   the query scan's refusal (`query_bracket_errors` without its entry arm), and that
//!   refusal's location — FAIL:
//!     a_query_pattern_refuses_the_entry_by_name
//!
//!   PASS UNDER EACH OF THOSE, by design — they are the fences:
//!     a_nominal_entry_is_unchanged — its entry is a name, which the converter's first
//!       arm reads.
//!     a_variable_entry_is_unchanged — a variable is a term.
//!     a_positional_constant_entry_is_unchanged — the positional route already handed a
//!       constant to `convert_term`.
//!     a_let_annotation_is_no_entry — an annotation is read where its `let` is built, and
//!       is a payload of another kind (`ParseAux::TypeExpr`) whatever its shape.
//!     an_effect_row_entry_is_its_row (its fact row) — WI-366 B1's own route.
//!
//! THE BOUNDARY. Only the operation body's walk carries the entry as the type value it
//! is. A clause's own term holds it as the term the clause matches, so a `@[simp]` rule
//! that writes such a bracket on its right-hand side, or binds a variable to the entry on
//! its left, hands the operation body it fires in a former of the type meta-language, and
//! the load is refused at the sort names inside it. Reading every type written in a
//! clause's term is WI-20260823-53W12's.

use anthill_core::eval::Value;
use anthill_core::kb::term_view::views_structurally_equal;
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_errors_of, load_kb_with, query_unary};

/// The four structural entries of the ticket: a tag for the row's namespace, and the text.
const SHAPES: [(&str, &str); 4] = [
    ("arrow", "(Int64) -> Int64"),
    ("nullary", "() -> Int64"),
    ("named", "(a: Int64, b: Int64)"),
    ("positional", "(Int64, String)"),
];

/// `test.<ns>`: `Box`, `Eb` and `Vec` to write brackets on, `idt` to hand a type value
/// through, `decl` with `declared` as its parameters' types — the row's text in a type
/// position — and `body`.
fn source(ns: &str, declared: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Type, Bool, String, Int64}}
  sort Box[V]
    operation tag() -> Int64 = 7
    operation keep(x: V) -> V = x
  end
  sort Eb[E]
    operation tag() -> Int64 = 8
  end
  sort Vec[T, N]
    operation tag() -> Int64 = 9
  end
  operation idt(t: Type) -> Type = t
  operation inc(x: Int64) -> Int64 = x + 1
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

/// Load `body` beside `decl(declared)` and assert that `r` has one answer, the type
/// `decl`'s first parameter is declared with — and not the type its second is, so the
/// comparison is one that tells two types apart.
fn is_the_declared_type(ns: &str, declared_params: &str, body: &str) {
    let mut kb = load_kb_with(&source(ns, declared_params, body));
    let got = answers(&mut kb, ns);
    assert_eq!(got.len(), 1, "{ns}: expected one answer, got {got:?}");
    let want = declared(&kb, ns, 0);
    let other = declared(&kb, ns, 1);
    assert!(
        views_structurally_equal(&kb, &got[0], &want),
        "{ns}: the answer {:?} is not the declared type {want:?}",
        got[0]
    );
    assert!(
        !views_structurally_equal(&kb, &got[0], &other),
        "{ns}: the answer {:?} is also the other declared type {other:?}",
        got[0]
    );
}

/// [`is_the_declared_type`] once a shape: `bracket_of(entry)` is the type the row writes,
/// declared beside a type no row writes, and `body_of(entry)` the row.
fn each_shape(row: &str, bracket_of: impl Fn(&str) -> String, body_of: impl Fn(&str) -> String) {
    for (tag, entry) in SHAPES {
        let ns = format!("{row}{tag}");
        let declared_params = format!("x: {}, y: Box[V = Bool]", bracket_of(entry));
        is_the_declared_type(&ns, &declared_params, &body_of(entry));
    }
}

/// `Box[V = <entry>]`.
fn boxed(entry: &str) -> String {
    format!("Box[V = {entry}]")
}

/// The integers `r` answers in `body`, loaded beside a `decl` that plays no part.
fn ints(ns: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&source(ns, "x: Int64", body));
    answers(&mut kb, ns)
        .into_iter()
        .map(|v| match v {
            Value::Int(n) => n,
            other => panic!("{ns}: expected an Int64, got {other:?}"),
        })
        .collect()
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, "x: Int64", body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    format!("{errs:?}")
}

/// A refusal's sentences with what differs between two fixtures of one row taken out:
/// the position, and the namespace.
fn sentences(ns: &str, body: &str) -> Vec<String> {
    let said: Vec<String> = load_errors_of(&source(ns, "x: Int64", body))
        .into_iter()
        .map(|e| {
            let said = e.split_once(": ").map_or(e.as_str(), |(_, said)| said);
            said.replace(ns, "NS")
        })
        .collect();
    assert!(!said.is_empty(), "{ns}: must be refused, and loaded clean");
    said
}

/// The message such an entry drew before: its text read as a name.
const UNRESOLVED: &str = "unresolved name '(";

// ── the rule: an operation body ─────────────────────────────────────────────

/// An argument at a `Type` parameter, evaluated: the value is the type the same text is
/// in `decl`'s signature.
#[test]
fn an_argument_is_the_type_its_text_is_in_a_signature() {
    each_shape("tcsgtarg", boxed, |e| {
        format!(
            "  operation go() -> Type = idt({})\n  rule r(?x) :- ?x <=> go()",
            boxed(e)
        )
    });
}

/// A `let` binds the type value: it is handed on as one, and a dot on the bound name is
/// the sort's companion call.
#[test]
fn a_let_binds_the_type() {
    each_shape("tcsgtlet", boxed, |e| {
        format!(
            "  operation go() -> Type =\n    let t = {}\n    idt(t)\n  rule r(?x) :- ?x <=> go()",
            boxed(e)
        )
    });
    for (tag, entry) in SHAPES {
        let ns = format!("tcsgtletdot{tag}");
        let body = format!(
            "  operation go() -> Int64 =\n    let t = {}\n    t.tag()\n  rule r(?x) :- ?x <=> go()",
            boxed(entry)
        );
        assert_eq!(ints(&ns, &body), [7], "{ns}");
    }
}

/// An operation's result declared `Type`.
#[test]
fn a_result_is_the_type() {
    each_shape("tcsgtres", boxed, |e| {
        format!(
            "  operation ty() -> Type = {}\n  rule r(?x) :- ?x <=> ty()",
            boxed(e)
        )
    });
}

/// One bracket down: the entry of an entry.
#[test]
fn one_bracket_down_is_the_type() {
    let nested = |e: &str| boxed(&boxed(e));
    each_shape("tcsgtdown", nested, |e| {
        format!(
            "  operation go() -> Type = idt({})\n  rule r(?x) :- ?x <=> go()",
            nested(e)
        )
    });
}

/// An entry written without its parameter's name binds the parameter the named one
/// names where the bracket is evaluated — in an operation body, at the top of the term
/// and one bracket down.
#[test]
fn a_positional_entry_is_the_named_one() {
    each_shape("tcsgtpos", boxed, |e| {
        format!("  operation go() -> Type = idt(Box[{e}])\n  rule r(?x) :- ?x <=> go()")
    });
    let nested = |e: &str| boxed(&boxed(e));
    each_shape("tcsgtposdown", nested, |e| {
        format!("  operation go() -> Type = idt(Box[V = Box[{e}]])\n  rule r(?x) :- ?x <=> go()")
    });
}

/// In a clause's own term the positional entry and the named one are two inputs normalized
/// to one term, for a structural entry as for a nominal one: a fact holding the one is
/// matched by a goal writing the other, as an operation body evaluates both to one type
/// (user, 2026-10-17). They were two terms, each matched by itself alone.
#[test]
fn a_positional_entry_in_a_clauses_term_is_the_named_one() {
    for (tag, entry) in SHAPES {
        let ns = format!("tcsgtposfact{tag}");
        let body = format!("  fact holds(Box[{entry}])\n  rule r(?x) :- holds(Box[{entry}]), ?x <=> 1");
        assert_eq!(ints(&ns, &body), [1], "{ns}");
        let ns = format!("tcsgtposfactnamed{tag}");
        let body =
            format!("  fact holds(Box[{entry}])\n  rule r(?x) :- holds(Box[V = {entry}]), ?x <=> 1");
        assert_eq!(ints(&ns, &body), [1], "{ns}");
        let ns = format!("tcsgtnamedfactpos{tag}");
        let body =
            format!("  fact holds(Box[V = {entry}])\n  rule r(?x) :- holds(Box[{entry}]), ?x <=> 1");
        assert_eq!(ints(&ns, &body), [1], "{ns}");
    }
    let body = "  fact holds(Box[String])\n  rule r(?x) :- holds(Box[V = String]), ?x <=> 1";
    assert_eq!(ints("tcsgtposfactnominal", body), [1]);
    // A fact and a rule may write the bracket as their head, entry and all.
    for (ns, body) in [
        ("tcsgtposheadfact", "  fact Box[(Int64) -> Int64]\n  rule r(?x) :- Box[(Int64) -> Int64], ?x <=> 1"),
        ("tcsgtposheadrule", "  rule Box[(Int64) -> String] :- true\n  rule r(?x) :- Box[(Int64) -> String], ?x <=> 1"),
        ("tcsgtposheadrow", "  fact Eb[{}]\n  rule r(?x) :- Eb[{}], ?x <=> 1"),
    ] {
        assert_eq!(ints(ns, body), [1], "{ns}");
    }
    let body = "  fact Box[(Int64) -> Int64]\n  rule r(?x) :- Box[(Int64) -> String], ?x <=> 1";
    assert_eq!(ints("tcsgtposheadno", body), [0i64; 0]);
}

/// A parenthesized receiver in an operation body is its companion call: each calls
/// `tag`, each hands `keep` a value of the entry's type back, and each refuses another
/// value with the sentence the other gives — which names the entry's type.
#[test]
fn a_parenthesized_receiver_in_an_operation_body_answers_as_its_companion_call() {
    for (tag, entry) in SHAPES {
        let b = boxed(entry);
        for (spelling, receiver) in [("paren", format!("({b})")), ("comp", b.clone())] {
            let ns = format!("tcsgtrecv{tag}{spelling}");
            let body =
                format!("  operation go() -> Int64 = {receiver}.tag()\n  rule r(?x) :- ?x <=> go()");
            assert_eq!(ints(&ns, &body), [7], "{ns}");
        }
        let refused = |spelling: &str, receiver: &str| {
            let ns = format!("tcsgtrecvno{tag}{spelling}");
            let body = format!("  operation go() -> Bool = {receiver}.keep(true)");
            sentences(&ns, &body)
        };
        let paren = refused("paren", &format!("({b})"));
        assert_eq!(paren, refused("comp", &b), "{tag}");
        assert!(
            paren.iter().any(|s| s.contains("keep.x") && s.contains("got Bool")),
            "{tag}: {paren:?}"
        );
        assert!(!format!("{paren:?}").contains(UNRESOLVED), "{tag}: {paren:?}");
    }
    // A value of the entry's type is taken, and is the value: the function is called.
    for (spelling, receiver) in [
        ("paren", "(Box[V = (Int64) -> Int64])"),
        ("comp", "Box[V = (Int64) -> Int64]"),
    ] {
        let ns = format!("tcsgtrecvkeep{spelling}");
        let body = format!(
            "  operation go() -> Int64 =\n    let f = {receiver}.keep(inc)\n    f(1)\n  rule r(?x) :- ?x <=> go()"
        );
        assert_eq!(ints(&ns, &body), [2], "{ns}");
    }
}

// ── the rule: a clause's own term ───────────────────────────────────────────

/// The same pair in a rule body.
#[test]
fn a_parenthesized_receiver_in_a_rule_body_answers_as_its_companion_call() {
    for (tag, entry) in SHAPES {
        let b = boxed(entry);
        for (spelling, receiver) in [("paren", format!("({b})")), ("comp", b.clone())] {
            let ns = format!("tcsgtrrecv{tag}{spelling}");
            let body = format!("  rule r(?x) :- ?x <=> {receiver}.tag()");
            assert_eq!(ints(&ns, &body), [7], "{ns}");
        }
        let refused = |spelling: &str, receiver: &str| {
            let ns = format!("tcsgtrrecvno{tag}{spelling}");
            sentences(&ns, &format!("  rule r(?x) :- ?x <=> {receiver}.keep(true)"))
        };
        let paren = refused("paren", &format!("({b})"));
        assert_eq!(paren, refused("comp", &b), "{tag}");
        assert!(
            paren.iter().any(|s| s.contains("keep.x") && s.contains("got Bool")),
            "{tag}: {paren:?}"
        );
    }
    // A variable of the clause inside the entry is the clause's: the call is made at the
    // type the earlier goal bound it to.
    let body = "  fact pick(Int64)\n  rule r(?x) :- pick(?a), ?x <=> (Box[V = (?a) -> Int64]).tag()";
    assert_eq!(ints("tcsgtrrecvvar", body), [7]);
}

/// A fact holding the type is matched by a goal that writes it, and by no goal that
/// writes another; a variable in the goal's place is bound to the stored type.
#[test]
fn a_fact_is_matched_by_a_goal() {
    for (i, (tag, entry)) in SHAPES.into_iter().enumerate() {
        let other = SHAPES[(i + 1) % SHAPES.len()].1;
        let fact = format!("  fact holds({})", boxed(entry));
        let ns = format!("tcsgtfact{tag}");
        let body = format!("{fact}\n  rule r(?x) :- holds({}), ?x <=> 1", boxed(entry));
        assert_eq!(ints(&ns, &body), [1], "{ns}");
        let ns = format!("tcsgtfactno{tag}");
        let body = format!("{fact}\n  rule r(?x) :- holds({}), ?x <=> 1", boxed(other));
        assert_eq!(ints(&ns, &body), [0i64; 0], "{ns}");
    }
    each_shape("tcsgtfactvar", boxed, |e| {
        format!("  fact holds({})\n  rule r(?x) :- holds(?x)", boxed(e))
    });
    // A named tuple is ordered: its components in another order are another type.
    let body = "  fact holds(Box[V = (a: Int64, b: String)])\n  rule r(?x) :- holds(Box[V = (b: String, a: Int64)]), ?x <=> 1";
    assert_eq!(ints("tcsgtfactorder", body), [0i64; 0]);
    // Under negation the goal is decided, not floundered on.
    let body = "  fact holds(Box[V = (Int64) -> Int64])\n  rule r(?x) :- not holds(Box[V = (Int64) -> String]), ?x <=> 1";
    assert_eq!(ints("tcsgtfactnot", body), [1]);
    let body = "  fact holds(Box[V = (Int64) -> Int64])\n  rule r(?x) :- not holds(Box[V = (Int64) -> Int64]), ?x <=> 1";
    assert_eq!(ints("tcsgtfactnotno", body), [0i64; 0]);
}

/// A rule's head holds the type as a fact does.
#[test]
fn a_rule_head_holds_the_type() {
    each_shape("tcsgthead", boxed, |e| {
        format!("  rule hd({}) :- true\n  rule r(?x) :- hd(?x)", boxed(e))
    });
}

/// A variable written inside the entry is a variable of the clause: it is bound by the
/// match, in a goal and in a fact.
#[test]
fn a_variable_inside_the_entry_binds() {
    is_the_declared_type(
        "tcsgtvargoal",
        "x: String, y: Int64",
        "  fact holds(Box[V = (Int64) -> String])\n  rule r(?x) :- holds(Box[V = (Int64) -> ?x])",
    );
    is_the_declared_type(
        "tcsgtvarfact",
        "x: String, y: Int64",
        "  fact holds(Box[V = (?a) -> ?a])\n  rule r(?x) :- holds(Box[V = (String) -> ?x])",
    );
    // One variable twice in the fact is one type: no goal at two types matches it.
    let body = "  fact holds(Box[V = (?a) -> ?a])\n  rule r(?x) :- holds(Box[V = (String) -> Int64]), ?x <=> 1";
    assert_eq!(ints("tcsgtvarfactno", body), [0i64; 0]);
}

/// The value an operation body builds, the term a fact stores and the argument a rule
/// body writes are one type: each matches the others.
#[test]
fn the_three_walks_build_one_value() {
    for (tag, entry) in SHAPES {
        let b = boxed(entry);
        let ns = format!("tcsgtwalksop{tag}");
        let body = format!(
            "  operation mk() -> Type = {b}\n  fact holds({b})\n  rule r(?x) :- ?t <=> mk(), holds(?t), ?x <=> 1"
        );
        assert_eq!(ints(&ns, &body), [1], "{ns}");
        let ns = format!("tcsgtwalksrule{tag}");
        let body =
            format!("  fact holds({b})\n  rule r(?x) :- ?t <=> idt({b}), holds(?t), ?x <=> 1");
        assert_eq!(ints(&ns, &body), [1], "{ns}");
        let ns = format!("tcsgtwalkseq{tag}");
        let body = format!(
            "  operation mk() -> Type = {b}\n  operation same(a: Type, b: Type) -> Bool = anthill.prelude.PartialEq.eq(a, b)\n  operation go() -> Int64 = if same({b}, mk()) then 1 else 0\n  rule r(?x) :- ?x <=> go()"
        );
        assert_eq!(ints(&ns, &body), [1], "{ns}");
    }
    // Two types that differ in the entry alone are told apart by the same comparison.
    let body = "  operation same(a: Type, b: Type) -> Bool = anthill.prelude.PartialEq.eq(a, b)\n  operation go() -> Int64 = if same(Box[V = (Int64) -> Int64], Box[V = (Int64) -> String]) then 1 else 0\n  rule r(?x) :- ?x <=> go()";
    assert_eq!(ints("tcsgtwalksne", body), [0]);
}

/// Under a rule's `let` and `if` — written as an operation body is, typed as one — the
/// bracket loads with a structural entry as it does with a nominal one, and a variable of
/// the clause inside the entry is the clause's.
#[test]
fn an_entry_under_a_rules_let_and_if_is_the_type() {
    for (tag, entry) in SHAPES {
        let b = boxed(entry);
        let ns = format!("tcsgtrulelet{tag}");
        let body = format!("  rule r(?x) :- ?t <=> (let t = {b}\n    t), ?x <=> 1");
        assert_eq!(ints(&ns, &body), [1], "{ns}");
        let ns = format!("tcsgtruleif{tag}");
        let body = format!("  rule r(?x) :- ?t <=> (if true then {b} else Box[V = Int64]), ?x <=> 1");
        assert_eq!(ints(&ns, &body), [1], "{ns}");
    }
    // The clause's variable inside the entry is bound where the rule fires: the answer
    // holds the type the earlier goal gave it, and no variable.
    let mut kb = load_kb_with(&source(
        "tcsgtrulevar",
        "x: Int64",
        "  fact pick(String)\n  rule r(?x) :- pick(?a), ?x <=> (if true then Box[V = (?a) -> Int64] else Box[V = Int64])",
    ));
    let got = answers(&mut kb, "tcsgtrulevar");
    assert_eq!(got.len(), 1, "{got:?}");
    let printed = match &got[0] {
        Value::Node(occ) => anthill_core::persistence::print::TermPrinter::new(&kb).print_occurrence(occ),
        other => panic!("expected the expression the clause holds, got {other:?}"),
    };
    // The entry is printed as the type it is (WI-20261022-DRGCP): a substitution rebuilt it
    // over the bound variable, and that carrier used to be written as the application
    // `Arrow(param: String, …)`, which this row read the parameter off.
    assert!(printed.contains("(String) -> Int64"), "{printed}");
    assert!(!printed.contains('?'), "{printed}");
    assert!(!printed.contains("<spliced>"), "{printed}");
}

/// A `match` operation called with its scrutinee unbound is unfolded arm by arm, and an
/// arm that holds such a bracket is one of them.
#[test]
fn a_match_arm_is_unfolded_past_the_entry() {
    for (tag, entry) in SHAPES {
        let ns = format!("tcsgtunfold{tag}");
        let body = format!(
            "  sort Sel\n    entity one\n    entity two\n  end\n  operation pk(s: Sel) -> Type = match s\n    case one -> {}\n    case two -> Box[V = Bool]\n  rule r(?t) :- pk(?s) = ?t",
            boxed(entry)
        );
        let declared_params = format!("x: {}, y: Box[V = Bool]", boxed(entry));
        let mut kb = load_kb_with(&source(&ns, &declared_params, &body));
        let got = answers(&mut kb, &ns);
        assert_eq!(got.len(), 2, "{ns}: {got:?}");
        let (first, second) = (declared(&kb, &ns, 0), declared(&kb, &ns, 1));
        assert!(views_structurally_equal(&kb, &got[0], &first), "{ns}: {:?}", got[0]);
        assert!(views_structurally_equal(&kb, &got[1], &second), "{ns}: {:?}", got[1]);
    }
}

// ── the fences ──────────────────────────────────────────────────────────────

/// A nominal entry: the argument, the receiver and the fact answer as before.
#[test]
fn a_nominal_entry_is_unchanged() {
    is_the_declared_type(
        "tcsgtnomarg",
        "x: Box[V = anthill.prelude.Function[A = Int64, B = Int64]], y: Box[V = Bool]",
        "  operation go() -> Type = idt(Box[V = anthill.prelude.Function[A = Int64, B = Int64]])\n  rule r(?x) :- ?x <=> go()",
    );
    assert_eq!(
        ints(
            "tcsgtnomrecv",
            "  operation go() -> Int64 = (Box[V = String]).tag()\n  rule r(?x) :- ?x <=> go()"
        ),
        [7]
    );
    assert_eq!(
        ints(
            "tcsgtnomfact",
            "  fact holds(Box[V = String])\n  rule r(?x) :- holds(Box[V = String]), ?x <=> 1"
        ),
        [1]
    );
}

/// A variable entry is bound to the stored entry.
#[test]
fn a_variable_entry_is_unchanged() {
    is_the_declared_type(
        "tcsgtvarentry",
        "x: String, y: Int64",
        "  fact holds(Box[V = String])\n  rule r(?x) :- holds(Box[V = ?x])",
    );
}

/// A constant written positionally: stored in a fact and matched, and bound at a
/// companion call.
#[test]
fn a_positional_constant_entry_is_unchanged() {
    assert_eq!(
        ints(
            "tcsgtconstpos",
            "  fact holds(Vec[Int64, 3])\n  rule r(?n) :- holds(Vec[Int64, ?n])"
        ),
        [3]
    );
    assert_eq!(
        ints(
            "tcsgtconstcomp",
            "  operation go() -> Int64 = Vec[Int64, 3].tag()\n  rule r(?x) :- ?x <=> go()"
        ),
        [9]
    );
}

/// A `let`'s annotation written as an arrow type is the annotation, not an argument of
/// the `let`.
#[test]
fn a_let_annotation_is_no_entry() {
    let body = "  operation go() -> Int64 =\n    let f: (Int64) -> Int64 = inc\n    f(1)\n  rule r(?x) :- ?x <=> go()";
    assert_eq!(ints("tcsgtanno", body), [2]);
}

// ── beside the rule ─────────────────────────────────────────────────────────

/// An effect row is an entry of the same kind. A fact stored it before; an operation body
/// now evaluates it — the bracket is the type `decl` declares — and its parenthesized
/// receiver answers as its companion call in both bodies.
#[test]
fn an_effect_row_entry_is_its_row() {
    assert_eq!(
        ints(
            "tcsgtrowfact",
            "  fact holds(Eb[E = {}])\n  rule r(?x) :- holds(Eb[E = {}]), ?x <=> 1"
        ),
        [1]
    );
    is_the_declared_type(
        "tcsgtrowop",
        "x: Eb[E = {}], y: Box[V = Bool]",
        "  operation go() -> Type = idt(Eb[E = {}])\n  rule r(?x) :- ?x <=> go()",
    );
    is_the_declared_type(
        "tcsgtrowpos",
        "x: Eb[E = {}], y: Box[V = Bool]",
        "  operation go() -> Type = idt(Eb[{}])\n  rule r(?x) :- ?x <=> go()",
    );
    for (ns, body) in [
        (
            "tcsgtrowrecv",
            "  operation go() -> Int64 = (Eb[E = {}]).tag()\n  rule r(?x) :- ?x <=> go()",
        ),
        (
            "tcsgtrowcomp",
            "  operation go() -> Int64 = Eb[E = {}].tag()\n  rule r(?x) :- ?x <=> go()",
        ),
        ("tcsgtrowrrecv", "  rule r(?x) :- ?x <=> (Eb[E = {}]).tag()"),
        ("tcsgtrowrcomp", "  rule r(?x) :- ?x <=> Eb[E = {}].tag()"),
    ] {
        assert_eq!(ints(ns, body), [8], "{ns}");
    }
    // The operation-body value and the stored fact are one type.
    assert_eq!(
        ints(
            "tcsgtrowwalks",
            "  operation mk() -> Type = Eb[E = {}]\n  fact holds(Eb[E = {}])\n  rule r(?x) :- ?t <=> mk(), holds(?t), ?x <=> 1"
        ),
        [1]
    );
}

// ── the refusals ────────────────────────────────────────────────────────────

/// In an operation body the entry is read as one type when the body is loaded, so a type
/// parameter inside it — the operation's or its sort's, with a `TypeValue` clause or
/// without — a variable, and a projection off a value parameter are refused, naming the
/// entry and the name. A receiver's bracket binds the call's types and is no value: there
/// a parameter is the caller's.
#[test]
fn a_type_parameter_inside_the_entry_is_refused() {
    for (ns, body, name, entry) in [
        (
            "tcsgtopen",
            "  operation g[T]() -> Type = Box[V = (T) -> Int64]",
            "`T`",
            "(?T) -> Int64",
        ),
        (
            "tcsgtopenreq",
            "  import anthill.reflect.TypeValue\n  operation g[T]() -> Type requires TypeValue[T = T] = Box[V = (T) -> Int64]",
            "`T`",
            "(?T) -> Int64",
        ),
        (
            "tcsgtopensort",
            "  sort Bx[W]\n    operation me() -> Type = Box[V = (a: W, b: Int64)]\n  end",
            "`W`",
            "(a: W, b: Int64)",
        ),
        (
            "tcsgtopenlet",
            "  operation g[T]() -> Int64 =\n    let t = Box[V = (T) -> Int64]\n    t.tag()",
            "`T`",
            "(?T) -> Int64",
        ),
        (
            "tcsgtopenvar",
            "  operation g() -> Type = Box[V = (?v) -> Int64]",
            "`v`",
            "(?v) -> Int64",
        ),
        (
            "tcsgtopenrow",
            "  operation g[R]() -> Type = Eb[E = {R}]",
            "`R`",
            "{?R}",
        ),
        (
            "tcsgtopenproj",
            "  sort Cell[W]\n    entity cell(v: W)\n  end\n  operation g(s: Cell[W = Int64]) -> Type = Box[V = (s.W) -> Int64]",
            "`s.W`",
            "(s.W) -> Int64",
        ),
    ] {
        let errs = refusal(ns, body);
        assert!(errs.contains("bracket's entry in a value position"), "{ns}: {errs}");
        assert!(errs.contains(&format!("which names {name}")), "{ns}: {errs}");
        assert!(errs.contains(&format!("`{entry}`")), "{ns}: {errs}");
    }
    // The receiver, in both spellings, under a caller that says the parameter.
    for (ns, receiver) in [
        ("tcsgtopenrecv", "(Box[V = (T) -> Int64])"),
        ("tcsgtopencomp", "Box[V = (T) -> Int64]"),
    ] {
        let body = format!(
            "  operation g[T]() -> Int64 = {receiver}.tag()\n  operation c() -> Int64 = g[T = String]()\n  rule r(?x) :- ?x <=> c()"
        );
        assert_eq!(ints(ns, &body), [7], "{ns}");
    }
}

/// A value inside the entry is the gated value-in-type binding, in an operation body and
/// in a fact, not a name spelled with the entry's text.
#[test]
fn a_value_inside_the_entry_is_refused() {
    for (ns, body) in [
        (
            "tcsgtdenotedop",
            "  operation g() -> Type = Box[V = (person: \"name\")]",
        ),
        ("tcsgtdenotedfact", "  fact holds(Box[V = (person: \"name\")])"),
    ] {
        let errs = refusal(ns, body);
        assert!(errs.contains("value-in-type binding in type argument"), "{ns}: {errs}");
        assert!(!errs.contains(UNRESOLVED), "{ns}: {errs}");
    }
}

/// A name inside the entry that resolves to nothing is reported as that name, where the
/// whole entry's text was.
#[test]
fn a_name_inside_the_entry_is_reported_as_itself() {
    for (ns, body) in [
        ("tcsgtzorkop", "  operation g() -> Type = Box[V = (Zork) -> Int64]"),
        ("tcsgtzorkfact", "  fact holds(Box[V = (Zork) -> Int64])"),
        ("tcsgtzorkgoal", "  rule r(?x) :- holds(Box[V = (a: Zork, b: Int64)]), ?x <=> 1"),
    ] {
        let errs = refusal(ns, body);
        assert!(errs.contains("unresolved name 'Zork'"), "{ns}: {errs}");
        assert!(!errs.contains(UNRESOLVED), "{ns}: {errs}");
    }
}

/// `(A)` is no type in a bracket's entry either: the converter refuses it there with the
/// sentence it gives it in a signature.
#[test]
fn a_lone_parenthesized_type_is_no_type() {
    let said = |body: &str| {
        let errs = anthill_core::parse::parse(&source("tcsgtlone", "x: Int64", body))
            .err()
            .unwrap_or_else(|| panic!("`{body}` must not parse"));
        format!("{errs:?}")
    };
    let entry = said("  operation g() -> Type = Box[V = (Int64)]");
    assert!(entry.contains("a single parenthesized type is not a type"), "{entry}");
    let signature = said("  operation g(x: Box[V = (Int64)]) -> Int64 = 0");
    assert!(signature.contains("a single parenthesized type is not a type"), "{signature}");
}

/// `require[…]` takes a spec instance. An entry standing as its whole argument is refused
/// by that sentence, as a bare goal and as an equation's operand, and as a binding of
/// the spec a tuple type and an arrow type stay on the list of what names no sort
/// (`wi_qhdgc_require_spec_logical_variable_test`), named by their text.
#[test]
fn an_entry_is_no_spec_instance() {
    let program = |ns: &str, goal: &str| {
        format!(
            r#"
namespace test.{ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end
  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  fact seed(leaf())
  rule r(?r) :- seed(?x), {goal}, Desc.describe(?x, ?r)
end
"#
        )
    };
    for (ns, goal, written) in [
        ("tcsgtreqtuple", "?d = require[(Leaf, Leaf)]", "`(Leaf, Leaf)`"),
        ("tcsgtreqarrow", "?d = require[(Leaf) -> Leaf]", "`(Leaf) -> Leaf`"),
        ("tcsgtreqrow", "?d = require[{}]", "`{}`"),
        ("tcsgtreqgoal", "require[(a: Leaf, b: Leaf)]", "`(a: Leaf, b: Leaf)`"),
    ] {
        let errs = load_errors_of(&program(ns, goal));
        let said = format!("{errs:?}");
        assert!(said.contains("`require[…]` takes a spec instance"), "{ns}: {said}");
        assert!(said.contains(written), "{ns}: {said}");
    }
    for (ns, goal, written) in [
        ("tcsgtreqbindtuple", "?d = require[Desc[T = (Leaf, Leaf)]]", "`(Leaf, Leaf)`"),
        ("tcsgtreqbindarrow", "?d = require[Desc[(Leaf) -> Leaf]]", "`(Leaf) -> Leaf`"),
    ] {
        let said = format!("{:?}", load_errors_of(&program(ns, goal)));
        assert!(
            said.contains(&format!("{written} in it names neither a sort nor one of `Desc`'s own type parameters")),
            "{ns}: {said}"
        );
    }
    // The control: a spec instance in the same place answers.
    let mut kb = load_kb_with(&program("tcsgtreqok", "?d = require[Desc[T = Leaf]]"));
    assert!(matches!(answers(&mut kb, "tcsgtreqok")[..], [Value::Int(7)]));
}

/// A sort's parameter may carry the name of a channel a call's bracket rides
/// (`recv_type`, `type_args`); an entry bound to it is the entry, in an operation body,
/// in a fact and in a query pattern.
#[test]
fn a_parameter_named_like_a_bracket_channel_takes_an_entry() {
    let ns = "tcsgtchannel";
    let bracket = "Rb[recv_type = (Int64) -> Int64, type_args = {}]";
    let mut kb = load_kb_with(&source(
        ns,
        &format!("x: {bracket}, y: Box[V = Bool]"),
        &format!(
            "  sort Rb[recv_type, type_args]\n  end\n  operation go() -> Type = idt({bracket})\n  fact holds({bracket})\n  rule r(?x) :- ?x <=> go()"
        ),
    ));
    let got = answers(&mut kb, ns);
    assert_eq!(got.len(), 1, "{got:?}");
    let want = declared(&kb, ns, 0);
    assert!(views_structurally_equal(&kb, &got[0], &want), "{:?}", got[0]);
    let query = crate::common::query_pattern_term(
        &mut kb,
        &format!("test.{ns}.holds(test.{ns}.Rb[recv_type = ?a, type_args = {{}}])"),
    );
    let rows = kb.resolve(&[query], &Default::default());
    assert_eq!(rows.len(), 1);
    assert!(rows[0].is_definite());
}

/// A query pattern's walk has no type lowering: such an entry is refused where the
/// pattern is scanned, by a sentence of its own, and a variable in its place answers the
/// stored type.
#[test]
fn a_query_pattern_refuses_the_entry_by_name() {
    use anthill_core::kb::load;
    use anthill_core::parse;

    let ns = "tcsgtquery";
    let mut kb = load_kb_with(&source(
        ns,
        "x: Box[V = (Int64) -> Int64], y: Box[V = Bool]",
        "  fact holds(Box[V = (Int64) -> Int64])",
    ));
    for pattern in [
        format!("test.{ns}.holds(test.{ns}.Box[V = (anthill.prelude.Int64) -> anthill.prelude.Int64])"),
        format!("test.{ns}.holds(test.{ns}.Box[(a: anthill.prelude.Int64, b: anthill.prelude.Int64)])"),
    ] {
        let parsed = parse::parse(&format!("fact {pattern}")).unwrap();
        let errors = load::scan_query_definitions(&mut kb, &[&parsed]);
        let said = load::LoadError::render_all(&errors).collect::<Vec<_>>().join("\n");
        assert!(said.contains("is not read in a query pattern"), "{pattern}: {said}");
        assert!(!said.contains(UNRESOLVED), "{pattern}: {said}");
        // At its line and column in the pattern, not at a byte range.
        assert!(said.contains("1:"), "{pattern}: {said}");
        assert!(!said.contains(".."), "{pattern}: {said}");
    }
    let query = crate::common::query_pattern_term(
        &mut kb,
        &format!("test.{ns}.holds(test.{ns}.Box[V = ?v])"),
    );
    let rows = kb.resolve(&[query], &Default::default());
    assert_eq!(rows.len(), 1);
    assert!(rows[0].is_definite());
}
