//! WI-1024 — `value_functor`: one question, every carrier, and the carriers that
//! must stay out.
//!
//! `value_functor` answers "which sort / constructor does this value REFERENCE?"
//! for `KB.facts_of`, `stored_facts_of`, `is_modifiable`, `sort_query` lowering,
//! the `MatchDispatch` pre-filter, `Modify`'s resource key, and eight readers in
//! anthill-stl's reflect bridge. It was the fifth by-carrier `matches!` of the
//! class WI-1023 removed, and it had a `_ => None` catch-all — so a carrier that
//! gained a structural head fell into it silently. That is how `Value::SymbolRef`
//! went missing until WI-1016, and how `OpRef` / `Requirement` went missing again
//! when WI-1019 gave them heads.
//!
//! THE RULE THE WHOLE FILE TURNS ON: **a structural head is not a referent.** A
//! head naming the value's reflect ENCODING (`Dictionary`, `OpRef`, a `Lambda`
//! occurrence's constructor) must not be read as a sort the value references —
//! doing so turns a loud `TypeMismatch` into a silently empty answer. So the three
//! naming carriers route through `ViewHead::functor_sym`, and the runtime handles
//! and occurrences are an explicit `None`. `Value::Node` is the interesting `None`:
//! a bare `Expr::Ref(s)` genuinely names `s`, but no head test separates that from
//! an encoding on this carrier, and admitting it obliges two paired destructure
//! sites — WI-1025.
//!
//! Each test states, MEASURED, what it reports when the change under it is backed
//! out — and which pass either way BY DESIGN.

use smallvec::SmallVec;

use anthill_core::eval::{value_functor, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::Term;
use anthill_core::span::{SourceId, SourceSpan};

mod common;

const SRC: &str = r#"
namespace test.wi1024
  sort Item
    entity Box(id: String)
  end
  fact Box(id: "B-001")
end
"#;

fn box_sym(interp: &mut Interpreter) -> Symbol {
    interp.kb_mut().resolve_qualified_name_sym("test.wi1024.Item.Box")
}

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 3)
}

fn node(e: Expr) -> Value {
    Value::Node(NodeOccurrence::new_expr(e, span(), None))
}

/// An occurrence that is an APPLICATION, not a name. It must carry an argument: a
/// nullary `Expr::Apply` of a constructor canonicalizes to `ViewHead::Ref` through
/// `functor_view_head` (WI-436), so a zero-arg one would test the other case.
fn applied_node(functor: Symbol, arg: Symbol) -> Value {
    node(Expr::Apply {
        functor,
        pos_args: vec![NodeOccurrence::new_expr(Expr::Ref(arg), span(), None)],
        named_args: vec![],
        type_args: vec![],
    })
}

// ── the predicate itself, carrier by carrier ────────────────────────────────

/// The whole answer table, read off the `pub` reader directly rather than
/// inferred from a consumer's behaviour — so each row names ITS carrier when it
/// goes red.
///
/// CONTROLS, each MEASURED:
///  - move `OpRef | Requirement | Node` into the routed arm: `requirement`,
///    `node-ref`, `node-apply` and `node-spliced-dict` all report `Some(..)` —
///    each an encoding (or a laundered handle) read as a referent, which is the
///    whole thing this file forbids. `opref` reports `Some(OpRef)` too.
///
/// The `term-ref` / `symbolref` / `entity` / `term-app` rows pass EITHER WAY BY
/// DESIGN — they are the pre-existing arms, here so "the rewrite is
/// answer-for-answer identical for them" is asserted rather than argued.
#[test]
fn value_functor_answers_by_what_the_head_denotes() {
    let mut interp = common::interp_for(SRC);
    let sym = box_sym(&mut interp);
    let dict_sym = interp.kb().resolve_symbol("anthill.realization.runtime.Dictionary");
    let ident_tid = interp.kb_mut().alloc(Term::Ident(sym));
    let nullary_fn =
        Value::term(interp.kb_mut().resolve_qualified_name_term("test.wi1024.Item.Box"));
    let string_sym = interp.kb().resolve_symbol("anthill.prelude.String");
    let applied = {
        let id = interp.kb_mut().intern("id");
        let arg = interp.kb_mut().alloc(Term::Ref(string_sym));
        Value::term(interp.kb_mut().alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(id, arg)]),
        }))
    };
    let dict = Value::Requirement(interp.alloc_requirement(sym, SmallVec::new()));

    let rows: Vec<(&str, Value, Option<Symbol>)> = vec![
        // Names, on all four carriers of a name — the WI-1016 rule.
        ("term-ref", Value::term(interp.kb_mut().alloc(Term::Ref(sym))), Some(sym)),
        ("term-nullary-fn", nullary_fn, Some(sym)),
        ("symbolref", Value::SymbolRef(sym), Some(sym)),

        // An APPLICATION on the term carrier still answers its functor: that is
        // pre-existing and load-bearing — `facts_of(kb, List[T = Int64])` (WI-707).
        ("term-app", applied, Some(sym)),
        (
            "entity",
            Value::Entity {
                functor: sym,
                pos: std::rc::Rc::from(vec![Value::Str("B-001".into())]),
                named: std::rc::Rc::from(Vec::<(Symbol, Value)>::new()),
            },
            Some(sym),
        ),
        // NOT names. `Ident` is unresolved; a tuple has no functor at all.
        ("term-ident", Value::term(ident_tid), None),
        ("tuple", Value::Tuple {
            pos: std::rc::Rc::from(Vec::<Value>::new()),
            named: std::rc::Rc::from(Vec::<(Symbol, Value)>::new()),
        }, None),
        // Structural heads that name an ENCODING, not a referent — and one that
        // would launder an excluded carrier. `node-ref` is the row that is `None`
        // even though it DOES name a symbol: see WI-1025.
        ("requirement", dict.clone(), None),
        ("opref", Value::OpRef { op: sym, dict: None, named: None }, None),
        ("node-ref", node(Expr::Ref(sym)), None),
        ("node-apply", applied_node(sym, string_sym), None),
        ("node-spliced-dict", node(Expr::Spliced(dict)), None),
    ];

    // PREMISE for the exclusion rows: their heads really DO present a symbol, so
    // `None` is a DECISION and not an absent shape. Without this the rows would
    // pass for the wrong reason — the WI-1023 lesson about probes that sample an
    // empty population.
    {
        use anthill_core::kb::term_view::{TermView, ViewHead};
        let spliced = node(Expr::Spliced(
            Value::Requirement(interp.alloc_requirement(sym, SmallVec::new())),
        ));
        assert!(
            matches!(spliced.head(interp.kb()), ViewHead::Functor { functor: Some(f), .. } if f == dict_sym),
            "premise: a spliced dictionary heads as the Dictionary CONSTRUCTOR — the laundering route",
        );
        assert!(
            matches!(node(Expr::Ref(sym)).head(interp.kb()), ViewHead::Ref(f) if f == sym),
            "premise: a bare Ref occurrence DOES name its symbol (WI-1025)",
        );
        assert!(
            matches!(
                applied_node(sym, string_sym).head(interp.kb()),
                ViewHead::Functor { functor: Some(_), .. }
            ),
            "premise: an ARG-BEARING applied occurrence heads as a functor \
             (a nullary one canonicalizes to Ref, so it would not exercise this)",
        );
    }

    // COLLECTED, not asserted per row: a per-row assert names ONE carrier when a
    // change is backed out and hides the rest.
    let wrong: Vec<(&str, Option<Symbol>, Option<Symbol>)> = rows
        .into_iter()
        .map(|(name, v, want)| (name, want, value_functor(interp.kb(), &v)))
        .filter(|(_, want, got)| want != got)
        .collect();
    assert!(wrong.is_empty(), "(row, want, got): {wrong:?}");
}

/// THE ANTI-DRIFT GUARD, and the one the exhaustive match cannot give.
///
/// `match` with no `_` arm catches a `Value` variant being ADDED. It cannot catch
/// the drift that actually happened twice: an EXISTING variant gaining a
/// structural head (WI-1019 gave `OpRef` / `Requirement` theirs) while this reader
/// keeps answering `None` by default. So: any carrier whose head yields a
/// `functor_sym` must be either routed here or one of the deliberate exclusions.
///
/// CONTROL, MEASURED by deleting the `Value::OpRef { .. } | Value::Requirement(_)`
/// arm's entry from `DELIBERATE` below: the test reports both as undeclared.
#[test]
fn a_carrier_with_a_functor_head_is_routed_or_deliberately_excluded() {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let mut interp = common::interp_for(SRC);
    let sym = box_sym(&mut interp);
    // Carriers deliberately NOT routed: the two runtime handles, and every
    // occurrence form (WI-1025). Anything else with a naming head must be routed.
    const DELIBERATE: &[&str] = &["requirement", "opref", "node-ref", "node-apply"];
    let samples: Vec<(&str, Value)> = vec![
        ("requirement", Value::Requirement(interp.alloc_requirement(sym, SmallVec::new()))),
        ("opref", Value::OpRef { op: sym, dict: None, named: None }),
        ("node-apply", applied_node(sym, interp.kb().resolve_symbol("anthill.prelude.String"))),
        ("entity", Value::Entity {
            functor: sym,
            pos: std::rc::Rc::from(Vec::<Value>::new()),
            named: std::rc::Rc::from(Vec::<(Symbol, Value)>::new()),
        }),
        ("term-ref", Value::term(interp.kb_mut().alloc(Term::Ref(sym)))),
        ("symbolref", Value::SymbolRef(sym)),
        ("node-ref", node(Expr::Ref(sym))),
    ];
    let undeclared: Vec<&str> = samples
        .into_iter()
        .filter(|(name, v)| {
            let has_functor_head = matches!(
                v.head(interp.kb()),
                ViewHead::Functor { functor: Some(_), .. } | ViewHead::Ref(_)
            );
            has_functor_head
                && value_functor(interp.kb(), v).is_none()
                && !DELIBERATE.contains(name)
        })
        .map(|(name, _)| name)
        .collect();
    assert!(
        undeclared.is_empty(),
        "a carrier grew a functor head and this reader still answers None: {undeclared:?}",
    );
}

// ── the consumer sees it ────────────────────────────────────────────────────

/// End to end through `KB.facts_of`, the shortest live consumer: every naming
/// carrier resolves the SAME sort, and a runtime handle stays a LOUD error rather
/// than becoming an empty list.
///
/// The fact list is compared by CONTENT, not length — four rows returning four
/// different one-element lists would agree on `len()`.
///
/// CONTROL, MEASURED: route `Requirement` through `functor_sym` → the handle row
/// returns `Ok(nil)`, a silent empty answer to a type error. The two carrier rows
/// pass EITHER WAY BY DESIGN (both are pre-existing arms); they are here so the
/// end-to-end claim is "one sort, one answer", not one carrier measured alone.
#[test]
fn facts_of_reads_the_sort_through_every_naming_carrier() {
    let mut interp = common::interp_for(SRC);
    let sym = box_sym(&mut interp);
    let carriers: Vec<(&str, Value)> = vec![
        ("term", Value::term(interp.kb_mut().resolve_qualified_name_term("test.wi1024.Item.Box"))),
        ("symbolref", Value::SymbolRef(sym)),
    ];
    let mut answers: Vec<(&str, Vec<String>)> = Vec::new();
    for (name, v) in carriers {
        let list = interp
            .call("anthill.reflect.KB.facts_of", &[Value::Unit, v])
            .unwrap_or_else(|e| panic!("{name}: facts_of should resolve the sort, got {e:?}"));
        let heads: Vec<String> = common::list_heads(&list)
            .iter()
            .map(|h| format!("{:?}", value_functor(interp.kb(), h)))
            .collect();
        answers.push((name, heads));
    }
    // PREMISE: the fixture really has a fact, so "all agree" is not three empty
    // lists agreeing with each other.
    assert_eq!(answers[0].1.len(), 1, "the fixture asserts exactly one Box fact");
    assert!(
        answers.iter().all(|(_, h)| *h == answers[0].1),
        "one sort, one fact list, whichever carrier named it: {answers:?}",
    );

    // And the handle: loud, with the message only `value_functor`'s `None` branch
    // mints — so this is coupled to THIS reader, not to any `TypeMismatch`.
    let dict = Value::Requirement(interp.alloc_requirement(sym, SmallVec::new()));
    let err = interp
        .call("anthill.reflect.KB.facts_of", &[Value::Unit, dict])
        .expect_err("a dictionary is a type error at a sort slot, not an empty answer");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("Type (entity reference)"),
        "and it is `kb_facts_of`'s own value_functor-None branch, got {msg}",
    );
}
