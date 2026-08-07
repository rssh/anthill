//! WI-1024 — `value_functor`: one question, every carrier, and the carriers that
//! must stay out.
//!
//! `value_functor` answers "which sort / constructor does this value REFERENCE?"
//! for `KB.facts_of`, `stored_facts_of`, `is_modifiable`, `sort_query` lowering,
//! the `MatchDispatch` pre-filter, `Modify`'s resource key, and eight readers in
//! anthill-stl's reflect bridge. It was the fifth by-carrier `matches!` of the
//! class WI-1023 removed, and it had a `_ => None` catch-all — so a carrier that
//! gained a structural head fell into it silently. That is how `Value::SymbolRef`
//! went missing until WI-1016, and how `OpRef` / the dictionary went missing again
//! when WI-1019 gave them heads.
//!
//! THE RULE THE WHOLE FILE TURNS ON: **a structural head is not a referent.** A
//! head naming the value's reflect ENCODING (`OpRef`, a `Lambda` occurrence's
//! constructor) must not be read as a sort the value references — doing so turns
//! a loud `TypeMismatch` into a silently empty answer.
//!
//! WI-1025 RESTATED THAT RULE MORE PRECISELY and moved the `Node` rows with it:
//! read the head when the carrier has a faithful TERM FORM, refuse when the head
//! is view-only. An occurrence lowers, so it is read like the rest; `OpRef` does
//! not (`alloc_from_value` answers `UnsupportedVariant`), so its WI-1019 head has
//! no stored term behind it.
//!
//! WI-1045 MOVED THE DICTIONARY ACROSS THAT LINE, and the rule is what moved it,
//! not an exception to it. A dictionary is no longer a handle with a view-only
//! head: it is an ordinary `Value::Entity`, and the IR node the typer emits is
//! `Dictionary(sub₀ … subₙ₋₁, impl: S)` — the SAME functor and key set. So it has
//! a faithful term form and reads like every other entity. The measurement that
//! settles it is that WI-1040 already shipped σ-side dictionaries in that carrier:
//! `value_functor` has been answering `Some(Dictionary)` for one of the two forms
//! since then, so what changed here is that the OTHER form stopped disagreeing.
//!
//! Each test states, MEASURED, what it reports when the change under it is backed
//! out — and which pass either way BY DESIGN.

use smallvec::SmallVec;

use anthill_core::eval::{value_functor, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::Term;
use anthill_core::span::{SourceId, SourceSpan};

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
///  - move `OpRef` into the routed arm: it reports `Some(..)` — a view-only head
///    read as a referent, which is what this file forbids.
///  - drop the `Expr::Spliced` cancellation from the `Node` arm: `node-spliced-op`
///    reports `Some(OpRef)`, laundering the carrier the row above just excluded.
///  - drop the `Node` arm entirely (WI-1024's shape): `node-ref` and `node-apply`
///    report `None` while their term twins report `Some` — one thing, two carriers,
///    two answers.
///
/// The `term-ref` / `symbolref` / `entity` / `term-app` rows pass EITHER WAY BY
/// DESIGN — they are the pre-existing arms, here so "the rewrite is
/// answer-for-answer identical for them" is asserted rather than argued.
#[test]
fn value_functor_answers_by_what_the_head_denotes() {
    let mut interp = crate::common::interp_for(SRC);
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
    let dict = crate::common::dict(&interp, sym, []).into_value();

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
        // An occurrence lowers, so it reads like the other naming carriers
        // (WI-1025) — a bare `Ref` names its symbol and an application its functor,
        // exactly as the `term-ref` / `term-app` rows above.
        ("node-ref", node(Expr::Ref(sym)), Some(sym)),
        ("node-apply", applied_node(sym, string_sym), Some(sym)),
        // WI-1045 — a dictionary DOES have a faithful term form now (the typer
        // emits `Dictionary(subs…, impl: S)` with this very functor and key set),
        // so it reads like the `entity` row above. Not an exception to the file's
        // rule: the rule is "read the head when the carrier lowers", and this one
        // now does.
        ("dictionary", dict.clone(), Some(dict_sym)),
        ("node-spliced-dict", node(Expr::Spliced(dict)), Some(dict_sym)),
        // No faithful term form: the WI-1019 head is a view-only presentation.
        ("opref", Value::OpRef { op: sym, dict: None, named: None }, None),
        // …and the one way an excluded carrier's head could still arrive: an
        // occurrence WRAPPING it. `occ_head` reads through a top-level `Spliced`,
        // so the reader cancels the double wrap the way `Value::node` would have.
        (
            "node-spliced-op",
            node(Expr::Spliced(Value::OpRef { op: sym, dict: None, named: None })),
            None,
        ),
    ];

    // PREMISE for the exclusion rows: their heads really DO present a symbol, so
    // `None` is a DECISION and not an absent shape. Without this the rows would
    // pass for the wrong reason — the WI-1023 lesson about probes that sample an
    // empty population.
    {
        use anthill_core::kb::term_view::{TermView, ViewHead};
        let spliced = node(Expr::Spliced(Value::OpRef { op: sym, dict: None, named: None }));
        assert!(
            matches!(spliced.head(interp.kb()), ViewHead::Functor { functor: Some(_), .. }),
            "premise: a spliced OpRef heads as the OpRef CONSTRUCTOR — the laundering route",
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
/// structural head (WI-1019 gave `OpRef` and the then-`Requirement` carrier
/// theirs) while this reader keeps answering `None` by default. So: any carrier
/// whose head yields a `functor_sym` must be either routed here or one of the
/// deliberate exclusions.
///
/// CONTROL, MEASURED by deleting `"opref"` from `DELIBERATE` below: the test
/// reports it as undeclared. The `dictionary` sample is here on the ROUTED side
/// since WI-1045 — it is what a carrier crossing this line looks like, and it must
/// not read as undeclared either.
#[test]
fn a_carrier_with_a_functor_head_is_routed_or_deliberately_excluded() {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let mut interp = crate::common::interp_for(SRC);
    let sym = box_sym(&mut interp);
    // The carrier deliberately NOT routed: the one with no faithful term form.
    // Anything else with a naming head must be routed.
    const DELIBERATE: &[&str] = &["opref"];
    let samples: Vec<(&str, Value)> = vec![
        ("dictionary", crate::common::dict(&interp, sym, []).into_value()),
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
/// CONTROL, MEASURED: route `OpRef` through `functor_sym` → the handle row returns
/// `Ok(nil)`, a silent empty answer to a type error. The two carrier rows pass
/// EITHER WAY BY DESIGN (both are pre-existing arms); they are here so the
/// end-to-end claim is "one sort, one answer", not one carrier measured alone.
///
/// WI-1045 — the handle row's SUBJECT changed from a dictionary to an `OpRef`,
/// and the claim did not. A dictionary stopped being a runtime handle: it is an
/// entity naming the `Dictionary` sort, so `facts_of` answers that sort's facts
/// exactly as it does for any other entity. `OpRef` is still a handle with no term
/// form, so it is still the carrier this guard is about.
#[test]
fn facts_of_reads_the_sort_through_every_naming_carrier() {
    let mut interp = crate::common::interp_for(SRC);
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
        let heads: Vec<String> = crate::common::list_heads(&list)
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
    let opref = Value::OpRef { op: sym, dict: None, named: None };
    let err = interp
        .call("anthill.reflect.KB.facts_of", &[Value::Unit, opref])
        .expect_err("an OpRef is a type error at a sort slot, not an empty answer");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("Type (entity reference)"),
        "and it is `kb_facts_of`'s own value_functor-None branch, got {msg}",
    );
}
