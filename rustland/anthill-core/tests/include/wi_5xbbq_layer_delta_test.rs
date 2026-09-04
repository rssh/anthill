//! WI-5XBBQ — THE DELTA OF A SCOPED LOAD, and the provenance that makes it usable.
//!
//! WI-SPGBP made a load DISCARDABLE and said what it does not buy: "A layer stops the
//! candidate RETARGETING a trusted symbol … It does NOT stop the candidate adding a
//! CLAUSE under that same trusted symbol." These are the two readers that make that
//! question askable from anthill — what the layer INTRODUCED, and what its source text
//! ASSERTED — plus the clause-origin bit without which the second answer is unusable.
//!
//! The policy built on them is `examples/guardians/lib/gate.anthill`; `guardians_test`
//! drives it end to end. These rows pin the readers themselves.

use anthill_core::eval::value::Value;

use crate::common;

/// A candidate that declares a sort, mints a predicate through a RULE HEAD, writes one
/// `fact` and one `rule`, and — the case the mint mark cannot see — REDECLARES a name
/// the base already owns.
const CANDIDATE: &str = r#"
namespace xbbq.cand
  import anthill.prelude.{Int64}
  sort Widget
    entity gadget(id: Int64)
  end

  fact gadget(id: 7)

  rule wide(?i)
    :- gadget(id: ?i)
end

namespace xbbq.base
  import anthill.prelude.{Int64}
  sort Thing
    entity thing(id: Int64)
  end
end
"#;

/// The BASE already owns `xbbq.base.Thing`, so the candidate's second namespace above
/// is a REDECLARATION rather than a definition.
const BASE: &str = r#"
namespace xbbq.base
  import anthill.prelude.{Int64}
  import anthill.prelude.Option.{some}
  sort Thing
    entity thing(id: Int64)
  end
end
"#;

fn call_loaded(interp: &mut anthill_core::eval::Interpreter, src: &str) -> Value {
    let list = interp
        .build_list_value(vec![Value::Str(src.to_string())], &[])
        .expect("build List[String]");
    interp
        .call("anthill.reflect.KB.loaded", &[list])
        .expect("KB.loaded")
}

/// `(qualified name, minted, declared)` for every row `KB.layer_symbols` answers.
fn symbols(interp: &mut anthill_core::eval::Interpreter, layer: &Value) -> Vec<(String, bool, bool)> {
    let rows = interp
        .call("anthill.reflect.KB.layer_symbols", &[layer.clone()])
        .expect("layer_symbols");
    list_items(interp, &rows)
        .into_iter()
        .map(|r| {
            let sym = interp
                .kb()
                .value_symbol(&field(interp, &r, "symbol"))
                .expect("a LayerSymbol carries a symbol");
            (
                interp.kb().qualified_name_of(sym).to_string(),
                as_bool(&field(interp, &r, "minted")),
                as_bool(&field(interp, &r, "declared")),
            )
        })
        .collect()
}

/// `(head functor's qualified name, bodied)` for every row `KB.layer_clauses` answers.
///
/// The functor is an `Option`: a DENIAL (`rule ⊥ :- …`) heads at the kernel's bottom,
/// which interns no symbol, so `None` is a row this reader must be able to produce.
fn clauses(
    interp: &mut anthill_core::eval::Interpreter,
    layer: &Value,
) -> Vec<(Option<String>, bool)> {
    let rows = interp
        .call("anthill.reflect.KB.layer_clauses", &[layer.clone()])
        .expect("layer_clauses");
    list_items(interp, &rows)
        .into_iter()
        .map(|r| {
            let opt = field(interp, &r, "functor");
            let name = match &opt {
                Value::Entity { functor, .. }
                    if interp.kb().qualified_name_of(*functor).ends_with("Option.none") =>
                {
                    None
                }
                _ => {
                    let inner = field(interp, &opt, "value");
                    let sym = interp
                        .kb()
                        .value_symbol(&inner)
                        .expect("a `some` functor carries a Symbol");
                    Some(interp.kb().qualified_name_of(sym).to_string())
                }
            };
            (name, as_bool(&field(interp, &r, "bodied")))
        })
        .collect()
}

fn as_bool(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        other => panic!("expected a Bool, got {other:?}"),
    }
}

fn field(interp: &anthill_core::eval::Interpreter, v: &Value, name: &str) -> Value {
    match v {
        Value::Entity { named, .. } => named
            .iter()
            .find(|(s, _)| interp.kb().local_name_of(*s) == name)
            .unwrap_or_else(|| panic!("no `{name}` in {v:?}"))
            .1
            .clone(),
        other => panic!("not an entity: {other:?}"),
    }
}

fn list_items(interp: &anthill_core::eval::Interpreter, v: &Value) -> Vec<Value> {
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { functor, .. } = &cur {
        if !interp.kb().qualified_name_of(*functor).ends_with("List.cons") {
            break;
        }
        out.push(field(interp, &cur, "head"));
        cur = field(interp, &cur, "tail");
    }
    out
}

/// WI-5XBBQ — the DEFINITION half, and both of its flags.
///
/// WHAT FAILS WHEN BACKED OUT: drop `declared` (leaving only the mint high-water mark)
/// and the redeclaration assertion reds — the base's `Thing` is re-entered rather than
/// minted, so nothing above the mark names it.
#[test]
fn xbbq_layer_symbols_reports_what_the_layer_minted_and_what_it_redeclared() {
    let mut interp = common::interp_for(BASE);
    let layer = call_loaded(&mut interp, CANDIDATE);
    let rows = symbols(&mut interp, &layer);

    let row = |qn: &str| -> (bool, bool) {
        rows.iter()
            .find(|(n, _, _)| n == qn)
            .map(|(_, m, d)| (*m, *d))
            .unwrap_or_else(|| panic!("{qn} is not in the delta; have: {rows:#?}"))
    };

    // MINTED AND DECLARED — an ordinary new declaration.
    assert_eq!(row("xbbq.cand.Widget"), (true, true));
    assert_eq!(row("xbbq.cand.Widget.gadget"), (true, true));

    // MINTED, NOT DECLARED — §8.6: a rule head is RESOLVED, not declared, so a
    // predicate a `rule` brought into existence has no declaration-ledger entry. The
    // containment rule needs it all the same, since its own clauses head there.
    assert_eq!(row("xbbq.cand.wide"), (true, false));

    // DECLARED, NOT MINTED — THE THIRD CHANNEL. The base already owns
    // `xbbq.base.Thing`, so the candidate's redeclaration re-enters the SAME symbol
    // and the high-water mark never sees it.
    assert_eq!(row("xbbq.base.Thing"), (false, true));
}

/// WI-5XBBQ — the ASSERTION half, and the provenance filter that makes it mean
/// "what the source text wrote".
///
/// WHAT FAILS WHEN BACKED OUT: stop marking a `fact` / `rule` item `ClauseOrigin::Source`
/// and both positive assertions red; remove the `origin == Source` filter and the
/// negative one reds, because the loader's own `SortInfo` / `EntityInfo` rows for
/// `Widget` are `ClauseKind::Fact` too and would come back as the candidate's.
#[test]
fn xbbq_layer_clauses_reports_the_source_text_and_not_the_loaders_own_rows() {
    let mut interp = common::interp_for(BASE);
    let layer = call_loaded(&mut interp, CANDIDATE);
    let rows = clauses(&mut interp, &layer);

    assert!(
        rows.contains(&(Some("xbbq.cand.Widget.gadget".to_string()), false)),
        "the `fact` the source wrote must be reported, unbodied; got {rows:#?}"
    );
    assert!(
        rows.contains(&(Some("xbbq.cand.wide".to_string()), true)),
        "the `rule` the source wrote must be reported, bodied; got {rows:#?}"
    );
    // The candidate declares a sort with an entity, so the loader banked `SortInfo`,
    // `EntityInfo` and `FieldInfo` rows about it in the SAME clause range. None is the
    // candidate's, and telling them apart is the whole of `ClauseOrigin`.
    assert!(
        rows.iter()
            .all(|(n, _)| !n.as_deref().is_some_and(|n| n.starts_with("anthill.reflect."))),
        "a loader-emitted metadata row must not read as source-written; got {rows:#?}"
    );
    assert_eq!(rows.len(), 2, "exactly the two clauses the source wrote: {rows:#?}");
}

/// WI-5XBBQ — the clause form with NO head functor, which is why `LayerClause.functor`
/// is an `Option` rather than a `Symbol`.
///
/// A DENIAL (`rule ⊥ :- …`) heads at the kernel's bottom, and that interns no symbol.
/// Reporting it as `None` is what lets a policy refuse it; the reader this replaced
/// raised an `Internal` error instead, which a checker had no way to turn into a
/// verdict — found by review.
///
/// WHAT FAILS WHEN BACKED OUT: drop the `mark_source_clause` call from `load_rule`'s
/// head loop and this answers zero rows.
#[test]
fn xbbq_a_denial_is_reported_with_no_functor_rather_than_refused() {
    let mut interp = common::interp_for(BASE);
    let layer = call_loaded(
        &mut interp,
        "namespace xbbq.deny\n  rule ⊥ :- xbbq.base.Thing.thing(id: ?i)\nend\n",
    );
    let rows = clauses(&mut interp, &layer);
    assert_eq!(
        rows,
        vec![(None, true)],
        "a denial must be reported as one bodied clause with no functor; got {rows:#?}"
    );
}

/// WI-5XBBQ — the provenance bit itself, read at the KB rather than through the delta.
///
/// `ClauseKind` cannot answer this — its `Fact` variant covers "a `fact` — INCLUDING
/// loader-synthesized metadata facts" — so a clause store holding both is
/// indistinguishable without it. Asserted on the two rows a single `sort … entity …`
/// plus one `fact` produces: the program's own clause, and the `EntityInfo` row the
/// loader banked about the very same declaration.
///
/// WHAT FAILS WHEN BACKED OUT: drop `mark_source_clause` from `load_fact` and the first
/// assertion reds; mark the loader's emissions `Source` and the second does.
#[test]
fn xbbq_clause_origin_separates_the_source_text_from_the_loaders_emissions() {
    use anthill_core::kb::ClauseOrigin;

    let kb = common::load_kb_with(
        r#"
namespace xbbq.prov
  import anthill.prelude.{Int64}
  sort Widget
    entity gadget(id: Int64)
  end

  fact gadget(id: 7)
end
"#,
    );

    let origins = |qn: &str| -> Vec<ClauseOrigin> {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("{qn} must be in the KB"));
        kb.rules_by_functor(sym)
            .into_iter()
            .map(|id| kb.clause_origin(id))
            .collect()
    };

    assert!(
        origins("xbbq.prov.Widget.gadget").contains(&ClauseOrigin::Source),
        "the `fact` the source wrote must read as Source"
    );
    let emitted = origins("anthill.reflect.EntityInfo");
    assert!(!emitted.is_empty(), "the loader banks EntityInfo rows");
    assert!(
        emitted.iter().all(|o| *o == ClauseOrigin::Derived),
        "every loader-emitted metadata row must read as Derived; got {emitted:?}"
    );
}

/// WI-5XBBQ — a delta is a question about a LAYER, and the two ways of not having one
/// are refused rather than answered.
///
/// The empty list is the one wrong answer available here: it says "this candidate
/// contributed nothing", which is precisely what a forged candidate would like the
/// checker to believe.
#[test]
fn xbbq_a_delta_is_refused_for_the_ambient_kb_and_for_a_shadowed_layer() {
    let mut interp = common::interp_for(BASE);

    let ambient = interp.call("anthill.reflect.KB.kb", &[]).expect("kb()");
    let e = interp
        .call("anthill.reflect.KB.layer_symbols", &[ambient])
        .expect_err("the ambient KB has no delta");
    assert!(
        format!("{e:?}").contains("names no layer"),
        "the ambient refusal must say the argument names no layer; got {e:?}"
    );

    // An OUTER layer while an inner one is applied: its marks would be measured
    // against a knowledge base the inner layer has already changed.
    let outer = call_loaded(&mut interp, CANDIDATE);
    let _inner = call_loaded(
        &mut interp,
        "namespace xbbq.inner\n  sort Extra\n    entity extra\n  end\nend\n",
    );
    let e = interp
        .call("anthill.reflect.KB.layer_clauses", &[outer])
        .expect_err("an outer layer's delta must be refused while an inner one is applied");
    assert!(
        format!("{e:?}").contains("not the innermost"),
        "the refusal must name the shadowing; got {e:?}"
    );
}
