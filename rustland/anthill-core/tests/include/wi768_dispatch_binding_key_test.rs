//! WI-768 — a spec-op call on a rule citation DISPATCHES to the provider that matches it.
//!
//! WI-726 and WI-764 taught the typer that a WRITTEN parameterized type and a rule
//! citation of the same relation describe ONE type, even though the two producers spell
//! the slot's key differently: a written `Relation[T = .., E = ..]` keys `T`/`E` BARE (the
//! loader lowers via `reintern(p.last())`), while a relation VALUE from a rule citation
//! keys them CANONICALLY (`anthill.prelude.Relation.T`). DISPATCH was deliberately left on
//! raw symbol identity, so the two subsystems disagreed: the call type-checked and then
//! silently failed to dispatch — `match_candidate_against_goal` missed the key, dropped the
//! provider, and the call was never pinned to it.
//!
//! Nothing about that was loud. Type-checking reported ZERO errors, and at runtime
//! value-directed dispatch still found the impl, so the only visible trace was the missing
//! static pin — which is why this file asserts on the pin rather than on a diagnostic or an
//! evaluated result. The measured symptom, with a second provider in play, was the typer
//! resolving `Unique` to the WRONG impl (the general one) where the written-annotation
//! spelling of the same call resolved to the specific one.
//!
//! The A/B below is the whole point: the two cases are the SAME program apart from where
//! the argument's type comes from — a rule citation vs an operation whose return is
//! written. Before the fix the citation case produced no classification at all and the
//! written case pinned; now both pin to the same impl.

use crate::common::load_kb_with;
use anthill_core::kb::KnowledgeBase;

/// The relation every case cites: schema `(name: String, age: Int64)`.
const REL: &str = r#"
  import anthill.prelude.{String, Int64, Relation, Error}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
"#;

const SCHEMA: &str = "Relation[T = (name: String, age: Int64), E = {Error}]";

/// The `impl_op_sym` of every `PinNow` the typer wrote onto `<ns>.use_it`'s body,
/// rendered as qualified names. Empty means the call was never pinned to an impl.
fn pinned_impls(kb: &KnowledgeBase, ns: &str) -> Vec<String> {
    let use_it = kb
        .try_resolve_symbol(&format!("{ns}.use_it"))
        .unwrap_or_else(|| panic!("{ns}.use_it registered"));
    let body = kb.op_body_node(use_it).expect("use_it has a body");
    let mut out = Vec::new();
    anthill_core::kb::node_occurrence::visit_classifications(body, &mut |_, c| {
        if let anthill_core::kb::typing::CallClass::PinNow { impl_op_sym, .. } = c {
            out.push(kb.qualified_name_of(*impl_op_sym).to_string());
        }
    });
    out
}

/// Build the A/B program. `arg` is the spec-op call's argument; `extra` supplies the
/// helper that `arg` may reference. `provided` is the schema the provider claims.
fn program(ns: &str, provided: &str, arg: &str, extra: &str) -> String {
    format!(
        r#"
namespace {ns}
{REL}
  sort Labelled
    sort T = ?
    operation label(x: T) -> Int64
  end

  sort PersonRelLabel
    provides Labelled[T = {provided}]
    operation label(x: {provided}) -> Int64 = 7
  end

  {extra}
  operation use_it() -> Int64 = Labelled.label({arg})
end
"#
    )
}

/// THE REGRESSION. The argument is a rule citation, so its type carries CANONICAL binding
/// keys while the provider's `provides Labelled[T = Relation[…]]` carries BARE ones. Raw
/// identity missed the pair and dropped `PersonRelLabel` — this asserted list was EMPTY.
#[test]
fn wi768_citation_typed_argument_dispatches_to_its_provider() {
    let src = program("test.wi768cite", SCHEMA, "person_row", "");
    let kb = load_kb_with(&src);
    assert_eq!(
        pinned_impls(&kb, "test.wi768cite"),
        vec!["test.wi768cite.PersonRelLabel.label".to_string()],
        "a spec-op call whose argument is a rule CITATION must dispatch to the provider \
         written for that schema; an empty list is the WI-768 defect — the binding keys \
         are spelled canonically on the value and bare on the provider, and dispatch \
         dropped the candidate on a raw-identity key miss",
    );
}

/// The CONTROL, and the reason the case above is a defect rather than a limitation: the
/// SAME call dispatches when the argument's type comes from a WRITTEN return annotation,
/// whose keys are bare and so matched by raw identity all along. Only the provenance of
/// the argument's type differs between the two.
#[test]
fn wi768_annotation_typed_argument_dispatches_the_same_way() {
    let src = program(
        "test.wi768ann",
        SCHEMA,
        "src()",
        &format!("operation src() -> {SCHEMA} = person_row"),
    );
    let kb = load_kb_with(&src);
    assert_eq!(
        pinned_impls(&kb, "test.wi768ann"),
        vec!["test.wi768ann.PersonRelLabel.label".to_string()],
        "the written-annotation spelling of the same call must still dispatch — this half \
         of the A/B passed before the fix, and pins the claim that the two differ ONLY in \
         where the argument's type came from",
    );
}

/// NON-VACUITY — a guard against FUTURE over-acceptance, not a discriminator of this fix.
///
/// Stated plainly, per the lesson WI-764 recorded: this test also passes with the fix
/// reverted, because before it dispatch rejected EVERY parameterized provider, including
/// the wrong ones. What it pins is the other half of the pair — that finding a binding by
/// LABEL rather than by symbol identity still CHECKS the bound value. A key match that
/// started SKIPPING the slot instead of comparing it would dispatch this happily; it must
/// not, because `name` is a `String`, not an `Int64`.
#[test]
fn wi768_a_provider_for_a_different_schema_is_not_dispatched() {
    let src = program(
        "test.wi768wrong",
        "Relation[T = (name: Int64, age: Int64), E = {Error}]",
        "person_row",
        "",
    );
    let kb = load_kb_with(&src);
    assert!(
        pinned_impls(&kb, "test.wi768wrong").is_empty(),
        "a provider claiming `name: Int64` must not be dispatched for a relation whose \
         `name` is a String — matching a binding key by label must still compare the value \
         behind it",
    );
}
