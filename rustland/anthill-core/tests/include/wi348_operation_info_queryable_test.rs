//! WI-348 — the driving consumer, end-to-end through a real loaded op.
//!
//! The WI's thesis: `OperationInfo` must be SLD-queryable AND it carries
//! `denoted` (an effect `Modify[c]`), so it must be a *value fact* (a
//! `Value::Node`-carrying, indexed, queryable head). The Phase A/B substrate
//! tests in `kb/mod.rs` prove this for a *synthetic* `f(denoted(value: Ref(c)))`
//! head. These tests prove it for the actual consumer: an operation whose
//! effects clause is `Modify[c]`, whose `OperationInfo` the loader therefore
//! builds as a value fact (`assert_fact_value`, the `else` branch of
//! `load_operation`).
//!
//! Two claims:
//!   1. the value fact is SLD-queryable — the discrimination tree indexes it,
//!      an `OperationInfo(...)` goal resolves against it, and a query var bound
//!      to one of its named args is extracted carrier-faithfully from the
//!      `Value::Entity` head;
//!   2. the `Modify[c]` effect rides *in* the fact (no `op_effects` side-table)
//!      and reads back through the shared `op_info` funnel as a `Value::Node`
//!      with occurrence identity intact — the WI-348 payoff, via a real op.

use anthill_core::eval::Value;
use anthill_core::kb::op_info;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::intern::Symbol;
use smallvec::SmallVec;

use crate::common::load_kb_with;

/// A single operation whose `effects Modify[c]` forces its `OperationInfo` to be
/// a value fact (the `Modify[c]` label is a `Value::Node`, which a hash-consed
/// term cannot hold). Mirrors the `wi205_cell_test` ops known to load + type.
const SRC: &str = r#"
namespace test.wi348_op_query
  import anthill.prelude.{Int64, Cell, Unit}

  operation overwrite(c: Cell, n: Int64) -> Unit effects Modify[c] = Cell.set(c, n)
end
"#;

const OP_QN: &str = "test.wi348_op_query.overwrite";

/// The full named-arg key set of an `OperationInfo` fact (the single source of
/// truth in `load_operation`). A discrimination-tree query must match the fact's
/// total arity, so a query goal carries all of these — `name` ground, the rest
/// fresh vars — never a partial `OperationInfo(name: ?n)` (which would key on a
/// different arity and miss the fact). WI-087 added `meta`.
const OP_INFO_FIELDS: [&str; 8] =
    ["name", "params", "return_type", "effects", "requires", "ensures", "type_params", "meta"];

fn op_sym(kb: &KnowledgeBase) -> Symbol {
    kb.try_resolve_symbol(OP_QN).expect("overwrite op symbol after load")
}

/// Find the `OperationInfo` fact RuleId whose `name` field refers to `op` —
/// the same by-functor + `head_name_ref` walk `lookup_operation_info` uses.
fn operation_info_rid(kb: &KnowledgeBase, op: Symbol) -> RuleId {
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")
        .expect("OperationInfo schema symbol");
    kb.rules_by_functor(op_info_sym)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .find(|rid| op_info::head_name_ref(kb, kb.rule_head_value(*rid)) == Some(op))
        .expect("OperationInfo fact for overwrite")
}

#[test]
fn modify_op_operation_info_is_a_sld_queryable_value_fact() {
    let mut kb = load_kb_with(SRC);
    let op = op_sym(&kb);

    // (a) The head is a value fact — `Value::Entity`, not a hash-consed
    // `Value::Term(Fn)` — because the `Modify[c]` effect is a `Value::Node`.
    let rid = operation_info_rid(&kb, op);
    assert!(
        matches!(kb.rule_head_value(rid), Value::Entity { .. }),
        "an op with a `Modify[c]` effect must store its OperationInfo as a value \
         fact (Value::Entity head), got {:?}",
        kb.rule_head_value(rid),
    );

    // (b) Build a full-arity goal: `OperationInfo(name: Ref(op), effects: ?e, …)`
    // with the remaining fields fresh vars. `name` ground isolates this op's fact
    // among all OperationInfo facts (stdlib included); `effects: ?e` extracts the
    // denoted-bearing field from the value-fact head.
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo").unwrap();
    let name_ref = kb.alloc(Term::Ref(op));
    let e_sym = kb.intern("e");
    let effects_var = kb.fresh_var(e_sym);
    let effects_var_t = kb.alloc(Term::Var(Var::Global(effects_var)));

    let named_args: SmallVec<[(Symbol, TermId); 2]> = OP_INFO_FIELDS
        .iter()
        .map(|field| {
            let key = kb.intern(field);
            let val = match *field {
                "name" => name_ref,
                "effects" => effects_var_t,
                _ => {
                    let v = kb.fresh_var(key);
                    kb.alloc(Term::Var(Var::Global(v)))
                }
            };
            (key, val)
        })
        .collect();
    let goal = kb.alloc(Term::Fn {
        functor: op_info_sym,
        pos_args: SmallVec::new(),
        named_args,
    });

    // (c) Discrimination-tree match resolves the value fact and binds `?e` to its
    // effects field carrier-faithfully (the `extract_value_at_path` Named arm).
    let results = kb.query(goal);
    let matched: Vec<_> = results.iter().filter(|(r, _)| *r == rid).collect();
    assert_eq!(
        matched.len(), 1,
        "the OperationInfo value fact must be found exactly once by the goal",
    );
    assert!(
        matched[0].1.resolve_as_value(effects_var).is_some(),
        "`?e` must bind to the value fact's effects field — carrier-faithful \
         binding extraction from a Value::Entity head",
    );

    // (d) The full SLD entry point (`resolve`) — what `:- OperationInfo(…)` runs —
    // also finds it; the value fact flows through the resolver, not just the tree.
    let config = ResolveConfig { max_solutions: 1024, ..ResolveConfig::default() };
    let solutions = kb.resolve(&[goal], &config);
    assert!(
        !solutions.is_empty(),
        "a Node-bearing OperationInfo value fact must be SLD-queryable via resolve",
    );
}

#[test]
fn modify_op_effect_label_rides_in_fact_as_node() {
    let kb = load_kb_with(SRC);
    let op = op_sym(&kb);

    // The shared funnel every consumer (typer, eval, reflect `KB.operations`)
    // uses. With `op_effects` collapsed into the fact (WI-348 payoff), the
    // labels come straight from the fact head — and a `Modify[c]` label comes
    // back as a `Value::Node`, occurrence intact, never re-grounded to a term.
    let rec = op_info::lookup_operation_info(&kb, op)
        .expect("lookup_operation_info for overwrite");

    let node_modify = rec.effects.iter().any(|eff| match eff {
        Value::Node(_) => matches!(
            eff.head(&kb),
            ViewHead::Functor { functor: Some(f), .. }
                if kb.resolve_sym(f).rsplit('.').next() == Some("Modify")
        ),
        _ => false,
    });
    assert!(
        node_modify,
        "the `Modify[c]` effect must ride in the OperationInfo fact and read back \
         as a Value::Node headed by `Modify`; got effects: {:?}",
        rec.effects,
    );
}
