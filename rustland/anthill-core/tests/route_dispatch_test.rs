//! Integration tests for proposal 007 §11 + 026.1 Q4 Stage B —
//! routing-side wiring. A registered `RouteHandler` surfaces external
//! row sources to the SLD resolver: a goal whose head functor matches a
//! registered handler pulls candidates from the handler's
//! `ExternalStream` in addition to the in-KB discrim-tree results.
//!
//! Acceptance criteria:
//! 1. A query against a routed functor yields solutions for each
//!    matching external row.
//! 2. The main `TermStore` does not grow during the scan
//!    (lineage-preserving bindings — no per-row `TermStore::alloc`).
//! 3. Variable bindings reach the answer substitution as `Value::Entity`
//!    or scalar `Value::*` variants — not as `Value::Term`.

mod common;

use anthill_core::eval::Value;
use anthill_core::eval::stream::ExternalStream;
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use smallvec::SmallVec;

/// In-memory backend yielding three WorkItem rows. Each row is a
/// `Value::Entity { functor, named: [(id, Str), (description, Str)] }`
/// — no TermStore allocation.
struct WorkItemBackend {
    rows: std::vec::IntoIter<(String, String)>,
    functor: Symbol,
    id_field: Symbol,
    description_field: Symbol,
}

impl ExternalStream for WorkItemBackend {
    fn next(&mut self) -> Option<Value> {
        let (id, desc) = self.rows.next()?;
        // Named args sorted canonically by Symbol::index() to match the
        // KB-side `Term::Fn { named_args }` invariant — TermView's
        // discrim-tree walker drives off this order.
        let mut named = vec![
            (self.id_field, Value::Str(id)),
            (self.description_field, Value::Str(desc)),
        ];
        named.sort_by_key(|(s, _)| s.index());
        Some(Value::Entity {
            functor: self.functor,
            pos: Vec::new(),
            named,
        })
    }
    fn description(&self) -> &str { "WorkItemBackend[in-memory]" }
}

#[test]
fn stage_b_routed_goal_yields_external_rows() {
    // Declare a tiny WorkItem sort. The route handler will surface
    // synthetic rows that don't exist in the KB.
    let src = r#"
namespace test.route_dispatch
  sort Demo
    entity WorkItem(id: String, description: String)
  end
end
"#;
    let mut kb = common::load_kb_with(src);

    // Resolve the symbols we need — the entity functor and its field keys.
    let functor = kb.try_resolve_symbol("test.route_dispatch.Demo.WorkItem")
        .expect("WorkItem entity should be loaded");
    // Field keys on a fact head are interned via `reintern` (short names),
    // so the query side must match by interning the same short names.
    let id_field = kb.intern("id");
    let description_field = kb.intern("description");

    // Register the route handler for the WorkItem functor.
    let rows = vec![
        ("WI-001".to_string(), "first".to_string()),
        ("WI-002".to_string(), "second".to_string()),
        ("WI-003".to_string(), "third".to_string()),
    ];
    let rows_clone = rows.clone();
    kb.register_route_handler(functor, move |_kb: &_, _pattern| {
        Box::new(WorkItemBackend {
            rows: rows_clone.clone().into_iter(),
            functor,
            id_field,
            description_field,
        }) as Box<dyn ExternalStream>
    });

    // Build the goal pattern: WorkItem(id: ?id, description: ?desc).
    let id_var_name = kb.intern("id_v");
    let desc_var_name = kb.intern("desc_v");
    let id_var = kb.fresh_var(id_var_name);
    let desc_var = kb.fresh_var(desc_var_name);
    let id_var_term = kb.alloc(Term::Var(Var::Global(id_var)));
    let desc_var_term = kb.alloc(Term::Var(Var::Global(desc_var)));

    // Named args must be sorted canonically by symbol index — match the
    // KB's `Term::Fn { named_args }` invariant.
    let mut named: Vec<(Symbol, anthill_core::kb::term::TermId)> = vec![
        (id_field, id_var_term),
        (description_field, desc_var_term),
    ];
    named.sort_by_key(|(s, _)| s.index());
    let named_args: SmallVec<[(Symbol, anthill_core::kb::term::TermId); 2]> =
        SmallVec::from_vec(named);
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args,
    });

    // Snapshot the TermStore before the scan.
    let baseline = kb.term_store_len();

    // Resolve. Each external row should match the variable-headed pattern
    // and yield a solution.
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        solutions.len(),
        3,
        "expected one solution per external row (got {})",
        solutions.len()
    );

    // Each solution's bindings must surface the row's String values
    // directly as `Value::Str`, not via a hash-consed `Value::Term`.
    let mut ids: Vec<String> = solutions.iter()
        .filter_map(|s| s.subst.resolve_as_value(id_var).cloned())
        .filter_map(|v| match v {
            Value::Str(s) => Some(s),
            _ => None,
        })
        .collect();
    ids.sort();
    assert_eq!(ids, vec!["WI-001", "WI-002", "WI-003"], "id bindings reach σ as Value::Str");

    // Lineage-preservation: the bind-side flowed through bind_value,
    // never bind_term. The TermStore should be unchanged from baseline.
    let after = kb.term_store_len();
    assert_eq!(
        after, baseline,
        "TermStore must not grow during routed-goal scan \
         (baseline={baseline}, after={after})"
    );
}

