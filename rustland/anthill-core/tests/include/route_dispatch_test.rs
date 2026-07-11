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


use anthill_core::eval::Value;
use anthill_core::eval::stream::ExternalStream;
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var, VarId};
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
            pos: Vec::new().into(),
            named: named.into(),
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
    let mut kb = crate::common::load_kb_with(src);

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

/// WI-649: a route handler that returns a row whose `id` field references
/// the goal's OWN query var inside a nested entity — the one constructible
/// route to a cyclic external-row bind (`?id ↦ wrap(?id)`). External rows
/// enter σ through the resolver's fact fast-path, which binds a non-`Term`
/// carrier WITHOUT the unifier's occurs-check. Since WI-629 `reify_value`
/// recurses into `Value::Entity` children, a cyclic σ that reached
/// reification overflowed the host stack instead of failing loudly.
///
/// The test's DIRECTLY-OBSERVED property is that the WI-649 occurs-check at
/// that bind site drops the cyclic candidate as an occurs-failure (no finite
/// term satisfies `?id = wrap(?id)`), so the query yields ZERO solutions. That
/// drop is the *source-level* prevention — it stops the cyclic σ from ever
/// forming, which is what would otherwise overflow the deep reification. NB
/// `kb.resolve` does not itself deep-reify the answer, so the overflow is
/// prevented here rather than reproduced-then-bounded; the emit-witness
/// (`emits`) makes the zero-solution assertion non-vacuous (see below).
struct CyclicRowBackend {
    functor: Symbol,
    wrap_functor: Symbol,
    id_field: Symbol,
    description_field: Symbol,
    /// The goal's query var — the row references it to close the cycle.
    id_var: VarId,
    /// Shared with the test: bumped on emit so the test can prove the cyclic
    /// row was actually produced and matched (else `0 solutions` could mean
    /// "candidate dropped" OR "row never emitted" — a vacuous pass).
    emits: std::rc::Rc<std::cell::Cell<u32>>,
    emitted: bool,
}

impl ExternalStream for CyclicRowBackend {
    fn next(&mut self) -> Option<Value> {
        if self.emitted {
            return None;
        }
        self.emitted = true;
        self.emits.set(self.emits.get() + 1);
        // `id` carries an entity that mentions the goal's own query var, so
        // the discrim match binds `?id ↦ wrap(?id)` — a cyclic σ.
        let cyclic = Value::Entity {
            functor: self.wrap_functor,
            pos: vec![Value::Var(Var::Global(self.id_var))].into(),
            named: Vec::new().into(),
        };
        let mut named = vec![
            (self.id_field, cyclic),
            (self.description_field, Value::Str("x".to_string())),
        ];
        named.sort_by_key(|(s, _)| s.index());
        Some(Value::Entity {
            functor: self.functor,
            pos: Vec::new().into(),
            named: named.into(),
        })
    }
    fn description(&self) -> &str { "CyclicRowBackend[WI-649]" }
}

#[test]
fn wi649_cyclic_external_row_bind_is_dropped_not_overflowed() {
    let src = r#"
namespace test.route_dispatch_cyclic
  sort Demo
    entity WorkItem(id: String, description: String)
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);

    let functor = kb.try_resolve_symbol("test.route_dispatch_cyclic.Demo.WorkItem")
        .expect("WorkItem entity should be loaded");
    let id_field = kb.intern("id");
    let description_field = kb.intern("description");
    let wrap_functor = kb.intern("wrap");

    // Allocate the goal's query var FIRST so the backend can reference it.
    let id_var_name = kb.intern("id_v");
    let desc_var_name = kb.intern("desc_v");
    let id_var = kb.fresh_var(id_var_name);
    let desc_var = kb.fresh_var(desc_var_name);

    // Emit-witness shared between the handler's backend and this test.
    let emits = std::rc::Rc::new(std::cell::Cell::new(0u32));
    let emits_for_handler = emits.clone();
    kb.register_route_handler(functor, move |_kb: &_, _pattern| {
        Box::new(CyclicRowBackend {
            functor,
            wrap_functor,
            id_field,
            description_field,
            id_var,
            emits: emits_for_handler.clone(),
            emitted: false,
        }) as Box<dyn ExternalStream>
    });

    // Goal: WorkItem(id: ?id, description: ?desc).
    let id_var_term = kb.alloc(Term::Var(Var::Global(id_var)));
    let desc_var_term = kb.alloc(Term::Var(Var::Global(desc_var)));
    let mut named: Vec<(Symbol, anthill_core::kb::term::TermId)> = vec![
        (id_field, id_var_term),
        (description_field, desc_var_term),
    ];
    named.sort_by_key(|(s, _)| s.index());
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_vec(named),
    });

    // The single emitted row binds `?id ↦ wrap(?id)`, a cyclic σ. The
    // occurs-check drops it: zero solutions, and — the point of the ticket —
    // no stack overflow. (Pre-WI-649 this bound the cycle into σ.)
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    // Non-vacuity: the cyclic row must actually have been emitted and reached
    // matching, so `0 solutions` reflects the occurs-check DROP — not a route
    // that was never consulted or a match that silently failed.
    assert!(
        emits.get() >= 1,
        "cyclic row must be emitted so the zero-solution assertion is not vacuous (emits={})",
        emits.get()
    );
    assert_eq!(
        solutions.len(),
        0,
        "cyclic external-row bind must be dropped as an occurs-failure (got {} solution(s))",
        solutions.len()
    );
}

