//! Integration tests for proposal 026.1 Q4 — external-backed stream sources
//! (WI-052). Covers `eval::stream::{ExternalStream, StreamSource::External}`.
//!
//! Acceptance: a 10K-row external scan drains through `splitFirst` to
//! exhaustion and the main `TermStore` size does not grow during the scan.
//! This is the lineage-preservation guarantee from proposal 026.1
//! §"Scale: external-backed KBs".


use anthill_core::eval::Value;
use anthill_core::eval::stream::{ExternalStream, StreamSource};
use anthill_core::intern::Symbol;

use crate::common::interp_for;

/// A row-source that yields `WorkItem` entities from an in-memory vector
/// without ever promoting them into the KB's `TermStore`. Demonstrates the
/// canonical Q4 shape: `Value::Entity` rows constructed inline, surfaced
/// to the resolver via `StreamSource::External`. A production backend
/// (filesystem, SQL cursor, GitHub API) plugs into this same trait — only
/// the row-source differs.
struct WorkItemRowStream {
    rows: std::vec::IntoIter<WorkItemRow>,
    functor: Symbol,
    id_field: Symbol,
    description_field: Symbol,
}

#[derive(Clone)]
struct WorkItemRow {
    id: String,
    description: String,
}

impl ExternalStream for WorkItemRowStream {
    fn next(&mut self) -> Option<Value> {
        let row = self.rows.next()?;
        Some(Value::Entity {
            functor: self.functor,
            pos: Vec::new().into(),
            named: vec![
                (self.id_field, Value::Str(row.id)),
                (self.description_field, Value::Str(row.description)),
            ].into(),
        })
    }
    fn description(&self) -> &str { "WorkItemRowStream[in-memory]" }
}

#[test]
fn q4_external_stream_yields_value_entity_rows() {
    let mut interp = interp_for("namespace test.q4_smoke end\n");

    let functor = interp.kb_mut().intern("WorkItem");
    let id_field = interp.kb_mut().intern("id");
    let description_field = interp.kb_mut().intern("description");

    let rows = vec![
        WorkItemRow { id: "WI-001".into(), description: "first".into() },
        WorkItemRow { id: "WI-002".into(), description: "second".into() },
    ];
    let stream = Box::new(WorkItemRowStream {
        rows: rows.into_iter(),
        functor,
        id_field,
        description_field,
    });

    let handle = interp.alloc_stream(StreamSource::External(stream));
    assert_eq!(interp.stream_arena_live_count(), 1);

    let mut yielded = Vec::new();
    let mut h = handle;
    loop {
        match interp.stream_split_first(&h).expect("split_first") {
            Some((v, rest)) => { yielded.push(v); h = rest; }
            None => break,
        }
    }

    assert_eq!(yielded.len(), 2, "two rows yielded before exhaustion");
    for v in &yielded {
        match v {
            Value::Entity { functor: f, .. } => assert_eq!(*f, functor),
            other => panic!("expected Value::Entity, got {:?}", other),
        }
    }

    drop(h);
    assert_eq!(interp.stream_arena_live_count(), 0, "slot reclaimed after exhaustion");
}

/// Q4 acceptance: scanning 10K external rows must NOT grow the main
/// `TermStore`. Lineage-preserving bindings — Value::Entity rows enter σ
/// via bind_value, never `TermStore::alloc`. Proposal 026.1 §Scale +
/// proposal 007 §11 Two ingestion paths.
#[test]
fn q4_ten_thousand_row_scan_does_not_grow_term_store() {
    const N: usize = 10_000;

    let mut interp = interp_for("namespace test.q4_scale end\n");

    let functor = interp.kb_mut().intern("WorkItem");
    let id_field = interp.kb_mut().intern("id");
    let description_field = interp.kb_mut().intern("description");

    let baseline = interp.kb().term_store_len();

    let rows: Vec<WorkItemRow> = (0..N)
        .map(|i| WorkItemRow {
            id: format!("WI-{i:06}"),
            description: format!("item-{i}"),
        })
        .collect();
    let stream = Box::new(WorkItemRowStream {
        rows: rows.into_iter(),
        functor,
        id_field,
        description_field,
    });

    let mut h = interp.alloc_stream(StreamSource::External(stream));
    let mut count = 0usize;
    loop {
        match interp.stream_split_first(&h).expect("split_first") {
            Some((_v, rest)) => { count += 1; h = rest; }
            None => break,
        }
    }
    drop(h);

    assert_eq!(count, N, "all rows surfaced through splitFirst");

    let after = interp.kb().term_store_len();
    assert_eq!(
        after, baseline,
        "TermStore must not grow during external-stream scan \
         (baseline={baseline}, after={after}, rows={N})"
    );
    assert_eq!(interp.stream_arena_live_count(), 0, "stream slot reclaimed");
}
