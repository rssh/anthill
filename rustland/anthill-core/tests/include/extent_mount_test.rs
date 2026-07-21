//! WI-797 — the `ExtentSource` mount wired into resolution and load
//! (proposal 057 §"Mounts", successor to the retired `RouteHandler`).
//!
//! A functor owned by a mounted `ExtentSource` (`kb.extents`) has its reads
//! delegated to the source's `query`: the goal's ground argument slots are
//! pushed down as a `QueryPattern`, and the returned rows resolve on the same
//! candidate path as resident rules — entering σ as raw `Value`s (no
//! `TermStore` allocation). Acceptance:
//! 1. an all-free goal over a mounted, seeded `InMemoryExtentSource` enumerates
//!    every seeded row (as `Value::*`, not `Value::Term`);
//! 2. a ground-keyed goal pushes the key down and yields exactly the match;
//! 3. a mounted goal interleaves correctly with a resident conjunct for another
//!    functor (the resident binding grounds the mounted key → by-id pushdown);
//! 4. a source-file `fact` for an owned functor is refused at load; and
//! 5. registering an owner over a functor that already has resident facts is
//!    refused (the load-then-mount complement).

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::extent::{ArgKey, ExtentRegError, InMemoryExtentSource};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Literal, Term, TermId, Var, VarId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

/// Read a solved variable as an `i64` regardless of carrier: a mounted row binds
/// it as a raw `Value::Int`, a resident fact as a hash-consed `Value::Term{Int}`.
fn sol_int(kb: &KnowledgeBase, sol: &Solution, var: VarId) -> Option<i64> {
    match sol.subst.resolve_as_value(var)? {
        Value::Int(n) => Some(*n),
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Const(Literal::Int(n)) => Some(*n),
            _ => None,
        },
        _ => None,
    }
}

const BASE: &str = r#"
namespace test.extent
  sort Demo
    entity WorkItem(id: Int64, description: String)
    entity Tag(id: Int64)
  end
end
"#;

/// The mounted functor's qualified name (its `owned()` registration key).
const WORKITEM_QN: &str = "test.extent.Demo.WorkItem";

/// A `WorkItem(id: <n>, description: <s>)` row as a raw `Value::Entity` — the
/// shape `InMemoryExtentSource` seeds and the resolver matches, with named args
/// in canonical symbol order (as the KB's `Term::Fn { named_args }` invariant).
fn workitem_row(functor: Symbol, id_field: Symbol, desc_field: Symbol, id: i64, desc: &str) -> Value {
    let mut named = vec![
        (id_field, Value::Int(id)),
        (desc_field, Value::Str(desc.to_string())),
    ];
    named.sort_by_key(|(s, _)| s.index());
    Value::Entity { functor, pos: [].into(), named: named.into() }
}

/// Load `BASE` into a fresh KB and return `(kb, workitem_functor, id_field,
/// desc_field)`.
fn kb_with_base() -> (KnowledgeBase, Symbol, Symbol, Symbol) {
    let mut kb = crate::common::load_kb_with(BASE);
    let functor = kb
        .try_resolve_symbol(WORKITEM_QN)
        .expect("WorkItem entity loaded");
    let id_field = kb.intern("id");
    let desc_field = kb.intern("description");
    (kb, functor, id_field, desc_field)
}

/// Seed + mount an `InMemoryExtentSource` for `WorkItem`, keyed by `id`.
fn mount_workitems(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    id_field: Symbol,
    desc_field: Symbol,
    rows: &[(i64, &str)],
) {
    let rows: Vec<Value> = rows
        .iter()
        .map(|(id, desc)| workitem_row(functor, id_field, desc_field, *id, desc))
        .collect();
    let src = InMemoryExtentSource::new(kb, WORKITEM_QN, ArgKey::Named(id_field), rows)
        .expect("well-formed seed");
    kb.register_extent_owner(Box::new(src))
        .expect("register mounted WorkItem source");
}

/// A goal `WorkItem(id: <id_arg>, description: ?desc)` as a `TermId`, returning
/// the goal plus the `?desc` var id. `id_arg` is either a ground literal or a
/// fresh var, so one builder serves both the enumeration and by-id cases.
fn workitem_goal(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    id_field: Symbol,
    desc_field: Symbol,
    id_arg: TermId,
) -> (TermId, anthill_core::kb::term::VarId) {
    let desc_name = kb.intern("desc_q");
    let desc_var = kb.fresh_var(desc_name);
    let desc_term = kb.alloc(Term::Var(Var::Global(desc_var)));
    let mut named: Vec<(Symbol, TermId)> = vec![(id_field, id_arg), (desc_field, desc_term)];
    named.sort_by_key(|(s, _)| s.index());
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_vec(named),
    });
    (goal, desc_var)
}

// ── (1) enumeration ────────────────────────────────────────────

#[test]
fn all_free_goal_enumerates_every_seeded_row() {
    let (mut kb, functor, id_field, desc_field) = kb_with_base();
    mount_workitems(&mut kb, functor, id_field, desc_field, &[(1, "first"), (2, "second"), (3, "third")]);

    let id_name = kb.intern("id_q");
    let id_var = kb.fresh_var(id_name);
    let id_term = kb.alloc(Term::Var(Var::Global(id_var)));
    let (goal, desc_var) = workitem_goal(&mut kb, functor, id_field, desc_field, id_term);

    // Baseline AFTER goal construction — the invariant is that the *scan* interns
    // nothing (rows enter σ via `bind_value`), not that building the goal is free.
    let baseline = kb.term_store_len();
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(solutions.len(), 3, "one solution per seeded row");

    // Bindings surface as raw `Value::*` (no hash-consed `Value::Term`).
    let mut ids: Vec<i64> = solutions
        .iter()
        .filter_map(|s| match s.subst.resolve_as_value(id_var) {
            Some(Value::Int(n)) => Some(*n),
            _ => None,
        })
        .collect();
    ids.sort();
    assert_eq!(ids, vec![1, 2, 3], "each id reaches σ as a raw Value::Int");

    let mut descs: Vec<String> = solutions
        .iter()
        .filter_map(|s| match s.subst.resolve_as_value(desc_var) {
            Some(Value::Str(s)) => Some(s.clone()),
            _ => None,
        })
        .collect();
    descs.sort();
    assert_eq!(descs, vec!["first", "second", "third"]);

    // Lineage-preserving: extent rows bind through `bind_value`, never interning.
    assert_eq!(kb.term_store_len(), baseline, "TermStore must not grow during the mounted scan");
}

// ── (2) by-id pushdown ─────────────────────────────────────────

#[test]
fn ground_key_goal_pushes_down_and_yields_the_match() {
    let (mut kb, functor, id_field, desc_field) = kb_with_base();
    mount_workitems(&mut kb, functor, id_field, desc_field, &[(1, "first"), (2, "second"), (3, "third")]);

    // WorkItem(id: 2, description: ?desc) — id is ground → the by-id mode.
    let two = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(2)));
    let (goal, desc_var) = workitem_goal(&mut kb, functor, id_field, desc_field, two);

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(solutions.len(), 1, "exactly the id=2 row");
    match solutions[0].subst.resolve_as_value(desc_var) {
        Some(Value::Str(s)) => assert_eq!(s, "second"),
        other => panic!("expected Value::Str(\"second\"), got {other:?}"),
    }
}

// ── (3) interleaving with a resident conjunct ──────────────────

#[test]
fn mounted_goal_interleaves_with_resident_conjunct() {
    // `Tag` is resident (facts for 1, 2); `WorkItem` is mounted (rows 1, 2, 3).
    // Goal `Tag(id: ?x), WorkItem(id: ?x, description: ?d)`: the resident Tag
    // grounds ?x, which the mounted WorkItem goal pushes down as a by-id query.
    // Answers are the ids present in BOTH → {1, 2}.
    let src = r#"
namespace test.extent
  sort Demo
    entity WorkItem(id: Int64, description: String)
    entity Tag(id: Int64)
  end

  fact Tag(id: 1)
  fact Tag(id: 2)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let functor = kb.try_resolve_symbol(WORKITEM_QN).expect("WorkItem loaded");
    let tag = kb.try_resolve_symbol("test.extent.Demo.Tag").expect("Tag loaded");
    let id_field = kb.intern("id");
    let desc_field = kb.intern("description");
    mount_workitems(&mut kb, functor, id_field, desc_field, &[(1, "first"), (2, "second"), (3, "third")]);

    // Shared ?x across both conjuncts.
    let x_name = kb.intern("x_q");
    let x_var = kb.fresh_var(x_name);
    let x_term = kb.alloc(Term::Var(Var::Global(x_var)));
    let tag_goal = kb.alloc(Term::Fn {
        functor: tag,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_vec(vec![(id_field, x_term)]),
    });
    let (wi_goal, _desc_var) = workitem_goal(&mut kb, functor, id_field, desc_field, x_term);

    let solutions = kb.resolve(&[tag_goal, wi_goal], &ResolveConfig::default());
    let mut xs: Vec<i64> = solutions.iter().filter_map(|s| sol_int(&kb, s, x_var)).collect();
    xs.sort();
    assert_eq!(xs, vec![1, 2], "only ids present in both the resident Tag facts and the mounted rows");
}

// ── (4) loader refusal: mount-then-load ────────────────────────

#[test]
fn source_fact_for_owned_functor_refused_at_load() {
    // Phase 1: load stdlib + BASE (declares WorkItem, no facts).
    let stdlib = crate::common::collect_stdlib_and_rust_bindings();
    let stdlib_parsed: Vec<_> = stdlib
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).expect("parse stdlib"))
        .collect();
    let base_parsed = parse::parse(BASE).expect("parse base");
    let mut refs: Vec<&_> = stdlib_parsed.iter().collect();
    refs.push(&base_parsed);

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_stdlib(&mut kb, &refs, &NullResolver).expect("phase-1 load");

    // Phase 2: mount WorkItem, THEN load a file that seeds a resident fact for it.
    let functor = kb.try_resolve_symbol(WORKITEM_QN).expect("WorkItem loaded");
    let id_field = kb.intern("id");
    let desc_field = kb.intern("description");
    mount_workitems(&mut kb, functor, id_field, desc_field, &[(1, "first")]);

    let offending = parse::parse(
        r#"
namespace test.extent.more
  import test.extent.Demo.{WorkItem}
  fact WorkItem(id: 9, description: "resident")
end
"#,
    )
    .expect("parse offending");
    let errs = load::load_incremental(&mut kb, &[&offending], &NullResolver)
        .expect_err("a resident fact for a mounted functor must be refused at load");
    assert!(
        errs.iter().any(|e| e.to_string().contains("owned by a mounted extent source")),
        "expected FunctorOwnedByExtent, got: {:?}",
        errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
}

// ── (4b) loader refusal: a bodied rule with a mounted head ─────

#[test]
fn source_rule_for_owned_functor_refused_at_load() {
    // Same as (4), but the offending clause is a bodied `rule` (the WI refuses "a
    // fact OR a same-head bodied rule"). Its head functor is the mounted one.
    let stdlib = crate::common::collect_stdlib_and_rust_bindings();
    let stdlib_parsed: Vec<_> = stdlib
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).expect("parse stdlib"))
        .collect();
    let base_parsed = parse::parse(BASE).expect("parse base");
    let mut refs: Vec<&_> = stdlib_parsed.iter().collect();
    refs.push(&base_parsed);

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_stdlib(&mut kb, &refs, &NullResolver).expect("phase-1 load");

    let functor = kb.try_resolve_symbol(WORKITEM_QN).expect("WorkItem loaded");
    let id_field = kb.intern("id");
    let desc_field = kb.intern("description");
    mount_workitems(&mut kb, functor, id_field, desc_field, &[(1, "first")]);

    let offending = parse::parse(
        r#"
namespace test.extent.more
  import test.extent.Demo.{WorkItem, Tag}
  rule WorkItem(id: ?x, description: "derived")
    :- Tag(id: ?x)
end
"#,
    )
    .expect("parse offending rule");
    let errs = load::load_incremental(&mut kb, &[&offending], &NullResolver)
        .expect_err("a resident bodied rule for a mounted functor must be refused at load");
    assert!(
        errs.iter().any(|e| {
            let s = e.to_string();
            s.contains("owned by a mounted extent source") && s.contains("rule")
        }),
        "expected FunctorOwnedByExtent for a rule, got: {:?}",
        errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
}

// ── (5) registration refusal: load-then-mount ──────────────────

#[test]
fn register_owner_over_resident_functor_refused() {
    // Tag is loaded WITH resident facts, so mounting an owner over it collides.
    let src = r#"
namespace test.extent
  sort Demo
    entity Tag(id: Int64)
  end
  fact Tag(id: 1)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let tag = kb.try_resolve_symbol("test.extent.Demo.Tag").expect("Tag loaded");
    let id_field = kb.intern("id");
    let tag_row = Value::Entity {
        functor: tag,
        pos: [].into(),
        named: [(id_field, Value::Int(1))].into(),
    };
    // Seed itself is fine (a keyed row); the collision is at registration.
    let src = InMemoryExtentSource::new(&kb, "test.extent.Demo.Tag", ArgKey::Named(id_field), vec![tag_row])
        .expect("seed ok");
    let err = kb
        .register_extent_owner(Box::new(src))
        .expect_err("registering over a resident functor must be refused");
    assert!(
        matches!(err, ExtentRegError::ResidentCollision { .. }),
        "expected ResidentCollision, got {err:?}"
    );
}
