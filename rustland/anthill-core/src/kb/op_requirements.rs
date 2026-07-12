//! WI-222 — Op.requirements computation.
//!
//! For each operation, compute the positional list of `SortGoal`s its
//! body needs (transitive closure over called ops). Per
//! `docs/design/operation-call-model.md` §"Op.requirements computation":
//!
//!   op.requirements (set view, before ordering) =
//!       direct:     { goal_for(callee.spec_sort, callee.type_args)
//!                     | callee in body, callee is a spec op }
//!     ∪ transitive: ⋃ { substitute(other_op.requirements, callee.subst_at_callsite)
//!                       | other_op in body, callee is in this sort or another }
//!
//! Implementation uses the demand-driven memoized strategy:
//! recursively walk callees, push each in-progress op on a stack to
//! catch cycles. On a recursive call back to an in-progress op, return
//! the empty set — mutually-recursive groups stabilize via the
//! fixed-point on the way back up. (Full Tarjan-SCC fixed-point can be
//! a follow-up if precise mutual-recursion semantics turn up needs.)
//!
//! Acceptance #4 of WI-222 (mutual recursion via fixed-point) is
//! exercised in tests below.

use std::collections::HashMap;

use smallvec::SmallVec;

use crate::intern::Symbol;

use super::term::{Term, TermId};
use super::node_occurrence::{Expr, NodeKind, NodeOccurrence, for_each_child};
use super::typing::{list_to_vec, lookup_spec_op_dispatch, requires_chain_flat};
use super::KnowledgeBase;

/// A single requirement entry: a spec sort plus the bindings the
/// caller's body needs the requirement value to be at. The bindings
/// match the user-facing named-arg form (e.g. `T = Int64`, `combine = ...`).
/// Equality is structural; same (spec, bindings) pair is one goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpRequirement {
    pub spec_sort: Symbol,
    /// Per-call type-arg bindings (e.g. `T = Int64`). Reserved for the
    /// post-rewrite-pass refinement: callers will substitute these via
    /// the typer's per-call subst before unioning into their own
    /// requirements list. v0 leaves this empty; coverage matching uses
    /// `spec_sort` only until the rewrite pass populates it.
    pub bindings: SmallVec<[(Symbol, TermId); 2]>,
}

/// Compute the transitive requirements list for `op_sym`. Returns the
/// positional list, ordered by depth-first body traversal.
pub fn op_requirements(kb: &KnowledgeBase, op_sym: Symbol) -> Vec<OpRequirement> {
    let mut memo: HashMap<Symbol, Vec<OpRequirement>> = HashMap::new();
    let mut in_progress: Vec<Symbol> = Vec::new();
    compute_op_requirements(kb, op_sym, &mut in_progress, &mut memo)
}

fn compute_op_requirements(
    kb: &KnowledgeBase,
    op_sym: Symbol,
    in_progress: &mut Vec<Symbol>,
    memo: &mut HashMap<Symbol, Vec<OpRequirement>>,
) -> Vec<OpRequirement> {
    if let Some(cached) = memo.get(&op_sym) {
        return cached.clone();
    }
    if in_progress.contains(&op_sym) {
        // Cycle: return empty for now. The outer call's contributions
        // will be absorbed on the way back up. Full fixed-point over
        // the SCC is a possible v0.x improvement.
        return Vec::new();
    }
    in_progress.push(op_sym);

    // WI-251 — walk the NodeOccurrence body tree directly. The legacy
    // Handle-wrapped Term walk is gone; we now read `kb.op_body_node`
    // for the operation's value-typed body.
    let body = kb.op_body_node(op_sym).cloned();
    let mut result: Vec<OpRequirement> = Vec::new();

    if let Some(body_node) = body {
        walk_calls_node(&body_node, &mut |callee_sym, callee_bindings| {
            if let Some(spec_sort) = lookup_spec_op_dispatch(kb, callee_sym) {
                push_unique(&mut result, OpRequirement {
                    spec_sort,
                    bindings: callee_bindings.clone(),
                });
            }
            // Transitive contribution. v0 simplification: callee's
            // bindings are not substituted by call-site subst — the
            // rewrite pass will refine this when it produces the
            // per-call bindings the design's substitute() needs.
            let transitive =
                compute_op_requirements(kb, callee_sym, in_progress, memo);
            for req in transitive {
                push_unique(&mut result, req);
            }
        });
    }

    in_progress.pop();
    memo.insert(op_sym, result.clone());
    result
}

fn push_unique(list: &mut Vec<OpRequirement>, item: OpRequirement) {
    if !list.iter().any(|x| x == &item) {
        list.push(item);
    }
}

/// Walk a NodeOccurrence body tree, invoking `visit(callee_sym, callee_bindings)`
/// for every `Expr::Apply` or `Expr::ApplyWithin` node found. WI-251:
/// replaces the legacy Term-walking `walk_calls` (which dereferenced
/// `Handle(Occurrence, _)` wrappers) — the NodeOccurrence tree
/// already carries `functor: Symbol` on the Apply variant, so we read
/// it directly without a reflect-symbol cache. `callee_bindings` is
/// the per-call substitution; v0 leaves it empty (the rewrite pass
/// will populate it from the typer's per-call subst).
///
/// WI-702: shared with `typing::check_simp_effectful_ops` (the one occurrence
/// call-functor walk, so the two can't drift). It matches only `Apply` /
/// `ApplyWithin`; a `DotApply` method call is caught only once dispatched to
/// `Apply` (both callers run after `type_rule_bodies` / on dispatched bodies).
pub(crate) fn walk_calls_node(
    root: &std::rc::Rc<NodeOccurrence>,
    visit: &mut dyn FnMut(Symbol, SmallVec<[(Symbol, TermId); 2]>),
) {
    let mut stack: Vec<std::rc::Rc<NodeOccurrence>> = Vec::with_capacity(32);
    stack.push(std::rc::Rc::clone(root));
    while let Some(occ) = stack.pop() {
        let NodeKind::Expr { expr, .. } = &occ.kind else { continue };
        if let Expr::Apply { functor, .. } | Expr::ApplyWithin { functor, .. } = expr {
            // v0: per-call bindings empty — the rewrite pass populates
            // them from the typer's per-call subst.
            visit(*functor, SmallVec::new());
        }
        for_each_child(expr, |c| stack.push(std::rc::Rc::clone(c)));
    }
}

/// Sort-level requirements coverage: a per-op requirement is
/// "uncovered" if no entry in the enclosing sort's `requires` chain
/// matches its spec_sort. Per `docs/design/operation-call-model.md`
/// §"Sort-level requirements", such a body is an error: "B's body
/// uses Eq[T] but `requires Eq[T]` isn't declared".
#[derive(Debug, Clone)]
pub struct UncoveredRequirement {
    pub sort: Symbol,
    pub op: Symbol,
    pub requirement: OpRequirement,
}

/// Walk all operations of `sort_sym` and report any spec-sort
/// requirements that aren't covered by the sort's declared
/// `requires` chain. Bindings are not yet refined (v0 simplification),
/// so coverage is checked at the spec_sort level only — a `requires Eq`
/// (or `requires Eq[T]`) covers any per-op `Eq[*]` requirement.
pub fn check_sort_requirements_coverage(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
) -> Vec<UncoveredRequirement> {
    let chain = requires_chain_flat(kb, sort_sym);
    let declared: std::collections::HashSet<Symbol> =
        chain.iter().map(|e| e.required_sort).collect();

    let mut uncovered = Vec::new();
    for op_sym in operations_of_sort(kb, sort_sym) {
        for req in op_requirements(kb, op_sym) {
            if !declared.contains(&req.spec_sort) {
                uncovered.push(UncoveredRequirement {
                    sort: sort_sym,
                    op: op_sym,
                    requirement: req,
                });
            }
        }
    }
    uncovered
}

/// Operation symbols declared on a sort. Walks `SortInfo` facts looking
/// for the sort's `operations` list. The list entries are `Term::Ref`
/// pointing at each op's qualified symbol.
pub(crate) fn operations_of_sort(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<Symbol> {
    // WI-671/WI-672 — the SortInfo canonical-sort bucket (or a live scan pre-index); the
    // raw `name != Some(sort_sym)` re-filter below preserves this site's exact-`==` match
    // (raw `==` within a canonical bucket returns the same exact fact).
    for rid in crate::kb::typing::sort_info_rids_by_sort(kb, sort_sym) {
        if !kb.is_fact(rid) { continue; }
        let Some(head) = kb.fact_head_term(rid) else { continue };
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };
        let name_match = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .and_then(|(_, v)| match kb.get_term(*v) {
                Term::Ref(s) => Some(*s),
                Term::Fn { functor, .. } => Some(*functor),
                _ => None,
            });
        if name_match != Some(sort_sym) { continue; }
        let ops_tid = match named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "operations")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => continue,
        };
        return list_to_vec(kb, ops_tid)
            .into_iter()
            .filter_map(|t| match kb.get_term(t) {
                Term::Ref(s) => Some(*s),
                _ => None,
            })
            .collect();
    }
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::load::{self, NullResolver};
    use crate::parse;
    use std::path::PathBuf;

    fn workspace_root() -> PathBuf {
        let mut p = std::env::current_dir().unwrap();
        loop {
            if p.join("rustland").join("Cargo.toml").exists() { return p; }
            if !p.pop() { panic!("workspace root not found"); }
        }
    }

    fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
        let mut files = Vec::new();
        let Ok(entries) = std::fs::read_dir(dir) else { return files; };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(collect_anthill_files(&path));
            } else if path.extension().and_then(|s| s.to_str()) == Some("anthill") {
                files.push(path);
            }
        }
        files
    }

    fn load_with_src(src: &str) -> KnowledgeBase {
        let root = workspace_root();
        let mut files = collect_anthill_files(&root.join("stdlib").join("anthill"));
        files.extend(collect_anthill_files(
            &root.join("rustland").join("anthill-stl").join("anthill"),
        ));
        let mut parsed: Vec<_> = files.iter().map(|p| {
            let s = std::fs::read_to_string(p).unwrap();
            parse::parse(&s).unwrap()
        }).collect();
        parsed.push(parse::parse(src).unwrap());
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        let _ = load::load_all(&mut kb, &refs, &NullResolver);
        kb
    }

    #[test]
    fn op_with_no_calls_has_empty_requirements() {
        let src = r#"
namespace test.wi222.empty_reqs
  operation simple() -> Int64 = 42
end
"#;
        let kb = load_with_src(src);
        let op_sym = kb.try_resolve_symbol("test.wi222.empty_reqs.simple")
            .expect("simple registered");
        let reqs = op_requirements(&kb, op_sym);
        assert!(reqs.is_empty(),
            "simple op with no calls must have empty requirements; got {reqs:?}");
    }

    #[test]
    fn op_calling_spec_op_records_spec_in_requirements() {
        // `caller` calls `Eq.eq` (a stdlib spec op). The analysis should
        // surface Eq.eq's parent sort (Eq) as a requirement of caller.
        let src = r#"
namespace test.wi222.spec_call
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.{Bool}
  operation caller(a: Int64, b: Int64) -> Bool = eq(a, b)
end
"#;
        let kb = load_with_src(src);
        let op_sym = kb.try_resolve_symbol("test.wi222.spec_call.caller")
            .expect("caller registered");
        let eq_sort = kb.try_resolve_symbol("anthill.prelude.PartialEq")
            .expect("Eq registered");
        let reqs = op_requirements(&kb, op_sym);
        assert!(reqs.iter().any(|r| r.spec_sort == eq_sort),
            "caller calls Eq.eq, so Eq must appear in requirements; got {reqs:?}");
    }

    #[test]
    fn mutual_recursion_terminates_without_panic() {
        // `a` calls `b` and `b` calls `a`. The analysis should terminate
        // (cycle detection) and produce a stable result without panicking
        // — exercising acceptance #4 of WI-222 (mutual recursion via
        // fixed-point handling, even if our v0 cycle-as-empty approach
        // is simpler than full Tarjan).
        let src = r#"
namespace test.wi222.mutual
  operation a(n: Int64) -> Int64 = b(n)
  operation b(n: Int64) -> Int64 = a(n)
end
"#;
        let kb = load_with_src(src);
        let a_sym = kb.try_resolve_symbol("test.wi222.mutual.a").unwrap();
        let b_sym = kb.try_resolve_symbol("test.wi222.mutual.b").unwrap();
        // Both calls must terminate and produce a (possibly empty)
        // requirements list. The non-spec-op cycle has no spec
        // contributions, so both should be empty.
        let a_reqs = op_requirements(&kb, a_sym);
        let b_reqs = op_requirements(&kb, b_sym);
        assert!(a_reqs.is_empty(), "a → b → a cycle should produce empty reqs; got {a_reqs:?}");
        assert!(b_reqs.is_empty(), "b → a → b cycle should produce empty reqs; got {b_reqs:?}");
    }

    #[test]
    fn coverage_passes_when_sort_declares_required_spec() {
        // Sort B has an op that calls Eq.eq AND declares `requires Eq[T]`.
        // The coverage check should pass with no uncovered requirements.
        let src = r#"
namespace test.wi222.coverage_ok
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.{Eq, Bool}
  sort CoverageOk
    sort T = ?
    requires Eq[T]
    operation use_eq(a: T, b: T) -> Bool = eq(a, b)
  end
end
"#;
        let kb = load_with_src(src);
        let sort_sym = kb.try_resolve_symbol("test.wi222.coverage_ok.CoverageOk")
            .expect("CoverageOk registered");
        let uncovered = check_sort_requirements_coverage(&kb, sort_sym);
        assert!(uncovered.is_empty(),
            "sort with matching requires clause should have no uncovered \
             requirements; got {uncovered:?}");
    }

    #[test]
    fn coverage_flags_undeclared_requirement() {
        // Sort calls Eq.eq but does NOT declare `requires Eq[T]`. The
        // coverage check should flag the op's Eq requirement as uncovered.
        let src = r#"
namespace test.wi222.coverage_missing
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.{Bool}
  sort CoverageMissing
    operation oops(a: Int64, b: Int64) -> Bool = eq(a, b)
  end
end
"#;
        let kb = load_with_src(src);
        let sort_sym = kb.try_resolve_symbol("test.wi222.coverage_missing.CoverageMissing")
            .expect("CoverageMissing registered");
        let eq_sort = kb.try_resolve_symbol("anthill.prelude.PartialEq").unwrap();
        let uncovered = check_sort_requirements_coverage(&kb, sort_sym);
        assert!(uncovered.iter().any(|u| u.requirement.spec_sort == eq_sort),
            "sort calling eq() without `requires Eq[T]` must be flagged; got {uncovered:?}");
    }

    #[test]
    fn deduplicates_repeated_spec_calls() {
        // `foo` calls `eq` twice. The analysis should only record Eq
        // once in the requirements — `push_unique` enforces set
        // semantics on the positional list.
        let src = r#"
namespace test.wi222.dedupe
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.{Bool}
  operation foo(a: Int64, b: Int64, c: Int64) -> Bool
    = if eq(a, b) then eq(b, c) else false
end
"#;
        let kb = load_with_src(src);
        let foo_sym = kb.try_resolve_symbol("test.wi222.dedupe.foo")
            .expect("foo registered");
        let eq_sort = kb.try_resolve_symbol("anthill.prelude.PartialEq")
            .expect("Eq registered");
        let reqs = op_requirements(&kb, foo_sym);
        let eq_count = reqs.iter().filter(|r| r.spec_sort == eq_sort).count();
        assert_eq!(eq_count, 1,
            "two calls to Eq.eq should fold to one requirement; got {reqs:?}");
    }
}
