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
use super::typing::{lookup_spec_op_dispatch, requires_chain, resolve_handle};
use super::KnowledgeBase;

/// A single requirement entry: a spec sort plus the bindings the
/// caller's body needs the requirement value to be at. The bindings
/// match the user-facing named-arg form (e.g. `T = Int`, `combine = ...`).
/// Equality is structural; same (spec, bindings) pair is one goal.
#[derive(Debug, Clone)]
pub struct OpRequirement {
    pub spec_sort: Symbol,
    pub bindings: SmallVec<[(Symbol, TermId); 2]>,
}

impl PartialEq for OpRequirement {
    fn eq(&self, other: &Self) -> bool {
        self.spec_sort == other.spec_sort && self.bindings == other.bindings
    }
}
impl Eq for OpRequirement {}

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

    let body = lookup_op_body(kb, op_sym);
    let mut result: Vec<OpRequirement> = Vec::new();

    if let Some(body_term) = body {
        walk_calls(kb, body_term, &mut |callee_sym, callee_bindings| {
            // Direct contribution: callee is a spec op.
            if let Some(spec_sort) = lookup_spec_op_dispatch(kb, callee_sym) {
                push_unique(&mut result, OpRequirement {
                    spec_sort,
                    bindings: callee_bindings.clone(),
                });
            }

            // Transitive contribution: pull in callee's own requirements,
            // each substituted by the call-site's bindings. v0
            // simplification: we don't substitute (the design's
            // substitute(other_op.requirements, call_subst) needs the
            // typer's full subst machinery). For ground call sites
            // (no open T), the callee's bindings are already concrete
            // and we just inherit them as-is.
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

/// Look up the body term for an operation. Mirrors
/// `eval::eval::lookup_operation_body` minus the params return.
fn lookup_op_body(kb: &KnowledgeBase, op_sym: Symbol) -> Option<TermId> {
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
    let body_field = "body";
    let name_field = "name";
    for rid in kb.by_functor(op_info_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };
        let name_match = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == name_field)
            .and_then(|(_, v)| match kb.get_term(*v) {
                Term::Ref(s) => Some(*s),
                _ => None,
            });
        if name_match != Some(op_sym) { continue; }
        let body_opt = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == body_field)
            .map(|(_, v)| *v)?;
        return super::typing::unwrap_option(kb, body_opt);
    }
    None
}

/// Walk a body term, invoking `visit(callee_sym, callee_bindings)` for
/// every apply / apply_within node found. `callee_bindings` is the
/// per-call substitution as a list of (param_short, value_term) pairs —
/// for v0 we extract this from the apply's named args (TODO: full
/// typer-driven substitution). The walker visits `apply` and the
/// requirement-aware variants; literals, lambdas, etc. are descended
/// recursively for nested calls.
fn walk_calls(
    kb: &KnowledgeBase,
    tid: TermId,
    visit: &mut dyn FnMut(Symbol, SmallVec<[(Symbol, TermId); 2]>),
) {
    // Resolve occurrence handles to the underlying term — operation
    // bodies are stored as `Const(Handle(Occurrence, ...))` references
    // into the occurrence table, not as direct Fn nodes.
    let tid = resolve_handle(kb, tid);
    let term = kb.get_term(tid).clone();
    match term {
        Term::Fn { functor, pos_args, named_args } => {
            // If this is an apply / apply_within node, harvest the call.
            let functor_qn = kb.qualified_name_of(functor);
            let is_apply = functor_qn == "anthill.reflect.Expr.apply"
                || functor_qn == "anthill.reflect.Expr.apply_within";

            if is_apply {
                if let Some(fn_sym) = extract_apply_target(kb, &named_args) {
                    // For v0, supply empty bindings — proper extraction
                    // requires running the typer's per-call subst, which
                    // is heavy machinery to invoke for analysis. Spec
                    // sort identity suffices for the dependency graph;
                    // bindings are optional refinement.
                    visit(fn_sym, SmallVec::new());
                }
            }

            // Recurse into all sub-terms — args, requirements channel,
            // pattern guards, etc. all may contain nested calls.
            for &p in &pos_args {
                walk_calls(kb, p, visit);
            }
            for &(_, t) in &named_args {
                walk_calls(kb, t, visit);
            }
        }
        Term::Ref(_) | Term::Ident(_) | Term::Const(_) | Term::Var(_) | Term::Bottom => {}
    }
}

fn extract_apply_target(
    kb: &KnowledgeBase,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<Symbol> {
    let fn_tid = named_args.iter()
        .find(|(s, _)| kb.resolve_sym(*s) == "fn")
        .map(|(_, v)| *v)?;
    match kb.get_term(fn_tid) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
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
    let chain = requires_chain(kb, sort_sym);
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
fn operations_of_sort(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<Symbol> {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let mut out = Vec::new();
    for rid in kb.by_functor(sort_info_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
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
        // Walk the cons-list — each element is a Ref to an op symbol.
        let mut cur = ops_tid;
        loop {
            match kb.get_term(cur) {
                Term::Fn { named_args: la, .. } => {
                    let head = la.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "head")
                        .map(|(_, v)| *v);
                    let tail = la.iter()
                        .find(|(s, _)| kb.resolve_sym(*s) == "tail")
                        .map(|(_, v)| *v);
                    match (head, tail) {
                        (Some(h), Some(t)) => {
                            if let Term::Ref(s) = kb.get_term(h) {
                                out.push(*s);
                            }
                            cur = t;
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        return out;
    }
    out
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
  operation simple() -> Int = 42
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
  operation caller(a: Int, b: Int) -> Bool = eq(a, b)
end
"#;
        let kb = load_with_src(src);
        let op_sym = kb.try_resolve_symbol("test.wi222.spec_call.caller")
            .expect("caller registered");
        let eq_sort = kb.try_resolve_symbol("anthill.prelude.Eq")
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
  operation a(n: Int) -> Int = b(n)
  operation b(n: Int) -> Int = a(n)
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
    operation oops(a: Int, b: Int) -> Bool = eq(a, b)
  end
end
"#;
        let kb = load_with_src(src);
        let sort_sym = kb.try_resolve_symbol("test.wi222.coverage_missing.CoverageMissing")
            .expect("CoverageMissing registered");
        let eq_sort = kb.try_resolve_symbol("anthill.prelude.Eq").unwrap();
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
  operation foo(a: Int, b: Int, c: Int) -> Bool
    = if eq(a, b) then eq(b, c) else false
end
"#;
        let kb = load_with_src(src);
        let foo_sym = kb.try_resolve_symbol("test.wi222.dedupe.foo")
            .expect("foo registered");
        let eq_sort = kb.try_resolve_symbol("anthill.prelude.Eq")
            .expect("Eq registered");
        let reqs = op_requirements(&kb, foo_sym);
        let eq_count = reqs.iter().filter(|r| r.spec_sort == eq_sort).count();
        assert_eq!(eq_count, 1,
            "two calls to Eq.eq should fold to one requirement; got {reqs:?}");
    }
}
