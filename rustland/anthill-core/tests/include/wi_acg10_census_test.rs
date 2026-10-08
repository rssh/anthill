//! WI-20260926-ACG10 — the proposal-068 CENSUS (`docs/design/068-implementation.md` §1.2–1.3).
//!
//! A MEASUREMENT, not a capability test, and `#[ignore]`d for that reason: it answers "which
//! operation applications does 068 change, and where", so K4JGC can be measured before and
//! after against the same population. Run it explicitly:
//!
//! ```text
//! scripts/test.sh -p anthill-core --test wi_tests -- --ignored acg10_census --nocapture
//! ```
//!
//! For each corpus project it loads stdlib plus the project, then walks every STORED rule
//! whose source file belongs to the project:
//!  * every BODY GOAL — an operation application in a value position is a FRAGMENT ROOT
//!    (068 §1), counted by POSITION (a goal's argument, an operand of a named builtin, the
//!    goal itself being the call; `nested` when it sits under a constructor, tuple or
//!    collection literal) and by CALLEE (builtin / bodied / host / spec dispatch — with the
//!    typer's pin, dictionary or no classification — / rules / none). Calls inside a root's
//!    own arguments are part of that fragment and counted apart.
//!  * every HEAD — an operation application inside a relational head's arguments is a
//!    PATTERN OVER A CALL: the library code that compares an unevaluated application as data
//!    (§1.3). Equation heads are counted apart: their subject is an application by design.
//!
//! It classifies by SYMBOL KIND only — no typing (decision D5). The one thing it asserts is
//! that every project it counts LOADED: a partial KB would count a population that is not the
//! program's.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{ApplyDispatch, Expr, NodeOccurrence};
use anthill_core::kb::op_info::operation_is_declared;
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::typing::lookup_spec_op_dispatch;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;

#[derive(Default)]
struct Census {
    rules: usize,
    goals: usize,
    /// (position, callee) → fragment roots
    roots: BTreeMap<(String, String), usize>,
    /// operation applications inside a root's own arguments
    inner_calls: usize,
    set_literals: usize,
    /// fragment roots whose callee has no implementation of any kind, with their site
    none_sites: Vec<String>,
    /// relational heads holding an operation application: (site, head functor, operation)
    head_calls: Vec<String>,
    /// guarded equations (`lhs = rhs :- g`, `lhs <=> rhs :- g`): a head on `eq` / `unify`
    /// with a body — a rewrite, not a relational pattern
    guarded_eq_heads: usize,
    /// quantified-guard consequents (`-: lte(…)`): a head on a builtin comparison
    guard_consequents: Vec<String>,
    /// fragment roots in a goal's arguments — the population D3 changes — with their site
    goal_arg_sites: Vec<String>,
    /// equation heads whose SUBJECT'S ARGUMENTS hold an application (a rewrite pattern)
    eq_head_calls: usize,
}

struct Sites {
    text: HashMap<String, String>,
}

impl Sites {
    fn line(&mut self, path: &str, offset: u32) -> usize {
        let text = self
            .text
            .entry(path.to_string())
            .or_insert_with(|| std::fs::read_to_string(path).unwrap_or_default());
        let end = (offset as usize).min(text.len());
        text[..end].matches('\n').count() + 1
    }
}

fn callee_class(kb: &KnowledgeBase, f: Symbol, node: Option<&NodeOccurrence>) -> String {
    if kb.is_builtin(f) {
        return "builtin".into();
    }
    if kb.op_body_node(f).is_some() {
        return "bodied".into();
    }
    if kb.is_interpreter_mapped_op(f) {
        return "host".into();
    }
    if lookup_spec_op_dispatch(kb, f).is_some() {
        let how = match node.map(|n| n.apply_dispatch()) {
            Some(ApplyDispatch::Pin(_)) => "pin",
            Some(ApplyDispatch::NeedsDict(_)) => "dict",
            _ => "unclassified",
        };
        return format!("spec({how})");
    }
    if kb.rules_by_functor_iter(f).next().is_some() {
        return "rules".into();
    }
    "none".into()
}

fn args_of(e: &Expr) -> Vec<Rc<NodeOccurrence>> {
    let mut out = Vec::new();
    match e {
        Expr::Apply { pos_args, named_args, .. }
        | Expr::Constructor { pos_args, named_args, .. }
        | Expr::ConstructorWithin { pos_args, named_args, .. } => {
            out.extend(pos_args.iter().cloned());
            out.extend(named_args.iter().map(|(_, a)| Rc::clone(a)));
        }
        Expr::ApplyWithin { args, named_args, .. } => {
            out.extend(args.iter().cloned());
            out.extend(named_args.iter().map(|(_, a)| Rc::clone(a)));
        }
        Expr::DotApply { receiver, pos_args, named_args, .. } => {
            out.push(Rc::clone(receiver));
            out.extend(pos_args.iter().cloned());
            out.extend(named_args.iter().map(|(_, a)| Rc::clone(a)));
        }
        Expr::ListLit(xs) | Expr::SetLit(xs) => out.extend(xs.iter().cloned()),
        Expr::TupleLit { positional, named } => {
            out.extend(positional.iter().cloned());
            out.extend(named.iter().map(|(_, a)| Rc::clone(a)));
        }
        Expr::HoApply { args, .. } | Expr::HoApplyWithin { args, .. } => {
            out.extend(args.iter().cloned())
        }
        _ => {}
    }
    out
}

/// Operation applications anywhere under `n` (a fragment root's own arguments).
fn count_calls(kb: &KnowledgeBase, n: &NodeOccurrence) -> usize {
    let Some(e) = n.as_expr() else { return 0 };
    let own = match e {
        Expr::Apply { functor, .. } if operation_is_declared(kb, *functor) => 1,
        Expr::ApplyWithin { .. } | Expr::DotApply { .. } => 1,
        _ => 0,
    };
    own + args_of(e).iter().map(|a| count_calls(kb, a)).sum::<usize>()
}

fn site(kb: &KnowledgeBase, sites: &mut Sites, n: &NodeOccurrence) -> String {
    let path = kb.source_name(n.span.source).to_string();
    let line = sites.line(&path, n.span.span.start);
    format!("{}:{line}", short(&path))
}

fn short(path: &str) -> String {
    for marker in ["stdlib/", "examples/", "rustland/anthill-todo/"] {
        if let Some(i) = path.find(marker) {
            return path[i..].to_string();
        }
    }
    path.to_string()
}

struct Walk<'a> {
    kb: &'a KnowledgeBase,
    sites: &'a mut Sites,
    c: &'a mut Census,
}

impl Walk<'_> {
    fn root(&mut self, pos: &str, depth: usize, callee: String, n: &NodeOccurrence, f: Option<Symbol>) {
        let label = if depth == 0 { pos.to_string() } else { format!("{pos} nested") };
        let name = f.map(|f| self.kb.qualified_name_of(f).to_string()).unwrap_or_default();
        if callee == "none" {
            let s = site(self.kb, self.sites, n);
            self.c.none_sites.push(format!("{s}  {label}  {name}"));
        }
        if label.starts_with("goal-arg") {
            let s = site(self.kb, self.sites, n);
            self.c.goal_arg_sites.push(format!("{s}  {label}  {callee}  {name}"));
        }
        *self.c.roots.entry((label, callee)).or_default() += 1;
        if let Some(e) = n.as_expr() {
            self.c.inner_calls += args_of(e).iter().map(|a| count_calls(self.kb, a)).sum::<usize>();
        }
    }

    fn value(&mut self, n: &Rc<NodeOccurrence>, pos: &str, depth: usize) {
        let Some(e) = n.as_expr() else { return };
        match e {
            Expr::Apply { functor, .. } if operation_is_declared(self.kb, *functor) => {
                let callee = callee_class(self.kb, *functor, Some(n));
                self.root(pos, depth, callee, n, Some(*functor));
            }
            Expr::ApplyWithin { functor, .. } => {
                let callee = format!("woven:{}", callee_class(self.kb, *functor, None));
                self.root(pos, depth, callee, n, Some(*functor));
            }
            Expr::DotApply { .. } => self.root(pos, depth, "dot".into(), n, None),
            Expr::HoApply { .. } | Expr::HoApplyWithin { .. } => {
                self.root(pos, depth, "ho-apply".into(), n, None)
            }
            Expr::Match { .. }
            | Expr::If { .. }
            | Expr::Let { .. }
            | Expr::Lambda { .. }
            | Expr::LambdaWithin { .. } => self.root(pos, depth, "binder".into(), n, None),
            Expr::SetLit(_) => {
                self.c.set_literals += 1;
                for a in args_of(e) {
                    self.value(&a, pos, depth + 1);
                }
            }
            _ => {
                for a in args_of(e) {
                    self.value(&a, pos, depth + 1);
                }
            }
        }
    }

    fn goal(&mut self, g: &Rc<NodeOccurrence>) {
        self.c.goals += 1;
        let as_value = Value::Node(Rc::clone(g));
        let Some(e) = g.as_expr() else { return };
        if let Some(tag) = self.kb.get_builtin_view(&as_value) {
            let name = format!("{tag:?}");
            let goal_args = matches!(name.as_str(), "Not" | "PushChoice" | "PushAnd");
            for a in args_of(e) {
                if goal_args {
                    self.goal(&a);
                } else {
                    self.value(&a, &format!("operand:{name}"), 0);
                }
            }
            return;
        }
        match e {
            Expr::Apply { functor, .. } if operation_is_declared(self.kb, *functor) => {
                let callee = callee_class(self.kb, *functor, Some(g));
                self.root("goal-is-call", 0, callee, g, Some(*functor));
            }
            Expr::ApplyWithin { functor, .. } => {
                let callee = format!("woven:{}", callee_class(self.kb, *functor, None));
                self.root("goal-is-call", 0, callee, g, Some(*functor));
            }
            // A quantifier's SCOPING MARKER holds GOALS, not data: `forall_impl(tuple(binders),
            // tuple(antecedents…), tuple(consequent…))` and `forall_in` / `some_in(?x, xs,
            // tuple(body…))` (the converter's lowering) — each `tuple(…)` group is a list of
            // goals, and `forall_in`'s collection `xs` is the one data slot.
            Expr::Apply { functor, pos_args, .. } if is_scoping_marker(self.kb, *functor) => {
                let bounded = local_name(self.kb, *functor) != "forall_impl";
                for (i, a) in pos_args.iter().enumerate() {
                    if bounded && i == 1 {
                        self.value(a, "quantifier-collection", 0);
                        continue;
                    }
                    match a.as_expr() {
                        Some(Expr::Apply { functor: t, .. }) if local_name(self.kb, *t) == "tuple" => {
                            for g in args_of(a.as_expr().unwrap()) {
                                self.goal(&g);
                            }
                        }
                        _ => self.goal(a),
                    }
                }
            }
            _ => {
                for a in args_of(e) {
                    self.value(&a, "goal-arg", 0);
                }
            }
        }
    }
}

fn local_name(kb: &KnowledgeBase, f: Symbol) -> &str {
    let q = kb.qualified_name_of(f);
    q.rsplit('.').next().unwrap_or(q)
}

fn is_scoping_marker(kb: &KnowledgeBase, f: Symbol) -> bool {
    matches!(local_name(kb, f), "forall_impl" | "forall_in" | "some_in")
}

/// Operation applications inside a head's arguments, walked on the head's own carrier.
fn head_calls(kb: &KnowledgeBase, v: &Value, out: &mut Vec<Symbol>) {
    match v.head(kb) {
        ViewHead::Functor { functor, pos_arity, .. } => {
            if let Some(f) = functor {
                if operation_is_declared(kb, f) {
                    out.push(f);
                }
            }
            let mut children: Vec<Value> =
                (0..pos_arity).filter_map(|i| v.pos_arg(kb, i).map(|a| a.to_value())).collect();
            for k in v.named_keys(kb) {
                if let Some(a) = v.named_arg(kb, k) {
                    children.push(a.to_value());
                }
            }
            for c in children {
                head_calls(kb, &c, out);
            }
        }
        _ => {}
    }
}

fn head_args(kb: &KnowledgeBase, v: &Value) -> Vec<Value> {
    let ViewHead::Functor { pos_arity, .. } = v.head(kb) else { return Vec::new() };
    let mut out: Vec<Value> =
        (0..pos_arity).filter_map(|i| v.pos_arg(kb, i).map(|a| a.to_value())).collect();
    for k in v.named_keys(kb) {
        if let Some(a) = v.named_arg(kb, k) {
            out.push(a.to_value());
        }
    }
    out
}

/// NOT THE RECIPE, BY NAME (WI-20261008-RAH0Z): the census files each rule under a
/// project by the PATH of the source it is written in, the stdlib's own rules among
/// them, and the recipe's parsed stdlib carries no path — `kb.source_name` answers
/// `<unknown>` for it. Moved onto the recipe, the stdlib group counted NOTHING and said
/// so nowhere (found by /code-review); `acg10_census` now refuses that zero.
fn load_project(name: &str, own: &[PathBuf]) -> Option<KnowledgeBase> {
    let mut files = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
    files.extend(crate::common::collect_anthill_files(&crate::common::rust_stl_dir()));
    files.sort();
    files.extend(own.iter().cloned());
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
                .with_path(p.as_path())
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Some(kb),
        Err(errs) => {
            eprintln!("LOAD FAILED  {name}: {} error(s); first: {}", errs.len(), errs[0]);
            None
        }
    }
}

fn census(kb: &KnowledgeBase, belongs: &dyn Fn(&str) -> bool) -> Census {
    let mut c = Census::default();
    let mut sites = Sites { text: HashMap::new() };
    for rid in kb.live_rule_ids() {
        let body = kb.rule_body_nodes(rid).to_vec();
        let span = kb.rule_head_span(rid).or_else(|| body.first().map(|n| n.span));
        let Some(span) = span else { continue };
        let path = kb.source_name(span.source).to_string();
        if !belongs(&path) {
            continue;
        }
        c.rules += 1;
        {
            let mut w = Walk { kb, sites: &mut sites, c: &mut c };
            for g in &body {
                w.goal(g);
            }
        }
        let head = kb.rule_head_value(rid).clone();
        if kb.is_equation(rid) {
            // the subject is an application by design; count patterns inside ITS arguments
            let mut found = Vec::new();
            for side in head_args(kb, &head) {
                for a in head_args(kb, &side) {
                    head_calls(kb, &a, &mut found);
                }
            }
            if !found.is_empty() {
                c.eq_head_calls += 1;
            }
            continue;
        }
        let mut found = Vec::new();
        for a in head_args(kb, &head) {
            head_calls(kb, &a, &mut found);
        }
        if !found.is_empty() {
            let line = sites.line(&path, span.span.start);
            let head_sym = match head.head(kb) {
                ViewHead::Functor { functor: Some(f), .. } => Some(f),
                _ => None,
            };
            let hf = head_sym.map(|f| kb.qualified_name_of(f).to_string()).unwrap_or("?".into());
            if matches!(
                hf.as_str(),
                "anthill.prelude.PartialEq.eq" | "anthill.kernel.unify" | "anthill.kernel.struct_eq"
            ) {
                c.guarded_eq_heads += 1;
                continue;
            }
            if head_sym.is_some_and(|f| kb.is_builtin(f)) {
                c.guard_consequents.push(format!("{}:{line}  {hf}", short(&path)));
                continue;
            }
            let ops: Vec<String> =
                found.iter().map(|f| kb.qualified_name_of(*f).to_string()).collect();
            c.head_calls.push(format!("{}:{line}  {hf}  ⊇ {}", short(&path), ops.join(", ")));
        }
    }
    c
}

fn report(name: &str, c: &Census) {
    eprintln!("\n== {name}: {} rules, {} goals", c.rules, c.goals);
    for ((pos, callee), n) in &c.roots {
        eprintln!("   {n:>5}  {pos:<28} {callee}");
    }
    eprintln!(
        "   calls inside roots: {}   set literals: {}   equation heads with call patterns: {}   \
         guarded equations over calls: {}   guard consequents over calls: {}",
        c.inner_calls,
        c.set_literals,
        c.eq_head_calls,
        c.guarded_eq_heads,
        c.guard_consequents.len()
    );
    if !c.goal_arg_sites.is_empty() {
        eprintln!("   calls in a goal's arguments (D3's population):");
        for s in &c.goal_arg_sites {
            eprintln!("      {s}");
        }
    }
    if !c.none_sites.is_empty() {
        eprintln!("   roots whose callee has NO implementation:");
        for s in &c.none_sites {
            eprintln!("      {s}");
        }
    }
    if !c.head_calls.is_empty() {
        eprintln!("   relational heads holding an operation application:");
        for s in &c.head_calls {
            eprintln!("      {s}");
        }
    }
}

fn anthill_files_under(dir: &Path) -> Vec<PathBuf> {
    crate::common::collect_anthill_files(dir)
}

#[test]
#[ignore = "measurement: run with --ignored acg10_census --nocapture"]
fn acg10_census() {
    let root = crate::common::workspace_root();
    let stdlib = root.join("stdlib");
    let stl = root.join("rustland/anthill-stl");
    let mut projects: Vec<(String, PathBuf, Vec<PathBuf>)> = Vec::new();
    projects.push(("anthill-todo".into(), root.join("rustland/anthill-todo/anthill"),
        anthill_files_under(&root.join("rustland/anthill-todo/anthill"))));
    let ex = crate::common::examples_dir();
    let mut mini: Vec<PathBuf> = std::fs::read_dir(ex.join("classic-mini"))
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect();
    mini.sort();
    for d in mini {
        let n = format!("classic-mini/{}", d.file_name().unwrap().to_string_lossy());
        projects.push((n, d.clone(), anthill_files_under(&d)));
    }
    for n in ["github-todo", "sql-store", "guardians/lib", "webots-modelling/lf1"] {
        let d = ex.join(n);
        projects.push((n.to_string(), d.clone(), anthill_files_under(&d)));
    }

    // stdlib alone first: its rules are counted once, here.
    let kb = load_project("stdlib", &[]).expect("stdlib must load");
    let c = census(&kb, &|p| p.starts_with(stdlib.to_str().unwrap()) || p.starts_with(stl.to_str().unwrap()));
    assert!(
        c.rules > 0,
        "the stdlib census counted NO rule: no source in the KB is named by a path under \
         {} or {} — the files were loaded without their paths",
        stdlib.display(),
        stl.display()
    );
    report("stdlib (+ rust stl bindings)", &c);

    let mut failed = Vec::new();
    for (name, dir, own) in &projects {
        let Some(kb) = load_project(name, own) else {
            failed.push(name.clone());
            continue;
        };
        let d = dir.canonicalize().unwrap_or_else(|_| dir.clone());
        let d2 = dir.clone();
        let c = census(&kb, &|p| {
            let pp = Path::new(p);
            pp.starts_with(&d) || pp.starts_with(&d2)
        });
        report(name, &c);
    }
    assert!(failed.is_empty(), "projects that did not load, so were not counted: {failed:?}");
}
