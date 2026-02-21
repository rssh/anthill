/// IR → KB loading.
///
/// Converts a parsed `ParsedFile` into KnowledgeBase terms and facts.
/// Re-interns symbols, re-allocates terms into the hash-consed store,
/// registers sorts, and asserts facts.
///
/// The loader takes a `SourceResolver` to fetch imported files. The CLI
/// provides a real FS implementation; tests use `NullResolver`.

use std::collections::{HashMap, HashSet};

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::parse::ir::*;
use super::{KnowledgeBase, SortKind};
use super::term::{Term, TermId, FnArg, VarId};

// ── Source resolution ──────────────────────────────────────────

/// Abstraction over the filesystem for resolving import paths to source text.
pub trait SourceResolver {
    /// Resolve a source path (e.g. `"std/prelude"` or `"./banking"`) to its contents.
    fn resolve(&self, path: &str) -> Result<String, std::io::Error>;
}

/// A resolver that always fails — for tests that don't use imports.
pub struct NullResolver;

impl SourceResolver for NullResolver {
    fn resolve(&self, path: &str) -> Result<String, std::io::Error> {
        Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("NullResolver: cannot resolve '{path}'"),
        ))
    }
}

/// Join name segments into a single dot-separated string.
fn join_segments(interner: &crate::intern::Interner, segments: &[Symbol]) -> String {
    let mut out = String::new();
    for (i, &sym) in segments.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        out.push_str(interner.resolve(sym));
    }
    out
}

#[derive(Clone, Debug)]
pub struct LoadError {
    pub message: String,
}

impl LoadError {
    #[allow(dead_code)]
    fn new(msg: impl Into<String>) -> Self {
        Self { message: msg.into() }
    }
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "load error: {}", self.message)
    }
}

impl std::error::Error for LoadError {}

/// Load a parsed file into the knowledge base.
///
/// The `resolver` is used to fetch source text for `import_tools` declarations.
/// Pass `&NullResolver` if no imports are expected.
///
/// For multi-file projects with `import` declarations (including `where` clauses),
/// use `load_all` to load all files into the same KB so that cross-file references
/// resolve correctly.
pub fn load(
    kb: &mut KnowledgeBase,
    parsed: &ParsedFile,
    resolver: &dyn SourceResolver,
) -> Result<(), Vec<LoadError>> {
    let mut loaded_paths = HashSet::new();
    load_with_visited(kb, parsed, resolver, &mut loaded_paths)
}

/// Load multiple parsed files into the same knowledge base.
///
/// All files are loaded sequentially into the shared KB, so imports
/// referencing sorts/domains from other files in the set will find
/// their facts already present (order-independent for `where` clauses
/// since member facts from earlier files are visible to later ones).
pub fn load_all(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<(), Vec<LoadError>> {
    let mut loaded_paths = HashSet::new();
    let mut all_errors = Vec::new();
    for parsed in files {
        if let Err(errs) = load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
            all_errors.extend(errs);
        }
    }
    if all_errors.is_empty() {
        Ok(())
    } else {
        Err(all_errors)
    }
}

/// Internal: load with cycle detection via `loaded_paths`.
fn load_with_visited(
    kb: &mut KnowledgeBase,
    parsed: &ParsedFile,
    resolver: &dyn SourceResolver,
    loaded_paths: &mut HashSet<String>,
) -> Result<(), Vec<LoadError>> {
    let mut loader = Loader::new(kb, parsed, resolver, loaded_paths);
    loader.load_items(&parsed.items, None);

    if loader.errors.is_empty() {
        Ok(())
    } else {
        Err(loader.errors)
    }
}

struct Loader<'a> {
    kb: &'a mut KnowledgeBase,
    parsed: &'a ParsedFile,
    resolver: &'a dyn SourceResolver,
    loaded_paths: &'a mut HashSet<String>,
    // Map from parse-time TermId → KB TermId
    term_map: HashMap<u32, TermId>,
    // Map from parse-time Symbol → KB Symbol
    sym_map: HashMap<u32, Symbol>,
    // Map from parse-time VarId → KB VarId
    var_map: HashMap<u32, VarId>,
    errors: Vec<LoadError>,
}

impl<'a> Loader<'a> {
    fn new(
        kb: &'a mut KnowledgeBase,
        parsed: &'a ParsedFile,
        resolver: &'a dyn SourceResolver,
        loaded_paths: &'a mut HashSet<String>,
    ) -> Self {
        Self {
            kb,
            parsed,
            resolver,
            loaded_paths,
            term_map: HashMap::new(),
            sym_map: HashMap::new(),
            var_map: HashMap::new(),
            errors: Vec::new(),
        }
    }

    /// Re-intern a symbol from the parse interner into the KB interner.
    fn reintern(&mut self, sym: Symbol) -> Symbol {
        if let Some(&mapped) = self.sym_map.get(&sym.index()) {
            return mapped;
        }
        let s = self.parsed.interner.resolve(sym);
        let new_sym = self.kb.intern(s);
        self.sym_map.insert(sym.index(), new_sym);
        new_sym
    }

    /// Re-intern a parse IR Name as a single dot-joined KB Symbol.
    fn reintern_name(&mut self, name: &Name) -> Symbol {
        if name.segments.len() == 1 {
            self.reintern(name.segments[0])
        } else {
            let joined = join_segments(&self.parsed.interner, &name.segments);
            self.kb.intern(&joined)
        }
    }

    /// Convert a parse-time TermId to a KB TermId, re-allocating into the hash-consed store.
    fn convert_term(&mut self, parse_id: TermId) -> TermId {
        if let Some(&mapped) = self.term_map.get(&parse_id.raw()) {
            return mapped;
        }

        let parse_term = self.parsed.terms.get(parse_id).clone();
        let kb_term = match parse_term {
            Term::Const(lit) => Term::Const(lit),
            Term::Var(vid) => {
                let kb_vid = if let Some(&mapped) = self.var_map.get(&vid.raw()) {
                    mapped
                } else {
                    let name = self.reintern(vid.name());
                    let new_vid = self.kb.fresh_var(name);
                    self.var_map.insert(vid.raw(), new_vid);
                    new_vid
                };
                Term::Var(kb_vid)
            }
            Term::Fn { functor, args } => {
                let new_functor = self.reintern(functor);
                let new_args: SmallVec<[FnArg; 4]> = args
                    .iter()
                    .map(|a| match a {
                        FnArg::Positional(id) => FnArg::Positional(self.convert_term(*id)),
                        FnArg::Named(sym, id) => {
                            FnArg::Named(self.reintern(*sym), self.convert_term(*id))
                        }
                    })
                    .collect();
                Term::Fn { functor: new_functor, args: new_args }
            }
            Term::Ref(sym) => Term::Ref(self.reintern(sym)),
            Term::Unspecified { text, hints } => {
                let new_hints: SmallVec<[TermId; 2]> = hints
                    .iter()
                    .map(|&id| self.convert_term(id))
                    .collect();
                Term::Unspecified { text, hints: new_hints }
            }
            Term::Bottom => Term::Bottom,
            Term::Ident(sym) => Term::Ident(self.reintern(sym)),
        };

        let kb_id = self.kb.alloc(kb_term);
        self.term_map.insert(parse_id.raw(), kb_id);
        kb_id
    }

    /// Convert a Name to a sort term (nullary Fn term).
    fn name_to_sort_term(&mut self, name: &Name) -> TermId {
        let functor = self.reintern_name(name);
        self.kb.alloc(Term::Fn {
            functor,
            args: SmallVec::new(),
        })
    }

    /// Convert a TypeExpr to a type-term in the KB.
    fn type_expr_to_term(&mut self, ty: &TypeExpr) -> TermId {
        match ty {
            TypeExpr::Simple(name) => self.name_to_sort_term(name),
            TypeExpr::Parameterized { name, bindings } => {
                let name_term = self.name_to_sort_term(name);
                let mut args: SmallVec<[FnArg; 4]> = SmallVec::new();
                args.push(FnArg::Positional(name_term));
                for b in bindings {
                    let param_sym = self.reintern(b.param.last());
                    let bound_term = self.type_expr_to_term(&b.bound);
                    args.push(FnArg::Named(param_sym, bound_term));
                }

                // Note: validation that binding params are actual members is deferred
                // to a separate resolve pass.

                let param_type_sym = self.kb.intern("ParameterizedType");
                self.kb.alloc(Term::Fn {
                    functor: param_type_sym,
                    args,
                })
            }
        }
    }

    /// Load items (top-level or within a domain).
    fn load_items(&mut self, items: &[Item], domain: Option<TermId>) {
        let domain = domain.unwrap_or_else(|| self.kb.make_name_term("_global"));

        for item in items {
            match item {
                Item::Namespace(n) => self.load_namespace(n),
                Item::AbstractSort(s) => self.load_abstract_sort(s, domain),
                Item::SortWithBody(s) => self.load_sort_with_body(s, domain),
                Item::Rule(r) => self.load_rule(r, domain),
                Item::Operation(o) => self.load_operation(o, domain),
                Item::RequiresDecl(r) => self.load_requires_decl(r, domain),
                Item::Entity(e) => self.load_entity(e, domain),
                Item::Fact(f) => self.load_fact(f, domain),
                Item::Constraint(c) => self.load_constraint(c, domain),
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        self.load_operation(op, domain);
                    }
                }
                Item::RuleBlock(rb) => {
                    for rule in &rb.entries {
                        self.load_rule(rule, domain);
                    }
                }
                Item::Project(p) => self.load_project(p, domain),
                Item::Tool(t) => self.load_tool(t, domain),
                Item::WorkItem(w) => self.load_workitem(w, domain),
                Item::Feedback(f) => self.load_feedback(f, domain),
                Item::ImportTools(it) => self.load_import_tools(it, domain),
            }
        }
    }

    fn load_namespace(&mut self, n: &Namespace) {
        let ns_term = self.name_to_sort_term(&n.name);
        let ns_sort = self.kb.make_name_term("Namespace");

        // Assert namespace as a fact
        self.kb.assert_fact(ns_term, ns_sort, ns_term, None);

        // Emit member facts for direct children
        self.emit_member_facts_for_items(&n.items, ns_term);

        // Load nested items within this namespace scope
        self.load_items(&n.items, Some(ns_term));
    }

    fn load_abstract_sort(&mut self, s: &AbstractSort, domain: TermId) {
        let sort_term = self.name_to_sort_term(&s.name);
        let sort_sort = self.kb.make_name_term("Sort");

        self.kb.register_sort(sort_term, SortKind::Abstract);

        // Assert SortInfo fact
        let sort_info_sym = self.kb.intern("SortInfo");
        let abstract_sym = self.kb.intern("Abstract");
        let abstract_term = self.kb.alloc(Term::Ident(abstract_sym));
        let fact_term = self.kb.alloc(Term::Fn {
            functor: sort_info_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(sort_term),
                FnArg::Positional(abstract_term),
            ]),
        });
        self.kb.assert_fact(fact_term, sort_sort, domain, None);
    }

    fn load_sort_with_body(&mut self, s: &SortWithBody, parent_domain: TermId) {
        let sort_term = self.name_to_sort_term(&s.name);
        let sort_sort = self.kb.make_name_term("Sort");

        // Determine kind: Defined if it has direct entity children, Abstract otherwise
        let has_entities = s.items.iter().any(|item| matches!(item, Item::Entity(_)));
        let kind = if has_entities { SortKind::Defined } else { SortKind::Abstract };
        self.kb.register_sort(sort_term, kind);

        // Assert SortInfo fact
        let sort_info_sym = self.kb.intern("SortInfo");
        let kind_str = if has_entities { "Defined" } else { "Abstract" };
        let kind_sym = self.kb.intern(kind_str);
        let kind_term = self.kb.alloc(Term::Ident(kind_sym));
        let fact_term = self.kb.alloc(Term::Fn {
            functor: sort_info_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(sort_term),
                FnArg::Positional(kind_term),
            ]),
        });
        self.kb.assert_fact(fact_term, sort_sort, parent_domain, None);

        // Register direct entity children as constructor subsorts
        for item in &s.items {
            if let Item::Entity(e) = item {
                let ctor_term = self.name_to_sort_term(&e.name);
                self.kb.register_sort(ctor_term, SortKind::Constructor);
                self.kb.register_subsort(ctor_term, sort_term);

                // Assert Subsort fact
                let subsort_sym = self.kb.intern("Subsort");
                let subsort_fact = self.kb.alloc(Term::Fn {
                    functor: subsort_sym,
                    args: SmallVec::from_slice(&[
                        FnArg::Positional(ctor_term),
                        FnArg::Positional(sort_term),
                    ]),
                });
                self.kb.assert_fact(subsort_fact, sort_sort, parent_domain, None);
            }
        }

        // Emit member facts for direct children
        self.emit_member_facts_for_items(&s.items, sort_term);

        // Load all items within this sort's domain scope
        self.load_items(&s.items, Some(sort_term));
    }

    fn load_entity(&mut self, e: &Entity, domain: TermId) {
        let entity_sort = self.kb.make_name_term("Entity");
        let functor = self.reintern_name(&e.name);

        let args: SmallVec<[FnArg; 4]> = e.fields
            .iter()
            .map(|f| {
                let field_sym = self.reintern(f.name);
                let type_term = self.type_expr_to_term(&f.ty);
                FnArg::Named(field_sym, type_term)
            })
            .collect();

        let entity_term = self.kb.alloc(Term::Fn { functor, args });
        self.kb.assert_fact(entity_term, entity_sort, domain, None);
    }

    fn load_fact(&mut self, f: &Fact, domain: TermId) {
        let fact_sort = self.kb.make_name_term("Fact");
        let term = self.convert_term(f.term);

        let meta = f.meta.as_ref().map(|mb| self.load_meta_block(mb));
        self.kb.assert_fact(term, fact_sort, domain, meta);
    }

    fn load_rule(&mut self, r: &Rule, domain: TermId) {
        let rule_sort = self.kb.make_name_term("Rule");
        let rule_sym = self.kb.intern("Rule");

        let head_term = match &r.head {
            RuleHead::Term(tid) => self.convert_term(*tid),
            RuleHead::Bottom => self.kb.alloc(Term::Bottom),
        };

        let rule_term = self.kb.alloc(Term::Fn {
            functor: rule_sym,
            args: SmallVec::from_elem(FnArg::Positional(head_term), 1),
        });

        self.kb.assert_fact(rule_term, rule_sort, domain, None);
    }

    fn load_operation(&mut self, o: &Operation, domain: TermId) {
        let op_sort = self.kb.make_name_term("Operation");
        let functor = self.reintern_name(&o.name);

        let return_term = self.type_expr_to_term(&o.return_type);

        let mut args: SmallVec<[FnArg; 4]> = o.params
            .iter()
            .map(|p| {
                let param_sym = self.reintern(p.name);
                let type_term = self.type_expr_to_term(&p.ty);
                FnArg::Named(param_sym, type_term)
            })
            .collect();

        let ret_sym = self.kb.intern("_returns");
        args.push(FnArg::Named(ret_sym, return_term));

        let op_term = self.kb.alloc(Term::Fn { functor, args });
        self.kb.assert_fact(op_term, op_sort, domain, None);
    }

    fn load_constraint(&mut self, c: &Constraint, domain: TermId) {
        let constraint_sort = self.kb.make_name_term("Constraint");
        let constraint_sym = self.kb.intern("Constraint");

        let head_terms: SmallVec<[FnArg; 4]> = c.head
            .iter()
            .map(|&tid| FnArg::Positional(self.convert_term(tid)))
            .collect();

        let mut args: SmallVec<[FnArg; 4]> = SmallVec::new();

        let head_sym = self.kb.intern("head");
        let head_term = self.kb.alloc(Term::Fn {
            functor: head_sym,
            args: head_terms,
        });
        args.push(FnArg::Positional(head_term));

        if let Some(guard) = &c.guard {
            let guard_terms: SmallVec<[FnArg; 4]> = guard
                .iter()
                .map(|&tid| FnArg::Positional(self.convert_term(tid)))
                .collect();
            let guard_sym = self.kb.intern("guard");
            let guard_term = self.kb.alloc(Term::Fn {
                functor: guard_sym,
                args: guard_terms,
            });
            args.push(FnArg::Positional(guard_term));
        }

        let constraint_term = self.kb.alloc(Term::Fn {
            functor: constraint_sym,
            args,
        });

        self.kb.assert_fact(constraint_term, constraint_sort, domain, None);
    }

    fn load_requires_decl(&mut self, r: &RequiresDecl, domain: TermId) {
        let requirement_sort = self.kb.make_name_term("Requirement");
        let requires_sym = self.kb.intern("Requires");
        let type_term = self.type_expr_to_term(&r.type_expr);
        let requires_term = self.kb.alloc(Term::Fn {
            functor: requires_sym,
            args: SmallVec::from_elem(FnArg::Positional(type_term), 1),
        });
        self.kb.assert_fact(requires_term, requirement_sort, domain, None);
    }

    fn load_project(&mut self, p: &Project, domain: TermId) {
        let project_sort = self.kb.make_name_term("Project");
        let functor = self.reintern_name(&p.name);

        let project_term = self.kb.alloc(Term::Fn {
            functor,
            args: SmallVec::new(),
        });

        self.kb.assert_fact(project_term, project_sort, domain, None);
    }

    fn load_tool(&mut self, t: &Tool, domain: TermId) {
        let tool_sort = self.kb.make_name_term("Tool");
        let functor = self.reintern_name(&t.name);

        let cmd_term = self.kb.alloc(Term::Const(super::term::Literal::String(t.command.clone())));
        let cmd_sym = self.kb.intern("command");

        let tool_term = self.kb.alloc(Term::Fn {
            functor,
            args: SmallVec::from_elem(FnArg::Named(cmd_sym, cmd_term), 1),
        });

        self.kb.assert_fact(tool_term, tool_sort, domain, None);
    }

    fn load_workitem(&mut self, w: &WorkItem, domain: TermId) {
        let wi_sort = self.kb.make_name_term("WorkItem");
        let functor = self.reintern_name(&w.id);

        let status_term = self.load_work_status(&w.status);
        let status_sym = self.kb.intern("status");

        let mut args: SmallVec<[FnArg; 4]> = SmallVec::new();
        args.push(FnArg::Named(status_sym, status_term));

        if let Some(desc_id) = w.description {
            let desc = self.convert_term(desc_id);
            let desc_sym = self.kb.intern("description");
            args.push(FnArg::Named(desc_sym, desc));
        }

        let wi_term = self.kb.alloc(Term::Fn { functor, args });

        let meta = w.meta.as_ref().map(|mb| self.load_meta_block(mb));
        self.kb.assert_fact(wi_term, wi_sort, domain, meta);
    }

    fn load_work_status(&mut self, status: &WorkStatus) -> TermId {
        let status_str = match status {
            WorkStatus::Draft => "Draft",
            WorkStatus::Open => "Open",
            WorkStatus::Claimed { .. } => "Claimed",
            WorkStatus::Delivered { .. } => "Delivered",
            WorkStatus::Verified { .. } => "Verified",
            WorkStatus::Rejected { .. } => "Rejected",
            WorkStatus::ProposalRejected { .. } => "ProposalRejected",
            WorkStatus::Stale { .. } => "Stale",
        };
        let sym = self.kb.intern(status_str);
        self.kb.alloc(Term::Ident(sym))
    }

    fn load_feedback(&mut self, f: &Feedback, domain: TermId) {
        let feedback_sort = self.kb.make_name_term("Feedback");
        let feedback_sym = self.kb.intern("Feedback");

        let wi_functor = self.reintern_name(&f.workitem);
        let wi_term = self.kb.alloc(Term::Fn {
            functor: wi_functor,
            args: SmallVec::new(),
        });

        let content_term = self.convert_term(f.content);
        let wi_arg_sym = self.kb.intern("workitem");
        let content_sym = self.kb.intern("content");

        let feedback_term = self.kb.alloc(Term::Fn {
            functor: feedback_sym,
            args: SmallVec::from_slice(&[
                FnArg::Named(wi_arg_sym, wi_term),
                FnArg::Named(content_sym, content_term),
            ]),
        });

        self.kb.assert_fact(feedback_term, feedback_sort, domain, None);
    }

    fn load_import_tools(&mut self, it: &ImportTools, _domain: TermId) {
        for name in &it.names {
            let path = join_segments(&self.parsed.interner, &name.segments);
            if self.loaded_paths.contains(&path) {
                continue; // already loaded or in progress — skip to break cycles
            }
            self.loaded_paths.insert(path.clone());

            match self.resolver.resolve(&path) {
                Ok(source) => {
                    match crate::parse::parse(&source) {
                        Ok(imported) => {
                            if let Err(errs) = load_with_visited(
                                self.kb, &imported, self.resolver, self.loaded_paths,
                            ) {
                                self.errors.extend(errs);
                            }
                        }
                        Err(parse_errs) => {
                            for pe in parse_errs {
                                self.errors.push(LoadError {
                                    message: format!("parse error in import '{}': {}", path, pe.message),
                                });
                            }
                        }
                    }
                }
                Err(e) => {
                    self.errors.push(LoadError {
                        message: format!("cannot resolve import '{}': {}", path, e),
                    });
                }
            }
        }
    }

    // ── Import processing ─────────────────────────────────────

    // ── Member fact emission ───────────────────────────────────

    /// Emit a single member fact: member(name, kind, parent)
    /// with sort = Fn("Member",[]), domain = parent.
    fn emit_member_fact(&mut self, name_sym: Symbol, kind_str: &str, parent: TermId) {
        let member_sym = self.kb.intern("member");
        let member_sort = self.kb.make_name_term("Member");
        let name_term = self.kb.make_name_term_from_sym(name_sym);
        let kind_sym = self.kb.intern(kind_str);
        let kind_term = self.kb.alloc(Term::Ident(kind_sym));
        let member_term = self.kb.alloc(Term::Fn {
            functor: member_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(name_term),
                FnArg::Positional(kind_term),
                FnArg::Positional(parent),
            ]),
        });
        self.kb.assert_fact(member_term, member_sort, parent, None);
    }

    /// Emit member facts for all direct children of a sort/domain.
    fn emit_member_facts_for_items(&mut self, items: &[Item], parent: TermId) {
        for item in items {
            match item {
                Item::Entity(e) => {
                    let sym = self.reintern_name(&e.name);
                    self.emit_member_fact(sym, "Constructor", parent);
                }
                Item::AbstractSort(s) => {
                    let sym = self.reintern_name(&s.name);
                    self.emit_member_fact(sym, "Sort", parent);
                }
                Item::SortWithBody(s) => {
                    let sym = self.reintern_name(&s.name);
                    self.emit_member_fact(sym, "Sort", parent);
                }
                Item::Operation(o) => {
                    let sym = self.reintern_name(&o.name);
                    self.emit_member_fact(sym, "Operation", parent);
                }
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        let sym = self.reintern_name(&op.name);
                        self.emit_member_fact(sym, "Operation", parent);
                    }
                }
                Item::Rule(r) => {
                    if let Some(ref label) = r.label {
                        let sym = self.reintern_name(label);
                        self.emit_member_fact(sym, "Rule", parent);
                    }
                }
                Item::RuleBlock(rb) => {
                    for rule in &rb.entries {
                        if let Some(ref label) = rule.label {
                            let sym = self.reintern_name(label);
                            self.emit_member_fact(sym, "Rule", parent);
                        }
                    }
                }
                Item::Namespace(n) => {
                    let sym = self.reintern_name(&n.name);
                    self.emit_member_fact(sym, "Namespace", parent);
                }
                // Unnamed items: Fact, Constraint, Project, Tool, WorkItem, etc.
                _ => {}
            }
        }
    }

    fn load_meta_block(&mut self, mb: &MetaBlock) -> TermId {
        let meta_sym = self.kb.intern("meta");
        let args: SmallVec<[FnArg; 4]> = mb.entries
            .iter()
            .map(|e| {
                let key_sym = self.reintern(e.key.last());
                let val = self.convert_term(e.value);
                FnArg::Named(key_sym, val)
            })
            .collect();
        self.kb.alloc(Term::Fn {
            functor: meta_sym,
            args,
        })
    }
}
