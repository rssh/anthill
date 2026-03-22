/// IR → KB loading.
///
/// Converts a parsed `ParsedFile` into KnowledgeBase terms and facts.
/// Re-interns symbols, re-allocates terms into the hash-consed store,
/// registers sorts, and asserts facts.
///
/// **Pipeline:** scan_definitions (define all names) → load (fill KB with facts).
///
/// The loader takes a `SourceResolver` to fetch imported files. The CLI
/// provides a real FS implementation; tests use `NullResolver`.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use smallvec::SmallVec;

use crate::intern::{Symbol, SymbolDef, SymbolKind, ScopeInclusion, ResolveResult};
use crate::parse::ir::*;
use crate::span::{Span, SourceId, SourceSpan};
use super::{KnowledgeBase, SortKind};
use super::term::{Term, TermId, VarId, HandleKind, Literal};
use super::occurrence::OccurrenceId;

// ── Source resolution ──────────────────────────────────────────

/// Abstraction over the filesystem for resolving import paths to source text.
pub trait SourceResolver {
    /// Resolve a source path (e.g. `"std/prelude"` or `"./banking"`) to its contents.
    fn resolve(&self, path: &str) -> Result<String, std::io::Error>;
}

/// Resolves import paths by searching filesystem base directories.
///
/// Converts dotted import paths (e.g. `"anthill.prelude.List"`) to filesystem
/// paths (`"anthill/prelude/List.anthill"`) and searches each base directory.
pub struct FileSourceResolver {
    base_dirs: Vec<PathBuf>,
}

impl FileSourceResolver {
    pub fn new(base_dirs: Vec<PathBuf>) -> Self {
        Self { base_dirs }
    }
}

impl SourceResolver for FileSourceResolver {
    fn resolve(&self, path: &str) -> Result<String, std::io::Error> {
        let rel_path = path.replace('.', "/") + ".anthill";
        for base in &self.base_dirs {
            let full = base.join(&rel_path);
            if full.exists() {
                return std::fs::read_to_string(&full);
            }
        }
        Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("cannot resolve '{path}' in base dirs: {:?}", self.base_dirs),
        ))
    }
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

/// Extract the last dot-separated segment from a qualified name.
fn last_segment(qualified: &str) -> &str {
    qualified.rsplit('.').next().unwrap_or(qualified)
}

/// Construct a fully-qualified name by prepending a prefix.
/// If prefix is empty, returns name as-is.
fn make_qualified(prefix: &str, name: &str) -> String {
    if prefix.is_empty() { name.to_owned() } else { format!("{}.{}", prefix, name) }
}

/// Join name segments into a single dot-separated string.
fn join_segments(symbols: &crate::intern::SymbolTable, segments: &[Symbol]) -> String {
    let mut out = String::new();
    for (i, &sym) in segments.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        out.push_str(symbols.name(sym));
    }
    out
}

#[derive(Clone, Debug)]
pub enum LoadError {
    UnresolvedName {
        name: String,
        span: Span,
        scope_name: String,
    },
    UnresolvedImport {
        path: String,
        span: Span,
    },
    AmbiguousSymbol {
        name: String,
        candidates: Vec<String>,
        span: Span,
        scope_name: String,
    },
    Other {
        message: String,
    },
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::UnresolvedName { name, span, scope_name } => {
                write!(f, "unresolved name '{}' in scope '{}' at {}..{}", name, scope_name, span.start, span.end)
            }
            LoadError::UnresolvedImport { path, span } => {
                write!(f, "unresolved import '{}' at {}..{}", path, span.start, span.end)
            }
            LoadError::AmbiguousSymbol { name, candidates, span, scope_name } => {
                write!(f, "ambiguous symbol '{}' in scope '{}' at {}..{}: candidates {:?}", name, scope_name, span.start, span.end, candidates)
            }
            LoadError::Other { message } => {
                write!(f, "load error: {}", message)
            }
        }
    }
}

impl std::error::Error for LoadError {}

// ══════════════════════════════════════════════════════════════════
// Phase 1: Scan definitions
// ══════════════════════════════════════════════════════════════════

/// Scan all parsed files to define symbols (sorts, namespaces, entities,
/// operations, rules) and build the scope inclusion chain (requires, imports).
///
/// Two sub-passes over all files:
/// - Pass 1: Define all names, record exports and type params
/// - Pass 2: Process `requires` and `import` declarations → build parent scope chain
pub fn scan_definitions(kb: &mut KnowledgeBase, files: &[&ParsedFile]) -> Vec<LoadError> {
    let global = kb.make_name_term("_global");

    // Sub-pass 1: define all names
    for file in files {
        scan_items_pass1(kb, &file.items, &file.symbols, &file.terms, global, "");
    }

    // Sub-pass 2: process requires and imports (all sorts exist now)
    let mut errors = Vec::new();
    for file in files {
        scan_items_pass2(kb, &file.items, &file.symbols, global, "", &mut errors);
    }
    errors
}

/// Check if a scope term represents a sort (vs. the global scope or a namespace).
/// Heuristic: if the scope has a symbol defined as Sort kind, it's a sort scope.
fn is_sort_scope(kb: &KnowledgeBase, scope: TermId) -> bool {
    if let Term::Fn { functor, pos_args, named_args } = kb.get_term(scope) {
        if pos_args.is_empty() && named_args.is_empty() {
            if let crate::intern::SymbolDef::Resolved { kind: SymbolKind::Sort, .. } = kb.symbols.get(*functor) {
                return true;
            }
        }
    }
    false
}

/// For a dotted name like `"a.b.C"`, create implicit intermediate namespaces
/// `"a"` and `"a.b"` (if they don't already exist), returning the short name
/// (`"C"`) and the innermost scope (`a.b`'s term).
///
/// If the name has no dots, returns `(full_name, outer_scope)` unchanged.
///
/// `prefix` is the fully-qualified path of the enclosing scope. Intermediate
/// namespaces get qualified names prepended with this prefix.
fn ensure_intermediate_namespaces(
    kb: &mut KnowledgeBase,
    full_name: &str,
    outer_scope: TermId,
    prefix: &str,
) -> (String, TermId) {
    let segments: Vec<&str> = full_name.split('.').collect();
    if segments.len() <= 1 {
        return (full_name.to_owned(), outer_scope);
    }

    let mut current_scope = outer_scope;
    // Process all segments except the last one — each becomes a namespace
    for i in 0..segments.len() - 1 {
        let path: String = segments[..=i].join(".");
        let qualified_path = make_qualified(prefix, &path);
        let short = segments[i];

        // Check if this namespace already exists in the current scope
        let existing = kb.symbols.by_qualified_name.get(&qualified_path).copied().filter(|&sym| {
            matches!(
                kb.symbols.get(sym),
                SymbolDef::Resolved { kind: SymbolKind::Namespace, scope_raw, .. }
                if *scope_raw == current_scope.raw()
            )
        });

        let ns_term = if let Some(sym) = existing {
            // Reuse existing namespace
            kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            })
        } else {
            // Create implicit namespace
            let sym = kb.symbols.define(short, &qualified_path, SymbolKind::Namespace, current_scope.raw());
            let ns_term = kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            // Enclosing scope is visible from within this namespace
            kb.symbols.add_parent(ns_term.raw(), ScopeInclusion {
                parent_scope_raw: current_scope.raw(),
                instantiation_term_raw: current_scope.raw(),
                is_enclosing: true,
            });
            ns_term
        };

        current_scope = ns_term;
    }

    (segments.last().unwrap().to_string(), current_scope)
}

/// Create an operation scope and define its parameters.
///
/// Operations get their own scope so that parameter names are resolvable
/// in effects clauses (e.g., `effects (Modify[store])` where `store` is a parameter).
fn scan_operation_params(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    op: &Operation,
    op_sym: Symbol,
    enclosing_scope: TermId,
    prefix: &str,
) {
    if op.params.is_empty() {
        return;
    }
    // Allocate a scope term for the operation
    let op_term = kb.alloc(Term::Fn {
        functor: op_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    // Operation scope sees enclosing scope
    kb.symbols.add_parent(op_term.raw(), ScopeInclusion {
        parent_scope_raw: enclosing_scope.raw(),
        instantiation_term_raw: enclosing_scope.raw(),
        is_enclosing: true,
    });
    // Define each parameter in the operation's scope
    for p in &op.params {
        let param_name = parse_sym.name(p.name);
        let qualified = format!("{}.{}", prefix, param_name);
        kb.symbols.define(param_name, &qualified, SymbolKind::Param, op_term.raw());
    }
}

/// Sub-pass 1: define all names, record exports and type params.
///
/// `prefix` is the fully-qualified path of the enclosing scope (empty at top level).
/// Nested items get `qualified_name = prefix + "." + name`.
/// Define a rule's label and head functor as scoped symbols.
fn scan_rule(
    kb: &mut KnowledgeBase,
    r: &Rule,
    parse_sym: &crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
    scope: TermId,
    prefix: &str,
) {
    if let Some(ref label) = r.label {
        let name = join_segments(parse_sym, &label.segments);
        let qualified = make_qualified(prefix, &name);
        kb.symbols.define(&name, &qualified, SymbolKind::Rule, scope.raw());
    }
    if let Some(functor_name) = rule_head_functor_name(r, parse_sym, parse_terms) {
        let qualified = make_qualified(prefix, functor_name);
        kb.symbols.define(functor_name, &qualified, SymbolKind::Goal, scope.raw());
    }
}

/// Extract the head functor name from a rule, if the head is a Fn term.
fn rule_head_functor_name<'a>(
    r: &Rule,
    parse_sym: &'a crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
) -> Option<&'a str> {
    match &r.head {
        RuleHead::Term(tid) => {
            if let Term::Fn { functor, .. } = parse_terms.get(*tid) {
                Some(parse_sym.name(*functor))
            } else {
                None
            }
        }
        RuleHead::Bottom => None,
    }
}

fn scan_items_pass1(
    kb: &mut KnowledgeBase,
    items: &[Item],
    parse_sym: &crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
    scope: TermId,
    prefix: &str,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                // Reuse existing sort symbol if already defined (e.g. by register_prelude)
                let (sym, is_new) = if let Some(&existing) = kb.symbols.by_qualified_name.get(&qualified) {
                    (existing, false)
                } else {
                    (kb.symbols.define(&short, &qualified, SymbolKind::Sort, actual_scope.raw()), true)
                };
                let sort_term = kb.alloc(Term::Fn {
                    functor: sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                });
                if is_new {
                    // Implicit parent: the enclosing scope is visible from within the sort
                    kb.symbols.add_parent(sort_term.raw(), ScopeInclusion {
                        parent_scope_raw: actual_scope.raw(),
                        instantiation_term_raw: actual_scope.raw(),
                        is_enclosing: true,
                    });
                }
                // Record exports (additive — safe to re-apply)
                for export_name in &s.exports {
                    let n = join_segments(parse_sym, &export_name.segments);
                    kb.symbols.add_export(sort_term.raw(), &n);
                }
                // Recurse into sort body with the sort's qualified name as prefix
                scan_items_pass1(kb, &s.items, parse_sym, parse_terms, sort_term, &qualified);
            }
            Item::AbstractSort(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                let _sym = kb.symbols.define(&short, &qualified, SymbolKind::Sort, actual_scope.raw());
                // `sort T = ?` inside a SortWithBody = type parameter
                if matches!(s.definition, TypeExpr::Variable { .. }) && is_sort_scope(kb, scope) {
                    kb.symbols.add_type_param(scope.raw(), &short);
                }
            }
            Item::Namespace(n) => {
                let name = join_segments(parse_sym, &n.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                // Reuse existing namespace symbol if already defined in the same scope
                // (multiple files can contribute items to the same namespace).
                let existing = kb.symbols.by_qualified_name.get(&qualified).copied().filter(|&sym| {
                    matches!(
                        kb.symbols.get(sym),
                        SymbolDef::Resolved { kind: SymbolKind::Namespace, scope_raw, .. }
                        if *scope_raw == actual_scope.raw()
                    )
                });
                let (_sym, ns_term) = if let Some(sym) = existing {
                    let ns_term = kb.alloc(Term::Fn {
                        functor: sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::new(),
                    });
                    (sym, ns_term)
                } else {
                    let sym = kb.symbols.define(&short, &qualified, SymbolKind::Namespace, actual_scope.raw());
                    let ns_term = kb.alloc(Term::Fn {
                        functor: sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::new(),
                    });
                    // Implicit parent: the enclosing scope is visible from within the namespace
                    kb.symbols.add_parent(ns_term.raw(), ScopeInclusion {
                        parent_scope_raw: actual_scope.raw(),
                        instantiation_term_raw: actual_scope.raw(),
                        is_enclosing: true,
                    });
                    (sym, ns_term)
                };
                // Record exports (merge for existing namespaces)
                for export_name in &n.exports {
                    let en = join_segments(parse_sym, &export_name.segments);
                    kb.symbols.add_export(ns_term.raw(), &en);
                }
                // Recurse into namespace body with the namespace's qualified name as prefix
                scan_items_pass1(kb, &n.items, parse_sym, parse_terms, ns_term, &qualified);
            }
            Item::Entity(e) => {
                let name = join_segments(parse_sym, &e.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                // Reuse existing entity symbol if already defined (e.g. by register_prelude)
                if !kb.symbols.by_qualified_name.contains_key(&qualified) {
                    kb.symbols.define(&short, &qualified, SymbolKind::Entity, actual_scope.raw());
                }
            }
            Item::Operation(o) => {
                let name = join_segments(parse_sym, &o.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                let op_sym = kb.symbols.define(&short, &qualified, SymbolKind::Operation, actual_scope.raw());
                scan_operation_params(kb, parse_sym, o, op_sym, actual_scope, &qualified);
            }
            Item::OperationBlock(ob) => {
                for op in &ob.entries {
                    let name = join_segments(parse_sym, &op.name.segments);
                    let qualified = make_qualified(prefix, &name);
                    let op_sym = kb.symbols.define(&name, &qualified, SymbolKind::Operation, scope.raw());
                    scan_operation_params(kb, parse_sym, op, op_sym, scope, &qualified);
                }
            }
            Item::Rule(r) => {
                scan_rule(kb, r, parse_sym, parse_terms, scope, prefix);
            }
            Item::RuleBlock(rb) => {
                for rule in &rb.entries {
                    scan_rule(kb, rule, parse_sym, parse_terms, scope, prefix);
                }
            }
            Item::Constraint(_) => {
                // Constraints don't define named symbols
            }
            // Stage 0 items, facts, requires — handled elsewhere or not names
            _ => {}
        }
    }
}

/// Sub-pass 2: process requires declarations and imports → build parent scope chain.
///
/// `prefix` is the fully-qualified path of the enclosing scope (empty at top level).
fn scan_items_pass2(
    kb: &mut KnowledgeBase,
    items: &[Item],
    parse_sym: &crate::intern::SymbolTable,
    scope: TermId,
    prefix: &str,
    errors: &mut Vec<LoadError>,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(sort_term) = find_scope_by_name(kb, &qualified) {
                    // Process sort-level imports
                    process_imports(kb, parse_sym, &s.imports, sort_term, errors);
                    // Recurse
                    scan_items_pass2(kb, &s.items, parse_sym, sort_term, &qualified, errors);
                }
            }
            Item::Namespace(n) => {
                let name = join_segments(parse_sym, &n.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(ns_term) = find_scope_by_name(kb, &qualified) {
                    // Process namespace-level imports
                    process_imports(kb, parse_sym, &n.imports, ns_term, errors);
                    // Recurse
                    scan_items_pass2(kb, &n.items, parse_sym, ns_term, &qualified, errors);
                }
            }
            Item::RequiresDecl(r) => {
                let req_sort_name = type_expr_base_name(parse_sym, &r.type_expr);
                // Use scope-aware resolution first (handles imported/aliased names),
                // falling back to qualified-name lookup.
                let req_scope = resolve_name_to_scope(kb, &req_sort_name, scope)
                    .or_else(|| find_scope_by_name(kb, &req_sort_name));
                if let Some(req_scope) = req_scope {
                    // Create instantiation term
                    let inst_term = build_instantiation_term(kb, parse_sym, &r.type_expr, scope);
                    kb.symbols.add_parent(scope.raw(), ScopeInclusion {
                        parent_scope_raw: req_scope.raw(),
                        instantiation_term_raw: inst_term.raw(),
                        is_enclosing: false,
                    });
                }
            }
            _ => {}
        }
    }
}

/// Get the base name of a TypeExpr (ignoring bindings).
fn type_expr_base_name(parse_sym: &crate::intern::SymbolTable, ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Simple(name) => join_segments(parse_sym, &name.segments),
        TypeExpr::Parameterized { name, .. } => join_segments(parse_sym, &name.segments),
        TypeExpr::Variable { .. } => "?".to_owned(),
        TypeExpr::Tuple(_) => "TupleLiteral".to_owned(),
        TypeExpr::Arrow { effect: Some(_), .. } => "arrow_effect".to_owned(),
        TypeExpr::Arrow { .. } => "arrow".to_owned(),
    }
}

/// Resolve a name in the given scope context, returning a scope TermId.
/// Uses the full scope-aware resolution chain (locals, imports, parents).
fn resolve_name_to_scope(kb: &mut KnowledgeBase, name: &str, scope: TermId) -> Option<TermId> {
    match kb.symbols.resolve_in_scope(name, scope.raw()) {
        crate::intern::ResolveResult::Found(sym) => {
            Some(kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            }))
        }
        _ => None,
    }
}

/// Find a scope TermId by looking up a qualified name in the symbol table,
/// then reconstructing the nullary Fn term.
fn find_scope_by_name(kb: &mut KnowledgeBase, qualified: &str) -> Option<TermId> {
    let sym = *kb.symbols.by_qualified_name.get(qualified)?;
    Some(kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    }))
}

/// Build an instantiation term for `requires Eq[T]`.
fn build_instantiation_term(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    type_expr: &TypeExpr,
    _current_scope: TermId,
) -> TermId {
    match type_expr {
        TypeExpr::Simple(name) => {
            let n = join_segments(parse_sym, &name.segments);
            find_scope_by_name(kb, &n)
                .unwrap_or_else(|| kb.make_name_term(&n))
        }
        TypeExpr::Parameterized { name, bindings } => {
            let sort_name = join_segments(parse_sym, &name.segments);
            let sort_sym = kb.symbols.by_qualified_name.get(&sort_name).copied()
                .unwrap_or_else(|| kb.symbols.intern(&sort_name));
            let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
            let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            for b in bindings {
                let val = build_instantiation_term(kb, parse_sym, &b.bound, _current_scope);
                match &b.param {
                    Some(p) => {
                        let key = kb.symbols.intern(&join_segments(parse_sym, &p.segments));
                        named_args.push((key, val));
                    }
                    None => {
                        pos_args.push(val);
                    }
                }
            }
            kb.alloc(Term::Fn {
                functor: sort_sym,
                pos_args,
                named_args,
            })
        }
        TypeExpr::Variable { .. } => {
            // Variable in type position → just use a placeholder name term
            kb.make_name_term("?")
        }
        TypeExpr::Tuple(fields) => {
            let tuple_sym = kb.symbols.by_qualified_name.get("anthill.reflect.TupleLiteral").copied()
                .unwrap_or_else(|| kb.symbols.intern("TupleLiteral"));
            let named_args: SmallVec<[(Symbol, TermId); 2]> = fields.iter().map(|(sym, ty)| {
                let key = kb.symbols.intern(parse_sym.name(*sym));
                let val = build_instantiation_term(kb, parse_sym, ty, _current_scope);
                (key, val)
            }).collect();
            kb.alloc(Term::Fn {
                functor: tuple_sym,
                pos_args: SmallVec::new(),
                named_args,
            })
        }
        TypeExpr::Arrow { params, return_type, effect } => {
            let functor = if effect.is_some() {
                kb.symbols.intern("arrow_effect")
            } else {
                kb.symbols.intern("arrow")
            };
            let mut pos_args: SmallVec<[TermId; 4]> = params.iter()
                .map(|p| build_instantiation_term(kb, parse_sym, p, _current_scope))
                .collect();
            let ret = build_instantiation_term(kb, parse_sym, return_type, _current_scope);
            pos_args.push(ret);
            if let Some(eff) = effect {
                let eff_term = build_instantiation_term(kb, parse_sym, eff, _current_scope);
                pos_args.push(eff_term);
            }
            kb.alloc(Term::Fn {
                functor,
                pos_args,
                named_args: SmallVec::new(),
            })
        }
    }
}

/// Process `import` declarations → register imported names and parent scopes.
/// Unresolvable import paths produce errors.
fn process_imports(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    imports: &[Import],
    scope: TermId,
    errors: &mut Vec<LoadError>,
) {
    for imp in imports {
        let path = join_segments(parse_sym, &imp.path.segments);
        match &imp.kind {
            ImportKind::Plain => {
                // `import anthill.prelude.List` → make "List" resolvable locally
                // and add the target scope as a parent for accessing its contents.
                let found = kb.symbols.by_qualified_name.get(&path).copied();
                if let Some(original_sym) = found {
                    let short = last_segment(&path);
                    kb.symbols.add_import(scope.raw(), short, original_sym);
                }
                if let Some(target_scope) = find_scope_by_name(kb, &path) {
                    kb.symbols.add_parent(scope.raw(), ScopeInclusion {
                        parent_scope_raw: target_scope.raw(),
                        instantiation_term_raw: target_scope.raw(),
                        is_enclosing: false,
                    });
                } else if found.is_none() {
                    errors.push(LoadError::UnresolvedImport {
                        path: path.clone(),
                        span: imp.path.span,
                    });
                }
            }
            ImportKind::Selective(names) => {
                // `import anthill.prelude.{Eq, Ordered}` → for each name,
                // register a local alias. Parent-scope links are NOT added here —
                // if sort contents (operations) are needed, use `requires` or
                // wildcard import (`import path.*`) instead.
                //
                // Two strategies for finding the symbol:
                // 1. Direct qualified-name lookup (e.g., "anthill.prelude.Eq" as a
                //    top-level dotted name)
                // 2. Resolve short name within the base-path scope (e.g., "Term"
                //    defined inside `namespace anthill.reflect`)
                let base_scope = find_scope_by_name(kb, &path);
                if base_scope.is_none() && !kb.symbols.by_qualified_name.contains_key(&path) {
                    // The base path itself doesn't resolve
                    errors.push(LoadError::UnresolvedImport {
                        path: path.clone(),
                        span: imp.path.span,
                    });
                }
                for name in names {
                    let short = join_segments(parse_sym, &name.segments);
                    let qualified = format!("{}.{}", path, short);
                    // Try qualified lookup first, then resolve within base scope
                    let original_sym = kb.symbols.by_qualified_name.get(&qualified).copied()
                        .or_else(|| {
                            base_scope.and_then(|bs| {
                                match kb.symbols.resolve_in_scope(&short, bs.raw()) {
                                    crate::intern::ResolveResult::Found(sym) => Some(sym),
                                    _ => None,
                                }
                            })
                        });
                    if let Some(sym) = original_sym {
                        kb.symbols.add_import(scope.raw(), &short, sym);
                    } else {
                        errors.push(LoadError::UnresolvedImport {
                            path: qualified,
                            span: name.span,
                        });
                    }
                }
            }
            ImportKind::Wildcard => {
                if let Some(target_scope) = find_scope_by_name(kb, &path) {
                    kb.symbols.add_parent(scope.raw(), ScopeInclusion {
                        parent_scope_raw: target_scope.raw(),
                        instantiation_term_raw: target_scope.raw(),
                        is_enclosing: false,
                    });
                } else {
                    errors.push(LoadError::UnresolvedImport {
                        path: path.clone(),
                        span: imp.path.span,
                    });
                }
            }
        }
    }
}

// ── Prelude: built-in primitive sorts ────────────────────────────

/// Primitive sort names that are always available in the global scope.
/// These correspond to the stdlib primitive types (Int, Float, String, Bool).
pub const PRELUDE_SORTS: &[&str] = &["Int", "BigInt", "Float", "String", "Bool"];

/// KB-internal meta-sort names. Used as sort-of-sort markers (e.g. the sort
/// of a Fact entry is `Fact`). Not defined in any `.anthill` file.
const KERNEL_META_SORTS: &[&str] = &[
    "Sort", "Entity", "Fact", "Rule", "Operation", "Namespace",
    "Requirement", "Description", "Constraint", "Member",
];

/// KB-internal functor names used by the loader to construct fact terms.
/// Not defined in any `.anthill` file.
/// (EntityInfo and SortRequiresInfo are now declared in reflect.anthill.)
const KERNEL_FUNCTORS: &[&str] = &[
    "SortAlias",
    "member", "meta",
];

/// Register primitive sorts and kernel vocabulary in the global scope,
/// plus stdlib scope hierarchy for loader-referenced names.
///
/// Call this before `scan_definitions` / `load` to ensure that references to
/// `Int`, `Float`, `String`, `Bool` never produce unresolved-name errors,
/// and that all loader-internal functor names are resolvable.
///
/// Stdlib names (`cons`, `nil`, `some`, `none`, `SortInfo`, `FieldInfo`,
/// `OperationInfo`) are defined in their correct scopes with proper
/// qualified names, matching what `scan_definitions` would produce from
/// the stdlib `.anthill` files.  `scan_definitions` is idempotent for these
/// entries and will reuse the existing symbols.
pub fn register_prelude(kb: &mut KnowledgeBase) {
    let global = kb.make_name_term("_global");
    let global_raw = global.raw();
    for &name in PRELUDE_SORTS {
        if !kb.symbols.by_qualified_name.contains_key(name) {
            kb.symbols.define(name, name, SymbolKind::Sort, global_raw);
        }
    }
    for &name in KERNEL_META_SORTS {
        if !kb.symbols.by_qualified_name.contains_key(name) {
            kb.symbols.define(name, name, SymbolKind::Sort, global_raw);
        }
    }
    for &name in KERNEL_FUNCTORS {
        if !kb.symbols.by_qualified_name.contains_key(name) {
            kb.symbols.define(name, name, SymbolKind::Entity, global_raw);
        }
    }
    // Stdlib scope hierarchy: create scopes with correct qualified names
    // so the loader's resolve_symbol() finds names in the right scopes.
    // Idempotent: skipped on re-entry or when stdlib has already been scanned.
    register_stdlib_scopes(kb, global_raw);
    // Register builtin operations (eq, gt, add, etc.) for the resolver.
    kb.register_standard_builtins();
}

/// Create the stdlib scope hierarchy for names the loader references directly.
///
/// Mirrors the structure of `stdlib/anthill/prelude/{list,option}.anthill`
/// and `stdlib/anthill/reflect/reflect.anthill` so that `resolve_symbol("anthill.prelude.List.cons")`
/// etc. return properly-scoped symbols. When the real stdlib is loaded,
/// `scan_definitions` reuses these symbols (idempotent by qualified name).
fn register_stdlib_scopes(kb: &mut KnowledgeBase, global_raw: u32) {
    // Guard: if "anthill" already exists, the whole hierarchy is set up
    if kb.symbols.by_qualified_name.contains_key("anthill") {
        return;
    }

    // anthill namespace
    let anthill_sym = kb.symbols.define("anthill", "anthill", SymbolKind::Namespace, global_raw);
    let anthill_term = kb.alloc(Term::Fn {
        functor: anthill_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(anthill_term.raw(), ScopeInclusion {
        parent_scope_raw: global_raw,
        instantiation_term_raw: global_raw,
        is_enclosing: true,
    });

    // anthill.prelude namespace
    let prelude_sym = kb.symbols.define("prelude", "anthill.prelude", SymbolKind::Namespace, anthill_term.raw());
    let prelude_term = kb.alloc(Term::Fn {
        functor: prelude_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(prelude_term.raw(), ScopeInclusion {
        parent_scope_raw: anthill_term.raw(),
        instantiation_term_raw: anthill_term.raw(),
        is_enclosing: true,
    });

    // anthill.prelude.List sort
    let list_sym = kb.symbols.define("List", "anthill.prelude.List", SymbolKind::Sort, prelude_term.raw());
    let list_term = kb.alloc(Term::Fn {
        functor: list_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(list_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    let cons_sym = kb.symbols.define("cons", "anthill.prelude.List.cons", SymbolKind::Entity, list_term.raw());
    let nil_sym = kb.symbols.define("nil", "anthill.prelude.List.nil", SymbolKind::Entity, list_term.raw());

    // anthill.prelude.Option sort
    let option_sym = kb.symbols.define("Option", "anthill.prelude.Option", SymbolKind::Sort, prelude_term.raw());
    let option_term = kb.alloc(Term::Fn {
        functor: option_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(option_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    let some_sym = kb.symbols.define("some", "anthill.prelude.Option.some", SymbolKind::Entity, option_term.raw());
    let none_sym = kb.symbols.define("none", "anthill.prelude.Option.none", SymbolKind::Entity, option_term.raw());

    // anthill.prelude.Eq sort (operations: eq, neq)
    let eq_sort_sym = kb.symbols.define("Eq", "anthill.prelude.Eq", SymbolKind::Sort, prelude_term.raw());
    let eq_sort_term = kb.alloc(Term::Fn {
        functor: eq_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(eq_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("eq", "anthill.prelude.Eq.eq", SymbolKind::Operation, eq_sort_term.raw());
    kb.symbols.define("neq", "anthill.prelude.Eq.neq", SymbolKind::Operation, eq_sort_term.raw());

    // anthill.prelude.Ordered sort (operations: compare, gt, lt, gte, lte, max, min)
    let ord_sort_sym = kb.symbols.define("Ordered", "anthill.prelude.Ordered", SymbolKind::Sort, prelude_term.raw());
    let ord_sort_term = kb.alloc(Term::Fn {
        functor: ord_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(ord_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("compare", "anthill.prelude.Ordered.compare", SymbolKind::Operation, ord_sort_term.raw());
    kb.symbols.define("gt", "anthill.prelude.Ordered.gt", SymbolKind::Operation, ord_sort_term.raw());
    kb.symbols.define("lt", "anthill.prelude.Ordered.lt", SymbolKind::Operation, ord_sort_term.raw());
    kb.symbols.define("gte", "anthill.prelude.Ordered.gte", SymbolKind::Operation, ord_sort_term.raw());
    kb.symbols.define("lte", "anthill.prelude.Ordered.lte", SymbolKind::Operation, ord_sort_term.raw());

    // anthill.prelude.Numeric sort (operations: add, sub, mul)
    let num_sort_sym = kb.symbols.define("Numeric", "anthill.prelude.Numeric", SymbolKind::Sort, prelude_term.raw());
    let num_sort_term = kb.alloc(Term::Fn {
        functor: num_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(num_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("add", "anthill.prelude.Numeric.add", SymbolKind::Operation, num_sort_term.raw());
    kb.symbols.define("sub", "anthill.prelude.Numeric.sub", SymbolKind::Operation, num_sort_term.raw());
    kb.symbols.define("mul", "anthill.prelude.Numeric.mul", SymbolKind::Operation, num_sort_term.raw());

    // anthill.prelude.BigInt namespace (conversion operations)
    let bigint_ns_sym = kb.symbols.define("BigInt", "anthill.prelude.BigInt", SymbolKind::Namespace, prelude_term.raw());
    let bigint_ns_term = kb.alloc(Term::Fn {
        functor: bigint_ns_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(bigint_ns_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("to_bigint", "anthill.prelude.BigInt.to_bigint", SymbolKind::Operation, bigint_ns_term.raw());
    kb.symbols.define("to_int", "anthill.prelude.BigInt.to_int", SymbolKind::Operation, bigint_ns_term.raw());

    // anthill.reflect namespace
    let reflect_sym = kb.symbols.define("reflect", "anthill.reflect", SymbolKind::Namespace, anthill_term.raw());
    let reflect_term = kb.alloc(Term::Fn {
        functor: reflect_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(reflect_term.raw(), ScopeInclusion {
        parent_scope_raw: anthill_term.raw(),
        instantiation_term_raw: anthill_term.raw(),
        is_enclosing: true,
    });
    let sort_info_sym = kb.symbols.define("SortInfo", "anthill.reflect.SortInfo", SymbolKind::Entity, reflect_term.raw());
    let field_info_sym = kb.symbols.define("FieldInfo", "anthill.reflect.FieldInfo", SymbolKind::Entity, reflect_term.raw());
    let op_info_sym = kb.symbols.define("OperationInfo", "anthill.reflect.OperationInfo", SymbolKind::Entity, reflect_term.raw());
    let entity_info_sym = kb.symbols.define("EntityInfo", "anthill.reflect.EntityInfo", SymbolKind::Entity, reflect_term.raw());
    let sort_requires_info_sym = kb.symbols.define("SortRequiresInfo", "anthill.reflect.SortRequiresInfo", SymbolKind::Entity, reflect_term.raw());
    let sort_view_sym = kb.symbols.define("SortView", "anthill.reflect.SortView", SymbolKind::Entity, reflect_term.raw());
    let set_literal_sym = kb.symbols.define("SetLiteral", "anthill.reflect.SetLiteral", SymbolKind::Entity, reflect_term.raw());
    let tuple_literal_sym = kb.symbols.define("TupleLiteral", "anthill.reflect.TupleLiteral", SymbolKind::Entity, reflect_term.raw());
    let list_literal_sym = kb.symbols.define("ListLiteral", "anthill.reflect.ListLiteral", SymbolKind::Entity, reflect_term.raw());

    // anthill.reflect.Expr sort + entities
    let expr_sym = kb.symbols.define("Expr", "anthill.reflect.Expr", SymbolKind::Sort, reflect_term.raw());
    let expr_term = kb.alloc(Term::Fn {
        functor: expr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(expr_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("match_expr", "anthill.reflect.Expr.match_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("if_expr", "anthill.reflect.Expr.if_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("let_expr", "anthill.reflect.Expr.let_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("lambda", "anthill.reflect.Expr.lambda", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("apply", "anthill.reflect.Expr.apply", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("constructor", "anthill.reflect.Expr.constructor", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("var_ref", "anthill.reflect.Expr.var_ref", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("int_lit", "anthill.reflect.Expr.int_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("bigint_lit", "anthill.reflect.Expr.bigint_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("float_lit", "anthill.reflect.Expr.float_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("string_lit", "anthill.reflect.Expr.string_lit", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("bool_lit", "anthill.reflect.Expr.bool_lit", SymbolKind::Entity, expr_term.raw());

    // anthill.reflect.Pattern sort + entities
    let pattern_sym = kb.symbols.define("Pattern", "anthill.reflect.Pattern", SymbolKind::Sort, reflect_term.raw());
    let pattern_term = kb.alloc(Term::Fn {
        functor: pattern_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(pattern_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("var_pattern", "anthill.reflect.Pattern.var_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("tuple_pattern", "anthill.reflect.Pattern.tuple_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("named_tuple_pattern", "anthill.reflect.Pattern.named_tuple_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("constructor_pattern", "anthill.reflect.Pattern.constructor_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("literal_pattern", "anthill.reflect.Pattern.literal_pattern", SymbolKind::Entity, pattern_term.raw());
    kb.symbols.define("wildcard", "anthill.reflect.Pattern.wildcard", SymbolKind::Entity, pattern_term.raw());

    // anthill.reflect standalone entities for expressions
    kb.symbols.define("MatchBranch", "anthill.reflect.MatchBranch", SymbolKind::Entity, reflect_term.raw());
    kb.symbols.define("ApplyArg", "anthill.reflect.ApplyArg", SymbolKind::Entity, reflect_term.raw());

    // anthill.reflect.TypedExpr sort
    let typed_expr_sym = kb.symbols.define("TypedExpr", "anthill.reflect.TypedExpr", SymbolKind::Sort, reflect_term.raw());
    let typed_expr_term = kb.alloc(Term::Fn {
        functor: typed_expr_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(typed_expr_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("typed", "anthill.reflect.TypedExpr.typed", SymbolKind::Entity, typed_expr_term.raw());

    // anthill.reflect.typing namespace
    let typing_sym = kb.symbols.define("typing", "anthill.reflect.typing", SymbolKind::Namespace, reflect_term.raw());
    let typing_term = kb.alloc(Term::Fn {
        functor: typing_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(typing_term.raw(), ScopeInclusion {
        parent_scope_raw: reflect_term.raw(),
        instantiation_term_raw: reflect_term.raw(),
        is_enclosing: true,
    });

    // Global imports: make fundamental constructors visible from any scope
    // that walks up to _global (like Haskell's Prelude auto-import).
    kb.symbols.add_import(global_raw, "cons", cons_sym);
    kb.symbols.add_import(global_raw, "nil", nil_sym);
    kb.symbols.add_import(global_raw, "some", some_sym);
    kb.symbols.add_import(global_raw, "none", none_sym);
    kb.symbols.add_import(global_raw, "SortInfo", sort_info_sym);
    kb.symbols.add_import(global_raw, "FieldInfo", field_info_sym);
    kb.symbols.add_import(global_raw, "OperationInfo", op_info_sym);
    kb.symbols.add_import(global_raw, "EntityInfo", entity_info_sym);
    kb.symbols.add_import(global_raw, "SortRequiresInfo", sort_requires_info_sym);
    kb.symbols.add_import(global_raw, "SortView", sort_view_sym);
    kb.symbols.add_import(global_raw, "SetLiteral", set_literal_sym);
    kb.symbols.add_import(global_raw, "TupleLiteral", tuple_literal_sym);
    kb.symbols.add_import(global_raw, "ListLiteral", list_literal_sym);
    // Arithmetic and comparison: globally importable (like Haskell Prelude).
    // Qualified names are guaranteed present — defined above in this function.
    for (qualified, short) in [
        ("anthill.prelude.Eq.eq", "eq"),
        ("anthill.prelude.Eq.neq", "neq"),
        ("anthill.prelude.Ordered.gt", "gt"),
        ("anthill.prelude.Ordered.lt", "lt"),
        ("anthill.prelude.Ordered.gte", "gte"),
        ("anthill.prelude.Ordered.lte", "lte"),
        ("anthill.prelude.Numeric.add", "add"),
        ("anthill.prelude.Numeric.sub", "sub"),
        ("anthill.prelude.Numeric.mul", "mul"),
        ("anthill.prelude.BigInt.to_bigint", "to_bigint"),
        ("anthill.prelude.BigInt.to_int", "to_int"),
    ] {
        let sym = kb.symbols.by_qualified_name[qualified];
        kb.symbols.add_import(global_raw, short, sym);
    }
}

// ══════════════════════════════════════════════════════════════════
// Phase 2: Load into KB
// ══════════════════════════════════════════════════════════════════

/// Load a parsed file into the knowledge base.
///
/// Scans definitions first, then loads facts into the KB.
pub fn load(
    kb: &mut KnowledgeBase,
    parsed: &ParsedFile,
    resolver: &dyn SourceResolver,
) -> Result<(), Vec<LoadError>> {
    // Ensure kernel vocabulary is registered (idempotent)
    register_prelude(kb);
    // Phase 1: Scan definitions from this file
    let mut all_errors = scan_definitions(kb, &[parsed]);
    kb.resolve_builtins();
    // Phase 2: Load
    let mut loaded_paths = HashSet::new();
    if let Err(errs) = load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
        all_errors.extend(errs);
    }
    // Phase 3: Resolve instantiations
    resolve_instantiations(kb);
    if all_errors.is_empty() {
        Ok(())
    } else {
        Err(all_errors)
    }
}

/// Load multiple parsed files into the same knowledge base.
///
/// Scans ALL files for definitions first, then loads them. This ensures
/// cross-file references resolve correctly regardless of load order.
pub fn load_all(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<(), Vec<LoadError>> {
    // Ensure kernel vocabulary is registered (idempotent)
    register_prelude(kb);
    // Phase 1: Scan all definitions across all files
    let mut all_errors = scan_definitions(kb, files);
    kb.resolve_builtins();

    // Phase 2: Load files with scope-aware resolution
    let mut loaded_paths = HashSet::new();
    for parsed in files {
        if let Err(errs) = load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
            all_errors.extend(errs);
        }
    }
    // Phase 3: Resolve instantiations
    resolve_instantiations(kb);
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
    let global = kb.make_name_term("_global");
    let mut loader = Loader::new(kb, parsed, resolver, loaded_paths, global);
    loader.load_items(&parsed.items, None);

    if loader.errors.is_empty() {
        Ok(())
    } else {
        Err(loader.errors)
    }
}

// ══════════════════════════════════════════════════════════════════
// Phase 3: Resolve instantiation bindings
// ══════════════════════════════════════════════════════════════════

/// Complete all ParameterizedType substitutions in SortRequiresInfo facts.
///
/// Called after load: (1) builds base substitutions from SortInfo facts,
/// (2) for each SortRequiresInfo fact, completes spec_inst with explicit bindings
/// and auto-bound same-named operations from the requiring sort's scope.
pub fn resolve_instantiations(kb: &mut KnowledgeBase) {
    build_base_substitutions(kb);
    resolve_requires_bindings(kb);
}

/// Build base substitution for each sort from its SortInfo fact.
///
/// The base substitution maps every slot (parameter + operation) to itself:
/// `{T → Ref(T), combine → Ref(combine), identity → Ref(identity)}`.
fn build_base_substitutions(kb: &mut KnowledgeBase) {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(sym) => sym,
        None => return,
    };

    let rule_ids = kb.by_functor(sort_info_sym);
    let mut sort_entries: Vec<(Symbol, Vec<(Symbol, TermId)>)> = Vec::new();

    for rid in rule_ids {
        if !kb.rule_body(rid).is_empty() {
            continue; // skip rules, only process facts
        }
        let head = kb.rule_head(rid);
        let term = kb.get_term(head).clone();
        if let Term::Fn { named_args, .. } = term {
            // Extract sort name symbol
            let name_sym = kb.intern("name");
            let parameters_sym = kb.intern("parameters");
            let operations_sym = kb.intern("operations");

            let sort_functor_sym = named_args.iter()
                .find(|(s, _)| *s == name_sym)
                .and_then(|(_, tid)| match kb.get_term(*tid) {
                    Term::Ref(sym) => Some(*sym),
                    _ => None,
                });

            let params_list_tid = named_args.iter()
                .find(|(s, _)| *s == parameters_sym)
                .map(|(_, tid)| *tid);

            let ops_list_tid = named_args.iter()
                .find(|(s, _)| *s == operations_sym)
                .map(|(_, tid)| *tid);

            if let Some(sort_sym) = sort_functor_sym {
                let mut base_subst = Vec::new();

                // Collect params
                if let Some(list_tid) = params_list_tid {
                    collect_ref_list(kb, list_tid, &mut base_subst);
                }

                // Collect operations
                if let Some(list_tid) = ops_list_tid {
                    collect_ref_list(kb, list_tid, &mut base_subst);
                }

                sort_entries.push((sort_sym, base_subst));
            }
        }
    }

    for (sym, subst) in sort_entries {
        kb.set_sort_base_subst(sym, subst);
    }
}

/// Walk a cons-list and collect (sym, Ref(sym)) pairs for each Ref element.
fn collect_ref_list(kb: &mut KnowledgeBase, list_tid: TermId, out: &mut Vec<(Symbol, TermId)>) {
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let mut current = list_tid;
    loop {
        match kb.get_term(current).clone() {
            Term::Fn { ref functor, ref named_args, .. } => {
                if *functor == nil_sym {
                    break;
                }
                if *functor == cons_sym {
                    let head_tid = named_args.iter()
                        .find(|(s, _)| *s == head_sym)
                        .map(|(_, t)| *t);
                    let tail_tid = named_args.iter()
                        .find(|(s, _)| *s == tail_sym)
                        .map(|(_, t)| *t);

                    if let Some(h) = head_tid {
                        if let Term::Ref(sym) = kb.get_term(h) {
                            out.push((*sym, h));
                        }
                    }

                    match tail_tid {
                        Some(t) => current = t,
                        None => break,
                    }
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
}

/// For each SortRequiresInfo fact with a SortView spec, complete the
/// instantiation by merging explicit bindings with auto-bound operations.
fn resolve_requires_bindings(kb: &mut KnowledgeBase) {
    let requires_sym = match kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") {
        Some(sym) => sym,
        None => return,
    };
    let param_type_sym = match kb.try_resolve_symbol("anthill.reflect.SortView") {
        Some(sym) => sym,
        None => return,
    };

    let sort_ref_field = kb.intern("sort_ref");
    let spec_field = kb.intern("spec");

    let rule_ids = kb.by_functor(requires_sym);

    // Collect facts to update: (rule_id, sort_ref_term, spec_sort_sym, explicit_named_args)
    let mut updates: Vec<(super::RuleId, TermId, Symbol, SmallVec<[(Symbol, TermId); 2]>)> = Vec::new();

    for rid in &rule_ids {
        if !kb.rule_body(*rid).is_empty() {
            continue;
        }
        let head = kb.rule_head(*rid);
        let head_term = kb.get_term(head).clone();

        if let Term::Fn { ref named_args, .. } = head_term {
            let sort_ref_tid = named_args.iter()
                .find(|(s, _)| *s == sort_ref_field)
                .map(|(_, t)| *t);
            let spec_tid = named_args.iter()
                .find(|(s, _)| *s == spec_field)
                .map(|(_, t)| *t);

            if let (Some(sr_tid), Some(si_tid)) = (sort_ref_tid, spec_tid) {
                let si_term = kb.get_term(si_tid).clone();
                if let Term::Fn { functor, pos_args, named_args: inst_named, .. } = si_term {
                    if functor == param_type_sym && !pos_args.is_empty() {
                        // Extract spec sort symbol from first pos_arg
                        let spec_sym = match kb.get_term(pos_args[0]) {
                            Term::Fn { functor: f, .. } => Some(*f),
                            Term::Ref(s) => Some(*s),
                            _ => None,
                        };

                        if let Some(ss) = spec_sym {
                            updates.push((*rid, sr_tid, ss, inst_named.clone()));
                        }
                    }
                }
            }
        }
    }

    // Now process each update
    for (rid, sort_ref_tid, spec_sort_sym, explicit_bindings) in updates {
        let base_subst = match kb.sort_base_subst(spec_sort_sym) {
            Some(bs) => bs.to_vec(),
            None => continue,
        };

        // Build complete bindings: start from base, override with explicit
        let mut complete: Vec<(Symbol, TermId)> = Vec::new();

        // Collect operation short names from the spec's SortInfo for auto-binding
        let op_syms = collect_sort_operations(kb, spec_sort_sym);
        let op_short_names: Vec<String> = op_syms.iter()
            .map(|s| {
                let name = kb.resolve_sym(*s);
                name.rsplit('.').next().unwrap_or(name).to_owned()
            })
            .collect();

        // Build a short-name lookup for explicit bindings.
        // Explicit bindings may use plain symbols (e.g., "T") while base_subst
        // uses scope-qualified symbols (e.g., "Monoid.T"). Match by short name.
        let explicit_by_short: Vec<(String, TermId)> = explicit_bindings.iter()
            .map(|(s, t)| {
                let name = kb.resolve_sym(*s);
                let short = name.rsplit('.').next().unwrap_or(name).to_owned();
                (short, *t)
            })
            .collect();

        for (slot_sym, default_tid) in &base_subst {
            let slot_name = kb.resolve_sym(*slot_sym);
            let slot_short = slot_name.rsplit('.').next().unwrap_or(slot_name).to_owned();

            // Check if explicit binding overrides this slot (by short name)
            let explicit_val = explicit_by_short.iter()
                .find(|(name, _)| *name == slot_short)
                .map(|(_, t)| *t);

            if let Some(val) = explicit_val {
                complete.push((*slot_sym, val));
            } else if op_short_names.contains(&slot_short) {
                // Auto-bind: look for same-named operation in the requiring sort's scope
                let auto_bound = find_operation_in_scope(kb, sort_ref_tid, &slot_short);
                match auto_bound {
                    Some(bound_sym) => {
                        let ref_term = kb.alloc(Term::Ref(bound_sym));
                        complete.push((*slot_sym, ref_term));
                    }
                    None => {
                        complete.push((*slot_sym, *default_tid));
                    }
                }
            } else {
                complete.push((*slot_sym, *default_tid));
            }
        }

        // Now build a new SortView term with complete bindings
        let old_head = kb.rule_head(rid);
        let old_head_term = kb.get_term(old_head).clone();
        if let Term::Fn { ref named_args, .. } = old_head_term {
            let old_spec_tid = named_args.iter()
                .find(|(s, _)| *s == spec_field)
                .map(|(_, t)| *t)
                .unwrap();

            let old_inst = kb.get_term(old_spec_tid).clone();
            if let Term::Fn { pos_args, .. } = old_inst {
                let new_named: SmallVec<[(Symbol, TermId); 2]> = complete.into_iter().collect();
                let new_inst = kb.alloc(Term::Fn {
                    functor: param_type_sym,
                    pos_args: pos_args.clone(),
                    named_args: new_named,
                });

                // Build new SortRequiresInfo fact with updated spec
                let new_named_args: SmallVec<[(Symbol, TermId); 2]> = named_args.iter()
                    .map(|(s, t)| {
                        if *s == spec_field {
                            (*s, new_inst)
                        } else {
                            (*s, *t)
                        }
                    })
                    .collect();
                let new_head = kb.alloc(Term::Fn {
                    functor: requires_sym,
                    pos_args: SmallVec::new(),
                    named_args: new_named_args,
                });

                // Retract old, assert new
                let sort = kb.rule_sort(rid);
                let domain = kb.rule_domain(rid);
                let meta = kb.rule_meta(rid);
                kb.retract(rid);
                kb.assert_fact(new_head, sort, domain, meta);
            }
        }
    }
}

/// Collect the operation symbols from a sort's SortInfo.
fn collect_sort_operations(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<Symbol> {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(sym) => sym,
        None => return Vec::new(),
    };
    let name_field = kb.intern("name");
    let operations_field = kb.intern("operations");

    let rule_ids = kb.by_functor(sort_info_sym);
    for rid in rule_ids {
        if !kb.rule_body(rid).is_empty() {
            continue;
        }
        let head = kb.rule_head(rid);
        if let Term::Fn { ref named_args, .. } = kb.get_term(head).clone() {
            let name_matches = named_args.iter()
                .find(|(s, _)| *s == name_field)
                .and_then(|(_, tid)| match kb.get_term(*tid) {
                    Term::Ref(sym) => Some(*sym == sort_sym),
                    _ => None,
                })
                .unwrap_or(false);

            if name_matches {
                let ops_tid = named_args.iter()
                    .find(|(s, _)| *s == operations_field)
                    .map(|(_, t)| *t);
                if let Some(list_tid) = ops_tid {
                    let mut ops = Vec::new();
                    let mut entries = Vec::new();
                    collect_ref_list(kb, list_tid, &mut entries);
                    for (sym, _) in entries {
                        ops.push(sym);
                    }
                    return ops;
                }
            }
        }
    }
    Vec::new()
}

/// Find an operation with the given short name in a sort's OperationInfo facts.
/// Uses the symbol table's scope to check if the operation belongs to the sort.
fn find_operation_in_scope(kb: &mut KnowledgeBase, sort_ref_tid: TermId, short_name: &str) -> Option<Symbol> {
    let op_info_sym = match kb.try_resolve_symbol("anthill.reflect.OperationInfo") {
        Some(sym) => sym,
        None => return None,
    };
    let name_field = kb.intern("name");

    // Get the sort symbol from the sort_ref term
    let sort_sym = match kb.get_term(sort_ref_tid) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(sym) => *sym,
        _ => return None,
    };

    let rule_ids = kb.by_functor(op_info_sym);
    for rid in rule_ids {
        if !kb.rule_body(rid).is_empty() {
            continue;
        }
        let head = kb.rule_head(rid);
        if let Term::Fn { ref named_args, .. } = kb.get_term(head).clone() {
            // Extract the operation symbol from the name field
            let op_sym = named_args.iter()
                .find(|(s, _)| *s == name_field)
                .and_then(|(_, tid)| match kb.get_term(*tid) {
                    Term::Ref(sym) => Some(*sym),
                    _ => None,
                });

            if let Some(op_s) = op_sym {
                // Check if the operation's scope is the sort
                let op_scope_matches = match kb.symbols.get(op_s) {
                    SymbolDef::Resolved { scope_raw, .. } => {
                        // The operation's scope_raw should point to a term whose functor is sort_sym
                        let scope_tid = TermId::from_raw(*scope_raw);
                        match kb.get_term(scope_tid) {
                            Term::Fn { functor, .. } => *functor == sort_sym,
                            _ => false,
                        }
                    }
                    _ => false,
                };

                if op_scope_matches {
                    let op_name = kb.resolve_sym(op_s);
                    let op_short = op_name.rsplit('.').next().unwrap_or(op_name);
                    if op_short == short_name {
                        return Some(op_s);
                    }
                }
            }
        }
    }
    None
}

/// Build a cons-list from a slice of TermIds: `cons(head: a, tail: cons(head: b, tail: nil()))`.
/// Uses the `anthill.prelude.List` constructors so list operations work.
fn build_list(kb: &mut KnowledgeBase, items: &[TermId]) -> TermId {
    build_list_with_tail(kb, items, None)
}

/// Build a cons/nil list with an optional tail (for `[a, b | t]` patterns).
/// If tail is None, terminates with nil.
fn build_list_with_tail(kb: &mut KnowledgeBase, items: &[TermId], tail: Option<TermId>) -> TermId {
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");

    let mut list = tail.unwrap_or_else(|| kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    }));

    for &item in items.iter().rev() {
        list = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head_sym, item), (tail_sym, list)]),
        });
    }

    list
}

/// Build `none()` — the Option.none constructor.
pub(crate) fn build_none(kb: &mut KnowledgeBase) -> TermId {
    let none_sym = kb.resolve_symbol("anthill.prelude.Option.none");
    kb.alloc(Term::Fn {
        functor: none_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    })
}

/// Build `some(value: v)` — the Option.some constructor wrapping a value.
pub(crate) fn build_some(kb: &mut KnowledgeBase, value: TermId) -> TermId {
    let some_sym = kb.resolve_symbol("anthill.prelude.Option.some");
    let value_sym = kb.intern("value");
    kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_elem((value_sym, value), 1),
    })
}

// ══════════════════════════════════════════════════════════════════
// Public: convert a parse-time term into a KB term with scope-aware resolution
// ══════════════════════════════════════════════════════════════════

/// Convert a parse-time term (from `SimpleTermStore`) into the KB's
/// hash-consed `TermStore`, resolving symbols through the KB's scope chain.
///
/// `scope_raw` is the scope in which to resolve names (typically `_global`).
/// `var_map` preserves variable identity: two `?x` in a query share the same
/// `VarId`. Pass an empty map on the first call; reuse the same map across
/// multiple terms that should share variables.
pub fn convert_query_term(
    kb: &mut KnowledgeBase,
    parse_terms: &SimpleTermStore,
    parse_symbols: &crate::intern::SymbolTable,
    parse_id: TermId,
    scope_raw: u32,
    var_map: &mut HashMap<u32, VarId>,
) -> TermId {
    let parse_term = parse_terms.get(parse_id).clone();
    match parse_term {
        Term::Const(lit) => kb.alloc(Term::Const(lit)),
        Term::Var(vid) => {
            let kb_vid = if let Some(&mapped) = var_map.get(&vid.raw()) {
                mapped
            } else {
                let name_str = parse_symbols.name(vid.name());
                let kb_name = kb.intern(name_str);
                let new_vid = kb.fresh_var(kb_name);
                var_map.insert(vid.raw(), new_vid);
                new_vid
            };
            kb.alloc(Term::Var(kb_vid))
        }
        Term::Fn { functor, pos_args, named_args } => {
            let functor_name = parse_symbols.name(functor);
            let kb_functor = resolve_name_in_kb(kb, functor_name, scope_raw);
            let new_pos: SmallVec<[TermId; 4]> = pos_args
                .iter()
                .map(|&id| convert_query_term(kb, parse_terms, parse_symbols, id, scope_raw, var_map))
                .collect();
            let mut new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                .iter()
                .map(|&(sym, id)| {
                    let n = parse_symbols.name(sym);
                    let kb_sym = kb.intern(n);
                    (kb_sym, convert_query_term(kb, parse_terms, parse_symbols, id, scope_raw, var_map))
                })
                .collect();

            // Expand partial named args: fill missing entity fields with fresh vars
            if let Some(all_fields) = kb.entity_field_names(kb_functor) {
                let all_fields = all_fields.to_vec();
                if new_named.len() < all_fields.len() {
                    let provided: HashSet<Symbol> = new_named.iter().map(|(s, _)| *s).collect();
                    for &field_sym in &all_fields {
                        if !provided.contains(&field_sym) {
                            let fresh = kb.fresh_var(field_sym);
                            let var_term = kb.alloc(Term::Var(fresh));
                            new_named.push((field_sym, var_term));
                        }
                    }
                    let order: HashMap<Symbol, usize> = all_fields.iter().enumerate()
                        .map(|(i, &s)| (s, i)).collect();
                    new_named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
                }
            }

            kb.alloc(Term::Fn { functor: kb_functor, pos_args: new_pos, named_args: new_named })
        }
        Term::Ident(sym) => {
            let name = parse_symbols.name(sym);
            if let Some(resolved) = resolve_name_in_kb_opt(kb, name, scope_raw) {
                kb.alloc(Term::Ref(resolved))
            } else {
                let kb_sym = kb.intern(name);
                kb.alloc(Term::Ident(kb_sym))
            }
        }
        Term::Ref(sym) => {
            let name = parse_symbols.name(sym);
            let kb_sym = resolve_name_in_kb(kb, name, scope_raw);
            kb.alloc(Term::Ref(kb_sym))
        }
        Term::Bottom => kb.alloc(Term::Bottom),
    }
}

/// Resolve a name in the KB: try qualified name first, then scope-aware resolution,
/// then fall back to intern.
fn resolve_name_in_kb(kb: &mut KnowledgeBase, name: &str, scope_raw: u32) -> Symbol {
    resolve_name_in_kb_opt(kb, name, scope_raw)
        .unwrap_or_else(|| kb.intern(name))
}

/// Try to resolve a name in the KB: qualified name first, then scope-aware resolution,
/// then fallback search by short name across all defined symbols.
fn resolve_name_in_kb_opt(kb: &KnowledgeBase, name: &str, scope_raw: u32) -> Option<Symbol> {
    if let Some(&sym) = kb.symbols.by_qualified_name.get(name) {
        return Some(sym);
    }
    match kb.symbols.resolve_in_scope(name, scope_raw) {
        ResolveResult::Found(sym) => Some(sym),
        _ => resolve_by_short_name(kb, name),
    }
}

/// Search all qualified names for one whose short name matches.
/// Returns the unique match, or None if not found or ambiguous.
fn resolve_by_short_name(kb: &KnowledgeBase, name: &str) -> Option<Symbol> {
    // First check entity short-name index (fast path)
    if let Some(&short) = kb.symbols.intern_map.get(name) {
        if let Some(qualified) = kb.entity_qualified_for_short(short) {
            return Some(qualified);
        }
    }
    // General fallback: scan by_qualified_name for matching short name.
    // When ambiguous, prefer builtins (e.g. anthill.reflect.not over anthill.prelude.Bool.not).
    let mut found: Option<Symbol> = None;
    let mut found_is_builtin = false;
    for (qname, &sym) in &kb.symbols.by_qualified_name {
        let short = qname.rsplit('.').next().unwrap_or(qname);
        if short == name {
            let is_builtin = kb.builtins.contains_key(&sym);
            if found.is_some() {
                if is_builtin && !found_is_builtin {
                    // New match is a builtin, replace the non-builtin
                    found = Some(sym);
                    found_is_builtin = true;
                } else if !is_builtin && found_is_builtin {
                    // Keep the existing builtin
                } else {
                    return None; // truly ambiguous
                }
            } else {
                found = Some(sym);
                found_is_builtin = is_builtin;
            }
        }
    }
    found
}

struct Loader<'a> {
    kb: &'a mut KnowledgeBase,
    parsed: &'a ParsedFile,
    resolver: &'a dyn SourceResolver,
    loaded_paths: &'a mut HashSet<String>,
    // Map from parse-time TermId → KB TermId
    term_map: HashMap<u32, TermId>,
    // Map from parse-time Symbol → KB Symbol (for reintern — plain intern)
    sym_map: HashMap<u32, Symbol>,
    // Map from parse-time VarId → KB VarId
    var_map: HashMap<u32, VarId>,
    errors: Vec<LoadError>,
    // Current scope for scope-aware resolution
    current_scope: TermId,
    // Description index counter per target (keyed by TermId raw)
    desc_index: HashMap<u32, i64>,
    // ── Occurrence tracking ─────────────────────────────────────
    // Source file id for this file's occurrences
    source_id: SourceId,
    // Symbol of the current owning declaration (operation, rule, etc.)
    current_owner: Option<Symbol>,
}

impl<'a> Loader<'a> {
    fn new(
        kb: &'a mut KnowledgeBase,
        parsed: &'a ParsedFile,
        resolver: &'a dyn SourceResolver,
        loaded_paths: &'a mut HashSet<String>,
        global_scope: TermId,
    ) -> Self {
        let source_id = kb.sources.register("<unknown>".to_string());
        Self {
            kb,
            parsed,
            resolver,
            loaded_paths,
            term_map: HashMap::new(),
            sym_map: HashMap::new(),
            var_map: HashMap::new(),
            errors: Vec::new(),
            current_scope: global_scope,
            desc_index: HashMap::new(),
            source_id,
            current_owner: None,
        }
    }

    /// Re-intern a symbol from the parse interner into the KB interner.
    /// Plain intern — no scope-aware resolution. Used for field names,
    /// param names, meta keys, variable names.
    fn reintern(&mut self, sym: Symbol) -> Symbol {
        if let Some(&mapped) = self.sym_map.get(&sym.index()) {
            return mapped;
        }
        let s = self.parsed.symbols.resolve(sym);
        let new_sym = self.kb.intern(s);
        self.sym_map.insert(sym.index(), new_sym);
        new_sym
    }

    /// Re-intern a parse IR Name as a single dot-joined KB Symbol.
    /// Plain intern — no scope-aware resolution.
    fn reintern_name(&mut self, name: &Name) -> Symbol {
        if name.segments.len() == 1 {
            self.reintern(name.segments[0])
        } else {
            let joined = join_segments(&self.parsed.symbols, &name.segments);
            self.kb.intern(&joined)
        }
    }

    /// Human-readable name for the current scope (for error messages).
    fn scope_display_name(&self) -> String {
        match self.kb.get_term(self.current_scope) {
            Term::Fn { functor, .. } => {
                match self.kb.symbols.get(*functor) {
                    SymbolDef::Resolved { short_name, .. } => short_name.clone(),
                    SymbolDef::Unresolved { name } => name.clone(),
                }
            }
            _ => "_unknown".to_owned(),
        }
    }

    /// Extract qualified names from a list of candidate symbols (for error messages).
    fn candidate_names(&self, candidates: &[Symbol]) -> Vec<String> {
        candidates.iter().map(|&sym| {
            match self.kb.symbols.get(sym) {
                SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                SymbolDef::Unresolved { name } => name.clone(),
            }
        }).collect()
    }

    /// Scope-aware symbol resolution for functors and type/sort references.
    /// If resolution finds a defined symbol, returns it; otherwise falls
    /// back to plain intern (term-level functors may be undefined data names).
    /// Ambiguous matches are still hard errors.
    fn remap_symbol(&mut self, sym: Symbol) -> Symbol {
        let name = self.parsed.symbols.name(sym);
        let scope = self.current_scope.raw();
        match self.kb.symbols.resolve_in_scope(name, scope) {
            ResolveResult::Found(resolved) => resolved,
            ResolveResult::Ambiguous(candidates) => {
                self.errors.push(LoadError::AmbiguousSymbol {
                    name: name.to_owned(),
                    candidates: self.candidate_names(&candidates),
                    span: Span::default(),
                    scope_name: self.scope_display_name(),
                });
                self.kb.symbols.intern(name)
            }
            ResolveResult::NotFound => {
                // Fallback 1: check entity short-name index
                let interned = self.kb.symbols.intern(name);
                if let Some(qualified) = self.kb.entity_qualified_for_short(interned) {
                    qualified
                } else if let Some(sym) = resolve_by_short_name(self.kb, name) {
                    // Fallback 2: search all qualified names by short name
                    sym
                } else {
                    interned
                }
            }
        }
    }

    /// Strict scope-aware symbol resolution: errors on unresolved names.
    /// Used for positions where a symbol *must* be defined (functor names,
    /// explicit references). Unlike `remap_symbol`, does not silently intern.
    fn remap_symbol_strict(&mut self, sym: Symbol) -> Symbol {
        let name = self.parsed.symbols.name(sym);
        let scope = self.current_scope.raw();
        match self.kb.symbols.resolve_in_scope(name, scope) {
            ResolveResult::Found(resolved) => resolved,
            ResolveResult::Ambiguous(candidates) => {
                self.errors.push(LoadError::AmbiguousSymbol {
                    name: name.to_owned(),
                    candidates: self.candidate_names(&candidates),
                    span: Span::default(),
                    scope_name: self.scope_display_name(),
                });
                self.kb.symbols.intern(name)
            }
            ResolveResult::NotFound => {
                let sym = self.kb.symbols.intern(name);
                self.errors.push(LoadError::UnresolvedName {
                    name: name.to_owned(),
                    span: Span::default(),
                    scope_name: self.scope_display_name(),
                });
                sym
            }
        }
    }

    /// Scope-aware name resolution for multi-segment names.
    fn remap_name(&mut self, name: &Name) -> Symbol {
        let lookup_name = if name.segments.len() == 1 {
            self.parsed.symbols.name(name.segments[0]).to_owned()
        } else {
            join_segments(&self.parsed.symbols, &name.segments)
        };
        let scope = self.current_scope.raw();
        match self.kb.symbols.resolve_in_scope(&lookup_name, scope) {
            ResolveResult::Found(resolved) => resolved,
            ResolveResult::Ambiguous(candidates) => {
                self.errors.push(LoadError::AmbiguousSymbol {
                    name: lookup_name.clone(),
                    candidates: self.candidate_names(&candidates),
                    span: name.span,
                    scope_name: self.scope_display_name(),
                });
                self.kb.symbols.intern(&lookup_name)
            }
            ResolveResult::NotFound => {
                // For multi-segment names, try qualified name lookup
                // (the name might be defined via dotted declaration in
                // an intermediate namespace not yet in our scope chain)
                if name.segments.len() > 1 {
                    if let Some(&sym) = self.kb.symbols.by_qualified_name.get(&lookup_name) {
                        return sym;
                    }
                }
                let sym = self.kb.symbols.intern(&lookup_name);
                self.errors.push(LoadError::UnresolvedName {
                    name: lookup_name,
                    span: name.span,
                    scope_name: self.scope_display_name(),
                });
                sym
            }
        }
    }

    /// Create an occurrence for a parse-time term, if it has a recorded span.
    fn maybe_create_occurrence(
        &mut self,
        parse_id: TermId,
        kb_id: TermId,
    ) -> Option<OccurrenceId> {
        if let Some(&span) = self.parsed.terms.spans.get(&parse_id) {
            let source_span = SourceSpan::from_span(self.source_id, span);
            let occ_id = self.kb.occurrences.alloc(
                kb_id, source_span, self.current_owner, true,
            );
            if let Term::Fn { functor, .. } = self.kb.terms.get(kb_id) {
                let functor = *functor;
                self.kb.occurrences.index_by_functor(occ_id, functor);
            }
            Some(occ_id)
        } else {
            None
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
            Term::Fn { functor, pos_args, named_args } => {
                let new_functor = self.remap_symbol(functor);

                // Desugar ListLiteral → cons/nil list
                // ListLiteral(a, b, c) → cons(a, cons(b, cons(c, nil)))
                // ListLiteral(a, b, tail: t) → cons(a, cons(b, t))
                if self.kb.qualified_name_of(new_functor) == "anthill.reflect.ListLiteral" {
                    let items: Vec<TermId> = pos_args.iter()
                        .map(|&id| self.convert_term(id))
                        .collect();
                    let tail_term = named_args.iter()
                        .find(|(sym, _)| self.parsed.symbols.name(*sym) == "tail")
                        .map(|&(_, id)| self.convert_term(id));
                    let kb_id = build_list_with_tail(self.kb, &items, tail_term);
                    self.term_map.insert(parse_id.raw(), kb_id);
                    if let Some(desc_texts) = self.parsed.terms.descriptions.get(&parse_id) {
                        let desc_texts = desc_texts.clone();
                        for desc_text in &desc_texts {
                            self.emit_desc_fact(kb_id, desc_text, self.current_scope);
                        }
                    }
                    return kb_id;
                }

                let new_pos: SmallVec<[TermId; 4]> = pos_args
                    .iter()
                    .map(|&id| self.convert_term(id))
                    .collect();
                let mut new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                    .iter()
                    .map(|&(sym, id)| (self.reintern(sym), self.convert_term(id)))
                    .collect();

                // Expand partial named args: fill missing entity fields with fresh vars
                if let Some(all_fields) = self.kb.entity_field_names(new_functor) {
                    let all_fields = all_fields.to_vec(); // borrow-safe copy
                    if new_named.len() < all_fields.len() {
                        let provided: HashSet<Symbol> = new_named.iter().map(|(s, _)| *s).collect();
                        for &field_sym in &all_fields {
                            if !provided.contains(&field_sym) {
                                let fresh = self.kb.fresh_var(field_sym);
                                let var_term = self.kb.alloc(Term::Var(fresh));
                                new_named.push((field_sym, var_term));
                            }
                        }
                        // Sort to match entity field order (discrimination tree is order-sensitive)
                        let order: HashMap<Symbol, usize> = all_fields.iter().enumerate()
                            .map(|(i, &s)| (s, i)).collect();
                        new_named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
                    }
                }

                Term::Fn { functor: new_functor, pos_args: new_pos, named_args: new_named }
            }
            Term::Ref(sym) => {
                let new_sym = self.remap_symbol_strict(sym);
                Term::Ref(new_sym)
            }
            Term::Bottom => Term::Bottom,
            Term::Ident(sym) => {
                let new_sym = self.remap_symbol(sym);
                // Promote to Ref if the symbol resolved to a defined name
                if self.kb.symbols.is_resolved(new_sym) {
                    Term::Ref(new_sym)
                } else {
                    Term::Ident(new_sym)
                }
            }
        };

        let kb_id = self.kb.alloc(kb_term);
        self.term_map.insert(parse_id.raw(), kb_id);

        // Emit Description facts if the variable has inline descriptions
        if let Some(desc_texts) = self.parsed.terms.descriptions.get(&parse_id) {
            let desc_texts = desc_texts.clone();
            for desc_text in &desc_texts {
                self.emit_desc_fact(kb_id, desc_text, self.current_scope);
            }
        }

        kb_id
    }

    // ── Expression conversion ─────────────────────────────────────
    //
    // Converts positional-arg expression terms (from the converter) into
    // named-arg KB entity terms matching the Expr/Pattern sorts in reflect.anthill.

    /// Convert a parse-time expression term into the KB's Expr representation.
    /// Dispatches on the functor name to restructure positional args into named args.
    /// Also creates an occurrence in the OccurrenceStore if the term has a span.
    /// Convert an expression term and create an occurrence.
    /// Returns (kb_term_id, occurrence_id). The occurrence_id is used by
    /// parent expressions to put Literal::Handle(Occurrence, occ_id) in
    /// ExprOccurrence-typed fields.
    fn convert_expr_term(&mut self, parse_id: TermId) -> (TermId, Option<OccurrenceId>) {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        let kb_id = match parse_term {
            Term::Fn { functor, pos_args, named_args } => {
                let name = self.parsed.symbols.name(functor).to_owned();
                match name.as_str() {
                    "match_expr" => self.load_match_expr(&pos_args),
                    "match_branch" => self.load_match_branch(&pos_args),
                    "if_expr" => self.load_if_expr(&pos_args),
                    "let_expr" => self.load_let_expr(&pos_args),
                    "lambda" => self.load_lambda_expr(&pos_args),
                    "pattern_var" => self.load_pattern_var(&pos_args),
                    "pattern_wildcard" => self.load_pattern_wildcard(),
                    "pattern_literal" => self.load_pattern_literal(&pos_args),
                    "pattern_constructor" => self.load_pattern_constructor(&pos_args),
                    "pattern_tuple" => self.load_pattern_tuple(&pos_args),
                    _ => self.load_apply_or_constructor(functor, &pos_args, &named_args),
                }
            }
            Term::Const(_) => self.load_literal_expr(parse_id),
            Term::Ident(_) => self.load_var_ref(parse_id),
            _ => self.convert_term(parse_id),
        };
        let occ_id = self.maybe_create_occurrence(parse_id, kb_id);
        (kb_id, occ_id)
    }

    /// Helper: convert child expression and return a Handle literal term
    /// containing its OccurrenceId (for ExprOccurrence-typed fields).
    /// Falls back to the raw TermId if no occurrence was created.
    fn convert_expr_child(&mut self, parse_id: TermId) -> TermId {
        let (kb_id, occ_id) = self.convert_expr_term(parse_id);
        match occ_id {
            Some(occ) => self.kb.alloc(Term::Const(Literal::Handle(HandleKind::Occurrence, occ.raw()))),
            None => kb_id,
        }
    }

    /// match_expr: pos_args[0] = scrutinee, pos_args[1..] = branches
    fn load_match_expr(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let scrutinee = self.convert_expr_child(pos_args[0]); // ExprOccurrence
        let mut branch_terms = Vec::new();
        for &tid in &pos_args[1..] {
            let (branch_kb_id, _) = self.convert_expr_term(tid); // MatchBranch (not ExprOccurrence)
            branch_terms.push(branch_kb_id);
        }
        let branches = build_list(self.kb, &branch_terms);
        let match_sym = self.kb.resolve_symbol("anthill.reflect.Expr.match_expr");
        let scrutinee_key = self.kb.intern("scrutinee");
        let branches_key = self.kb.intern("branches");
        self.kb.alloc(Term::Fn {
            functor: match_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (scrutinee_key, scrutinee),
                (branches_key, branches),
            ]),
        })
    }

    /// match_branch: pos_args[0] = pattern, pos_args[1] = body
    fn load_match_branch(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let (pattern, _) = self.convert_expr_term(pos_args[0]); // Pattern (not ExprOccurrence)
        let body = self.convert_expr_child(pos_args[1]); // ExprOccurrence
        let guard = build_none(self.kb);
        let branch_sym = self.kb.resolve_symbol("anthill.reflect.MatchBranch");
        let pattern_key = self.kb.intern("pattern");
        let guard_key = self.kb.intern("guard");
        let body_key = self.kb.intern("body");
        self.kb.alloc(Term::Fn {
            functor: branch_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (pattern_key, pattern),
                (guard_key, guard),
                (body_key, body),
            ]),
        })
    }

    /// if_expr: pos_args[0] = cond, pos_args[1] = then_branch, pos_args[2] = else_branch
    fn load_if_expr(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let cond = self.convert_expr_child(pos_args[0]); // ExprOccurrence
        let then_branch = self.convert_expr_child(pos_args[1]); // ExprOccurrence
        let else_branch = self.convert_expr_child(pos_args[2]); // ExprOccurrence
        let if_sym = self.kb.resolve_symbol("anthill.reflect.Expr.if_expr");
        let cond_key = self.kb.intern("cond");
        let then_key = self.kb.intern("then_branch");
        let else_key = self.kb.intern("else_branch");
        self.kb.alloc(Term::Fn {
            functor: if_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (cond_key, cond),
                (then_key, then_branch),
                (else_key, else_branch),
            ]),
        })
    }

    /// let_expr: pos_args[0] = pattern, pos_args[1] = value, pos_args[2] = body
    fn load_let_expr(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let (pattern, _) = self.convert_expr_term(pos_args[0]); // Pattern
        let value = self.convert_expr_child(pos_args[1]); // ExprOccurrence
        let body = self.convert_expr_child(pos_args[2]); // ExprOccurrence
        let let_sym = self.kb.resolve_symbol("anthill.reflect.Expr.let_expr");
        let pattern_key = self.kb.intern("pattern");
        let value_key = self.kb.intern("value");
        let body_key = self.kb.intern("body");
        self.kb.alloc(Term::Fn {
            functor: let_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (pattern_key, pattern),
                (value_key, value),
                (body_key, body),
            ]),
        })
    }

    /// lambda: pos_args[0] = param (pattern), pos_args[1] = body
    fn load_lambda_expr(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let (param, _) = self.convert_expr_term(pos_args[0]); // Pattern
        let body = self.convert_expr_child(pos_args[1]); // ExprOccurrence
        let lambda_sym = self.kb.resolve_symbol("anthill.reflect.Expr.lambda");
        let param_key = self.kb.intern("param");
        let body_key = self.kb.intern("body");
        self.kb.alloc(Term::Fn {
            functor: lambda_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (param_key, param),
                (body_key, body),
            ]),
        })
    }

    /// var_ref: Term::Ident(sym) → var_ref(name: Ref(sym))
    /// Uses reintern (plain) — lexical variables are NOT KB symbol references.
    fn load_var_ref(&mut self, parse_id: TermId) -> TermId {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        let name_ref = if let Term::Ident(sym) = parse_term {
            let kb_sym = self.reintern(sym);
            self.kb.alloc(Term::Ref(kb_sym))
        } else {
            self.convert_term(parse_id)
        };
        let var_ref_sym = self.kb.resolve_symbol("anthill.reflect.Expr.var_ref");
        let name_key = self.kb.intern("name");
        self.kb.alloc(Term::Fn {
            functor: var_ref_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(name_key, name_ref)]),
        })
    }

    /// Literal constant → int_lit/bigint_lit/float_lit/string_lit/bool_lit
    fn load_literal_expr(&mut self, parse_id: TermId) -> TermId {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        if let Term::Const(ref lit) = parse_term {
            let (entity_name, value_term) = match lit {
                super::term::Literal::Int(n) => (
                    "anthill.reflect.Expr.int_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::Int(*n))),
                ),
                super::term::Literal::BigInt(n) => (
                    "anthill.reflect.Expr.bigint_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::BigInt(n.clone()))),
                ),
                super::term::Literal::Float(f) => (
                    "anthill.reflect.Expr.float_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::Float(*f))),
                ),
                super::term::Literal::String(s) => (
                    "anthill.reflect.Expr.string_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::String(s.clone()))),
                ),
                super::term::Literal::Bool(b) => (
                    "anthill.reflect.Expr.bool_lit",
                    self.kb.alloc(Term::Const(super::term::Literal::Bool(*b))),
                ),
                super::term::Literal::Handle(kind, id) => (
                    "anthill.reflect.Expr.int_lit", // Handle literals shouldn't appear in source expressions
                    self.kb.alloc(Term::Const(super::term::Literal::Handle(*kind, *id))),
                ),
            };
            let entity_sym = self.kb.resolve_symbol(entity_name);
            let value_key = self.kb.intern("value");
            self.kb.alloc(Term::Fn {
                functor: entity_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(value_key, value_term)]),
            })
        } else {
            self.convert_term(parse_id)
        }
    }

    /// General function call or constructor — any Fn term not recognized as an expression keyword.
    fn load_apply_or_constructor(
        &mut self,
        parse_functor: Symbol,
        pos_args: &SmallVec<[TermId; 4]>,
        named_args: &SmallVec<[(Symbol, TermId); 2]>,
    ) -> TermId {
        let kb_functor = self.remap_symbol(parse_functor);
        let is_entity = matches!(
            self.kb.symbols.get(kb_functor),
            SymbolDef::Resolved { kind: SymbolKind::Entity, .. }
        );

        // Build ApplyArg list
        let apply_arg_sym = self.kb.resolve_symbol("anthill.reflect.ApplyArg");
        let arg_name_key = self.kb.intern("name");
        let arg_value_key = self.kb.intern("value");

        let mut arg_terms = Vec::new();
        for &tid in pos_args.iter() {
            let value = self.convert_expr_child(tid); // ExprOccurrence
            let none = build_none(self.kb);
            let arg = self.kb.alloc(Term::Fn {
                functor: apply_arg_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(arg_name_key, none), (arg_value_key, value)]),
            });
            arg_terms.push(arg);
        }
        for &(sym, tid) in named_args.iter() {
            let value = self.convert_expr_child(tid); // ExprOccurrence
            let reinterned = self.reintern(sym);
            let name_ref = self.kb.alloc(Term::Ref(reinterned));
            let some_name = build_some(self.kb, name_ref);
            let arg = self.kb.alloc(Term::Fn {
                functor: apply_arg_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(arg_name_key, some_name), (arg_value_key, value)]),
            });
            arg_terms.push(arg);
        }
        let args_list = build_list(self.kb, &arg_terms);
        let name_ref = self.kb.alloc(Term::Ref(kb_functor));

        if is_entity {
            let ctor_sym = self.kb.resolve_symbol("anthill.reflect.Expr.constructor");
            let name_key = self.kb.intern("name");
            let args_key = self.kb.intern("args");
            self.kb.alloc(Term::Fn {
                functor: ctor_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(name_key, name_ref), (args_key, args_list)]),
            })
        } else {
            let apply_sym = self.kb.resolve_symbol("anthill.reflect.Expr.apply");
            let fn_key = self.kb.intern("fn");
            let args_key = self.kb.intern("args");
            self.kb.alloc(Term::Fn {
                functor: apply_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(fn_key, name_ref), (args_key, args_list)]),
            })
        }
    }

    // ── Pattern conversion ───────────────────────────────────────

    /// pattern_var: pos_args[0] = Ident(name)
    fn load_pattern_var(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let name_term = self.parsed.terms.get(pos_args[0]).clone();
        let name_ref = if let Term::Ident(sym) = name_term {
            let kb_sym = self.reintern(sym);
            self.kb.alloc(Term::Ref(kb_sym))
        } else {
            self.convert_term(pos_args[0])
        };
        let type_ann = build_none(self.kb);
        let var_pattern_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.var_pattern");
        let name_key = self.kb.intern("name");
        let type_ann_key = self.kb.intern("type_ann");
        self.kb.alloc(Term::Fn {
            functor: var_pattern_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(name_key, name_ref), (type_ann_key, type_ann)]),
        })
    }

    /// pattern_wildcard: no args
    fn load_pattern_wildcard(&mut self) -> TermId {
        let wildcard_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.wildcard");
        self.kb.alloc(Term::Fn {
            functor: wildcard_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// pattern_literal: pos_args[0] = literal term
    fn load_pattern_literal(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let value = self.convert_term(pos_args[0]);
        let lit_pattern_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.literal_pattern");
        let value_key = self.kb.intern("value");
        self.kb.alloc(Term::Fn {
            functor: lit_pattern_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(value_key, value)]),
        })
    }

    /// pattern_constructor: pos_args[0] = Ident(name), pos_args[1..] = sub-patterns
    fn load_pattern_constructor(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let name_term = self.parsed.terms.get(pos_args[0]).clone();
        let name_ref = if let Term::Ident(sym) = name_term {
            let kb_sym = self.remap_symbol(sym);
            self.kb.alloc(Term::Ref(kb_sym))
        } else {
            self.convert_term(pos_args[0])
        };
        let mut sub_patterns = Vec::new();
        for &tid in &pos_args[1..] {
            let (pat_id, _) = self.convert_expr_term(tid); // Pattern
            sub_patterns.push(pat_id);
        }
        let args_list = build_list(self.kb, &sub_patterns);
        let ctor_pattern_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.constructor_pattern");
        let name_key = self.kb.intern("name");
        let args_key = self.kb.intern("args");
        self.kb.alloc(Term::Fn {
            functor: ctor_pattern_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(name_key, name_ref), (args_key, args_list)]),
        })
    }

    /// pattern_tuple: all pos_args are sub-patterns
    fn load_pattern_tuple(&mut self, pos_args: &SmallVec<[TermId; 4]>) -> TermId {
        let mut elements = Vec::new();
        for &tid in pos_args.iter() {
            let (elem_id, _) = self.convert_expr_term(tid); // Pattern
            elements.push(elem_id);
        }
        let elements_list = build_list(self.kb, &elements);
        let tuple_pattern_sym = self.kb.resolve_symbol("anthill.reflect.Pattern.tuple_pattern");
        let elements_key = self.kb.intern("elements");
        self.kb.alloc(Term::Fn {
            functor: tuple_pattern_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(elements_key, elements_list)]),
        })
    }

    /// Convert a Name to a sort term (nullary Fn term) using scope-aware resolution.
    fn name_to_sort_term(&mut self, name: &Name) -> TermId {
        let functor = self.remap_name(name);
        self.kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// Convert a TypeExpr to a type-term in the KB.
    fn type_expr_to_term(&mut self, ty: &TypeExpr) -> TermId {
        match ty {
            TypeExpr::Simple(name) => self.name_to_sort_term(name),
            TypeExpr::Parameterized { name, bindings } => {
                let name_term = self.name_to_sort_term(name);
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::from_elem(name_term, 1);
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for b in bindings {
                    let bound_term = self.type_expr_to_term(&b.bound);
                    match &b.param {
                        Some(p) => {
                            let param_sym = self.reintern(p.last());
                            named_args.push((param_sym, bound_term));
                        }
                        None => {
                            pos_args.push(bound_term);
                        }
                    }
                }

                let param_type_sym = self.kb.resolve_symbol("anthill.reflect.SortView");
                self.kb.alloc(Term::Fn {
                    functor: param_type_sym,
                    pos_args,
                    named_args,
                })
            }
            TypeExpr::Variable { term_id, descriptions } => {
                let kb_id = self.convert_term(*term_id);
                for desc_text in descriptions {
                    self.emit_desc_fact(kb_id, desc_text, self.current_scope);
                }
                kb_id
            }
            TypeExpr::Tuple(fields) => {
                let tuple_sym = self.kb.resolve_symbol("anthill.reflect.TupleLiteral");
                let named_args: SmallVec<[(Symbol, TermId); 2]> = fields.iter().map(|(sym, ty)| {
                    let key = self.reintern(*sym);
                    let val = self.type_expr_to_term(ty);
                    (key, val)
                }).collect();
                self.kb.alloc(Term::Fn {
                    functor: tuple_sym,
                    pos_args: SmallVec::new(),
                    named_args,
                })
            }
            TypeExpr::Arrow { params, return_type, effect } => {
                let functor_name = if effect.is_some() { "arrow_effect" } else { "arrow" };
                let functor = self.kb.symbols.intern(functor_name);
                let mut pos_args: SmallVec<[TermId; 4]> = params.iter()
                    .map(|p| self.type_expr_to_term(p))
                    .collect();
                pos_args.push(self.type_expr_to_term(return_type));
                if let Some(eff) = effect {
                    pos_args.push(self.type_expr_to_term(eff));
                }
                self.kb.alloc(Term::Fn {
                    functor,
                    pos_args,
                    named_args: SmallVec::new(),
                })
            }
        }
    }

    /// Load items (top-level or within a domain), tracking scope.
    fn load_items(&mut self, items: &[Item], domain: Option<TermId>) {
        let prev_scope = self.current_scope;
        let domain = domain.unwrap_or_else(|| self.kb.make_name_term("_global"));
        self.current_scope = domain;

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
                Item::Describe(d) => self.load_describe(d, domain),
            }
        }

        self.current_scope = prev_scope;
    }

    fn load_namespace(&mut self, n: &Namespace) {
        let ns_term = self.name_to_sort_term(&n.name);
        let ns_sort = self.kb.make_name_term("Namespace");

        // Assert namespace as a fact
        self.kb.assert_fact(ns_term, ns_sort, ns_term, None);

        // Set scope to namespace for member resolution
        let prev_scope = self.current_scope;
        self.current_scope = ns_term;

        // Emit member facts for direct children
        self.emit_member_facts_for_items(&n.items, ns_term);

        // Load nested items within this namespace scope
        self.load_items(&n.items, Some(ns_term));

        self.current_scope = prev_scope;
    }

    fn load_abstract_sort(&mut self, s: &AbstractSort, domain: TermId) {
        let sort_term = self.name_to_sort_term(&s.name);
        let sort_sort = self.kb.make_name_term("Sort");

        self.kb.register_sort(sort_term, SortKind::Abstract);

        // Both variable (sort T = ?Element) and alias (sort T = Int) emit SortAlias.
        // For variables, use convert_term directly to avoid double-emitting descriptions
        // (AbstractSort.descriptions already covers them via the loop below).
        let target_term = match &s.definition {
            TypeExpr::Variable { term_id, .. } => self.convert_term(*term_id),
            _ => self.type_expr_to_term(&s.definition),
        };
        let alias_sym = self.kb.resolve_symbol("SortAlias");
        let alias_fact = self.kb.alloc(Term::Fn {
            functor: alias_sym,
            pos_args: SmallVec::from_slice(&[sort_term, target_term]),
            named_args: SmallVec::new(),
        });
        self.kb.assert_fact(alias_fact, sort_sort, domain, None);

        // Emit Description facts for all description blocks
        for desc_text in &s.descriptions {
            self.emit_desc_fact(sort_term, desc_text, domain);
        }
    }

    fn load_sort_with_body(&mut self, s: &SortWithBody, parent_domain: TermId) {
        let sort_term = self.name_to_sort_term(&s.name);
        let sort_sort = self.kb.make_name_term("Sort");

        // Determine kind: Defined if it has direct entity children, Abstract otherwise
        let has_entities = s.items.iter().any(|item| matches!(item, Item::Entity(_)));
        let kind = if has_entities { SortKind::Defined } else { SortKind::Abstract };
        self.kb.register_sort(sort_term, kind);

        // Emit Description facts for all description blocks
        for desc_text in &s.descriptions {
            self.emit_desc_fact(sort_term, desc_text, parent_domain);
        }

        // Set scope to sort for child resolution
        let prev_scope = self.current_scope;
        self.current_scope = sort_term;

        // Pre-resolve symbols used for EntityInfo/FieldInfo (hoisted from loop)
        let field_info_sym = self.kb.resolve_symbol("anthill.reflect.FieldInfo");
        let entity_info_sym = self.kb.resolve_symbol("anthill.reflect.EntityInfo");
        let fi_name_sym = self.kb.intern("name");
        let fi_type_sym = self.kb.intern("type_name");
        let fields_field_sym = self.kb.intern("fields");
        self.kb.register_entity_fields(entity_info_sym, vec![fi_name_sym, fields_field_sym]);

        // Register direct entity children (entity → parent sort)
        for item in &s.items {
            if let Item::Entity(e) = item {
                let ctor_term = self.name_to_sort_term(&e.name);
                self.kb.register_sort(ctor_term, SortKind::Constructor);
                self.kb.register_entity_of(ctor_term, sort_term);

                // Build FieldInfo list for entity fields
                let ctor_functor = match self.kb.get_term(ctor_term) {
                    Term::Fn { functor, .. } => *functor,
                    _ => self.kb.intern("_unknown"),
                };
                let ctor_qualified = match self.kb.symbols.get(ctor_functor) {
                    SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                    SymbolDef::Unresolved { name } => name.clone(),
                };
                let field_terms: Vec<TermId> = e.fields
                    .iter()
                    .map(|f| {
                        let field_name_str = self.parsed.symbols.name(f.name).to_owned();
                        let field_qualified = format!("{}.{}", ctor_qualified, field_name_str);
                        let field_sym = if let Some(&existing) = self.kb.symbols.by_qualified_name.get(&field_qualified) {
                            existing
                        } else {
                            self.kb.symbols.define(&field_name_str, &field_qualified, SymbolKind::Field, ctor_term.raw())
                        };
                        let name_term = self.kb.alloc(Term::Ref(field_sym));
                        let type_term = self.type_expr_to_term(&f.ty);
                        self.kb.alloc(Term::Fn {
                            functor: field_info_sym,
                            pos_args: SmallVec::new(),
                            named_args: SmallVec::from_slice(&[
                                (fi_name_sym, name_term),
                                (fi_type_sym, type_term),
                            ]),
                        })
                    })
                    .collect();
                let fields_list = build_list(self.kb, &field_terms);

                // Assert EntityInfo fact (name stores sort term for entity_of compatibility)
                let entity_info_fact = self.kb.alloc(Term::Fn {
                    functor: entity_info_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[(fi_name_sym, ctor_term), (fields_field_sym, fields_list)]),
                });
                self.kb.assert_fact(entity_info_fact, sort_sort, parent_domain, None);
            }
        }

        // Emit member facts for direct children
        self.emit_member_facts_for_items(&s.items, sort_term);

        // Load all items within this sort's domain scope
        self.load_items(&s.items, Some(sort_term));

        // Now collect constructors, operations, parameters, requires from child items
        // (after loading, so all names are resolved in sort scope)
        let sort_functor = match self.kb.get_term(sort_term) {
            Term::Fn { functor, .. } => *functor,
            _ => self.kb.intern("_unknown"),
        };

        let mut ctor_refs = Vec::new();
        let mut op_refs = Vec::new();
        let mut param_refs = Vec::new();
        let mut req_terms = Vec::new();

        for item in &s.items {
            match item {
                Item::Entity(e) => {
                    let sym = self.remap_name(&e.name);
                    ctor_refs.push(self.kb.alloc(Term::Ref(sym)));
                }
                Item::Operation(o) => {
                    let sym = self.remap_name(&o.name);
                    op_refs.push(self.kb.alloc(Term::Ref(sym)));
                }
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        let sym = self.remap_name(&op.name);
                        op_refs.push(self.kb.alloc(Term::Ref(sym)));
                    }
                }
                Item::AbstractSort(abs) => {
                    if matches!(abs.definition, TypeExpr::Variable { .. }) {
                        let sym = self.remap_name(&abs.name);
                        param_refs.push(self.kb.alloc(Term::Ref(sym)));
                    }
                }
                Item::RequiresDecl(r) => {
                    let req_term = self.type_expr_to_term(&r.type_expr);
                    req_terms.push(req_term);
                }
                _ => {}
            }
        }

        let ctors_list = build_list(self.kb, &ctor_refs);
        let ops_list = build_list(self.kb, &op_refs);
        let params_list = build_list(self.kb, &param_refs);
        let requires_list = build_list(self.kb, &req_terms);

        // definition: Var for abstract (no entities), sort_term for defined
        let definition_term = if has_entities {
            sort_term
        } else {
            let anon_sym = self.kb.intern("?");
            let vid = self.kb.fresh_var(anon_sym);
            self.kb.alloc(Term::Var(vid))
        };

        // Assert SortInfo fact with named args
        let sort_info_sym = self.kb.resolve_symbol("anthill.reflect.SortInfo");
        let name_sym = self.kb.intern("name");
        let definition_sym = self.kb.intern("definition");
        let constructors_sym = self.kb.intern("constructors");
        let operations_sym = self.kb.intern("operations");
        let parameters_sym = self.kb.intern("parameters");
        let requires_sym = self.kb.intern("requires");

        // Register SortInfo fields for partial named-arg expansion
        self.kb.register_entity_fields(sort_info_sym, vec![
            name_sym, definition_sym, constructors_sym,
            operations_sym, parameters_sym, requires_sym,
        ]);
        let name_ref = self.kb.alloc(Term::Ref(sort_functor));

        let fact_term = self.kb.alloc(Term::Fn {
            functor: sort_info_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (name_sym, name_ref),
                (definition_sym, definition_term),
                (constructors_sym, ctors_list),
                (operations_sym, ops_list),
                (parameters_sym, params_list),
                (requires_sym, requires_list),
            ]),
        });
        self.kb.assert_fact(fact_term, sort_sort, parent_domain, None);

        self.current_scope = prev_scope;
    }

    fn load_entity(&mut self, e: &Entity, domain: TermId) {
        let entity_sort = self.kb.make_name_term("Entity");
        let functor = self.remap_name(&e.name);

        let named_args: SmallVec<[(Symbol, TermId); 2]> = e.fields
            .iter()
            .map(|f| {
                let field_sym = self.reintern(f.name);
                let type_term = self.type_expr_to_term(&f.ty);
                (field_sym, type_term)
            })
            .collect();

        // Register entity field names for partial named-arg expansion.
        // Register under both the qualified symbol (from remap_name) and
        // the short name, so that sugar-generated facts (which use unqualified
        // functor names like "WorkItem") can also look up entity fields.
        let field_names: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
        self.kb.register_entity_fields(functor, field_names.clone());
        let short_name = if e.name.segments.len() == 1 {
            self.parsed.symbols.name(e.name.segments[0]).to_owned()
        } else {
            // For multi-segment names, use the last segment as short name
            self.parsed.symbols.name(*e.name.segments.last().unwrap()).to_owned()
        };
        let short_sym = self.kb.intern(&short_name);
        if short_sym != functor {
            self.kb.register_entity_fields(short_sym, field_names);
            // Map short name → qualified symbol so remap_symbol can redirect
            self.kb.register_entity_short_name(short_sym, functor);
        }

        let entity_term = self.kb.alloc(Term::Fn { functor, pos_args: SmallVec::new(), named_args });
        self.kb.assert_fact(entity_term, entity_sort, domain, None);
    }

    fn load_fact(&mut self, f: &Fact, domain: TermId) {
        let sort_name = f.sort.as_deref().unwrap_or("Fact");
        let fact_sort = self.kb.make_name_term(sort_name);

        // Set owner: use the fact's head functor symbol if available
        let prev_owner = self.current_owner;
        if let Term::Fn { functor, .. } = self.parsed.terms.get(f.term) {
            self.current_owner = Some(self.remap_symbol(*functor));
        }

        let term = self.convert_term(f.term);
        // Create occurrence for the fact's top-level term
        self.maybe_create_occurrence(f.term, term);

        let meta = f.meta.as_ref().map(|mb| self.load_meta_block(mb));
        self.kb.assert_fact(term, fact_sort, domain, meta);

        self.current_owner = prev_owner;
    }

    fn load_rule(&mut self, r: &Rule, domain: TermId) {
        let rule_sort = self.kb.make_name_term("Rule");

        // Set owner for body occurrences (use rule label if available)
        let prev_owner = self.current_owner;
        if let Some(ref label) = r.label {
            self.current_owner = Some(self.remap_name(label));
        }

        let head_term = match &r.head {
            RuleHead::Term(tid) => self.convert_term(*tid),
            RuleHead::Bottom => self.kb.alloc(Term::Bottom),
        };

        let body: Vec<TermId> = r.body.as_ref()
            .map(|terms| terms.iter().map(|&tid| self.convert_term(tid)).collect())
            .unwrap_or_default();

        let meta = r.meta.as_ref().map(|mb| self.load_meta_block(mb));
        self.kb.assert_rule(head_term, body, rule_sort, domain, meta);

        self.current_owner = prev_owner;
    }

    fn load_operation(&mut self, o: &Operation, domain: TermId) {
        let op_sort = self.kb.make_name_term("Operation");
        let functor = self.remap_name(&o.name);

        // Set owner for expression occurrences
        let prev_owner = self.current_owner;
        self.current_owner = Some(functor);

        // Enter operation scope if params exist (scope created during scanning).
        // Operations without params don't get their own scope.
        let prev_scope = self.current_scope;
        if !o.params.is_empty() {
            let op_scope = self.kb.alloc(Term::Fn {
                functor,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            self.current_scope = op_scope;
        }

        let return_term = self.type_expr_to_term(&o.return_type);

        // Build FieldInfo list for params
        let field_info_sym = self.kb.resolve_symbol("anthill.reflect.FieldInfo");
        let fi_name_sym = self.kb.intern("name");
        let fi_type_sym = self.kb.intern("type_name");
        let op_qualified = match self.kb.symbols.get(functor) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        let param_terms: Vec<TermId> = o.params
            .iter()
            .map(|p| {
                let param_name_str = self.parsed.symbols.name(p.name).to_owned();
                // Register field symbol for parameter
                let field_qualified = format!("{}.{}", op_qualified, param_name_str);
                let field_sym = if let Some(&existing) = self.kb.symbols.by_qualified_name.get(&field_qualified) {
                    existing
                } else {
                    self.kb.symbols.define(&param_name_str, &field_qualified, SymbolKind::Field, self.current_scope.raw())
                };
                let name_term = self.kb.alloc(Term::Ref(field_sym));
                let type_term = self.type_expr_to_term(&p.ty);
                self.kb.alloc(Term::Fn {
                    functor: field_info_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (fi_name_sym, name_term),
                        (fi_type_sym, type_term),
                    ]),
                })
            })
            .collect();
        let params_list = build_list(self.kb, &param_terms);

        // Build effects list
        let effect_terms: Vec<TermId> = o.effects
            .iter()
            .map(|e| self.type_expr_to_term(&e.type_expr))
            .collect();
        let effects_list = build_list(self.kb, &effect_terms);

        // Build requires and ensures lists
        let requires_list = self.convert_clause_list(&o.requires);
        let ensures_list = self.convert_clause_list(&o.ensures);

        // Convert expression body if present (within operation scope)
        // body is Option[ExprOccurrence] — store OccurrenceId handle
        let (body_opt_term, body_expr_opt) = match o.body {
            Some(body_tid) => {
                let (kb_id, occ_id) = self.convert_expr_term(body_tid);
                let handle = match occ_id {
                    Some(occ) => self.kb.alloc(Term::Const(Literal::Handle(HandleKind::Occurrence, occ.raw()))),
                    None => kb_id,
                };
                (build_some(self.kb, handle), Some(kb_id))
            }
            None => (build_none(self.kb), None),
        };

        self.current_scope = prev_scope;
        self.current_owner = prev_owner;

        // Build OperationInfo term with named args matching the entity definition
        let op_info_sym = self.kb.resolve_symbol("anthill.reflect.OperationInfo");
        let name_sym = self.kb.intern("name");
        let params_sym = self.kb.intern("params");
        let return_type_sym = self.kb.intern("return_type");
        let effects_sym = self.kb.intern("effects");
        let requires_sym = self.kb.intern("requires");
        let ensures_sym = self.kb.intern("ensures");
        let body_sym = self.kb.intern("body");

        // name: Ref to operation symbol
        let name_ref = self.kb.alloc(Term::Ref(functor));

        let op_info = self.kb.alloc(Term::Fn {
            functor: op_info_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (name_sym, name_ref),
                (params_sym, params_list),
                (return_type_sym, return_term),
                (effects_sym, effects_list),
                (requires_sym, requires_list),
                (ensures_sym, ensures_list),
                (body_sym, body_opt_term),
            ]),
        });
        self.kb.assert_fact(op_info, op_sort, domain, None);

        // Emit OperationImpl fact for operations with expression bodies
        if let Some(body_expr) = body_expr_opt {
            if let Some(op_impl_sym) = self.kb.try_resolve_symbol("anthill.realization.OperationImpl") {
                let impl_sort = self.kb.make_name_term("OperationImpl");
                let operation_key = self.kb.intern("operation");
                let params_key = self.kb.intern("params");
                let body_key = self.kb.intern("body");

                let op_name_ref = self.kb.alloc(Term::Ref(functor));
                let param_syms: Vec<TermId> = o.params.iter().map(|p| {
                    let name = self.parsed.symbols.name(p.name).to_owned();
                    let sym = self.kb.intern(&name);
                    self.kb.alloc(Term::Ref(sym))
                }).collect();
                let params_list_impl = build_list(self.kb, &param_syms);

                let op_impl = self.kb.alloc(Term::Fn {
                    functor: op_impl_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (operation_key, op_name_ref),
                        (params_key, params_list_impl),
                        (body_key, body_expr),
                    ]),
                });
                self.kb.assert_fact(op_impl, impl_sort, domain, None);
            }
        }
    }

    fn load_constraint(&mut self, c: &Constraint, domain: TermId) {
        let constraint_sort = self.kb.make_name_term("Constraint");
        let constraint_sym = self.kb.resolve_symbol("Constraint");

        let head_pos: SmallVec<[TermId; 4]> = c.head
            .iter()
            .map(|&tid| self.convert_term(tid))
            .collect();

        let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();

        let head_sym = self.kb.intern("head");
        let head_term = self.kb.alloc(Term::Fn {
            functor: head_sym,
            pos_args: head_pos,
            named_args: SmallVec::new(),
        });
        pos_args.push(head_term);

        if let Some(guard) = &c.guard {
            let guard_pos: SmallVec<[TermId; 4]> = guard
                .iter()
                .map(|&tid| self.convert_term(tid))
                .collect();
            let guard_sym = self.kb.intern("guard");
            let guard_term = self.kb.alloc(Term::Fn {
                functor: guard_sym,
                pos_args: guard_pos,
                named_args: SmallVec::new(),
            });
            pos_args.push(guard_term);
        }

        let constraint_term = self.kb.alloc(Term::Fn {
            functor: constraint_sym,
            pos_args,
            named_args: SmallVec::new(),
        });

        self.kb.assert_fact(constraint_term, constraint_sort, domain, None);
    }

    fn load_requires_decl(&mut self, r: &RequiresDecl, domain: TermId) {
        let requirement_sort = self.kb.make_name_term("Requirement");
        let requires_sym = self.kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
        let type_term = self.type_expr_to_term(&r.type_expr);

        // Named args: sort_ref, spec
        let sort_ref_sym = self.kb.intern("sort_ref");
        let spec_sym = self.kb.intern("spec");
        self.kb.register_entity_fields(requires_sym, vec![sort_ref_sym, spec_sym]);
        let requires_term = self.kb.alloc(Term::Fn {
            functor: requires_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (sort_ref_sym, domain),
                (spec_sym, type_term),
            ]),
        });
        self.kb.assert_fact(requires_term, requirement_sort, domain, None);
    }

    fn load_describe(&mut self, d: &Describe, domain: TermId) {
        let target_term = self.name_to_sort_term(&d.target);
        for content in &d.contents {
            self.emit_desc_fact(target_term, content, domain);
        }
    }

    fn emit_desc_fact(&mut self, target: TermId, text: &str, domain: TermId) {
        let desc_sort = self.kb.make_name_term("Description");
        let desc_sym = self.kb.resolve_symbol("Description");
        let text_term = self.kb.alloc(Term::Const(super::term::Literal::String(text.to_string())));

        // Track description index per target
        let idx = self.desc_index.entry(target.raw()).or_insert(0);
        let index_term = self.kb.alloc(Term::Const(super::term::Literal::Int(*idx)));
        *idx += 1;

        let desc_fact = self.kb.alloc(Term::Fn {
            functor: desc_sym,
            pos_args: SmallVec::from_slice(&[target, text_term, index_term]),
            named_args: SmallVec::new(),
        });
        self.kb.assert_fact(desc_fact, desc_sort, domain, None);
    }

    /// Convert a list of clauses (each a Vec<TermId>) into a cons-list.
    /// Multi-goal clauses are wrapped in a conjunction term.
    fn convert_clause_list(&mut self, clauses: &[Vec<TermId>]) -> TermId {
        let clause_terms: Vec<TermId> = clauses
            .iter()
            .map(|clause| {
                let goal_terms: Vec<TermId> = clause.iter().map(|&tid| self.convert_term(tid)).collect();
                if goal_terms.len() == 1 {
                    goal_terms[0]
                } else {
                    let conj_sym = self.kb.intern("conjunction");
                    self.kb.alloc(Term::Fn {
                        functor: conj_sym,
                        pos_args: SmallVec::from_vec(goal_terms),
                        named_args: SmallVec::new(),
                    })
                }
            })
            .collect();
        build_list(self.kb, &clause_terms)
    }

    // ── Member fact emission ───────────────────────────────────

    fn emit_member_fact(&mut self, name_sym: Symbol, kind_str: &str, parent: TermId) {
        let member_sym = self.kb.resolve_symbol("member");
        let member_sort = self.kb.make_name_term("Member");
        let name_term = self.kb.make_name_term_from_sym(name_sym);
        let kind_sym = self.kb.intern(kind_str);
        let kind_term = self.kb.alloc(Term::Ident(kind_sym));
        let member_term = self.kb.alloc(Term::Fn {
            functor: member_sym,
            pos_args: SmallVec::from_slice(&[name_term, kind_term, parent]),
            named_args: SmallVec::new(),
        });
        self.kb.assert_fact(member_term, member_sort, parent, None);
    }

    fn emit_member_facts_for_items(&mut self, items: &[Item], parent: TermId) {
        for item in items {
            match item {
                Item::Entity(e) => {
                    let sym = self.remap_name(&e.name);
                    self.emit_member_fact(sym, "Constructor", parent);
                }
                Item::AbstractSort(s) => {
                    let sym = self.remap_name(&s.name);
                    self.emit_member_fact(sym, "Sort", parent);
                }
                Item::SortWithBody(s) => {
                    let sym = self.remap_name(&s.name);
                    self.emit_member_fact(sym, "Sort", parent);
                }
                Item::Operation(o) => {
                    let sym = self.remap_name(&o.name);
                    self.emit_member_fact(sym, "Operation", parent);
                }
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        let sym = self.remap_name(&op.name);
                        self.emit_member_fact(sym, "Operation", parent);
                    }
                }
                Item::Rule(r) => {
                    if let Some(ref label) = r.label {
                        let sym = self.remap_name(label);
                        self.emit_member_fact(sym, "Rule", parent);
                    }
                }
                Item::RuleBlock(rb) => {
                    for rule in &rb.entries {
                        if let Some(ref label) = rule.label {
                            let sym = self.remap_name(label);
                            self.emit_member_fact(sym, "Rule", parent);
                        }
                    }
                }
                Item::Namespace(n) => {
                    let sym = self.remap_name(&n.name);
                    self.emit_member_fact(sym, "Namespace", parent);
                }
                _ => {}
            }
        }
    }

    fn load_meta_block(&mut self, mb: &MetaBlock) -> TermId {
        let meta_sym = self.kb.resolve_symbol("meta");
        let named_args: SmallVec<[(Symbol, TermId); 2]> = mb.entries
            .iter()
            .map(|e| {
                let key_sym = self.reintern(e.key.last());
                let val = self.convert_term(e.value);
                (key_sym, val)
            })
            .collect();
        self.kb.alloc(Term::Fn {
            functor: meta_sym,
            pos_args: SmallVec::new(),
            named_args,
        })
    }
}
