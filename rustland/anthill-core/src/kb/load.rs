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

use smallvec::SmallVec;

use crate::intern::{Symbol, SymbolDef, SymbolKind, ScopeInclusion, ResolveResult};
use crate::parse::ir::*;
use crate::span::Span;
use super::{KnowledgeBase, SortKind};
use super::term::{Term, TermId, VarId};

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
        scan_items_pass1(kb, &file.items, &file.symbols, global, "");
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
/// in effects clauses (e.g., `effects (Modify{store})` where `store` is a parameter).
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
fn scan_items_pass1(
    kb: &mut KnowledgeBase,
    items: &[Item],
    parse_sym: &crate::intern::SymbolTable,
    scope: TermId,
    prefix: &str,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                let sym = kb.symbols.define(&short, &qualified, SymbolKind::Sort, actual_scope.raw());
                let sort_term = kb.alloc(Term::Fn {
                    functor: sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                });
                // Implicit parent: the enclosing scope is visible from within the sort
                kb.symbols.add_parent(sort_term.raw(), ScopeInclusion {
                    parent_scope_raw: actual_scope.raw(),
                    instantiation_term_raw: actual_scope.raw(),
                    is_enclosing: true,
                });
                // Record exports
                for export_name in &s.exports {
                    let n = join_segments(parse_sym, &export_name.segments);
                    kb.symbols.add_export(sort_term.raw(), &n);
                }
                // Recurse into sort body with the sort's qualified name as prefix
                scan_items_pass1(kb, &s.items, parse_sym, sort_term, &qualified);
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
                scan_items_pass1(kb, &n.items, parse_sym, ns_term, &qualified);
            }
            Item::Entity(e) => {
                let name = join_segments(parse_sym, &e.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                kb.symbols.define(&short, &qualified, SymbolKind::Entity, actual_scope.raw());
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
                if let Some(ref label) = r.label {
                    let name = join_segments(parse_sym, &label.segments);
                    let qualified = make_qualified(prefix, &name);
                    kb.symbols.define(&name, &qualified, SymbolKind::Rule, scope.raw());
                }
            }
            Item::RuleBlock(rb) => {
                for rule in &rb.entries {
                    if let Some(ref label) = rule.label {
                        let name = join_segments(parse_sym, &label.segments);
                        let qualified = make_qualified(prefix, &name);
                        kb.symbols.define(&name, &qualified, SymbolKind::Rule, scope.raw());
                    }
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

/// Build an instantiation term for `requires Eq{T}`.
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
            let sort_sym = kb.symbols.find_sort_symbol(&sort_name)
                .unwrap_or_else(|| kb.symbols.intern(&sort_name));
            let named_args: SmallVec<[(Symbol, TermId); 2]> = bindings.iter().map(|b| {
                let key = kb.symbols.intern(&join_segments(parse_sym, &b.param.segments));
                let val = build_instantiation_term(kb, parse_sym, &b.bound, _current_scope);
                (key, val)
            }).collect();
            kb.alloc(Term::Fn {
                functor: sort_sym,
                pos_args: SmallVec::new(),
                named_args,
            })
        }
        TypeExpr::Variable { .. } => {
            // Variable in type position → just use a placeholder name term
            kb.make_name_term("?")
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
pub const PRELUDE_SORTS: &[&str] = &["Int", "Float", "String", "Bool"];

/// Register primitive sorts in the global scope so they are always resolvable.
///
/// Call this before `scan_definitions` / `load` to ensure that references to
/// `Int`, `Float`, `String`, `Bool` never produce unresolved-name errors.
pub fn register_prelude(kb: &mut KnowledgeBase) {
    let global = kb.make_name_term("_global");
    for &name in PRELUDE_SORTS {
        kb.symbols.define(name, name, SymbolKind::Sort, global.raw());
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
    // Phase 1: Scan definitions from this file
    let mut all_errors = scan_definitions(kb, &[parsed]);
    // Phase 2: Load
    let mut loaded_paths = HashSet::new();
    if let Err(errs) = load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
        all_errors.extend(errs);
    }
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
    // Phase 1: Scan all definitions across all files
    let mut all_errors = scan_definitions(kb, files);

    // Phase 2: Load files with scope-aware resolution
    let mut loaded_paths = HashSet::new();
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
    let global = kb.make_name_term("_global");
    let mut loader = Loader::new(kb, parsed, resolver, loaded_paths, global);
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
    // Map from parse-time Symbol → KB Symbol (for reintern — plain intern)
    sym_map: HashMap<u32, Symbol>,
    // Map from parse-time VarId → KB VarId
    var_map: HashMap<u32, VarId>,
    errors: Vec<LoadError>,
    // Current scope for scope-aware resolution
    current_scope: TermId,
}

impl<'a> Loader<'a> {
    fn new(
        kb: &'a mut KnowledgeBase,
        parsed: &'a ParsedFile,
        resolver: &'a dyn SourceResolver,
        loaded_paths: &'a mut HashSet<String>,
        global_scope: TermId,
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
            current_scope: global_scope,
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
            ResolveResult::NotFound => self.kb.symbols.intern(name),
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
                let new_pos: SmallVec<[TermId; 4]> = pos_args
                    .iter()
                    .map(|&id| self.convert_term(id))
                    .collect();
                let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                    .iter()
                    .map(|&(sym, id)| (self.reintern(sym), self.convert_term(id)))
                    .collect();
                Term::Fn { functor: new_functor, pos_args: new_pos, named_args: new_named }
            }
            Term::Ref(sym) => {
                let new_sym = self.remap_symbol(sym);
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
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for b in bindings {
                    let param_sym = self.reintern(b.param.last());
                    let bound_term = self.type_expr_to_term(&b.bound);
                    named_args.push((param_sym, bound_term));
                }

                let param_type_sym = self.kb.intern("ParameterizedType");
                self.kb.alloc(Term::Fn {
                    functor: param_type_sym,
                    pos_args: SmallVec::from_elem(name_term, 1),
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
                Item::Project(p) => self.load_project(p, domain),
                Item::Tool(t) => self.load_tool(t, domain),
                Item::WorkItem(w) => self.load_workitem(w, domain),
                Item::Feedback(f) => self.load_feedback(f, domain),
                Item::ImportTools(it) => self.load_import_tools(it, domain),
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
        let alias_sym = self.kb.intern("SortAlias");
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

        // Assert SortInfo fact
        let sort_info_sym = self.kb.intern("SortInfo");
        let kind_str = if has_entities { "Defined" } else { "Abstract" };
        let kind_sym = self.kb.intern(kind_str);
        let kind_term = self.kb.alloc(Term::Ident(kind_sym));
        let fact_term = self.kb.alloc(Term::Fn {
            functor: sort_info_sym,
            pos_args: SmallVec::from_slice(&[sort_term, kind_term]),
            named_args: SmallVec::new(),
        });
        self.kb.assert_fact(fact_term, sort_sort, parent_domain, None);

        // Emit Description facts for all description blocks
        for desc_text in &s.descriptions {
            self.emit_desc_fact(sort_term, desc_text, parent_domain);
        }

        // Set scope to sort for child resolution
        let prev_scope = self.current_scope;
        self.current_scope = sort_term;

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
                    pos_args: SmallVec::from_slice(&[ctor_term, sort_term]),
                    named_args: SmallVec::new(),
                });
                self.kb.assert_fact(subsort_fact, sort_sort, parent_domain, None);
            }
        }

        // Emit member facts for direct children
        self.emit_member_facts_for_items(&s.items, sort_term);

        // Load all items within this sort's domain scope
        self.load_items(&s.items, Some(sort_term));

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

        let entity_term = self.kb.alloc(Term::Fn { functor, pos_args: SmallVec::new(), named_args });
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

        let head_term = match &r.head {
            RuleHead::Term(tid) => self.convert_term(*tid),
            RuleHead::Bottom => self.kb.alloc(Term::Bottom),
        };

        let body: Vec<TermId> = r.body.as_ref()
            .map(|terms| terms.iter().map(|&tid| self.convert_term(tid)).collect())
            .unwrap_or_default();

        let meta = r.meta.as_ref().map(|mb| self.load_meta_block(mb));
        self.kb.assert_rule(head_term, body, rule_sort, domain, meta);
    }

    fn load_operation(&mut self, o: &Operation, domain: TermId) {
        let op_sort = self.kb.make_name_term("Operation");
        let functor = self.remap_name(&o.name);

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

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = o.params
            .iter()
            .map(|p| {
                let param_sym = self.reintern(p.name);
                let type_term = self.type_expr_to_term(&p.ty);
                (param_sym, type_term)
            })
            .collect();

        let ret_sym = self.kb.intern("_returns");
        named_args.push((ret_sym, return_term));

        // Store effects as _effects(E1, E2, ...) named arg
        if !o.effects.is_empty() {
            let effect_terms: SmallVec<[TermId; 4]> = o.effects
                .iter()
                .map(|e| self.type_expr_to_term(&e.type_expr))
                .collect();
            let effects_functor = self.kb.intern("_effects");
            let effects_term = self.kb.alloc(Term::Fn {
                functor: effects_functor,
                pos_args: effect_terms,
                named_args: SmallVec::new(),
            });
            let effects_sym = self.kb.intern("_effects");
            named_args.push((effects_sym, effects_term));
        }

        self.current_scope = prev_scope;

        let op_term = self.kb.alloc(Term::Fn { functor, pos_args: SmallVec::new(), named_args });
        self.kb.assert_fact(op_term, op_sort, domain, None);
    }

    fn load_constraint(&mut self, c: &Constraint, domain: TermId) {
        let constraint_sort = self.kb.make_name_term("Constraint");
        let constraint_sym = self.kb.intern("Constraint");

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
        let requires_sym = self.kb.intern("Requires");
        let type_term = self.type_expr_to_term(&r.type_expr);
        let requires_term = self.kb.alloc(Term::Fn {
            functor: requires_sym,
            pos_args: SmallVec::from_elem(type_term, 1),
            named_args: SmallVec::new(),
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
        let desc_sym = self.kb.intern("Description");
        let text_term = self.kb.alloc(Term::Const(super::term::Literal::String(text.to_string())));
        let desc_fact = self.kb.alloc(Term::Fn {
            functor: desc_sym,
            pos_args: SmallVec::from_slice(&[target, text_term]),
            named_args: SmallVec::new(),
        });
        self.kb.assert_fact(desc_fact, desc_sort, domain, None);
    }

    fn load_project(&mut self, p: &Project, domain: TermId) {
        let project_sort = self.kb.make_name_term("Project");
        let functor = self.reintern_name(&p.name);

        let project_term = self.kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
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
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(cmd_sym, cmd_term)]),
        });

        self.kb.assert_fact(tool_term, tool_sort, domain, None);
    }

    fn load_workitem(&mut self, w: &WorkItem, domain: TermId) {
        let wi_sort = self.kb.make_name_term("WorkItem");
        let functor = self.reintern_name(&w.id);

        let status_term = self.load_work_status(&w.status);
        let status_sym = self.kb.intern("status");

        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named_args.push((status_sym, status_term));

        if let Some(desc_id) = w.description {
            let desc = self.convert_term(desc_id);
            let desc_sym = self.kb.intern("description");
            named_args.push((desc_sym, desc));
        }

        let wi_term = self.kb.alloc(Term::Fn { functor, pos_args: SmallVec::new(), named_args });

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
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });

        let content_term = self.convert_term(f.content);
        let wi_arg_sym = self.kb.intern("workitem");
        let content_sym = self.kb.intern("content");

        let feedback_term = self.kb.alloc(Term::Fn {
            functor: feedback_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (wi_arg_sym, wi_term),
                (content_sym, content_term),
            ]),
        });

        self.kb.assert_fact(feedback_term, feedback_sort, domain, None);
    }

    fn load_import_tools(&mut self, it: &ImportTools, _domain: TermId) {
        for name in &it.names {
            let path = join_segments(&self.parsed.symbols, &name.segments);
            if self.loaded_paths.contains(&path) {
                continue;
            }
            self.loaded_paths.insert(path.clone());

            match self.resolver.resolve(&path) {
                Ok(source) => {
                    match crate::parse::parse(&source) {
                        Ok(imported) => {
                            // Scan definitions from the imported file before loading
                            let scan_errs = scan_definitions(self.kb, &[&imported]);
                            self.errors.extend(scan_errs);
                            if let Err(errs) = load_with_visited(
                                self.kb, &imported, self.resolver, self.loaded_paths,
                            ) {
                                self.errors.extend(errs);
                            }
                        }
                        Err(parse_errs) => {
                            for pe in parse_errs {
                                self.errors.push(LoadError::Other {
                                    message: format!("parse error in import '{}': {}", path, pe.message),
                                });
                            }
                        }
                    }
                }
                Err(e) => {
                    self.errors.push(LoadError::Other {
                        message: format!("cannot resolve import '{}': {}", path, e),
                    });
                }
            }
        }
    }

    // ── Member fact emission ───────────────────────────────────

    fn emit_member_fact(&mut self, name_sym: Symbol, kind_str: &str, parent: TermId) {
        let member_sym = self.kb.intern("member");
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
        let meta_sym = self.kb.intern("meta");
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
