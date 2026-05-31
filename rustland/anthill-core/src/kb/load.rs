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
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::{Symbol, SymbolDef, SymbolKind, ScopeInclusion, ResolveResult};
use crate::parse::ir::*;
use crate::span::{Span, SourceId, SourceSpan};
use super::{KnowledgeBase, SortKind};
use super::term::{Term, TermId, Var, VarId, Literal};
use super::node_occurrence::{self, Expr, NodeOccurrence};
use super::typing::{extract_type_param, get_named_arg, list_to_vec};

// ── Load result ──────────────────────────────────────────────

/// Result of loading a file or set of files.
/// Contains the sort/enum terms defined, for targeted type checking.
#[derive(Debug, Default)]
pub struct LoadResult {
    /// Sort and enum terms defined during this load.
    pub defined_sorts: Vec<TermId>,
    /// RuleIds of facts asserted during this load, in source order.
    /// Parallel with `parsed.fact_spans()` so persistence backends can
    /// pair each fact's RuleId with its source byte range.
    pub fact_rule_ids: Vec<crate::kb::RuleId>,
}

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
    TypeMismatch {
        entity_name: String,
        field_name: String,
        expected_type: String,
        actual_type: String,
        span: Option<Span>,
    },
    /// WI-343: a carrier provides a spec whose own `requires` is not
    /// satisfied by that carrier — e.g. `fact PersistentCollection[List]`
    /// where `PersistentCollection requires Iterable` but `List` provides
    /// no `Iterable`. The satisfaction fact is unsound: the spec's contract
    /// does not hold for the carrier.
    UnsatisfiedProviderRequires {
        carrier: String,
        spec: String,
        required: String,
    },
    Other {
        message: String,
    },
}

impl LoadError {
    /// Format with line:col using source text, like ParseError::format_with_source.
    pub fn format_with_source(&self, source: &str) -> String {
        match self {
            LoadError::UnresolvedName { name, span, scope_name } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: unresolved name '{}' in scope '{}'", line, col, name, scope_name)
            }
            LoadError::UnresolvedImport { path, span } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: unresolved import '{}'", line, col, path)
            }
            LoadError::AmbiguousSymbol { name, candidates, span, scope_name } => {
                let (line, col) = Span::line_col(source, span.start);
                format!("{}:{}: ambiguous symbol '{}' in scope '{}': candidates {:?}", line, col, name, scope_name, candidates)
            }
            LoadError::TypeMismatch { entity_name, field_name, expected_type, actual_type, span } => {
                if let Some(sp) = span {
                    let (line, col) = Span::line_col(source, sp.start);
                    format!("{}:{}: type mismatch in {}.{}: expected {}, got {}", line, col, entity_name, field_name, expected_type, actual_type)
                } else {
                    format!("type mismatch in {}.{}: expected {}, got {}", entity_name, field_name, expected_type, actual_type)
                }
            }
            LoadError::UnsatisfiedProviderRequires { carrier, spec, required } => {
                format!("'{}' provides '{}', which requires '{}', but '{}' does not provide '{}' (add a `fact {}[…]` for the carrier)",
                    carrier, spec, required, carrier, required, required)
            }
            LoadError::Other { message } => {
                format!("load error: {}", message)
            }
        }
    }

    /// Errors that block load — execution must not proceed:
    /// - `TypeMismatch`: ill-typed program is unsound.
    /// - `UnresolvedImport`: imported names won't bind a local alias, so
    ///   any use-site that refers to them by short name relies on
    ///   accidental scope walks; better to fail at load time than silently
    ///   resolve to the wrong (or no) symbol.
    pub fn is_load_blocking(&self) -> bool {
        matches!(self,
            LoadError::TypeMismatch { .. }
            | LoadError::UnresolvedImport { .. }
            | LoadError::UnsatisfiedProviderRequires { .. })
    }
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
            LoadError::TypeMismatch { entity_name, field_name, expected_type, actual_type, span } => {
                if let Some(sp) = span {
                    write!(f, "type mismatch in {}.{}: expected {}, got {} at {}..{}", entity_name, field_name, expected_type, actual_type, sp.start, sp.end)
                } else {
                    write!(f, "type mismatch in {}.{}: expected {}, got {}", entity_name, field_name, expected_type, actual_type)
                }
            }
            LoadError::UnsatisfiedProviderRequires { carrier, spec, required } => {
                write!(f, "'{}' provides '{}', which requires '{}', but '{}' does not provide '{}'",
                    carrier, spec, required, carrier, required)
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

    // Sub-pass 2: process requires and imports (all sorts exist now). A
    // Selective import of a rule-defined predicate can't resolve here — its
    // head-functor Goal isn't registered until sub-pass 3 — so such names are
    // deferred into `pending` and retried below (WI-295).
    let mut errors = Vec::new();
    let mut pending: Vec<PendingImport> = Vec::new();
    for file in files {
        scan_items_pass2(kb, &file.items, &file.symbols, global, "", &mut errors, &mut pending);
    }

    // Sub-pass 3: register unlabeled rule head-functor Goals, binding to an
    // inherited/existing origin where one resolves (proposal 044 / B2).
    for file in files {
        scan_items_pass3(kb, &file.items, &file.symbols, &file.terms, global, "");
    }

    // Sub-pass 4 (WI-295): retry deferred predicate imports. Head-functor Goals
    // from sub-pass 3 are now in `by_qualified_name`, so a cross-namespace
    // rule-predicate import resolves like any declared name. (Resolve by
    // symbol, not `by_functor` — rules aren't asserted until the load phase.)
    for p in pending {
        match kb.symbols.by_qualified_name.get(&p.qualified).copied() {
            Some(sym) => kb.symbols.add_import(p.scope_raw, &p.short, sym),
            None => errors.push(LoadError::UnresolvedImport { path: p.qualified, span: p.span }),
        }
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

/// Create an operation scope and define its parameters plus the reserved
/// `result` name (proposal 041).
///
/// Operations always get their own scope so that:
/// - Parameter names are resolvable in effects clauses (e.g., `effects
///   (Modify[store])` where `store` is a parameter).
/// - The reserved name `result` is resolvable in effects and ensures
///   positions to refer to the operation's return value (proposal 041).
///   For named-tuple returns, components are accessed via the existing
///   field-projection syntax (`result.a`, per kernel-language.md §6.7).
///
/// Param-name conflict with `result` is checked at load time
/// (`load_operation`), not here — scan only defines symbols.
fn scan_operation_params(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    op: &Operation,
    op_sym: Symbol,
    enclosing_scope: TermId,
    prefix: &str,
) {
    // Allocate the scope term unconditionally so paramless ops still
    // resolve `result`.
    let op_term = kb.make_name_term_from_sym(op_sym);
    kb.symbols.add_parent(op_term.raw(), ScopeInclusion {
        parent_scope_raw: enclosing_scope.raw(),
        instantiation_term_raw: enclosing_scope.raw(),
        is_enclosing: true,
    });

    // Register each op type param as a Sort symbol AND flag it as a
    // type-param so bare uses (`x: T`) route through the type-param
    // branch in `type_expr_to_term` — same mechanism as `sort T = ?`
    // inside a sort body.
    for tp in &op.type_params {
        let tp_name = parse_sym.name(tp.name);
        let qualified = make_qualified(prefix, tp_name);
        kb.symbols.define(tp_name, &qualified, SymbolKind::Sort, op_term.raw());
        kb.symbols.add_type_param(op_term.raw(), tp_name);
    }

    for p in &op.params {
        let param_name = parse_sym.name(p.name);
        // Skip param-name `result` here; the load pass reports the
        // collision with the reserved return-value name.
        if param_name == "result" {
            continue;
        }
        let qualified = make_qualified(prefix, param_name);
        kb.symbols.define(param_name, &qualified, SymbolKind::Param, op_term.raw());
    }
    let result_qualified = make_qualified(prefix, "result");
    let result_sym = kb.symbols.define("result", &result_qualified, SymbolKind::Param, op_term.raw());
    // WI-341 step 1: record the result-binder symbol so `kb::region`
    // recognises an effect's result-region resource by symbol identity
    // rather than by parsing the symbol's spelling.
    kb.register_result_binder(result_sym);

    // Pre-register `result.<field>` for each named-tuple return component.
    // Effects rows take *types*, not general term expressions, so the dot
    // in `Modify[result.a]` is treated as part of a qualified name rather
    // than as field-access (§6.7). Pre-registering these locals lets
    // qualified-name lookup find them.
    //
    // Workaround pending WI-262 (type-level field projection). When that
    // lands this block can be removed and projection handled uniformly by
    // the resolver/typer for params of entity/tuple type as well.
    if let crate::parse::ir::TypeExpr::Tuple(fields) = &op.return_type {
        for (field_sym, _field_ty) in fields {
            let field_name = parse_sym.name(*field_sym);
            let dotted = format!("result.{}", field_name);
            let qualified = make_qualified(prefix, &dotted);
            kb.symbols.define(&dotted, &qualified, SymbolKind::Param, op_term.raw());
        }
    }
}

/// Sub-pass 1: define all names, record exports and type params.
///
/// `prefix` is the fully-qualified path of the enclosing scope (empty at top level).
/// Nested items get `qualified_name = prefix + "." + name`.
/// Define a rule's label as a scoped symbol (pass 1). The head-functor Goal
/// identity is registered later, in `scan_rule_goal` (pass 3), once `requires`
/// parents are wired — see proposal 044.
fn scan_rule(
    kb: &mut KnowledgeBase,
    r: &Rule,
    parse_sym: &crate::intern::SymbolTable,
    scope: TermId,
    prefix: &str,
) {
    if let Some(ref label) = r.label {
        let name = join_segments(parse_sym, &label.segments);
        let qualified = make_qualified(prefix, &name);
        kb.symbols.define(&name, &qualified, SymbolKind::Rule, scope.raw());
    }
}

/// Register an unlabeled rule's head functor as a scoped Goal symbol — UNLESS
/// the name already resolves in scope (proposal 044 / B2). The transitional
/// load strategy (proposal 032) is:
///
///   * labeled rule: the label IS the rule's identity (registered in pass 1);
///     no separate Goal entry is needed.
///   * unlabeled single-head rule: the head functor IS the rule's identity.
///
/// B2: when the head functor already resolves — an operation inherited via
/// `requires` (e.g. `Ordered`'s `eq` law resolving to `Eq.eq`), or a locally
/// declared operation — the rule binds to that ORIGIN symbol instead of
/// minting a shadowing sort-local `Goal`. Only a genuinely-new head predicate
/// (NotFound) gets a fresh Goal. Runs in pass 3 so the `requires` parent chain
/// is already wired.
fn scan_rule_goal(
    kb: &mut KnowledgeBase,
    r: &Rule,
    parse_sym: &crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
    scope: TermId,
    prefix: &str,
) {
    if r.label.is_some() {
        return;
    }
    if let Some(functor_name) = unlabeled_head_functor_name(r, parse_sym, parse_terms) {
        if matches!(
            kb.symbols.resolve_in_scope(functor_name, scope.raw()),
            crate::intern::ResolveResult::NotFound
        ) {
            let qualified = make_qualified(prefix, functor_name);
            kb.symbols.define(functor_name, &qualified, SymbolKind::Goal, scope.raw());
        }
    }
}

/// For an unlabeled rule with a single positive Fn head, return the
/// head's functor name. Multi-head, denial, or non-Fn heads return
/// None.
fn unlabeled_head_functor_name<'a>(
    r: &Rule,
    parse_sym: &'a crate::intern::SymbolTable,
    parse_terms: &SimpleTermStore,
) -> Option<&'a str> {
    if r.heads.len() != 1 {
        return None;
    }
    if let RuleHead::Term(tid) = &r.heads[0] {
        if let Term::Fn { functor, .. } = parse_terms.get(*tid) {
            return Some(parse_sym.name(*functor));
        }
    }
    None
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
                // Model C / job 2: user `export` statements (s.exports) have
                // NO effect — names are visible by default. The `exports` set
                // now holds ONLY entity-variant names (populated below), so the
                // export-filter on the variant-exposure parent link leaks just
                // the constructor variants, never the sort's operations.
                //
                // Expose the sort's constructor variants to the enclosing
                // scope: add each `entity` child short-name to the sort's
                // exports and link the sort scope as a non-enclosing parent of
                // `actual_scope`. The export-filtered parent walk in
                // `resolve_in_scope` then resolves bare `Open` to
                // `WorkStatus.Open` from the namespace, and two sorts sharing a
                // variant name resolve to `Ambiguous` rather than one winning.
                //
                // The parent link is added only when the sort has variants: an
                // empty `exports` set disables the filter (a no-entity sort, e.g.
                // a spec, is reachable only via `requires`/wildcard, which should
                // see all its operations).
                let mut has_variant = false;
                for item in &s.items {
                    if let Item::Entity(e) = item {
                        let vshort = parse_sym.name(*e.name.segments.last().unwrap());
                        kb.symbols.add_exposed(sort_term.raw(), vshort);
                        has_variant = true;
                    }
                }
                if is_new && has_variant {
                    kb.symbols.add_parent(actual_scope.raw(), ScopeInclusion {
                        parent_scope_raw: sort_term.raw(),
                        instantiation_term_raw: sort_term.raw(),
                        is_enclosing: false,
                    });
                }
                // Recurse into sort body with the sort's qualified name as prefix
                scan_items_pass1(kb, &s.items, parse_sym, parse_terms, sort_term, &qualified);
            }
            Item::AbstractSort(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let (short, actual_scope) = ensure_intermediate_namespaces(kb, &name, scope, prefix);
                let qualified = make_qualified(prefix, &name);
                let _sym = kb.symbols.define(&short, &qualified, SymbolKind::Sort, actual_scope.raw());
                // `sort T = ?` inside a SortWithBody or EnumDecl = type parameter
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
                // Model C / job 2: user `export` statements (n.exports) have no
                // effect — namespace members are visible by default.
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
                scan_rule(kb, r, parse_sym, scope, prefix);
            }
            Item::RuleBlock(rb) => {
                for rule in &rb.entries {
                    scan_rule(kb, rule, parse_sym, scope, prefix);
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
    pending: &mut Vec<PendingImport>,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let name = join_segments(parse_sym, &s.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(sort_term) = find_scope_by_name(kb, &qualified) {
                    process_imports(kb, parse_sym, &s.imports, sort_term, errors, pending);
                    scan_items_pass2(kb, &s.items, parse_sym, sort_term, &qualified, errors, pending);
                }
            }
            Item::Namespace(n) => {
                let name = join_segments(parse_sym, &n.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(ns_term) = find_scope_by_name(kb, &qualified) {
                    // Process namespace-level imports
                    process_imports(kb, parse_sym, &n.imports, ns_term, errors, pending);
                    // Recurse
                    scan_items_pass2(kb, &n.items, parse_sym, ns_term, &qualified, errors, pending);
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

/// Sub-pass 3: register unlabeled rule head functors as Goal symbols, now that
/// `requires`/import parents are wired (pass 2). A head functor that already
/// resolves — an inherited operation or a locally declared one — binds to that
/// origin rather than minting a shadowing sort-local symbol (proposal 044 / B2).
fn scan_items_pass3(
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
                let qualified = make_qualified(prefix, &name);
                if let Some(sort_term) = find_scope_by_name(kb, &qualified) {
                    scan_items_pass3(kb, &s.items, parse_sym, parse_terms, sort_term, &qualified);
                }
            }
            Item::Namespace(n) => {
                let name = join_segments(parse_sym, &n.name.segments);
                let qualified = make_qualified(prefix, &name);
                if let Some(ns_term) = find_scope_by_name(kb, &qualified) {
                    scan_items_pass3(kb, &n.items, parse_sym, parse_terms, ns_term, &qualified);
                }
            }
            Item::Rule(r) => scan_rule_goal(kb, r, parse_sym, parse_terms, scope, prefix),
            Item::RuleBlock(rb) => {
                for rule in &rb.entries {
                    scan_rule_goal(kb, rule, parse_sym, parse_terms, scope, prefix);
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
        TypeExpr::Arrow { effects, .. } if !effects.is_empty() => "arrow_effect".to_owned(),
        TypeExpr::Arrow { .. } => "arrow".to_owned(),
        TypeExpr::Denoted(_) => "denoted".to_owned(),
        // WI-327: nested base name peeks past the absence wrapper.
        TypeExpr::EffectAbsent(inner) => type_expr_base_name(parse_sym, inner),
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

/// Walk one level of nested scopes under `base_path` looking for a symbol
/// whose short name is `short`. Returns the symbol when exactly one match
/// is found (multiple matches → ambiguous, no match → none).
///
/// Used by selective-import resolution to find enum entities, which live
/// inside the enum's sort scope rather than directly under the surrounding
/// namespace. For example, `parse_ok` in
///   namespace ns
///     enum E { entity parse_ok(...) }
///   end
/// has qualified name `ns.E.parse_ok`, not `ns.parse_ok`. An import
/// `ns.{parse_ok}` should still bind it.
fn find_in_nested_scope(
    kb: &KnowledgeBase,
    base_path: &str,
    short: &str,
) -> Option<crate::intern::Symbol> {
    let needle_suffix = format!(".{short}");
    let prefix = format!("{base_path}.");
    let mut matches: SmallVec<[crate::intern::Symbol; 2]> = SmallVec::new();
    for (qname, sym) in kb.symbols.by_qualified_name.iter() {
        if !qname.starts_with(&prefix) || !qname.ends_with(&needle_suffix) {
            continue;
        }
        // Require exactly one intermediate segment between base and short:
        // base.<intermediate>.short. Keeps the search to immediate children
        // of the base scope (enums and named sub-scopes), not deeper trees.
        let middle = &qname[prefix.len()..qname.len() - needle_suffix.len()];
        if middle.is_empty() || middle.contains('.') {
            continue;
        }
        matches.push(*sym);
    }
    matches.sort_by_key(|s| s.index());
    matches.dedup();
    if matches.len() == 1 { Some(matches[0]) } else { None }
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
        // WI-302: value-in-type in a fact/provides binding. This free-fn path
        // has no access to the expr-occurrence builder; emit a placeholder
        // `denoted` for now (rare; the operation-signature path is the real one).
        TypeExpr::Denoted(_) => {
            let placeholder = kb.make_name_term("?");
            kb.make_denoted(placeholder)
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
        TypeExpr::Arrow { params, return_type, effects } => {
            let functor = if !effects.is_empty() {
                kb.symbols.intern("arrow_effect")
            } else {
                kb.symbols.intern("arrow")
            };
            let mut pos_args: SmallVec<[TermId; 4]> = params.iter()
                .map(|(_, p)| build_instantiation_term(kb, parse_sym, p, _current_scope))
                .collect();
            let ret = build_instantiation_term(kb, parse_sym, return_type, _current_scope);
            pos_args.push(ret);
            for eff in effects {
                let eff_term = build_instantiation_term(kb, parse_sym, eff, _current_scope);
                pos_args.push(eff_term);
            }
            kb.alloc(Term::Fn {
                functor,
                pos_args,
                named_args: SmallVec::new(),
            })
        }
        // WI-327: instantiation-term position for `-E` is not yet used
        // by any caller (absence forms only appear in effects positions,
        // which take the separate make_arrow_type path). Build a
        // placeholder so the match is total; if a caller ever lands a
        // `-E` here it'll surface as a malformed-name binding rather
        // than a panic.
        TypeExpr::EffectAbsent(_) => kb.make_name_term("?absent"),
    }
}

/// WI-295: a `Selective` import name that didn't resolve in sub-pass 2. A
/// rule-defined predicate's head-functor symbol isn't registered until
/// sub-pass 3 (`scan_rule_goal`), so cross-namespace predicate imports are
/// deferred and re-resolved by `scan_definitions`'s post-pass-3 retry.
struct PendingImport {
    scope_raw: u32,
    short: String,
    qualified: String,
    span: Span,
}

/// Process `import` declarations → register imported names and parent scopes.
/// Unresolvable import paths produce errors (deferred predicate imports go to
/// `pending` for the post-pass-3 retry — see `PendingImport`).
fn process_imports(
    kb: &mut KnowledgeBase,
    parse_sym: &crate::intern::SymbolTable,
    imports: &[Import],
    scope: TermId,
    errors: &mut Vec<LoadError>,
    pending: &mut Vec<PendingImport>,
) {
    for imp in imports {
        let raw_path = join_segments(parse_sym, &imp.path.segments);
        // Implicit-prelude fallback: a single-segment path like `Modify` that
        // doesn't resolve at top level falls back to `anthill.prelude.<path>`.
        // Mirrors the global short-name visibility of post-WI-215 prelude
        // effect sorts (Modify, Error, Suspension, Branch, MatchFailed).
        let path = if !raw_path.contains('.')
            && kb.symbols.by_qualified_name.get(&raw_path).is_none()
            && find_scope_by_name(kb, &raw_path).is_none()
        {
            let candidate = format!("anthill.prelude.{raw_path}");
            if kb.symbols.by_qualified_name.contains_key(&candidate)
                || find_scope_by_name(kb, &candidate).is_some()
            {
                candidate
            } else {
                raw_path
            }
        } else {
            raw_path
        };
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
                // Resolution strategies, in order:
                // 1. Direct qualified-name lookup (e.g., "anthill.prelude.Eq" as a
                //    top-level dotted name).
                // 2. Resolve short name within the base-path scope (catches names
                //    defined directly under the namespace).
                // 3. Walk one level of child sort/enum scopes within the base
                //    namespace. Without this, importing an enum entity by short
                //    name (`import anthill.cli.parse.{parse_ok}` where `parse_ok`
                //    is an entity inside `enum ParseResult`) fails, since its
                //    qualified name is `anthill.cli.parse.ParseResult.parse_ok`
                //    rather than `anthill.cli.parse.parse_ok`.
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
                    let original_sym = kb.symbols.by_qualified_name.get(&qualified).copied()
                        .or_else(|| {
                            base_scope.and_then(|bs| {
                                match kb.symbols.resolve_in_scope(&short, bs.raw()) {
                                    crate::intern::ResolveResult::Found(sym) => Some(sym),
                                    _ => None,
                                }
                            })
                        })
                        .or_else(|| find_in_nested_scope(kb, &path, &short));
                    if let Some(sym) = original_sym {
                        kb.symbols.add_import(scope.raw(), &short, sym);
                    } else {
                        // WI-295: a rule-defined predicate's head-functor symbol
                        // isn't registered until sub-pass 3 (scan_rule_goal),
                        // which runs after imports — so don't error yet. Defer
                        // to scan_definitions's post-pass-3 retry, which
                        // re-resolves it (erroring only if still unbound).
                        pending.push(PendingImport {
                            scope_raw: scope.raw(),
                            short,
                            qualified,
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

/// Effect sorts declared inside `namespace anthill.prelude` in
/// stdlib/anthill/prelude/effects.anthill that user code references by
/// short name (e.g. `effects {Modify[s], Error}`). Adding them to the
/// global scope's import list reproduces the implicit-prelude behaviour
/// that file-top-level bare `sort X` declarations had before WI-215.
pub const IMPLICIT_PRELUDE_EFFECTS: &[&str] =
    &["Modify", "Error", "Suspension", "Branch", "MatchFailed"];

/// Wire the implicit-prelude effect sorts (Modify, Error, …) into the
/// global scope's imports. Called after `scan_definitions` so the
/// qualified symbols already exist. Idempotent: re-adding an existing
/// import is harmless.
pub fn register_implicit_prelude_effects(kb: &mut KnowledgeBase) {
    let global_raw = kb.make_name_term("_global").raw();
    for &short in IMPLICIT_PRELUDE_EFFECTS {
        let qualified = format!("anthill.prelude.{short}");
        if let Some(&sym) = kb.symbols.by_qualified_name.get(&qualified) {
            kb.symbols.add_import(global_raw, short, sym);
        }
    }
}

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
    // WI-320 (proposal 045 §2.0.1) — emit the EffectsRuntime ↔ effects_rows
    // bridge fact. Lives here in Rust (not in stdlib/effects-runtime.anthill)
    // because surface `_type` doesn't admit entity-construction terms like
    // `effects_rows(?)` in type-arg position — that position is an
    // `application` (the `parameterized_type`/`instantiation_term` rules
    // were merged into one `application` rule under WI-311), and
    // `application` carries a type-arg list, not a value-position
    // entity-construction expression. The fact registers any
    // `effects_rows(...)`-shape Type as a valid `EffectsRuntime[Effects]`
    // binding — the kind discrimination for the `effects E = ? requires
    // EffectsRuntime[E]` desugaring.
    emit_effects_runtime_bridge_fact(kb);
}

/// Emit the WI-320 bridge fact:
/// `EffectsRuntime[Effects = effects_rows(effects_expr = ?fresh)]`.
///
/// Shape-analogous to `fact Effect[T = Modify[?]]` in effects.anthill — both
/// register a parameterized-sort-instantiation pattern as a satisfiable
/// goal — but emitted in Rust because the surface grammar's `_type` rule
/// does not admit entity-construction terms like `effects_rows(?)` in
/// type-arg position. The bridge is also *indexed differently* from the
/// stdlib precedent: a surface-syntax `fact F[…]` without a sort
/// annotation lands in `by_sort[Fact]` and `by_domain[<enclosing-scope>]`
/// (load_fact at load.rs ~5728, `f.sort.unwrap_or("Fact")`), whereas this
/// Rust-emitted fact uses `sort = domain = EffectsRuntime` to keep its
/// intent (a statement about EffectsRuntime) attached to its `by_sort` /
/// `by_domain` keys. Resolution still works through the discrim tree;
/// reflection consumers that enumerate `by_sort["Fact"]` won't see this
/// fact, which is intentional (it isn't a user-written fact). See
/// proposal 045 §2.0.1.
///
/// **Idempotency** — `register_prelude` is called more than once on the
/// same KB by the common test pattern (e.g. `register_prelude(&mut kb);
/// kb.register_standard_builtins(); load::load_all(&mut kb, …)` — `load_all`
/// itself re-enters `register_prelude`). `assert_rule_debruijn` does NOT
/// consult `fact_dedup` (only `assert_fact` does), so an unguarded second
/// call duplicates the rule entry in `by_sort` / `by_functor` / `by_domain`
/// / `discrim`. We therefore early-return when `by_functor[EffectsRuntime]`
/// is non-empty — at prelude-bootstrap time the bridge is the only fact
/// with this functor, so a non-empty entry means the bridge is already
/// installed.
fn emit_effects_runtime_bridge_fact(kb: &mut KnowledgeBase) {
    // Resolve the symbols. Both are unconditionally pre-registered by
    // `register_stdlib_scopes` above (line ~1187 for `effects_rows`, line
    // ~1258 for `EffectsRuntime`). A missing symbol here means
    // `register_stdlib_scopes` was bypassed or its definitions were
    // accidentally removed — a serious bootstrap regression. Per CLAUDE.md
    // (`avoid fallbacks, better know about errors early`) we panic with a
    // clear message rather than silently skipping the bridge (which would
    // leave the `requires EffectsRuntime[E]` desugaring undischargeable and
    // surface as a confusing "requires unmet" error at every effect-using
    // operation).
    let er_sort_sym = kb.try_resolve_symbol("anthill.prelude.EffectsRuntime").expect(
        "WI-320 bootstrap invariant: anthill.prelude.EffectsRuntime symbol \
         pre-registered by register_stdlib_scopes — see kb/load.rs",
    );
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.Type.effects_rows").expect(
        "WI-320 bootstrap invariant: anthill.prelude.Type.effects_rows symbol \
         pre-registered by register_stdlib_scopes — see kb/load.rs",
    );

    // Idempotency guard — see doc-comment above. The bridge is the only
    // rule with EffectsRuntime as its head functor at prelude bootstrap,
    // so a non-empty `by_functor` entry means it is already installed.
    if !kb.by_functor(er_sort_sym).is_empty() {
        return;
    }

    let effects_field_sym = kb.intern("Effects");
    let effects_expr_field_sym = kb.intern("effects_expr");

    // The inner wildcard — built as a Global var that `assert_rule_debruijn`
    // closes to `DeBruijn(0)` at rule finalization. The name `expr` is for
    // diagnostic display only (rendered as `?expr` by the pretty-printer's
    // sigil convention); equality / hash-cons key on VarId uses `id` only.
    let expr_var_name = kb.intern("expr");
    let expr_vid = kb.fresh_var(expr_var_name);
    let expr_var_term = kb.alloc(Term::Var(Var::Global(expr_vid)));

    // Build `effects_rows(effects_expr = ?expr)`.
    let effects_rows_term = kb.alloc(Term::Fn {
        functor: effects_rows_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(effects_expr_field_sym, expr_var_term)]),
    });

    // Build the head: `EffectsRuntime(Effects = effects_rows(effects_expr = ?expr))`.
    let head = kb.alloc(Term::Fn {
        functor: er_sort_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(effects_field_sym, effects_rows_term)]),
    });

    // The fact's sort is `EffectsRuntime` itself — same convention as the
    // stdlib's `fact Effect[T = Modify[?]]` (its fact sort is `Effect`).
    let er_sort_as_sort_term = kb.alloc(Term::Fn {
        functor: er_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });

    // Assert via `assert_rule_debruijn` to close the Global var to a
    // DeBruijn — fact = rule with empty body.
    kb.assert_rule_debruijn(head, vec![], er_sort_as_sort_term, er_sort_as_sort_term, None);
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

    // anthill.prelude.Type sort — type constructors for the typing pass
    let type_sort_sym = kb.symbols.define("Type", "anthill.prelude.Type", SymbolKind::Sort, prelude_term.raw());
    let type_sort_term = kb.alloc(Term::Fn {
        functor: type_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(type_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("sort_ref", "anthill.prelude.Type.sort_ref", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("parameterized", "anthill.prelude.Type.parameterized", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("arrow", "anthill.prelude.Type.arrow", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("type_var", "anthill.prelude.Type.type_var", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("named_tuple", "anthill.prelude.Type.named_tuple", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("nothing", "anthill.prelude.Type.nothing", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("denoted", "anthill.prelude.Type.denoted", SymbolKind::Entity, type_sort_term.raw());
    // WI-320 — variant-7 substrate: the EffectExpression-into-Type bridge.
    kb.symbols.define("effects_rows", "anthill.prelude.Type.effects_rows", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("TypeField", "anthill.prelude.Type.TypeField", SymbolKind::Entity, type_sort_term.raw());
    kb.symbols.define("TypeBinding", "anthill.prelude.Type.TypeBinding", SymbolKind::Entity, type_sort_term.raw());

    // WI-307 — v1a row-substrate: the EffectExpression algebra entities, the
    // payload `effects_rows` wraps. Pre-registered so `make_arrow_type` can
    // build the canonical `effects_rows(merge(present(…), …, empty_row))`
    // form for the arrow.effects field without depending on stdlib load
    // order. The stdlib `sort.anthill` re-declares the enum; the loader's
    // existing `if defined` guards make the re-declare idempotent.
    let effect_expr_sort_sym = kb.symbols.define("EffectExpression", "anthill.prelude.EffectExpression", SymbolKind::Sort, prelude_term.raw());
    let effect_expr_sort_term = kb.alloc(Term::Fn {
        functor: effect_expr_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(effect_expr_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("empty_row", "anthill.prelude.EffectExpression.empty_row", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("present", "anthill.prelude.EffectExpression.present", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("absent", "anthill.prelude.EffectExpression.absent", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("open", "anthill.prelude.EffectExpression.open", SymbolKind::Entity, effect_expr_sort_term.raw());
    kb.symbols.define("merge", "anthill.prelude.EffectExpression.merge", SymbolKind::Entity, effect_expr_sort_term.raw());

    // anthill.prelude.EffectsRuntime — variant-7 kind anchor (WI-320).
    // Pre-registered so the bridge-fact emission below can resolve the
    // symbol and assert the fact before stdlib loads. The stdlib file
    // `prelude/effects-runtime.anthill` re-declares the sort with its
    // `sort Effects = ?` parameter; the re-declare is idempotent (the
    // loader's existing `if defined` guards skip the symbol). No
    // entities, no operations — scope A is a pure kind anchor.
    let er_sort_sym = kb.symbols.define("EffectsRuntime", "anthill.prelude.EffectsRuntime", SymbolKind::Sort, prelude_term.raw());
    let er_sort_term = kb.alloc(Term::Fn {
        functor: er_sort_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(er_sort_term.raw(), ScopeInclusion {
        parent_scope_raw: prelude_term.raw(),
        instantiation_term_raw: prelude_term.raw(),
        is_enclosing: true,
    });

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

    // Proposal 038: register primitive sorts at anthill.prelude scope so
    // stdlib's `sort anthill.prelude.Int { ... }` reuses the same Symbol,
    // alias the bare QN for try_resolve_symbol("Int"), import into _global.
    for &name in PRELUDE_SORTS {
        let qualified = format!("anthill.prelude.{name}");
        let sym = kb.symbols.define(name, &qualified, SymbolKind::Sort, prelude_term.raw());
        let sort_term = kb.alloc(Term::Fn {
            functor: sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
        });
        kb.symbols.add_parent(sort_term.raw(), ScopeInclusion {
            parent_scope_raw: prelude_term.raw(),
            instantiation_term_raw: prelude_term.raw(),
            is_enclosing: true,
        });
        kb.symbols.by_qualified_name.insert(name.to_string(), sym);
        kb.symbols.add_import(global_raw, name, sym);
    }
    // BigInt conversion operations — pre-registered so stdlib body reuses them.
    let bigint_sym = kb.symbols.by_qualified_name["anthill.prelude.BigInt"];
    let bigint_term = kb.alloc(Term::Fn {
        functor: bigint_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
    });
    kb.symbols.define("to_bigint", "anthill.prelude.BigInt.to_bigint", SymbolKind::Operation, bigint_term.raw());
    kb.symbols.define("to_int", "anthill.prelude.BigInt.to_int", SymbolKind::Operation, bigint_term.raw());

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
    let sort_provides_info_sym = kb.symbols.define("SortProvidesInfo", "anthill.reflect.SortProvidesInfo", SymbolKind::Entity, reflect_term.raw());
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
    kb.symbols.define("lambda_expr", "anthill.reflect.Expr.lambda_expr", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("apply", "anthill.reflect.Expr.apply", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("ho_apply", "anthill.reflect.Expr.ho_apply", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("constructor", "anthill.reflect.Expr.constructor", SymbolKind::Entity, expr_term.raw());
    kb.symbols.define("dot_apply", "anthill.reflect.Expr.dot_apply", SymbolKind::Entity, expr_term.raw());
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

    // anthill.kernel namespace — resolver primitives (proposal 033).
    // Pre-declared here so that the loader's resolve_symbol calls find
    // these names with proper scoping when stdlib/anthill/kernel/ loads.
    let kernel_sym = kb.symbols.define("kernel", "anthill.kernel", SymbolKind::Namespace, anthill_term.raw());
    let kernel_term = kb.alloc(Term::Fn {
        functor: kernel_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    kb.symbols.add_parent(kernel_term.raw(), ScopeInclusion {
        parent_scope_raw: anthill_term.raw(),
        instantiation_term_raw: anthill_term.raw(),
        is_enclosing: true,
    });
    kb.symbols.define("push_choice", "anthill.kernel.push_choice", SymbolKind::Operation, kernel_term.raw());
    kb.symbols.define("or", "anthill.kernel.or", SymbolKind::Operation, kernel_term.raw());

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
    kb.symbols.add_import(global_raw, "SortProvidesInfo", sort_provides_info_sym);
    kb.symbols.add_import(global_raw, "SortView", sort_view_sym);
    kb.symbols.add_import(global_raw, "SetLiteral", set_literal_sym);
    kb.symbols.add_import(global_raw, "TupleLiteral", tuple_literal_sym);
    kb.symbols.add_import(global_raw, "ListLiteral", list_literal_sym);

    // Kernel builtins: globally visible (language primitives, not importable names)
    if let Some(&not_sym) = kb.symbols.by_qualified_name.get("anthill.reflect.not") {
        kb.symbols.add_import(global_raw, "not", not_sym);
    }
    if let Some(&push_choice_sym) = kb.symbols.by_qualified_name.get("anthill.kernel.push_choice") {
        kb.symbols.add_import(global_raw, "push_choice", push_choice_sym);
    }
    if let Some(&or_sym) = kb.symbols.by_qualified_name.get("anthill.kernel.or") {
        kb.symbols.add_import(global_raw, "or", or_sym);
    }

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
) -> Result<LoadResult, Vec<LoadError>> {
    register_prelude(kb);
    let mut all_errors = scan_definitions(kb, &[parsed]);
    kb.resolve_builtins();
    let mut loaded_paths = HashSet::new();
    let mut all_sorts = Vec::new();
    let mut all_fact_ids = Vec::new();
    match load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
        Ok(result) => {
            all_sorts.extend(result.defined_sorts);
            all_fact_ids.extend(result.fact_rule_ids);
        }
        Err(errs) => all_errors.extend(errs),
    }
    resolve_instantiations(kb);
    if all_errors.is_empty() {
        Ok(LoadResult { defined_sorts: all_sorts, fact_rule_ids: all_fact_ids })
    } else {
        Err(all_errors)
    }
}

/// Load multiple parsed files into the same knowledge base, including the
/// prelude. Scans ALL files for definitions first, then loads them, so that
/// cross-file references resolve correctly regardless of load order.
pub fn load_all(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    register_prelude(kb);
    load_phase(kb, files, resolver)
}

/// Alias of [`load_all`]. Named for clarity when loading stdlib as the first
/// phase of an incremental workflow; subsequent files can then be added via
/// [`load_incremental`] without reprocessing already-finalized facts.
pub fn load_stdlib(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    load_all(kb, files, resolver)
}

/// Load additional files on top of an already-populated KB. Skips
/// `register_prelude`. Relies on `resolve_instantiations` being idempotent
/// (`resolved_requires_facts` guard) so stdlib facts are not retracted or
/// reasserted. The returned `LoadResult.defined_sorts` contains only sorts
/// defined in `files`.
pub fn load_incremental(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    load_phase(kb, files, resolver)
}

fn load_phase(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<LoadResult, Vec<LoadError>> {
    load_phase_inner(kb, files, resolver).map(|(merged, _)| merged)
}

/// Same as [`load_phase`] but also returns each file's individual
/// `LoadResult`, parallel to `files`. Used by `IndexedFileStore` so the
/// caller can pair each file's `fact_rule_ids` with its on-disk path
/// without losing the per-file boundary information that the merged
/// `LoadResult` discards.
pub fn load_all_per_file(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<(LoadResult, Vec<LoadResult>), Vec<LoadError>> {
    register_prelude(kb);
    load_phase_inner(kb, files, resolver)
}

#[allow(unused_assignments)]
fn load_phase_inner(
    kb: &mut KnowledgeBase,
    files: &[&ParsedFile],
    resolver: &dyn SourceResolver,
) -> Result<(LoadResult, Vec<LoadResult>), Vec<LoadError>> {
    // WI-233: per-sub-phase timing, gated by ANTHILL_LOAD_TIMING=1.
    // Surfaces which step of the load pipeline dominates wall time
    // (scan / load / resolve / witnesses / typecheck / req_insertion).
    let timing = std::env::var("ANTHILL_LOAD_TIMING").map(|v| v == "1").unwrap_or(false);
    let mut t = std::time::Instant::now();
    macro_rules! mark {
        ($label:expr) => {
            if timing {
                let now = std::time::Instant::now();
                eprintln!("[load_timing]   {}: {:?}", $label, now.duration_since(t));
                t = now;
            }
        };
    }

    let mut all_errors = scan_definitions(kb, files);
    mark!("scan_definitions");
    kb.resolve_builtins();
    mark!("resolve_builtins");
    register_implicit_prelude_effects(kb);
    mark!("register_implicit_prelude_effects");

    let item_timing = std::env::var("ANTHILL_ITEM_TIMING").map(|v| v == "1").unwrap_or(false);
    if item_timing { reset_item_timings(); }
    let mut loaded_paths = HashSet::new();
    let mut all_sorts = Vec::new();
    let mut all_fact_ids = Vec::new();
    let mut per_file: Vec<LoadResult> = Vec::with_capacity(files.len());
    for parsed in files {
        match load_with_visited(kb, parsed, resolver, &mut loaded_paths) {
            Ok(result) => {
                all_sorts.extend(result.defined_sorts.clone());
                all_fact_ids.extend(result.fact_rule_ids.clone());
                per_file.push(result);
            }
            Err(errs) => {
                all_errors.extend(errs);
                per_file.push(LoadResult::default());
            }
        }
    }
    mark!(&format!("load_with_visited x {}", files.len()));
    if item_timing {
        print_item_timings(&format!("load_with_visited x {}", files.len()));
    }
    resolve_instantiations(kb);
    mark!("resolve_instantiations");
    register_requires_axiom_witnesses(kb);
    mark!("register_requires_axiom_witnesses");
    register_induction_axiom_witnesses(kb);
    mark!("register_induction_axiom_witnesses");
    register_specialization_witnesses(kb);
    mark!("register_specialization_witnesses");
    // WI-240 — precompute the per-impl-sort operations table before
    // typing, so the typer's spec-op dispatch reads it via
    // `kb.sort_ops_lookup` instead of the string-concat fallback.
    build_sort_ops_table(kb);
    mark!("build_sort_ops_table");
    // WI-283: `[simp]` firing over operation bodies now runs *inside* the
    // typer (`typing::build_type`), where it is type-directed — children
    // are typed first, so `min_sort`/`requires` guards have the operand's
    // type in hand. The typer is tree-producing: it writes each rewritten
    // (redex-free) body back via `set_op_body_node` before returning, so
    // req_insertion, eval, and codegen see the rewritten form. The former
    // pre-typer `simp_rewrite::run` pass (WI-277, guard-free, type-blind)
    // is retired from the pipeline; its machinery is reused by the typer.
    all_errors.extend(super::typing::type_check_sorts(kb, &all_sorts));
    mark!(&format!("type_check_sorts ({} sorts)", all_sorts.len()));
    // WI-231: the typer tagged each spec-op call site's occurrence
    // with a `CallClass`; run the requirement-insertion pass to emit
    // the IR rewrites into `kb.dispatch_rewrites`. Skipping this call
    // would leave the IR in the typed-but-unelaborated state (useful
    // for alternative codegen targets). WI-325: also returns any
    // `MissingRequiresForSpecOp` diagnostics from `UnresolvedSpecOp`
    // tags (typer-detected abstract spec-op calls without a covering
    // `requires`); merged into the load-time error list.
    let req_errors = super::req_insertion::run(kb);
    for err in req_errors {
        all_errors.push(err.to_load_error(kb));
    }
    mark!("req_insertion::run");
    // WI-343: provider-side requires coverage. For each `fact Spec[X]`,
    // every spec-level `requires` of Spec (at the provision's bindings)
    // must itself be satisfied — else the satisfaction fact is unsound.
    all_errors.extend(super::typing::check_provider_requires(kb));
    mark!("check_provider_requires");
    if all_errors.is_empty() {
        Ok((
            LoadResult { defined_sorts: all_sorts, fact_rule_ids: all_fact_ids },
            per_file,
        ))
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
) -> Result<LoadResult, Vec<LoadError>> {
    let global = kb.make_name_term("_global");
    let mut loader = Loader::new(kb, parsed, resolver, loaded_paths, global);
    loader.load_items(&parsed.items, None);

    let result = LoadResult {
        defined_sorts: loader.defined_sorts,
        fact_rule_ids: loader.fact_rule_ids,
    };
    if loader.errors.is_empty() {
        Ok(result)
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
    let name_sym = kb.intern("name");
    let parameters_sym = kb.intern("parameters");
    let operations_sym = kb.intern("operations");
    let mut sort_entries: Vec<(Symbol, Vec<(Symbol, TermId)>)> = Vec::new();

    for rid in rule_ids {
        if !kb.is_fact(rid) {
            continue; // skip rules, only process facts
        }
        let head = kb.rule_head(rid);
        let term = kb.get_term(head).clone();
        if let Term::Fn { named_args, .. } = term {
            let sort_functor_sym = named_args.iter()
                .find(|(s, _)| *s == name_sym)
                .and_then(|(_, tid)| match kb.get_term(*tid) {
                    Term::Ref(sym) => Some(*sym),
                    _ => None,
                });

            if let Some(sym) = sort_functor_sym {
                if kb.sort_base_subst(sym).is_some() {
                    continue;
                }
            }

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
        if kb.is_requires_resolved(*rid) {
            continue;
        }
        if !kb.is_fact(*rid) {
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
                let new_rid = kb.assert_fact(new_head, sort, domain, meta);
                kb.mark_requires_resolved(new_rid);
            }
        }
    }
}

/// Proposal 030 phase α.6: emit a synthetic `ProofRecord` fact for
/// every `requires <SE>` clause in a sort or operation declaration.
/// The witness is `ScopeAxiom(scope_kind, scope_qn, aspect)` —
/// definitionally checkable by re-reading the source declaration.
///
/// Naming: `<scope-qn>.requires.<SE-flat>` where `<SE-flat>` is the
/// spec's base sort short-name plus binding-value short-names sorted
/// by binding key. So `requires Eq[T]` inside `algebra.A` becomes
/// `algebra.A.requires.Eq_T`; `requires Monoid[T = Int]` becomes
/// `<scope>.requires.Monoid_Int`.
///
/// Records land with `result = Pending` for now — phase β's witness
/// checker transitions them to `Discharged` once the structural
/// dispatch on `aspect` confirms the cited declaration is present.
/// State hash is the sentinel `"scope-axiom"` since these records
/// have no SLD/SMT dep slice; staleness is detected by re-reading
/// the declaration directly during β.4 checking.
///
/// Idempotent: if a ProofRecord with the same `rule` field already
/// exists in the KB (e.g. a previous load_phase already registered
/// it), the auto-registration is skipped to avoid duplicate facts.
fn register_requires_axiom_witnesses(kb: &mut KnowledgeBase) {
    let requires_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") {
        Some(s) => s,
        None => return,
    };
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return,
    };
    let pending_sym = match kb.try_resolve_symbol(
        "anthill.realization.ObligationStatus.Pending"
    ) {
        Some(s) => s,
        None => return,
    };
    let strategy_open_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofStrategyOpen"
    ) {
        Some(s) => s,
        None => return,
    };
    let body_none_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofBodyNone"
    ) {
        Some(s) => s,
        None => return,
    };
    let scope_axiom_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.ProofWitness.ScopeAxiom"
    ) {
        Some(s) => s,
        None => return,
    };
    let nil_sym = match kb.try_resolve_symbol("anthill.prelude.List.nil") {
        Some(s) => s,
        None => return,
    };

    let sort_ref_field = kb.intern("sort_ref");
    let spec_field = kb.intern("spec");
    let rule_arg = kb.intern("rule");
    let strategy_arg = kb.intern("strategy");
    let body_arg = kb.intern("body");
    let result_arg = kb.intern("result");
    let deps_arg = kb.intern("dependencies");
    let using_arg = kb.intern("using");
    let witness_arg = kb.intern("witness");
    let state_hash_arg = kb.intern("state_hash");
    let parametric_context_arg = kb.intern("parametric_context");
    let scope_kind_arg = kb.intern("scope_kind");
    let scope_qn_arg = kb.intern("scope_qn");
    let aspect_arg = kb.intern("aspect");

    let existing_rule_qns = collect_existing_proof_record_qns(kb, record_sym);
    let requires_rids = kb.by_functor(requires_info_sym);
    let mut new_records: Vec<TermId> = Vec::new();

    for rid in requires_rids {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let head_term = kb.get_term(head).clone();
        let named = match head_term {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        let sort_ref_tid = match named.iter()
            .find(|(s, _)| *s == sort_ref_field).map(|(_, t)| *t) {
            Some(t) => t,
            None => continue,
        };
        let spec_tid = match named.iter()
            .find(|(s, _)| *s == spec_field).map(|(_, t)| *t) {
            Some(t) => t,
            None => continue,
        };

        let scope_qn = match qn_of_sort_ref(kb, sort_ref_tid) {
            Some(q) => q,
            None => continue,
        };
        let se_flat = match flatten_spec(kb, spec_tid) {
            Some(s) => s,
            None => continue,
        };
        let aspect_text = format!("requires.{se_flat}");
        let rule_qn_text = format!("{scope_qn}.{aspect_text}");
        if existing_rule_qns.contains(&rule_qn_text) { continue; }

        let scope_kind_term = kb.alloc(Term::Const(Literal::String("sort".to_string())));
        let scope_qn_term = kb.alloc(Term::Const(Literal::String(scope_qn.clone())));
        let aspect_term = kb.alloc(Term::Const(Literal::String(aspect_text)));
        let witness_term = kb.alloc(Term::Fn {
            functor: scope_axiom_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (scope_kind_arg, scope_kind_term),
                (scope_qn_arg, scope_qn_term),
                (aspect_arg, aspect_term),
            ]),
        });
        let strategy_term = kb.alloc(Term::Fn {
            functor: strategy_open_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_term = kb.alloc(Term::Fn {
            functor: body_none_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let pending_term = kb.alloc(Term::Fn {
            functor: pending_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let nil_term = kb.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let rule_text_term = kb.alloc(Term::Const(Literal::String(rule_qn_text)));
        let state_hash_term = kb.alloc(Term::Const(
            Literal::String("scope-axiom".to_string())
        ));

        let record_term = kb.alloc(Term::Fn {
            functor: record_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (rule_arg, rule_text_term),
                (strategy_arg, strategy_term),
                (body_arg, body_term),
                (result_arg, pending_term),
                (deps_arg, nil_term),
                (using_arg, nil_term),
                (witness_arg, witness_term),
                (state_hash_arg, state_hash_term),
                (parametric_context_arg, nil_term),
            ]),
        });
        new_records.push(record_term);
    }

    if new_records.is_empty() { return; }
    let record_sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let global_term = kb.make_name_term("_global");
    for rec in new_records {
        kb.assert_fact(rec, record_sort_term, global_term, None);
    }
}

/// Proposal 030 phase α.7: emit a synthetic `ProofRecord` fact for
/// every inductive sort's induction principle. Witness shape mirrors
/// α.6's `requires` clauses but with `aspect = "induction"`.
///
/// v0 scope: enum sorts (`SortInfo.kind = "enum"`) get an induction
/// ProofRecord. Non-enum sorts with recursive constructors are
/// deferred — recursion detection requires walking EntityInfo and
/// matching constructor field types against the parent sort, which
/// is straightforward but additional code; recursive ADTs picked up
/// in a follow-up sub-task. Primitives with hand-written `induction`
/// rules in stdlib (Int.induction, BigInt.induction, …) are *not*
/// re-registered here — those rules already exist as user-visible
/// anthill rules and phase γ resolves citations against them
/// directly. The auto-registered records here cover the kernel-
/// derived structural induction for user-declared inductive sorts.
///
/// The witness is `ScopeAxiom(scope_kind: "sort", scope_qn: <T>,
/// aspect: "induction")`. Phase β.4's check re-reads T's SortInfo
/// and confirms the constructor list matches what the principle was
/// derived from.
///
/// Idempotent across loads via the same `existing_rule_qns` guard
/// as α.6.
fn register_induction_axiom_witnesses(kb: &mut KnowledgeBase) {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(s) => s,
        None => return,
    };
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return,
    };
    let pending_sym = match kb.try_resolve_symbol(
        "anthill.realization.ObligationStatus.Pending"
    ) { Some(s) => s, None => return };
    let strategy_open_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofStrategyOpen"
    ) { Some(s) => s, None => return };
    let body_none_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofBodyNone"
    ) { Some(s) => s, None => return };
    let scope_axiom_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.ProofWitness.ScopeAxiom"
    ) { Some(s) => s, None => return };
    let nil_sym = match kb.try_resolve_symbol("anthill.prelude.List.nil") {
        Some(s) => s, None => return,
    };

    let rule_arg = kb.intern("rule");
    let strategy_arg = kb.intern("strategy");
    let body_arg = kb.intern("body");
    let result_arg = kb.intern("result");
    let deps_arg = kb.intern("dependencies");
    let using_arg = kb.intern("using");
    let witness_arg = kb.intern("witness");
    let state_hash_arg = kb.intern("state_hash");
    let parametric_context_arg = kb.intern("parametric_context");
    let scope_kind_arg = kb.intern("scope_kind");
    let scope_qn_arg = kb.intern("scope_qn");
    let aspect_arg = kb.intern("aspect");

    let existing_rule_qns = collect_existing_proof_record_qns(kb, record_sym);
    let sort_info_rids = kb.by_functor(sort_info_sym);
    let mut new_records: Vec<TermId> = Vec::new();

    for rid in sort_info_rids {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let head_term = kb.get_term(head).clone();
        let named = match head_term {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        if !sort_info_is_inductive(kb, &named) { continue; }
        let sort_qn = match sort_info_qn(kb, &named) {
            Some(q) => q,
            None => continue,
        };
        let rule_qn_text = format!("{sort_qn}.induction");
        if existing_rule_qns.contains(&rule_qn_text) { continue; }

        let scope_kind_term = kb.alloc(Term::Const(Literal::String("sort".to_string())));
        let scope_qn_term = kb.alloc(Term::Const(Literal::String(sort_qn)));
        let aspect_term = kb.alloc(Term::Const(Literal::String("induction".to_string())));
        let witness_term = kb.alloc(Term::Fn {
            functor: scope_axiom_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (scope_kind_arg, scope_kind_term),
                (scope_qn_arg, scope_qn_term),
                (aspect_arg, aspect_term),
            ]),
        });
        let strategy_term = kb.alloc(Term::Fn {
            functor: strategy_open_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let body_term = kb.alloc(Term::Fn {
            functor: body_none_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let pending_term = kb.alloc(Term::Fn {
            functor: pending_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let nil_term = kb.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let rule_text_term = kb.alloc(Term::Const(Literal::String(rule_qn_text)));
        let state_hash_term = kb.alloc(Term::Const(
            Literal::String("scope-axiom".to_string())
        ));

        let record_term = kb.alloc(Term::Fn {
            functor: record_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (rule_arg, rule_text_term),
                (strategy_arg, strategy_term),
                (body_arg, body_term),
                (result_arg, pending_term),
                (deps_arg, nil_term),
                (using_arg, nil_term),
                (witness_arg, witness_term),
                (state_hash_arg, state_hash_term),
                (parametric_context_arg, nil_term),
            ]),
        });
        new_records.push(record_term);
    }

    if new_records.is_empty() { return; }
    let record_sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let global_term = kb.make_name_term("_global");
    for rec in new_records {
        kb.assert_fact(rec, record_sort_term, global_term, None);
    }
}

/// Proposal 030 phase α.8 / WI-119 Variant 3 / WI-120 — emit
/// `Specialization`-witnessed ProofRecords for each `provides A[T =
/// X]` clause whose required laws all have Discharged ProofRecords
/// at the substitution.
///
/// Algorithm: walk `SortProvidesInfo` facts. For each `(X, A[T = X])`:
///   1. Resolve A's qualified name and the substitution σ from the
///      spec view's named bindings (filtering operation auto-bindings).
///   2. For each of A's auto-registered `<A-qn>.requires.<SE>`
///      ProofRecords (α.6), emit a `Specialization` ProofRecord
///      named `<X-qn>.provides.<A-flat>.<SE>` whose witness is
///      `Specialization { parametric: <A-qn>.requires.<SE>,
///      substitution: σ, instances: [] }`. The instances list is
///      empty in v0 — phase β.5's structural check verifies
///      coverage by walking the existing registry rather than
///      chasing a pre-baked instance-list. Future refinement: pre-
///      compute the per-law instance ProofRecord QNs and embed.
///   3. Phase β.5's check enforces: for each requires-law `<SE>`,
///      either an instance ProofRecord covers it at σ, or a
///      ScopeAxiom on X's own declaration does. Errors at check
///      time, not load time — so missing proofs surface in
///      `anthill check`'s integrity audit, not as load failures.
///
/// Idempotent across loads via `existing_rule_qns`.
fn register_specialization_witnesses(kb: &mut KnowledgeBase) {
    let provides_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return,
    };
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return,
    };
    let pending_sym = match kb.try_resolve_symbol(
        "anthill.realization.ObligationStatus.Pending"
    ) { Some(s) => s, None => return };
    let strategy_open_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofStrategyOpen"
    ) { Some(s) => s, None => return };
    let body_none_sym = match kb.try_resolve_symbol(
        "anthill.realization.ProofBodyNone"
    ) { Some(s) => s, None => return };
    let specialization_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.ProofWitness.Specialization"
    ) { Some(s) => s, None => return };
    let sort_binding_sym = match kb.try_resolve_symbol(
        "anthill.realization.witness.SortBinding"
    ) { Some(s) => s, None => return };
    let nil_sym = match kb.try_resolve_symbol("anthill.prelude.List.nil") {
        Some(s) => s, None => return,
    };
    let cons_sym = match kb.try_resolve_symbol("anthill.prelude.List.cons") {
        Some(s) => s, None => return,
    };

    let rule_arg = kb.intern("rule");
    let strategy_arg = kb.intern("strategy");
    let body_arg = kb.intern("body");
    let result_arg = kb.intern("result");
    let deps_arg = kb.intern("dependencies");
    let using_arg = kb.intern("using");
    let witness_arg = kb.intern("witness");
    let state_hash_arg = kb.intern("state_hash");
    let parametric_context_arg = kb.intern("parametric_context");
    let head_arg = kb.intern("head");
    let tail_arg = kb.intern("tail");
    let parametric_arg = kb.intern("parametric");
    let substitution_arg = kb.intern("substitution");
    let instances_arg = kb.intern("instances");
    let abstract_param_arg = kb.intern("abstract_param");
    let concrete_sort_arg = kb.intern("concrete_sort");

    let existing_rule_qns = collect_existing_proof_record_qns(kb, record_sym);

    // Snapshot all (X-qn, spec-tid) pairs first so we don't borrow-
    // conflict with kb mutations during ProofRecord construction.
    let provides_rids = kb.by_functor(provides_info_sym);
    let mut targets: Vec<(String, TermId)> = Vec::new();
    for rid in provides_rids {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let head_term = kb.get_term(head).clone();
        let named = match head_term {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        let sort_ref_tid = match super::typing::get_named_arg(kb, &named, "sort_ref") {
            Some(t) => t,
            None => continue,
        };
        let spec_tid = match super::typing::get_named_arg(kb, &named, "spec") {
            Some(t) => t,
            None => continue,
        };
        let x_qn = match qn_of_sort_ref(kb, sort_ref_tid) {
            Some(q) => q,
            None => continue,
        };
        targets.push((x_qn, spec_tid));
    }

    let mut new_records: Vec<TermId> = Vec::new();

    for (x_qn, spec_tid) in targets {
        let (a_short, a_qn, substitution) = match resolve_provides_spec(kb, spec_tid) {
            Some(t) => t,
            None => continue,
        };
        // Find every auto-registered <a_qn>.requires.<SE> record so
        // we can emit one Specialization per requires-law.
        let parametric_records: Vec<String> = existing_rule_qns
            .iter()
            .filter(|qn| qn.starts_with(&format!("{a_qn}.requires.")))
            .cloned()
            .collect();
        if parametric_records.is_empty() { continue; }

        for parametric_qn in parametric_records {
            let se_part = parametric_qn
                .strip_prefix(&format!("{a_qn}.requires."))
                .unwrap_or(&parametric_qn);
            let rule_qn_text = format!("{x_qn}.provides.{a_short}.{se_part}");
            if existing_rule_qns.contains(&rule_qn_text) { continue; }

            let parametric_term = kb.alloc(Term::Const(
                Literal::String(parametric_qn.clone())
            ));
            // Build the substitution cons-list of SortBinding entities.
            let binding_terms: Vec<TermId> = substitution.iter().map(|(k, v)| {
                let k_term = kb.alloc(Term::Const(Literal::String(k.clone())));
                let v_term = kb.alloc(Term::Const(Literal::String(v.clone())));
                kb.alloc(Term::Fn {
                    functor: sort_binding_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (abstract_param_arg, k_term),
                        (concrete_sort_arg, v_term),
                    ]),
                })
            }).collect();
            let substitution_list = build_cons_list(
                kb, &binding_terms, nil_sym, cons_sym, head_arg, tail_arg);
            let instances_list = kb.alloc(Term::Fn {
                functor: nil_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });

            let witness_term = kb.alloc(Term::Fn {
                functor: specialization_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[
                    (parametric_arg, parametric_term),
                    (substitution_arg, substitution_list),
                    (instances_arg, instances_list),
                ]),
            });
            let strategy_term = kb.alloc(Term::Fn {
                functor: strategy_open_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let body_term = kb.alloc(Term::Fn {
                functor: body_none_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let pending_term = kb.alloc(Term::Fn {
                functor: pending_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let nil_term = kb.alloc(Term::Fn {
                functor: nil_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let rule_text_term = kb.alloc(Term::Const(Literal::String(rule_qn_text)));
            let state_hash_term = kb.alloc(Term::Const(
                Literal::String("specialization".to_string())
            ));

            let record_term = kb.alloc(Term::Fn {
                functor: record_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[
                    (rule_arg, rule_text_term),
                    (strategy_arg, strategy_term),
                    (body_arg, body_term),
                    (result_arg, pending_term),
                    (deps_arg, nil_term),
                    (using_arg, nil_term),
                    (witness_arg, witness_term),
                    (state_hash_arg, state_hash_term),
                    (parametric_context_arg, nil_term),
                ]),
            });
            new_records.push(record_term);
        }
    }

    if new_records.is_empty() { return; }
    let record_sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let global_term = kb.make_name_term("_global");
    for rec in new_records {
        kb.assert_fact(rec, record_sort_term, global_term, None);
    }
}

/// WI-240 — build the per-sort operations table: each sort symbol
/// carries a `op_short → impl_op_symbol` map of the operations it can
/// dispatch (docs/design/operation-call-model.md §"Sort symbols carry
/// their own operations table").
///
/// Two passes:
///   1. **Own ops.** For every sort `S`, record `S.<op> → S.<op>` for
///      each op `S` itself declares. A direct/concrete impl thus
///      resolves its own ops without any spec involvement.
///   2. **Inherited spec ops.** For every impl sort `S` with a
///      `fact Spec[bindings]`, walk `Spec`'s declared operations. For
///      each op `S` does *not* declare itself (pass 1 already recorded
///      the ones it does), record the spec op `Spec.<op>` — its body
///      comes from the spec's rewrite rule or a registered builtin,
///      resolved at runtime. This mirrors the old dispatch fallback
///      (`impl.<op>` if the impl declares it, else `spec.<op>`); the
///      separate decision of whether to *rewrite* a spec-op call to a
///      runnable impl op stays in the typer (`op_has_runnable_body`).
///
/// This precomputes (once, at load time) the decision the dispatch
/// fallback used to make per-call via
/// `try_resolve_symbol("{impl_qn}.{op}").or_else(spec_qn)`. Consumers
/// read it via `kb.sort_ops_lookup(impl_sort, op_short)` — a direct
/// table lookup. Idempotent: re-running overwrites with equal values.
pub fn build_sort_ops_table(kb: &mut KnowledgeBase) {
    // One `SortInfo` scan shared by both passes: pass 1 records each
    // sort's own ops, pass 2 reads the spec sort's ops from the same
    // map. Scanning per sort via `operations_of_sort` would be
    // O(sorts²). Snapshot before inserting: interning short names
    // mutates `kb`, which can't overlap the `by_functor` walk.
    let sort_ops: HashMap<Symbol, Vec<Symbol>> = sorts_and_own_ops(kb).into_iter().collect();

    // ── Pass 1: every sort's own declared operations. ──────────────
    for (sort_sym, ops) in &sort_ops {
        for &op_sym in ops {
            let short_sym = intern_op_short(kb, op_sym);
            kb.insert_sort_op(*sort_sym, short_sym, op_sym);
        }
    }

    // ── Pass 2: inherited spec ops for `fact Spec[bindings]` impls. ─
    let provides_sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return,
    };
    // Snapshot (impl_sort, spec_sort) pairs first — populating the
    // table interns short names (mutating `kb`), which can't overlap
    // the `by_functor` borrow walk.
    let mut pairs: Vec<(Symbol, Symbol)> = Vec::new();
    for rid in kb.by_functor(provides_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };
        let sort_ref_tid = match super::typing::get_named_arg(kb, &named, "sort_ref") {
            Some(t) => t,
            None => continue,
        };
        let spec_tid = match super::typing::get_named_arg(kb, &named, "spec") {
            Some(t) => t,
            None => continue,
        };
        let impl_sym = match sort_ref_functor(kb, sort_ref_tid) {
            Some(s) => s,
            None => continue,
        };
        let spec_sym = match provides_spec_base_sym(kb, spec_tid) {
            Some(s) => s,
            None => continue,
        };
        pairs.push((impl_sym, spec_sym));
    }

    for (impl_sym, spec_sym) in pairs {
        let Some(spec_ops) = sort_ops.get(&spec_sym) else { continue };
        for &spec_op_sym in spec_ops {
            let short_sym = intern_op_short(kb, spec_op_sym);
            // Pass 1 already recorded the impl's own override (if it
            // declares this op). Only fill the inherited spec default
            // when the impl doesn't declare the op itself.
            if kb.sort_ops_lookup(impl_sym, short_sym).is_none() {
                kb.insert_sort_op(impl_sym, short_sym, spec_op_sym);
            }
        }
    }
}

/// Intern the short name of an operation symbol (`Spec.lt` → `lt`) —
/// the `sort_ops` inner key. Borrows the QN, slices, then interns the
/// slice (no intermediate `String`).
fn intern_op_short(kb: &mut KnowledgeBase, op_sym: Symbol) -> Symbol {
    let short = last_segment(kb.qualified_name_of(op_sym)).to_string();
    kb.intern(&short)
}

/// Walk `SortInfo` facts once, returning each sort symbol paired with
/// the operation symbols it declares. `build_sort_ops_table` collects
/// this into a map both passes share — a single scan instead of one
/// `SortInfo` walk per sort.
fn sorts_and_own_ops(kb: &KnowledgeBase) -> Vec<(Symbol, Vec<Symbol>)> {
    let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let mut out: Vec<(Symbol, Vec<Symbol>)> = Vec::new();
    for rid in kb.by_functor(sort_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        let sort_sym = match named.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "name")
            .map(|(_, v)| *v)
            .map(|t| kb.get_term(t))
        {
            Some(Term::Ref(s) | Term::Ident(s) | Term::Fn { functor: s, .. }) => *s,
            _ => continue,
        };
        let ops = match named.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "operations")
            .map(|(_, v)| *v)
        {
            Some(ops_tid) => super::typing::list_to_vec(kb, ops_tid)
                .into_iter()
                .filter_map(|t| match kb.get_term(t) {
                    Term::Ref(s) => Some(*s),
                    _ => None,
                })
                .collect(),
            None => Vec::new(),
        };
        out.push((sort_sym, ops));
    }
    out
}

/// Extract the carrier sort symbol from a `SortProvidesInfo.sort_ref`
/// term — a `sort_ref(name: Ref(S))`, a bare `Ref(S)`/`Ident(S)`, or a
/// nullary `Fn` whose functor is `S`.
pub(crate) fn sort_ref_functor(kb: &KnowledgeBase, term: TermId) -> Option<Symbol> {
    match kb.get_term(term) {
        Term::Fn { functor, named_args, .. } => {
            // `sort_ref(name: Ref(S))` wrapping — prefer the inner name.
            if let Some(name_tid) = named_args.iter()
                .find(|(k, _)| kb.resolve_sym(*k) == "name")
                .map(|(_, v)| *v)
            {
                if let Term::Ref(s) | Term::Ident(s) = kb.get_term(name_tid) {
                    return Some(*s);
                }
            }
            Some(*functor)
        }
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Extract the spec sort symbol from a `SortProvidesInfo.spec` term:
/// the base of a `SortView(Spec, …)` wrapper, or a bare spec ref.
pub(crate) fn provides_spec_base_sym(kb: &KnowledgeBase, spec: TermId) -> Option<Symbol> {
    match kb.get_term(spec) {
        Term::Fn { functor, pos_args, .. } => {
            let f_short = last_segment(kb.qualified_name_of(*functor));
            if f_short == "SortView" {
                let base = pos_args.first().copied()?;
                match kb.get_term(base) {
                    Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
                        Some(*functor)
                    }
                    _ => None,
                }
            } else {
                Some(*functor)
            }
        }
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Resolve a SortProvidesInfo.spec term into:
/// - the spec's short name (used as `<A-flat>` in the rule QN)
/// - the spec's qualified name (used to find α.6's requires records)
/// - the substitution as `Vec<(abstract_param, concrete_sort_short)>`
fn resolve_provides_spec(
    kb: &KnowledgeBase,
    spec: TermId,
) -> Option<(String, String, Vec<(String, String)>)> {
    // Peel `SortView(Spec, …)` (or a bare spec ref) down to the base
    // spec symbol — same logic as `provides_spec_base_sym`.
    let base_sym = provides_spec_base_sym(kb, spec)?;
    let qn = kb.qualified_name_of(base_sym).to_owned();
    let short = last_segment(&qn).to_owned();
    // The type-parameter substitution lives in the outer `SortView`'s
    // named args; a plain `provides Foo` (non-SortView Fn or bare ref)
    // carries none.
    let sub = match kb.get_term(spec) {
        Term::Fn { functor, named_args, .. }
            if last_segment(kb.qualified_name_of(*functor)) == "SortView" =>
        {
            sort_view_substitution(kb, named_args)
        }
        _ => Vec::new(),
    };
    Some((short, qn, sub))
}

/// Parse a `SortView`'s named args into the type-parameter substitution
/// `Vec<(abstract_param_short, concrete_sort_short)>`, sorted by param.
/// Operation-valued args are skipped (they bind ops, not type params).
fn sort_view_substitution(
    kb: &KnowledgeBase,
    named_args: &[(Symbol, TermId)],
) -> Vec<(String, String)> {
    use crate::intern::SymbolKind;
    let mut sub: Vec<(String, String)> = named_args.iter().filter_map(|(k_sym, v_tid)| {
        let value_sym = match kb.get_term(*v_tid) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => Some(*functor),
            _ => None,
        };
        if let Some(vs) = value_sym {
            if matches!(kb.kind_of(vs), Some(SymbolKind::Operation)) {
                return None;
            }
        }
        let k_short = last_segment(kb.resolve_sym(*k_sym)).to_owned();
        let v_short = match value_sym {
            Some(s) => last_segment(kb.resolve_sym(s)).to_owned(),
            None => "_".to_string(),
        };
        Some((k_short, v_short))
    }).collect();
    sub.sort_by(|a, b| a.0.cmp(&b.0));
    sub
}

/// Build a cons/nil list using explicit functor symbols. Mirrors
/// `build_list` but accepts pre-resolved nil/cons/head/tail symbols
/// — useful when the caller already resolved them once and wants
/// to avoid re-lookups in inner loops.
pub(crate) fn build_cons_list(
    kb: &mut KnowledgeBase,
    items: &[TermId],
    nil_sym: Symbol,
    cons_sym: Symbol,
    head_arg: Symbol,
    tail_arg: Symbol,
) -> TermId {
    let mut list = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    for &item in items.iter().rev() {
        list = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head_arg, item), (tail_arg, list)]),
        });
    }
    list
}

/// True iff a SortInfo fact's `kind` field is `"enum"` — the v0
/// detection criterion for "needs an induction principle". The
/// loader emits `kind` as `Term::Ident(intern("enum"))` (see
/// `assert_sort_info`), so we look up the symbol's interned name.
/// Recursive ADTs (kind = "sort" with self-referential constructor
/// fields) are deferred; this function returns false for them today.
pub fn sort_info_is_inductive(
    kb: &KnowledgeBase,
    named: &SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let kind_tid = match super::typing::get_named_arg(kb, named, "kind") {
        Some(t) => t,
        None => return false,
    };
    match kb.get_term(kind_tid) {
        Term::Ident(s) | Term::Ref(s) => kb.resolve_sym(*s) == "enum",
        Term::Const(Literal::String(s)) => s == "enum",
        _ => false,
    }
}

/// Resolve a SortInfo's `name` field to its qualified name. The
/// `name` field is a symbol reference (Term::Ref / Term::Ident /
/// nullary Fn), encoded by the loader as `<sort-qn>` in the
/// symbol table.
pub fn sort_info_qn(
    kb: &KnowledgeBase,
    named: &SmallVec<[(Symbol, TermId); 2]>,
) -> Option<String> {
    let tid = super::typing::get_named_arg(kb, named, "name")?;
    let sym = match kb.get_term(tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        Term::Fn { functor, .. } => *functor,
        _ => return None,
    };
    Some(kb.qualified_name_of(sym).to_owned())
}

/// Read the `rule` field of every existing `ProofRecord` fact so the
/// auto-registration in `register_requires_axiom_witnesses` can skip
/// duplicates.
fn collect_existing_proof_record_qns(kb: &KnowledgeBase, record_sym: Symbol) -> HashSet<String> {
    let mut out = HashSet::new();
    for rid in kb.by_functor(record_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            if let Some(tid) = super::typing::get_named_arg(kb, named_args, "rule") {
                if let Term::Const(Literal::String(s)) = kb.get_term(tid) {
                    out.insert(s.clone());
                }
            }
        }
    }
    out
}

/// Detect an equational rule head (WI-139): the head term is an
/// `=` application like `add(?a, ?b) = add(?b, ?a)`. Used by
/// `load_rule` to gate the `by_functor` index — bare equational
/// rules are cite-required only and must not drive automatic SLD
/// rewriting (which would loop on `add_comm`-style laws).
pub fn is_equational_head(kb: &KnowledgeBase, head: TermId) -> bool {
    if let Term::Fn { functor, .. } = kb.get_term(head) {
        let qn = kb.qualified_name_of(*functor);
        let short = qn.rsplit('.').next().unwrap_or(qn);
        // The kernel's equality predicate. Aliases that resolve to
        // the same builtin are normalised at scan-time, so this
        // suffix-match is sufficient.
        return short == "=" || short == "eq";
    }
    false
}

/// Test whether a rule's `meta` block contains a flag with the
/// given key. Treats both `[name]` (no value) and `[name: anything]`
/// as "flag is present" — the loader stores the meta as a `meta(...)`
/// term whose `named_args` carry the entries.
pub fn meta_has_flag(kb: &KnowledgeBase, meta: Option<TermId>, key: &str) -> bool {
    let tid = match meta { Some(t) => t, None => return false };
    if let Term::Fn { named_args, .. } = kb.get_term(tid) {
        for (k, _) in named_args.iter() {
            if kb.resolve_sym(*k) == key { return true; }
        }
    }
    false
}

/// Resolve a `SortRequiresInfo.sort_ref` term to the qualified name
/// of the enclosing scope (sort or operation). Returns the canonical
/// `qualified_name` rather than the short display name so the
/// emitted ProofRecord rule QN is project-unique.
pub fn qn_of_sort_ref(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    match kb.get_term(term) {
        Term::Fn { functor, .. } => Some(kb.qualified_name_of(*functor).to_owned()),
        Term::Ref(s) | Term::Ident(s) => Some(kb.qualified_name_of(*s).to_owned()),
        _ => None,
    }
}

/// Flatten a `SortRequiresInfo.spec` term to the deterministic
/// short-name signature used in `requires.<SE-flat>` rule QNs. For
/// `SortView(Eq, T = X)` the result is `Eq_<short(X)>`. For a plain
/// nullary sort term `Foo`, the result is `Foo`. Bindings are sorted
/// by their binding key short name to keep the encoding stable
/// across reorderings. Operation auto-bindings (binding values that
/// resolve to operation symbols) are filtered out — they are
/// derived from `resolve_requires_bindings` and not user-written, so
/// they should not pollute the SE-flat. Type-parameter and
/// concrete-sort bindings remain.
pub fn flatten_spec(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    use crate::intern::SymbolKind;
    let term_ref = kb.get_term(term);
    let (functor, pos_args, named_args) = match term_ref {
        Term::Fn { functor, pos_args, named_args } =>
            (*functor, pos_args.clone(), named_args.clone()),
        _ => return None,
    };
    let functor_name = kb.resolve_sym(functor);
    let functor_short = functor_name.rsplit('.').next().unwrap_or(functor_name);
    if functor_short != "SortView" {
        return Some(functor_short.to_owned());
    }
    let base_short = match pos_args.first().map(|t| kb.get_term(*t)) {
        Some(Term::Fn { functor, .. }) | Some(Term::Ref(functor)) | Some(Term::Ident(functor)) => {
            let n = kb.resolve_sym(*functor);
            n.rsplit('.').next().unwrap_or(n).to_owned()
        }
        _ => return None,
    };
    let mut bindings: Vec<(String, String)> = named_args.iter().filter_map(|(k_sym, v_tid)| {
        let value_sym = match kb.get_term(*v_tid) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => Some(*functor),
            _ => None,
        };
        // Skip operation auto-bindings — they aren't part of the
        // user-written Sort-Expr.
        if let Some(vs) = value_sym {
            if matches!(kb.kind_of(vs), Some(SymbolKind::Operation)) {
                return None;
            }
        }
        let k_name = kb.resolve_sym(*k_sym);
        let k_short = k_name.rsplit('.').next().unwrap_or(k_name).to_owned();
        let v_short = match value_sym {
            Some(s) => {
                let n = kb.resolve_sym(s);
                n.rsplit('.').next().unwrap_or(n).to_owned()
            }
            None => match kb.get_term(*v_tid) {
                Term::Const(Literal::String(s)) => format!("str_{s}"),
                _ => "_".to_string(),
            },
        };
        Some((k_short, v_short))
    }).collect();
    bindings.sort_by(|a, b| a.0.cmp(&b.0));
    if bindings.is_empty() {
        Some(base_short)
    } else {
        let parts: Vec<String> = bindings.into_iter().map(|(_, v)| v).collect();
        Some(format!("{base_short}_{}", parts.join("_")))
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
        if !kb.is_fact(rid) {
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
/// Resolve a `short_name` to an operation declared on the sort named by
/// `sort_ref_tid` (its `OperationInfo` scope equals that sort). Used by the
/// WI-279 dot-dispatch default fallback: `?x.m(args)` resolves `m` against
/// the receiver's least sort.
pub(crate) fn find_operation_in_scope(kb: &mut KnowledgeBase, sort_ref_tid: TermId, short_name: &str) -> Option<Symbol> {
    let op_info_sym = match kb.try_resolve_symbol("anthill.reflect.OperationInfo") {
        Some(sym) => sym,
        None => return None,
    };
    // Get the sort symbol from the sort_ref term
    let sort_sym = match kb.get_term(sort_ref_tid) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(sym) => *sym,
        _ => return None,
    };

    let rule_ids = kb.by_functor(op_info_sym);
    for rid in rule_ids {
        if !kb.is_fact(rid) {
            continue;
        }
        // WI-348: carrier-agnostic — the OperationInfo head may be a value fact
        // (Node-carrying) for ops with a `denoted` effect. Extract the op
        // symbol from the `name` field through the shared `op_info` helper.
        let op_sym = crate::kb::op_info::head_name_ref(kb, kb.rule_head_value(rid));
        {
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

/// WI-348 — build a carrier-agnostic cons/nil list of `Value`s, the value-fact
/// twin of [`build_list`]. Used for an `OperationInfo` effects list that carries
/// a `Value::Node` label (`Modify[c]`), which cannot live in a `TermId` list.
/// `cons`/`nil` cells are `Value::Entity`s over the same prelude constructors,
/// so the result decomposes into the same `DiscrimKey`s as a term list.
fn build_value_list(kb: &mut KnowledgeBase, items: Vec<crate::eval::value::Value>) -> crate::eval::value::Value {
    use crate::eval::value::Value;
    use std::rc::Rc;
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");

    let mut list = Value::Entity {
        functor: nil_sym,
        pos: Rc::from(Vec::<Value>::new()),
        named: Rc::from(Vec::<(Symbol, Value)>::new()),
    };
    for item in items.into_iter().rev() {
        list = Value::Entity {
            functor: cons_sym,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(head_sym, item), (tail_sym, list)]),
        };
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
        Term::Var(Var::Global(vid)) => {
            let kb_vid = if let Some(&mapped) = var_map.get(&vid.raw()) {
                mapped
            } else {
                let name_str = parse_symbols.name(vid.name());
                let kb_name = kb.intern(name_str);
                let new_vid = kb.fresh_var(kb_name);
                var_map.insert(vid.raw(), new_vid);
                new_vid
            };
            kb.alloc(Term::Var(Var::Global(kb_vid)))
        }
        Term::Var(Var::DeBruijn(n)) => kb.alloc(Term::Var(Var::DeBruijn(n))),
        Term::Var(Var::Rigid(_)) => {
            // Rigid vars are introduced only post-open by the resolver,
            // never present in stored terms — should not appear here.
            unreachable!("Var::Rigid in stored parse term")
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
            // Always sort named args to match entity field order (required for
            // discrimination tree matching — both facts and patterns must have
            // named args in the same order). Positional args also count as
            // "provided" — `ToolPasses("cargo-test")` covers `tool` via
            // pos_args[0], so the field shouldn't be re-stuffed with a fresh
            // var in named (which would shadow the positional value at
            // materialization time).
            if let Some(all_fields) = kb.entity_field_names(kb_functor) {
                let all_fields = all_fields.to_vec();
                if new_named.len() + new_pos.len() < all_fields.len() {
                    let mut provided: HashSet<Symbol> = new_named
                        .iter().map(|(s, _)| *s).collect();
                    for (i, &field_sym) in all_fields.iter().enumerate() {
                        if i < new_pos.len() {
                            provided.insert(field_sym);
                        }
                    }
                    for &field_sym in &all_fields {
                        if !provided.contains(&field_sym) {
                            let fresh = kb.fresh_var(field_sym);
                            let var_term = kb.alloc(Term::Var(Var::Global(fresh)));
                            new_named.push((field_sym, var_term));
                        }
                    }
                }
                let order: HashMap<Symbol, usize> = all_fields.iter().enumerate()
                    .map(|(i, &s)| (s, i)).collect();
                new_named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
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
        Term::ParseAux(_) => unreachable!(
            "parse-only Term::ParseAux variant reached convert_query_term (loader should strip it)",
        ),
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
/// TODO: The short-name fallback masks missing imports. Track as a bug to fix scope chain.
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
/// This is a workaround for incomplete scope resolution — names should
/// be resolvable via the scope chain without this fallback.
///
/// `SymbolKind::Param` symbols are skipped: operation parameters and
/// fields are encapsulated to their op body's scope and must NOT leak
/// out via short-name fallback. Pre-WI-264 a body's bare `y` could
/// accidentally resolve to (e.g.) `anthill.prelude.Float.atan2.y` —
/// the stdlib operation's parameter — and the typer's silent-None bail
/// masked the consequences. With the typer's Result propagation any
/// such mis-qualification surfaces as `UnresolvedName`, so the fallback
/// must not introduce it in the first place.
fn resolve_by_short_name(kb: &KnowledgeBase, name: &str) -> Option<Symbol> {
    use crate::intern::{SymbolDef, SymbolKind};

    // Scan by_qualified_name for matching short name
    let mut found: Option<Symbol> = None;
    let mut found_is_builtin = false;
    for (qname, &sym) in &kb.symbols.by_qualified_name {
        let short = qname.rsplit('.').next().unwrap_or(qname);
        if short != name {
            continue;
        }
        // Encapsulated kinds: never reachable by short-name fallback.
        // Op params and entity fields are local to their declaring
        // scope; reaching them via global short-name lookup is a leak.
        if let SymbolDef::Resolved { kind, .. } = kb.symbols.get(sym) {
            if matches!(kind, SymbolKind::Param | SymbolKind::Field) {
                continue;
            }
        }
        let is_builtin = kb.builtins.contains_key(&sym);
        if found.is_some() {
            if is_builtin && !found_is_builtin {
                found = Some(sym);
                found_is_builtin = true;
            } else if !is_builtin && found_is_builtin {
                // Keep existing builtin
            } else {
                return None; // ambiguous
            }
        } else {
            found = Some(sym);
            found_is_builtin = is_builtin;
        }
    }
    found
}

// WI-233: per-item-kind aggregator (count, total time). Gated by
// ANTHILL_ITEM_TIMING=1. Aggregates across all files in a pass; the
// outer phase reset+print helpers below.
thread_local! {
    static ITEM_TIMINGS: std::cell::RefCell<std::collections::HashMap<&'static str, (u32, std::time::Duration)>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

pub fn reset_item_timings() {
    ITEM_TIMINGS.with(|m| m.borrow_mut().clear());
}

pub fn print_item_timings(label: &str) {
    ITEM_TIMINGS.with(|m| {
        let m = m.borrow();
        let mut entries: Vec<_> = m.iter().collect();
        entries.sort_by_key(|(_, (_, d))| std::cmp::Reverse(*d));
        eprintln!("[item_timing/{label}]");
        for (kind, (count, total)) in entries {
            eprintln!("  {kind:>16}: {count:>5} items, {total:?}");
        }
    });
}

/// Work-stack opcode for the iterative expression loader. `Visit`
/// dispatches a parse-time term (leaf → emit kb_id; non-leaf → push
/// a `Build` frame + child `Visit`s). `Build` consumes
/// already-converted children from the result stack and assembles
/// the parent kb_id, keeping host stack usage O(1) regardless of
/// source nesting depth.
enum LoadWorkOp {
    Visit(TermId),
    Build(LoadBuildFrame),
    /// Open a let/lambda/match-branch local-name scope. The frame's
    /// (name → symbol) entries shadow same-named rules / params /
    /// constructors / etc. during the body's visit, so the body's
    /// bare-name reference resolves to the let-bound symbol instead
    /// of an unrelated qualified one found by `resolve_by_short_name`.
    PushLocalScope(HashMap<String, Symbol>),
    /// Close the topmost local-name scope. Paired with a preceding
    /// `PushLocalScope` so push/pop nest correctly under iterative
    /// dispatch.
    PopLocalScope,
    /// WI-304: enter occurrence-suppression for a let/lambda/match pattern
    /// subtree. The term walk visits the pattern as a child, but in the
    /// occurrence the pattern lives in a `TermId` field (not a child
    /// occurrence), so the pattern subtree must push NOTHING to
    /// `expr_occ_results`. Nests via a counter.
    PushOccSuppress,
    /// WI-304: leave occurrence-suppression (pairs with `PushOccSuppress`).
    PopOccSuppress,
}

/// Post-order assembly frame for the iterative expression loader.
/// Each variant pairs an `outer_parse_id` (consumed by the final
/// `create_occurrence` span record) with the structural metadata
/// (counts, names, functors) needed to drain the right number of
/// converted children from the result stack and rebuild the parent.
enum LoadBuildFrame {
    MatchExpr {
        outer_parse_id: TermId,
        branch_count: usize,
    },
    MatchBranch {
        outer_parse_id: TermId,
    },
    IfExpr {
        outer_parse_id: TermId,
    },
    LetExpr {
        outer_parse_id: TermId,
    },
    Lambda {
        outer_parse_id: TermId,
    },
    PatternConstructor {
        outer_parse_id: TermId,
        name_ref: TermId,
        sub_pattern_count: usize,
    },
    PatternTuple {
        outer_parse_id: TermId,
        element_count: usize,
    },
    ApplyOrConstructor {
        outer_parse_id: TermId,
        functor: Symbol,
        pos_count: usize,
        named_keys: SmallVec<[Symbol; 2]>,
    },
    /// WI-278: re-encode a parse `dot_apply(receiver, Ident(name),
    /// ...args)` into the reflect `dot_apply(receiver, name: Ref,
    /// args: List[ApplyArg])`. `name_ref` is pre-resolved (the name is
    /// metadata, not a child); the receiver and args are drained from
    /// `results`.
    DotApply {
        outer_parse_id: TermId,
        name_ref: TermId,
        pos_count: usize,
        named_keys: SmallVec<[Symbol; 2]>,
    },
}

struct Loader<'a> {
    kb: &'a mut KnowledgeBase,
    parsed: &'a ParsedFile,
    #[allow(dead_code)]
    resolver: &'a dyn SourceResolver,
    #[allow(dead_code)]
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
    // Cache: type param name → TermId (Var) per scope, so all references to T share the same Var
    type_param_vars: HashMap<(u32, String), TermId>,
    // Description index counter per target (keyed by TermId raw)
    desc_index: HashMap<u32, i64>,
    // ── Occurrence tracking ─────────────────────────────────────
    // Source file id for this file's occurrences
    source_id: SourceId,
    // Symbol of the current owning declaration (operation, rule, etc.)
    current_owner: Option<Symbol>,
    // Sort/enum terms defined in this file (for targeted type checking)
    defined_sorts: Vec<TermId>,
    // RuleIds of top-level user `fact …(…)` blocks, in source order.
    // Persistence backends (IndexedFileStore et al.) zip this with the
    // corresponding parsed.fact_spans() to populate per-fact source maps
    // so retract can drop a specific block without reconstructing it
    // from a content fingerprint.
    fact_rule_ids: Vec<crate::kb::RuleId>,
    // Pre-resolved symbols for the iterative expression loader. The 15
    // keys below are hit on every non-leaf node in `build_load` — caching
    // them once at `Loader::new` avoids repeated hashmap lookups in the
    // hot path.
    expr_syms: ExprBuilderSyms,
    // Reusable work / result stacks for `convert_expr_term`. Kept on
    // the loader and `mem::take`-swapped at each entry so a single pair
    // of allocations amortizes across every operation body.
    expr_work: Vec<LoadWorkOp>,
    expr_results: Vec<TermId>,
    // WI-304: parallel occurrence-result stack for `convert_expr_term`. As
    // the term walk builds each KB Term, the matching `NodeOccurrence` is
    // built natively here, so an op body's occurrence tree is produced
    // directly rather than re-inferred from the term via
    // `materialize_from_handle`.
    expr_occ_results: Vec<Rc<NodeOccurrence>>,
    // WI-304: match-branch metadata captured at each MatchBranch build, drained
    // by the enclosing MatchExpr build into a `BuildFrame::Match`.
    expr_match_metas: Vec<node_occurrence::BranchMeta>,
    // WI-304: occurrence-suppression depth. While > 0 (inside a let/lambda/
    // match pattern subtree) the leaf/build arms push nothing to
    // `expr_occ_results` — the pattern is a `TermId` field, not a child.
    occ_suppress: usize,
    // Stack of local-name scopes opened by `let`, `lambda`, and
    // `match_branch` during expression conversion. Each entry maps a
    // short name to its KB Symbol (the pattern's interned bare symbol).
    // Name resolution in `remap_symbol` consults this stack before
    // walking the `current_scope` chain so a body's reference to a
    // let-bound name doesn't accidentally resolve to an unrelated
    // rule / op / param of the same short name via
    // `resolve_by_short_name`. Pushed by the let/match/lambda visit
    // arms; popped by `LoadWorkOp::PopLocalScope`.
    local_names_stack: Vec<HashMap<String, Symbol>>,
}

/// Pre-resolved symbols used by `build_load`. Populated once at
/// `Loader::new`; all named-arg keys + functor symbols for the kb
/// canonical Expr / Pattern shape live here so the iterative loader
/// never re-hashes the same string.
struct ExprBuilderSyms {
    match_expr: Symbol,
    match_branch: Symbol,
    if_expr: Symbol,
    let_expr: Symbol,
    lambda: Symbol,
    constructor_pattern: Symbol,
    tuple_pattern: Symbol,
    constructor: Symbol,
    apply: Symbol,
    dot_apply: Symbol,
    apply_arg: Symbol,
    k_scrutinee: Symbol,
    k_branches: Symbol,
    k_pattern: Symbol,
    k_guard: Symbol,
    k_body: Symbol,
    k_cond: Symbol,
    k_then: Symbol,
    k_else: Symbol,
    k_value: Symbol,
    k_type_name: Symbol,
    k_param: Symbol,
    k_name: Symbol,
    k_receiver: Symbol,
    k_args: Symbol,
    k_elements: Symbol,
    k_fn: Symbol,
    k_type_args: Symbol,
    type_arg: Symbol,
}

impl ExprBuilderSyms {
    fn new(kb: &mut KnowledgeBase) -> Self {
        Self {
            match_expr: kb.resolve_symbol("anthill.reflect.Expr.match_expr"),
            match_branch: kb.resolve_symbol("anthill.reflect.MatchBranch"),
            if_expr: kb.resolve_symbol("anthill.reflect.Expr.if_expr"),
            let_expr: kb.resolve_symbol("anthill.reflect.Expr.let_expr"),
            lambda: kb.resolve_symbol("anthill.reflect.Expr.lambda_expr"),
            constructor_pattern: kb.resolve_symbol("anthill.reflect.Pattern.constructor_pattern"),
            tuple_pattern: kb.resolve_symbol("anthill.reflect.Pattern.tuple_pattern"),
            constructor: kb.resolve_symbol("anthill.reflect.Expr.constructor"),
            apply: kb.resolve_symbol("anthill.reflect.Expr.apply"),
            dot_apply: kb.resolve_symbol("anthill.reflect.Expr.dot_apply"),
            apply_arg: kb.resolve_symbol("anthill.reflect.ApplyArg"),
            k_scrutinee: kb.intern("scrutinee"),
            k_branches: kb.intern("branches"),
            k_pattern: kb.intern("pattern"),
            k_guard: kb.intern("guard"),
            k_body: kb.intern("body"),
            k_cond: kb.intern("cond"),
            k_then: kb.intern("then_branch"),
            k_else: kb.intern("else_branch"),
            k_value: kb.intern("value"),
            k_type_name: kb.intern("type_name"),
            k_param: kb.intern("param"),
            k_name: kb.intern("name"),
            k_receiver: kb.intern("receiver"),
            k_args: kb.intern("args"),
            k_elements: kb.intern("elements"),
            k_fn: kb.intern("fn"),
            k_type_args: kb.intern("type_args"),
            type_arg: kb.intern("type_arg"),
        }
    }
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
        let expr_syms = ExprBuilderSyms::new(kb);
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
            type_param_vars: HashMap::new(),
            defined_sorts: Vec::new(),
            fact_rule_ids: Vec::new(),
            source_id,
            current_owner: None,
            expr_syms,
            expr_work: Vec::with_capacity(64),
            expr_results: Vec::with_capacity(64),
            expr_occ_results: Vec::new(),
            expr_match_metas: Vec::new(),
            occ_suppress: 0,
            local_names_stack: Vec::new(),
        }
    }

    /// Look up a name in the let/lambda/match-branch scope stack.
    /// Returns the bound KB symbol when the name is in scope.
    fn lookup_local_name(&self, name: &str) -> Option<Symbol> {
        for frame in self.local_names_stack.iter().rev() {
            if let Some(&sym) = frame.get(name) {
                return Some(sym);
            }
        }
        None
    }

    /// Build a let/lambda/match-branch local-name scope frame from the
    /// pattern's bound variable names. Returns the frame to push onto
    /// `local_names_stack`. Empty patterns (wildcard, literal) produce
    /// an empty frame; callers should skip the Push/Pop ops in that
    /// case to avoid no-op stack churn.
    fn build_pattern_scope_frame(&mut self, parse_id: TermId) -> HashMap<String, Symbol> {
        let mut frame: HashMap<String, Symbol> = HashMap::new();
        self.collect_pattern_names_into(parse_id, &mut frame);
        frame
    }

    /// Walk a parse-time pattern term and add each bound variable's
    /// (short_name → KB symbol) entry into `frame`. The KB symbol is
    /// the bare intern of the short name, matching what
    /// `load_pattern_var → reintern` produces for the pattern itself.
    fn collect_pattern_names_into(
        &mut self,
        parse_id: TermId,
        frame: &mut HashMap<String, Symbol>,
    ) {
        // Borrow `parsed.terms` immutably; `kb.intern` borrows kb mutably.
        // Extract the structural data we need first, drop the borrow,
        // then intern.
        let (functor_name, pos_args, named_args) = {
            let t = self.parsed.terms.get(parse_id);
            match t {
                Term::Fn { functor, pos_args, named_args } => {
                    let n = self.parsed.symbols.name(*functor).to_owned();
                    (n, pos_args.clone(), named_args.clone())
                }
                _ => return,
            }
        };
        match functor_name.as_str() {
            "pattern_var" => {
                if let Some(&first) = pos_args.first() {
                    if let Term::Ident(sym) = self.parsed.terms.get(first) {
                        let name = self.parsed.symbols.name(*sym).to_owned();
                        let kb_sym = self.kb.intern(&name);
                        frame.insert(name, kb_sym);
                    }
                }
            }
            "pattern_tuple" => {
                for sub in pos_args {
                    self.collect_pattern_names_into(sub, frame);
                }
            }
            "pattern_constructor" => {
                // pos_args[0] is the constructor name; the rest are
                // positional sub-patterns. `named_args` carries the
                // `case Foo(field = pat)` form's sub-patterns under
                // their field names — those bind too.
                for sub in pos_args.into_iter().skip(1) {
                    self.collect_pattern_names_into(sub, frame);
                }
                for (_, sub) in named_args {
                    self.collect_pattern_names_into(sub, frame);
                }
            }
            _ => {}
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
    ///
    /// Consults the let/lambda/match-branch local-name scope stack
    /// first. A pattern-bound name in scope shadows any same-short-name
    /// rule / op / param / etc., so a body's reference to a let-bound
    /// `y` doesn't accidentally pull in `Float.atan2.y` via
    /// `resolve_by_short_name`.
    fn remap_symbol(&mut self, sym: Symbol) -> Symbol {
        let name = self.parsed.symbols.name(sym);
        if let Some(local) = self.lookup_local_name(name) {
            return local;
        }
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
                // Dotted name: try segment-aware resolution. Resolve the
                // head segment in scope (Map → anthill.prelude.Map), then
                // append the trailing segments to its qualified path and
                // look the result up directly. Covers the dotted-call form
                // `Map.empty()` and proposal-035 form (3) `Map[...].empty()`,
                // both of which produce a single joined Symbol "Map.empty"
                // that doesn't appear in any scope's locals/imports.
                if let Some((head, tail)) = name.split_once('.') {
                    if let ResolveResult::Found(head_sym) =
                        self.kb.symbols.resolve_in_scope(head, scope)
                    {
                        let head_qualified = match self.kb.symbols.get(head_sym) {
                            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                            SymbolDef::Unresolved { name } => name.clone(),
                        };
                        let probe = format!("{}.{}", head_qualified, tail);
                        if let Some(&q_sym) = self.kb.symbols.by_qualified_name.get(&probe) {
                            return q_sym;
                        }
                    }
                }
                // Fallback: global short-name search by qualified-name suffix.
                let interned = self.kb.symbols.intern(name);
                if let Some(sym) = resolve_by_short_name(self.kb, name) {
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

    /// Record a stored term's source span on the KB's
    /// `term_spans` / `functor_spans` side-tables — typing.rs and
    /// other passes read these for error-reporting spans.
    /// First-write-wins on both keys mirrors the legacy
    /// `the legacy occurrence by-term index/by_functor.first()` semantics.
    fn create_occurrence(&mut self, parse_id: TermId, kb_id: TermId) {
        let span = self.parsed.terms.span(parse_id);
        let source_span = SourceSpan::from_span(self.source_id, span);
        self.kb.term_spans.entry(kb_id).or_insert(source_span);
        if let Term::Fn { functor, .. } = self.kb.terms.get(kb_id) {
            let functor = *functor;
            self.kb.functor_spans.entry(functor).or_insert(source_span);
        }
    }

    /// True iff `ty` is `sort_ref(name: <List sym>)`.
    fn is_list_sort_ref(kb: &KnowledgeBase, ty: TermId) -> bool {
        let Term::Fn { functor, named_args, .. } = kb.get_term(ty) else { return false };
        if kb.resolve_sym(*functor) != "sort_ref" { return false; }
        let Some(name_tid) = get_named_arg(kb, named_args, "name") else { return false };
        let Term::Ref(target) = kb.get_term(name_tid) else { return false };
        let n = kb.qualified_name_of(*target);
        n == "anthill.prelude.List" || n == "anthill.prelude.List.List"
    }

    /// `Some(element_hint)` if `ty` is List-shaped, else `None` — outer
    /// `Some` signals "desugar ListLiteral here" (WI-007), inner `Option`
    /// is the element-type hint to propagate. Recurses through wrappers like
    /// `Option[T = List[T = X]]` since the runtime stores the inner list
    /// directly without the `some(…)` envelope.
    fn find_list_element_type(kb: &KnowledgeBase, ty: TermId) -> Option<Option<TermId>> {
        if Self::is_list_sort_ref(kb, ty) { return Some(None); }
        let Term::Fn { functor, named_args, .. } = kb.get_term(ty) else { return None };
        if kb.resolve_sym(*functor) != "parameterized" { return None; }

        let base_is_list = get_named_arg(kb, named_args, "base")
            .map(|b| Self::is_list_sort_ref(kb, b))
            .unwrap_or(false);
        if base_is_list {
            return Some(extract_type_param(kb, ty, "T"));
        }

        let bindings = get_named_arg(kb, named_args, "bindings")?;
        for binding in list_to_vec(kb, bindings) {
            if let Term::Fn { named_args: ba, .. } = kb.get_term(binding) {
                if let Some(value) = get_named_arg(kb, ba, "value") {
                    if let Some(inner) = Self::find_list_element_type(kb, value) {
                        return Some(inner);
                    }
                }
            }
        }
        None
    }

    /// Convert a parse-time TermId to a KB TermId, re-allocating into the hash-consed store.
    fn convert_term(&mut self, parse_id: TermId) -> TermId {
        self.convert_term_with_expected(parse_id, None)
    }

    /// Like `convert_term` but takes an optional expected-type hint that drives
    /// context-aware ListLiteral desugaring (WI-007). When `expected` is a
    /// `List`-shaped type, `ListLiteral` is rewritten to `cons/nil`; otherwise
    /// it stays in the KB as `ListLiteral` for downstream consumers.
    fn convert_term_with_expected(&mut self, parse_id: TermId, expected: Option<TermId>) -> TermId {
        if let Some(&mapped) = self.term_map.get(&parse_id.raw()) {
            return mapped;
        }

        let parse_term = self.parsed.terms.get(parse_id).clone();
        let kb_term = match parse_term {
            Term::Const(lit) => Term::Const(lit),
            Term::Var(Var::Global(vid)) => {
                let kb_vid = if let Some(&mapped) = self.var_map.get(&vid.raw()) {
                    mapped
                } else {
                    let name = self.reintern(vid.name());
                    let new_vid = self.kb.fresh_var(name);
                    self.var_map.insert(vid.raw(), new_vid);
                    new_vid
                };
                Term::Var(Var::Global(kb_vid))
            }
            Term::Var(Var::DeBruijn(n)) => Term::Var(Var::DeBruijn(n)),
            Term::Var(Var::Rigid(_)) => {
                unreachable!("Var::Rigid in stored parse term")
            }
            Term::Fn { functor, pos_args, named_args } => {
                // WI-278: re-encode a *converter-emitted* parse
                // `dot_apply(receiver, Ident(name), ...positional)` + named
                // call-args into the canonical reflect form
                // `dot_apply(receiver, name: Ref, args: List[ApplyArg])`. The
                // top-level wrapper matches the occurrence path (convert_expr's
                // LoadBuildFrame::DotApply); the children differ on purpose —
                // here they stay bare terms (convert_term-recursed: Const / Var
                // / Fn), since term consumers (smt-gen, the [simp] engine) read
                // raw terms, whereas convert_expr wraps them as reflect Expr
                // nodes. Do NOT "unify" the two paths. Without this, the generic
                // Fn conversion below leaves receiver/name *positional* and
                // stuffs a fresh var into the dot_apply entity's `args` field —
                // a malformed dot_apply no consumer can read (rule bodies reach
                // dot_apply here via load_rule → convert_term, not convert_expr).
                //
                // `dot_apply` is NOT a reserved name, and convert_term also
                // sees rule/fact/query terms the user typed. The arity +
                // `Ident`-name guard matches only the converter form: a
                // user-written `dot_apply(?x)` / `dot_apply()` / a user
                // `entity dot_apply` (named-arg construction) falls through to
                // generic conversion — and MUST, else `pos_args[1]` would panic
                // on < 2 positional args.
                if self.parsed.symbols.name(functor) == "dot_apply"
                    && pos_args.len() >= 2
                    && matches!(self.parsed.terms.get(pos_args[1]), Term::Ident(_))
                {
                    let receiver = self.convert_term(pos_args[0]);
                    // The name is metadata at pos_args[1] (an Ident) — resolve
                    // to a Ref, don't recurse it as a child.
                    let name_term = self.parsed.terms.get(pos_args[1]).clone();
                    let name_ref = if let Term::Ident(sym) = name_term {
                        let kb_sym = self.remap_symbol(sym);
                        self.kb.alloc(Term::Ref(kb_sym))
                    } else {
                        self.convert_term(pos_args[1])
                    };
                    let mut arg_terms: SmallVec<[TermId; 4]> = SmallVec::new();
                    for &pid in &pos_args[2..] {
                        let value = self.convert_term(pid);
                        let none = build_none(self.kb);
                        arg_terms.push(self.mk_apply_arg(none, value));
                    }
                    for &(sym, pid) in named_args.iter() {
                        let value = self.convert_term(pid);
                        let reinterned = self.reintern(sym);
                        let arg_name = self.kb.alloc(Term::Ref(reinterned));
                        let some_name = build_some(self.kb, arg_name);
                        arg_terms.push(self.mk_apply_arg(some_name, value));
                    }
                    let args_list = build_list(self.kb, &arg_terms);
                    let (dot, k_receiver, k_name, k_args) = {
                        let s = &self.expr_syms;
                        (s.dot_apply, s.k_receiver, s.k_name, s.k_args)
                    };
                    let kb_id = self.kb.alloc(Term::Fn {
                        functor: dot,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (k_receiver, receiver),
                            (k_name, name_ref),
                            (k_args, args_list),
                        ]),
                    });
                    self.term_map.insert(parse_id.raw(), kb_id);
                    return kb_id;
                }

                let new_functor = self.remap_symbol(functor);

                // WI-007 context-aware ListLiteral desugaring: only rewrite
                // `ListLiteral → cons/nil` when the surrounding field type is
                // List-shaped (recursing through wrappers like
                // `Option[T = List[T = X]]`). The inner `Option<TermId>` is
                // the recursive element-type hint, so nested
                // `[[...], ...]` for `List[T = List[T = X]]` propagates.
                let elem_hint = expected.and_then(|e| Self::find_list_element_type(self.kb, e));
                if self.kb.qualified_name_of(new_functor) == "anthill.reflect.ListLiteral"
                    && elem_hint.is_some()
                {
                    let elem_expected = elem_hint.flatten();
                    let items: Vec<TermId> = pos_args.iter()
                        .map(|&id| self.convert_term_with_expected(id, elem_expected))
                        .collect();
                    let tail_term = named_args.iter()
                        .find(|(sym, _)| self.parsed.symbols.name(*sym) == "tail")
                        .map(|&(_, id)| self.convert_term_with_expected(id, expected));
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
                    .enumerate()
                    .map(|(i, &id)| {
                        // WI-342: field types are carrier-agnostic; the
                        // conversion hint only wants a ground `TermId` (a
                        // denoted-bearing field is no literal-typing hint → None).
                        let exp = self.kb.entity_field_types(new_functor)
                            .and_then(|ft| ft.get(i).and_then(|(_, t)| t.as_term()));
                        self.convert_term_with_expected(id, exp)
                    })
                    .collect();
                // WI-271: skip parse-only ParseAux children (let_expr's
                // `type_name`, apply's `type_args`) — they are read
                // directly at the LoadBuildFrame::LetExpr /
                // ApplyOrConstructor build sites via
                // `read_parse_type_annotation` /
                // `read_parse_call_type_args`. Routing them through
                // convert_term_with_expected would hit the unreachable
                // ParseAux arm below.
                // Pre-collect the non-ParseAux args so the closure
                // body's `self`-mut calls don't re-borrow during
                // iteration.
                let visible_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                    .iter()
                    .filter(|&&(_, id)| !self.is_parse_aux(id))
                    .copied()
                    .collect();
                let mut new_named: SmallVec<[(Symbol, TermId); 2]> = visible_named
                    .into_iter()
                    .map(|(sym, id)| {
                        let new_sym = self.reintern(sym);
                        let exp = self.kb.entity_field_types(new_functor)
                            .and_then(|ft| ft.iter().find(|(s, _)| *s == new_sym).and_then(|(_, t)| t.as_term()));
                        (new_sym, self.convert_term_with_expected(id, exp))
                    })
                    .collect();

                // Expand partial named args: fill missing entity fields with fresh vars
                // Always sort named args to match entity field order.
                // Positional args also count as "provided" — `ToolPasses("x")`
                // covers `tool` via pos_args[0], so it shouldn't be re-stuffed
                // with a fresh var in named (which would shadow the positional
                // at materialization time).
                if let Some(all_fields) = self.kb.entity_field_names(new_functor) {
                    let all_fields = all_fields.to_vec(); // borrow-safe copy
                    if new_named.len() + new_pos.len() < all_fields.len() {
                        let mut provided: HashSet<Symbol> = new_named
                            .iter().map(|(s, _)| *s).collect();
                        for (i, &field_sym) in all_fields.iter().enumerate() {
                            if i < new_pos.len() {
                                provided.insert(field_sym);
                            }
                        }
                        for &field_sym in &all_fields {
                            if !provided.contains(&field_sym) {
                                let fresh = self.kb.fresh_var(field_sym);
                                let var_term = self.kb.alloc(Term::Var(Var::Global(fresh)));
                                new_named.push((field_sym, var_term));
                            }
                        }
                    }
                    let order: HashMap<Symbol, usize> = all_fields.iter().enumerate()
                        .map(|(i, &s)| (s, i)).collect();
                    new_named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
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
            Term::ParseAux(_) => {
                // WI-271: parse-only payload (TypeExpr / SortBindings).
                // Reaches `convert_term_with_expected` when the loader
                // recurses into a let_expr / apply's `type_name` /
                // `type_args` child without first stripping the
                // ParseAux. Specialized handlers at the LetExpr /
                // ApplyOrConstructor build sites read these children
                // directly and call `type_expr_to_term` /
                // `build_call_type_args` — they should NOT route
                // through generic `convert_term`.
                unreachable!(
                    "Term::ParseAux reached convert_term_with_expected — \
                     the LetExpr/ApplyOrConstructor build site must read \
                     and lower it directly before recursing",
                );
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
    // Converts positional-arg expression terms (from the parse-time IR)
    // into named-arg KB entity terms matching the Expr / Pattern sorts
    // in reflect.anthill. Also populates `kb.term_spans` /
    // `kb.functor_spans` so passes downstream can resolve a span from a
    // stored TermId.

    /// Convert a parse-time expression term into the KB's Expr
    /// representation using a work-stack walker. Each `Visit(parse_id)`
    /// produces a leaf kb_id directly or pushes a `Build` frame +
    /// child Visits; when the frame fires it consumes its children's
    /// kb_ids from the result stack and assembles the parent. Runs in
    /// O(1) host stack regardless of source nesting depth.
    fn convert_expr_term(&mut self, parse_id: TermId) -> (TermId, Rc<NodeOccurrence>) {
        let mut work = std::mem::take(&mut self.expr_work);
        let mut results = std::mem::take(&mut self.expr_results);
        work.clear();
        results.clear();
        // WI-304: occurrence stacks operate directly on `self` (the visit/build
        // arms take `&mut self`). Clear them at entry; they end empty after the
        // root is popped below. `convert_expr_term` is never re-entrant.
        self.expr_occ_results.clear();
        self.expr_match_metas.clear();
        debug_assert_eq!(self.occ_suppress, 0, "convert_expr_term: stale occ_suppress on entry");
        work.push(LoadWorkOp::Visit(parse_id));
        while let Some(op) = work.pop() {
            match op {
                LoadWorkOp::Visit(pid) => self.visit_load(pid, &mut work, &mut results),
                LoadWorkOp::Build(frame) => self.build_load(frame, &mut results),
                LoadWorkOp::PushLocalScope(scope) => {
                    self.local_names_stack.push(scope);
                }
                LoadWorkOp::PopLocalScope => {
                    self.local_names_stack.pop();
                }
                LoadWorkOp::PushOccSuppress => {
                    self.occ_suppress += 1;
                }
                LoadWorkOp::PopOccSuppress => {
                    self.occ_suppress -= 1;
                }
            }
        }
        debug_assert_eq!(results.len(), 1, "iterative loader: expected exactly one result");
        let kb_id = results.pop().expect("iterative loader: empty result stack");
        self.expr_work = work;
        self.expr_results = results;

        // WI-304: pop the single root occurrence built in parallel with the
        // term. `expr_occ_results` was cleared at entry (below) and operated
        // on directly through the walk via `&mut self`.
        debug_assert_eq!(
            self.expr_occ_results.len(),
            1,
            "convert_expr_term: expected exactly one occurrence, got {}",
            self.expr_occ_results.len(),
        );
        let occ = self.expr_occ_results.pop()
            .expect("convert_expr_term: empty occurrence stack");
        debug_assert!(self.expr_match_metas.is_empty(), "convert_expr_term: leftover branch metas");
        (kb_id, occ)
    }

    /// Dispatch a single parse-time expression term: produce a leaf
    /// kb_id directly or push a Build frame + child Visits.
    fn visit_load(
        &mut self,
        parse_id: TermId,
        work: &mut Vec<LoadWorkOp>,
        results: &mut Vec<TermId>,
    ) {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        match parse_term {
            Term::Fn { functor, pos_args, named_args } => {
                let name = self.parsed.symbols.name(functor).to_owned();
                match name.as_str() {
                    "match_expr" => {
                        let branch_count = pos_args.len() - 1;
                        work.push(LoadWorkOp::Build(LoadBuildFrame::MatchExpr {
                            outer_parse_id: parse_id,
                            branch_count,
                        }));
                        for &child in pos_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(child));
                        }
                    }
                    "match_branch" => {
                        // Pattern names are bound for the branch body.
                        let frame = self.build_pattern_scope_frame(pos_args[0]);
                        work.push(LoadWorkOp::Build(LoadBuildFrame::MatchBranch {
                            outer_parse_id: parse_id,
                        }));
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PopLocalScope);
                        }
                        work.push(LoadWorkOp::Visit(pos_args[1])); // body
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PushLocalScope(frame));
                        }
                        // WI-304: the pattern is a TermId field on the branch,
                        // not a child occurrence — suppress its subtree.
                        work.push(LoadWorkOp::PopOccSuppress);
                        work.push(LoadWorkOp::Visit(pos_args[0])); // pattern
                        work.push(LoadWorkOp::PushOccSuppress);
                    }
                    "if_expr" => {
                        work.push(LoadWorkOp::Build(LoadBuildFrame::IfExpr {
                            outer_parse_id: parse_id,
                        }));
                        work.push(LoadWorkOp::Visit(pos_args[2]));
                        work.push(LoadWorkOp::Visit(pos_args[1]));
                        work.push(LoadWorkOp::Visit(pos_args[0]));
                    }
                    "let_expr" => {
                        // The let-pattern's bound names are in scope for
                        // the body but not for the value, so push the
                        // scope frame between value and body. Pop order
                        // on the stack: build_let → pop_scope → body →
                        // push_scope → value → pattern, so push them in
                        // reverse. Skip the scope ops entirely when the
                        // pattern binds no names (wildcard / literal).
                        let frame = self.build_pattern_scope_frame(pos_args[0]);
                        work.push(LoadWorkOp::Build(LoadBuildFrame::LetExpr {
                            outer_parse_id: parse_id,
                        }));
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PopLocalScope);
                        }
                        work.push(LoadWorkOp::Visit(pos_args[2])); // body
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PushLocalScope(frame));
                        }
                        work.push(LoadWorkOp::Visit(pos_args[1])); // value
                        // WI-304: pattern is a TermId field on the let, not a
                        // child occurrence — suppress its subtree.
                        work.push(LoadWorkOp::PopOccSuppress);
                        work.push(LoadWorkOp::Visit(pos_args[0])); // pattern
                        work.push(LoadWorkOp::PushOccSuppress);
                    }
                    "lambda_expr" => {
                        // Lambda param is in scope for the body.
                        let frame = self.build_pattern_scope_frame(pos_args[0]);
                        work.push(LoadWorkOp::Build(LoadBuildFrame::Lambda {
                            outer_parse_id: parse_id,
                        }));
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PopLocalScope);
                        }
                        work.push(LoadWorkOp::Visit(pos_args[1])); // body
                        if !frame.is_empty() {
                            work.push(LoadWorkOp::PushLocalScope(frame));
                        }
                        // WI-304: param is a TermId field on the lambda, not a
                        // child occurrence — suppress its subtree.
                        work.push(LoadWorkOp::PopOccSuppress);
                        work.push(LoadWorkOp::Visit(pos_args[0])); // param
                        work.push(LoadWorkOp::PushOccSuppress);
                    }
                    "pattern_var" => {
                        let kb_id = self.load_pattern_var(&pos_args);
                        self.create_occurrence(parse_id, kb_id);
                        results.push(kb_id);
                        self.push_leaf_occ(kb_id);
                    }
                    "pattern_wildcard" => {
                        let kb_id = self.load_pattern_wildcard();
                        self.create_occurrence(parse_id, kb_id);
                        results.push(kb_id);
                        self.push_leaf_occ(kb_id);
                    }
                    "pattern_literal" => {
                        let kb_id = self.load_pattern_literal(&pos_args);
                        self.create_occurrence(parse_id, kb_id);
                        results.push(kb_id);
                        self.push_leaf_occ(kb_id);
                    }
                    "pattern_constructor" => {
                        // The constructor name (pos_args[0]) is a leaf Ident — pre-resolve
                        // it now so the Build frame can drain only the sub-pattern children.
                        let name_term = self.parsed.terms.get(pos_args[0]).clone();
                        let name_ref = if let Term::Ident(sym) = name_term {
                            let kb_sym = self.remap_symbol(sym);
                            self.kb.alloc(Term::Ref(kb_sym))
                        } else {
                            self.convert_term(pos_args[0])
                        };
                        let sub_pattern_count = pos_args.len() - 1;
                        work.push(LoadWorkOp::Build(LoadBuildFrame::PatternConstructor {
                            outer_parse_id: parse_id,
                            name_ref,
                            sub_pattern_count,
                        }));
                        for &child in pos_args[1..].iter().rev() {
                            work.push(LoadWorkOp::Visit(child));
                        }
                    }
                    "dot_apply" => {
                        // Parse shape: pos_args = [receiver, Ident(name),
                        // ...positional]; named_args = named call args. The
                        // name is metadata (pre-resolve, don't Visit); the
                        // receiver + args are children.
                        let name_term = self.parsed.terms.get(pos_args[1]).clone();
                        let name_ref = if let Term::Ident(sym) = name_term {
                            let kb_sym = self.remap_symbol(sym);
                            self.kb.alloc(Term::Ref(kb_sym))
                        } else {
                            self.convert_term(pos_args[1])
                        };
                        let positional = &pos_args[2..];
                        let named_keys: SmallVec<[Symbol; 2]> =
                            named_args.iter().map(|&(sym, _)| sym).collect();
                        work.push(LoadWorkOp::Build(LoadBuildFrame::DotApply {
                            outer_parse_id: parse_id,
                            name_ref,
                            pos_count: positional.len(),
                            named_keys,
                        }));
                        // Push named (reversed), positional (reversed), then
                        // receiver last so it pops/lands first.
                        for &(_, tid) in named_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                        for &tid in positional.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                        work.push(LoadWorkOp::Visit(pos_args[0]));
                    }
                    "pattern_tuple" => {
                        let element_count = pos_args.len();
                        work.push(LoadWorkOp::Build(LoadBuildFrame::PatternTuple {
                            outer_parse_id: parse_id,
                            element_count,
                        }));
                        for &child in pos_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(child));
                        }
                    }
                    _ => {
                        // WI-271: filter out parse-only auxiliary
                        // children (Term::ParseAux). These hold the
                        // let_expr annotation / apply type-args and
                        // are consumed directly at the
                        // LoadBuildFrame::ApplyOrConstructor build by
                        // `read_parse_call_type_args` and
                        // `read_parse_type_annotation`; the work-stack
                        // walker must not recurse into them.
                        let visible_named: Vec<(Symbol, TermId)> = named_args.iter()
                            .filter(|&&(_, tid)| !self.is_parse_aux(tid))
                            .copied()
                            .collect();
                        let named_keys: SmallVec<[Symbol; 2]> =
                            visible_named.iter().map(|&(sym, _)| sym).collect();
                        let pos_count = pos_args.len();
                        work.push(LoadWorkOp::Build(LoadBuildFrame::ApplyOrConstructor {
                            outer_parse_id: parse_id,
                            functor,
                            pos_count,
                            named_keys,
                        }));
                        for &(_, tid) in visible_named.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                        for &tid in pos_args.iter().rev() {
                            work.push(LoadWorkOp::Visit(tid));
                        }
                    }
                }
            }
            Term::Const(_) => {
                let kb_id = self.load_literal_expr(parse_id);
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                self.push_leaf_occ(kb_id);
            }
            Term::Ident(_) => {
                let kb_id = self.load_var_ref(parse_id);
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                self.push_leaf_occ(kb_id);
            }
            _ => {
                let kb_id = self.convert_term(parse_id);
                self.create_occurrence(parse_id, kb_id);
                results.push(kb_id);
                self.push_leaf_occ(kb_id);
            }
        }
    }

    /// WI-304: push the native leaf `NodeOccurrence` for a just-built leaf
    /// kb_id, unless we're inside a suppressed pattern subtree (where the
    /// pattern is a `TermId` field, not a child occurrence). Mirrors the leaf
    /// arms of `node_occurrence::visit_term`.
    fn push_leaf_occ(&mut self, kb_id: TermId) {
        if self.occ_suppress == 0 {
            let occ = node_occurrence::build_expr_leaf(self.kb, kb_id);
            self.expr_occ_results.push(occ);
        }
    }

    /// Assemble a parent kb_id from its already-converted children
    /// (read in pushed order from the tail of `results`, then truncated).
    fn build_load(&mut self, frame: LoadBuildFrame, results: &mut Vec<TermId>) {
        match frame {
            LoadBuildFrame::MatchExpr { outer_parse_id, branch_count } => {
                let drain_start = results.len() - (branch_count + 1);
                let scrutinee = results[drain_start];
                let branches = build_list(self.kb, &results[drain_start + 1..]);
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.match_expr,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_scrutinee, scrutinee),
                        (s.k_branches, branches),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    let n = self.expr_match_metas.len();
                    let branches = self.expr_match_metas.split_off(n - branch_count);
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::Match { span, branches },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::MatchBranch { outer_parse_id } => {
                let drain_start = results.len() - 2;
                let pattern = results[drain_start];
                let body = results[drain_start + 1];
                results.truncate(drain_start);
                let guard = build_none(self.kb);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.match_branch,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_pattern, pattern),
                        (s.k_guard, guard),
                        (s.k_body, body),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    // WI-304: the body occurrence is already on
                    // `expr_occ_results` (pattern was suppressed; guard is
                    // always none here). Record branch metadata for the
                    // enclosing MatchExpr build to drain.
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    self.expr_match_metas.push(node_occurrence::BranchMeta {
                        pattern,
                        has_guard: false,
                        span,
                    });
                }
            }
            LoadBuildFrame::IfExpr { outer_parse_id } => {
                let drain_start = results.len() - 3;
                let cond = results[drain_start];
                let then_branch = results[drain_start + 1];
                let else_branch = results[drain_start + 2];
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.if_expr,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_cond, cond),
                        (s.k_then, then_branch),
                        (s.k_else, else_branch),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::If { span },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::LetExpr { outer_parse_id } => {
                let drain_start = results.len() - 3;
                let pattern = results[drain_start];
                let value = results[drain_start + 1];
                let body = results[drain_start + 2];
                results.truncate(drain_start);
                let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
                    (self.expr_syms.k_pattern, pattern),
                    (self.expr_syms.k_value, value),
                    (self.expr_syms.k_body, body),
                ]);
                // WI-271: `let x : T = e1; e2` annotation is now inline
                // on the parse let_expr Term::Fn as a `type_name`
                // named arg pointing at a `Term::ParseAux(TypeExpr(T))`
                // node — replaces the prior
                // `SimpleTermStore::let_type_annotations` HashMap.
                // Unwrap the ParseAux and lower the TypeExpr to a KB
                // Term via the existing `type_expr_to_term` so the
                // typer (proposal 035 form 1 + WI-270) sees the same
                // `k_type_name` slot on the KB Term::Fn as before.
                if let Some(ty_expr) = self.read_parse_type_annotation(outer_parse_id) {
                    let ty_term = self.type_expr_to_term(&ty_expr);
                    named.push((self.expr_syms.k_type_name, ty_term));
                }
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: self.expr_syms.let_expr,
                    pos_args: SmallVec::new(),
                    named_args: named,
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    // Read the `type_name` slot back off the just-built term;
                    // pattern is the captured `pattern` TermId field (suppressed
                    // on the occ stack, so the occ stack holds only [value, body]).
                    let type_annotation = if let Term::Fn { named_args, .. } = self.kb.get_term(kb_id) {
                        named_args.iter()
                            .find(|(k, _)| *k == self.expr_syms.k_type_name)
                            .map(|(_, v)| *v)
                    } else {
                        None
                    };
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::Let { span, pattern, type_annotation },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::Lambda { outer_parse_id } => {
                let drain_start = results.len() - 2;
                let param = results[drain_start];
                let body = results[drain_start + 1];
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.lambda,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_param, param),
                        (s.k_body, body),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::Lambda { span, param },
                        &mut self.expr_occ_results,
                    );
                }
            }
            LoadBuildFrame::PatternConstructor {
                outer_parse_id,
                name_ref,
                sub_pattern_count,
            } => {
                let drain_start = results.len() - sub_pattern_count;
                let args_list = build_list(self.kb, &results[drain_start..]);
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.constructor_pattern,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_name, name_ref),
                        (s.k_args, args_list),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                // WI-304: a constructor pattern is only reached inside a
                // suppressed pattern subtree (let/lambda/match pattern), so it
                // never contributes a child occurrence.
                debug_assert!(self.occ_suppress > 0, "pattern_constructor outside suppression");
            }
            LoadBuildFrame::PatternTuple { outer_parse_id, element_count } => {
                let drain_start = results.len() - element_count;
                let elements_list = build_list(self.kb, &results[drain_start..]);
                results.truncate(drain_start);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.tuple_pattern,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[(s.k_elements, elements_list)]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                debug_assert!(self.occ_suppress > 0, "pattern_tuple outside suppression");
            }
            LoadBuildFrame::ApplyOrConstructor {
                outer_parse_id,
                functor: parse_functor,
                pos_count,
                named_keys,
            } => {
                let total = pos_count + named_keys.len();
                let drain_start = results.len() - total;

                let kb_functor = self.remap_symbol(parse_functor);
                let is_entity = matches!(
                    self.kb.symbols.get(kb_functor),
                    SymbolDef::Resolved { kind: SymbolKind::Entity, .. }
                );

                let mut arg_terms: SmallVec<[TermId; 4]> = SmallVec::with_capacity(total);
                for i in 0..pos_count {
                    let value = results[drain_start + i];
                    let none = build_none(self.kb);
                    arg_terms.push(self.mk_apply_arg(none, value));
                }
                for (i, &sym) in named_keys.iter().enumerate() {
                    let value = results[drain_start + pos_count + i];
                    let reinterned = self.reintern(sym);
                    let name_ref = self.kb.alloc(Term::Ref(reinterned));
                    let some_name = build_some(self.kb, name_ref);
                    arg_terms.push(self.mk_apply_arg(some_name, value));
                }
                results.truncate(drain_start);
                let args_list = build_list(self.kb, &arg_terms);
                let name_ref = self.kb.alloc(Term::Ref(kb_functor));

                let type_args_tid = self.build_call_type_args(outer_parse_id);

                let s = &self.expr_syms;
                let kb_id = if is_entity {
                    self.kb.alloc(Term::Fn {
                        functor: s.constructor,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (s.k_name, name_ref),
                            (s.k_args, args_list),
                        ]),
                    })
                } else {
                    let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
                        (s.k_fn, name_ref),
                        (s.k_args, args_list),
                    ]);
                    if let Some(tid) = type_args_tid {
                        named.push((s.k_type_args, tid));
                    }
                    self.kb.alloc(Term::Fn {
                        functor: s.apply,
                        pos_args: SmallVec::new(),
                        named_args: named,
                    })
                };
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    // Reintern the parse named keys to the SAME KB symbols the
                    // term's ApplyArg names use (see the named loop above), so
                    // the occurrence's named args line up with the term.
                    let occ_named_keys: Vec<Symbol> =
                        named_keys.iter().map(|s| self.reintern(*s)).collect();
                    let frame = if is_entity {
                        node_occurrence::BuildFrame::Constructor {
                            span, name: kb_functor, pos_count, named_keys: occ_named_keys,
                        }
                    } else {
                        let type_args = node_occurrence::collect_type_args(self.kb, type_args_tid);
                        node_occurrence::BuildFrame::Apply {
                            span, functor: kb_functor, pos_count,
                            named_keys: occ_named_keys, type_args,
                        }
                    };
                    node_occurrence::build_frame(self.kb, frame, &mut self.expr_occ_results);
                }
            }
            LoadBuildFrame::DotApply { outer_parse_id, name_ref, pos_count, named_keys } => {
                // Result layout (drain_start..): receiver, positional args,
                // named args. Build the reflect `dot_apply(receiver, name,
                // args: List[ApplyArg])` — the same ApplyArg encoding the
                // apply path uses, so `materialize_from_handle` round-trips it.
                let total = 1 + pos_count + named_keys.len();
                let drain_start = results.len() - total;
                let receiver = results[drain_start];
                let mut arg_terms: SmallVec<[TermId; 4]> = SmallVec::with_capacity(pos_count + named_keys.len());
                for i in 0..pos_count {
                    let value = results[drain_start + 1 + i];
                    let none = build_none(self.kb);
                    arg_terms.push(self.mk_apply_arg(none, value));
                }
                for (i, &sym) in named_keys.iter().enumerate() {
                    let value = results[drain_start + 1 + pos_count + i];
                    let reinterned = self.reintern(sym);
                    let arg_name = self.kb.alloc(Term::Ref(reinterned));
                    let some_name = build_some(self.kb, arg_name);
                    arg_terms.push(self.mk_apply_arg(some_name, value));
                }
                results.truncate(drain_start);
                let args_list = build_list(self.kb, &arg_terms);
                let s = &self.expr_syms;
                let kb_id = self.kb.alloc(Term::Fn {
                    functor: s.dot_apply,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (s.k_receiver, receiver),
                        (s.k_name, name_ref),
                        (s.k_args, args_list),
                    ]),
                });
                self.create_occurrence(outer_parse_id, kb_id);
                results.push(kb_id);
                if self.occ_suppress == 0 {
                    let span = SourceSpan::from_span(
                        self.source_id, self.parsed.terms.span(outer_parse_id));
                    let name = if let Term::Ref(s) = self.kb.get_term(name_ref) {
                        *s
                    } else {
                        panic!("dot_apply name_ref is not a Term::Ref");
                    };
                    let occ_named_keys: Vec<Symbol> =
                        named_keys.iter().map(|s| self.reintern(*s)).collect();
                    node_occurrence::build_frame(
                        self.kb,
                        node_occurrence::BuildFrame::DotApply {
                            span, name, pos_count, named_keys: occ_named_keys,
                        },
                        &mut self.expr_occ_results,
                    );
                }
            }
        }
    }

    /// WI-271: lower the parse-side `[A = Int, B = String]` call
    /// bindings — read from the apply parse Term's `type_args`
    /// named arg pointing at a `Term::ParseAux(SortBindings(...))`
    /// node — into a cons-list of `type_arg(name: Option[Ref],
    /// value: Type)` entries the typer reads to seed its
    /// substitution. Returns `None` when the call has no explicit
    /// bindings.
    fn build_call_type_args(&mut self, parse_id: TermId) -> Option<TermId> {
        let bindings = self.read_parse_call_type_args(parse_id)?;
        if bindings.is_empty() {
            return None;
        }
        let entries: Vec<TermId> = bindings.iter().map(|b| {
            // The binding's `param` (e.g. "A" in `[A = Int]`) is a label
            // referring to the callee's type-param, NOT a value to look
            // up in the caller's scope. Intern as a bare symbol.
            let name_opt = match &b.param {
                Some(name) => {
                    let raw = join_segments(&self.parsed.symbols, &name.segments);
                    let sym = self.kb.intern(&raw);
                    let name_ref = self.kb.alloc(Term::Ref(sym));
                    build_some(self.kb, name_ref)
                }
                None => build_none(self.kb),
            };
            let value = self.type_expr_to_term(&b.bound);
            let s = &self.expr_syms;
            self.kb.alloc(Term::Fn {
                functor: s.type_arg,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[
                    (s.k_name, name_opt),
                    (s.k_value, value),
                ]),
            })
        }).collect();
        Some(build_list(self.kb, &entries))
    }

    /// WI-271: is the term at `id` a parse-only `Term::ParseAux`?
    /// Used by the loader's child-walkers to filter parse-aux children
    /// out of the generic visit/recurse paths — those children are
    /// consumed directly at the LetExpr / ApplyOrConstructor build
    /// sites via `read_parse_*` helpers.
    fn is_parse_aux(&self, id: TermId) -> bool {
        matches!(self.parsed.terms.get(id), Term::ParseAux(_))
    }

    /// WI-271: extract a parse-only `ParseAux` payload from a parent
    /// parse `Term::Fn`'s named arg. `key` is the unresolved parse-side
    /// name (e.g. `"type_name"`, `"type_args"`); `extract` projects the
    /// `ParseAux` enum to the expected inner shape. Returns `None`
    /// when the named arg is absent, points at a non-ParseAux, or its
    /// ParseAux variant doesn't match what `extract` accepts.
    fn read_parse_aux<T>(
        &self,
        parent_id: TermId,
        key: &str,
        extract: impl FnOnce(&crate::parse::ir::ParseAux) -> Option<T>,
    ) -> Option<T> {
        let named_args = match self.parsed.terms.get(parent_id) {
            Term::Fn { named_args, .. } => named_args,
            _ => return None,
        };
        let key_sym = self.parsed.symbols.lookup(key)?;
        let aux_tid = named_args.iter()
            .find(|(s, _)| *s == key_sym)
            .map(|(_, t)| *t)?;
        match self.parsed.terms.get(aux_tid) {
            Term::ParseAux(aux) => extract(aux.as_ref()),
            _ => None,
        }
    }

    /// WI-271: the `let pat : T = …` annotation child of a let_expr.
    fn read_parse_type_annotation(&self, let_parse_id: TermId) -> Option<crate::parse::ir::TypeExpr> {
        self.read_parse_aux(let_parse_id, "type_name", |aux| match aux {
            crate::parse::ir::ParseAux::TypeExpr(ty) => Some(ty.clone()),
            _ => None,
        })
    }

    /// WI-271: the `op[A = Int, B = String](…)` bindings child of an apply.
    fn read_parse_call_type_args(&self, apply_parse_id: TermId) -> Option<Vec<crate::parse::ir::SortBinding>> {
        self.read_parse_aux(apply_parse_id, "type_args", |aux| match aux {
            crate::parse::ir::ParseAux::SortBindings(bindings) => Some(bindings.clone()),
            _ => None,
        })
    }

    /// Build an `ApplyArg(name: …, value: …)` term using cached syms.
    fn mk_apply_arg(&mut self, name: TermId, value: TermId) -> TermId {
        let s = &self.expr_syms;
        self.kb.alloc(Term::Fn {
            functor: s.apply_arg,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(s.k_name, name), (s.k_value, value)]),
        })
    }

    /// var_ref: Term::Ident(sym) → var_ref(name: Ref(sym))
    /// Uses reintern (plain) — lexical variables are NOT KB symbol references.
    /// WI-246: build the `NodeOccurrence` for one rule-body goal atom — the
    /// rule's resolver/typer goal source — NATIVELY from the parse IR, so a
    /// loaded rule body no longer round-trips through the lossy term→occurrence
    /// `materialize_from_handle` re-inference.
    ///
    /// Generic applications and leaves are built directly: a non-entity,
    /// non-reflect `Term::Fn` becomes `Expr::Apply { functor, pos, named }`
    /// (matching `materialize`'s `UnknownFn` build — a goal atom is just an
    /// application; `occ_head` reads it as a `Functor`), and `Const`/`Var`/
    /// `Ref`/`Ident`/`Bottom` map to their `Expr` leaves. Var identity is shared
    /// with the term body via `self.var_map` (the body-term `convert_term` runs
    /// first, so every body var is already mapped). Source spans are taken from
    /// the parse term — info the term-derived path lost (rule-body terms get no
    /// `term_spans` entry, so `materialize` gave them `empty_span`).
    ///
    /// Falls back to `materialize(convert_term(parse_id))` for:
    /// - entity functors — `convert_term` expands partial fields with fresh vars
    ///   (load.rs); the memoized `convert_term` returns the SAME expanded term so
    ///   the occurrence shares those vars (a native rebuild would mint different
    ///   ones); and
    /// - reflect / control-flow forms (`is_reflect_form_functor`) — whose
    ///   occurrence shape isn't a plain `Apply`.
    /// Both are reachable as nested args too (e.g. `member(?x, cons(..))`); the
    /// memoized `convert_term` keeps every subterm consistent. Narrowing these
    /// fallbacks (native entities / structural reflect patterns, fixing the
    /// `apply(args: ?V)` collapse) is later work.
    fn build_body_atom_occurrence(&mut self, parse_id: TermId) -> Rc<NodeOccurrence> {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        let span = SourceSpan::from_span(self.source_id, self.parsed.terms.span(parse_id));
        let expr = match parse_term {
            Term::Const(lit) => Expr::Const(lit),
            Term::Var(Var::Global(vid)) => {
                // WI-246: this walk IS the rule body's var-identity source (the
                // term body is gone). Map the parse var to its KB var, minting a
                // fresh one on the first occurrence — mirroring `convert_term`'s
                // `Var::Global` arm — and sharing it across body atoms and the
                // (already-converted) head via the same `var_map`. The De Bruijn
                // closing then collects these from the occurrence body
                // (`collect_occurrence_global_vars_ordered`).
                let kb_vid = if let Some(&mapped) = self.var_map.get(&vid.raw()) {
                    mapped
                } else {
                    let name = self.reintern(vid.name());
                    let new_vid = self.kb.fresh_var(name);
                    self.var_map.insert(vid.raw(), new_vid);
                    new_vid
                };
                // Mirror `convert_term`'s tail (load.rs ~3989): a body variable
                // can carry inline descriptions (`?x {< … >}?`); emit them as
                // Description facts targeting the Global var term, as the dropped
                // term-body `convert_term` walk did. (Entity / reflect-form atoms
                // still emit via the `convert_term` call in the Fn arm below; this
                // covers vars in generic predicate atoms.)
                if let Some(desc_texts) = self.parsed.terms.descriptions.get(&parse_id) {
                    let desc_texts = desc_texts.clone();
                    let target = self.kb.alloc(Term::Var(Var::Global(kb_vid)));
                    for desc_text in &desc_texts {
                        self.emit_desc_fact(target, desc_text, self.current_scope);
                    }
                }
                Expr::Var(Var::Global(kb_vid))
            }
            Term::Var(Var::DeBruijn(n)) => Expr::Var(Var::DeBruijn(n)),
            Term::Var(Var::Rigid(_)) => unreachable!("Var::Rigid in stored parse term"),
            Term::Ref(sym) => Expr::Ref(self.remap_symbol_strict(sym)),
            Term::Ident(sym) => {
                let new_sym = self.remap_symbol(sym);
                // Promote to Ref if the symbol resolved to a defined name —
                // mirrors `convert_term`'s Ident arm + `materialize`'s leaf map.
                if self.kb.symbols.is_resolved(new_sym) {
                    Expr::Ref(new_sym)
                } else {
                    Expr::Ident(new_sym)
                }
            }
            Term::Bottom => Expr::Bottom,
            Term::ParseAux(_) => unreachable!(
                "Term::ParseAux reached build_body_atom_occurrence — a body atom \
                 (or its non-ParseAux child) is never a parse-only payload",
            ),
            Term::Fn { functor, pos_args, named_args } => {
                let new_functor = self.remap_symbol(functor);
                if self.kb.entity_field_names(new_functor).is_some()
                    || node_occurrence::is_reflect_form_functor(self.kb, new_functor)
                {
                    let kb_term = self.convert_term(parse_id); // memoized hit
                    return node_occurrence::materialize_from_handle(self.kb, kb_term);
                }
                // Native generic application. Positional in source order; named
                // ParseAux-filtered (type_args / type_name are read elsewhere)
                // with `reintern`ed keys in source order — matching `convert_term`
                // (no entity-field sort for non-entity functors) and thus the
                // `UnknownFn` materialization.
                let mut pos: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(pos_args.len());
                for &pid in pos_args.iter() {
                    pos.push(self.build_body_atom_occurrence(pid));
                }
                let mut named: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
                for &(sym, pid) in named_args.iter() {
                    if self.is_parse_aux(pid) {
                        continue;
                    }
                    let key = self.reintern(sym);
                    let child = self.build_body_atom_occurrence(pid);
                    named.push((key, child));
                }
                Expr::Apply { functor: new_functor, pos_args: pos, named_args: named, type_args: Vec::new() }
            }
        };
        NodeOccurrence::new_expr(expr, span, None)
    }

    fn load_var_ref(&mut self, parse_id: TermId) -> TermId {
        let parse_term = self.parsed.terms.get(parse_id).clone();
        let name_ref = if let Term::Ident(sym) = parse_term {
            let kb_sym = self.remap_symbol(sym);
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
                super::term::Literal::Handle(_, _) => {
                    unreachable!("Handle literals cannot appear in source expressions")
                }
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

    /// Find the `Var` target of `SortAlias(<sym>, Var)`. Matches by
    /// exact `Symbol` identity first (one pass), then by short name as
    /// a fallback (second pass). The two-pass order matters: short-name
    /// resolution is ambiguous when many sorts share a type-param name
    /// (`sort T = ?` in List, Option, Stream …), and an exact match
    /// elsewhere in the table must take precedence over an earlier
    /// short-name hit.
    fn find_sort_alias_var(&self, sym: Symbol) -> Option<TermId> {
        let alias_sym = self.kb.try_resolve_symbol("SortAlias")?;
        let sort_name = self.kb.resolve_sym(sym);
        let scan = |matches: &dyn Fn(Symbol, &str) -> bool| -> Option<TermId> {
            for rid in self.kb.by_functor(alias_sym) {
                if !self.kb.is_fact(rid) { continue; }
                let head = self.kb.rule_head(rid);
                let Term::Fn { pos_args, .. } = self.kb.get_term(head) else { continue };
                if pos_args.len() < 2 { continue; }
                let Term::Fn { functor, .. } = self.kb.get_term(pos_args[0]) else { continue };
                if !matches(*functor, self.kb.resolve_sym(*functor)) { continue; }
                if matches!(self.kb.get_term(pos_args[1]), Term::Var(_)) {
                    return Some(pos_args[1]);
                }
            }
            None
        };
        scan(&|f, _| f == sym).or_else(|| scan(&|_, n| n == sort_name))
    }

    fn name_to_sort_term(&mut self, name: &Name) -> TermId {
        let functor = self.remap_name(name);
        self.kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    /// Convert a TypeExpr to a Type entity term in the KB.
    /// Produces sort_ref, parameterized, arrow, type_var, named_tuple terms.
    fn type_expr_to_term(&mut self, ty: &TypeExpr) -> TermId {
        match ty {
            TypeExpr::Simple(name) => {
                let sort_sym = self.remap_name(name);
                let short_name = self.kb.resolve_sym(sort_sym).to_owned();
                // If this symbol is a type parameter, use a Var directly.
                // All references to the same type param within a scope share the same Var.
                if self.kb.symbols.is_type_param(self.current_scope.raw(), &short_name) {
                    let key = (self.current_scope.raw(), short_name.clone());
                    if let Some(&cached) = self.type_param_vars.get(&key) {
                        return cached;
                    }
                    // Try SortAlias first (if abstract sort already loaded)
                    let var_tid = if let Some(alias_var) = self.find_sort_alias_var(sort_sym) {
                        alias_var
                    } else {
                        let var_sym = self.kb.intern(&short_name);
                        let vid = self.kb.fresh_var(var_sym);
                        self.kb.alloc(Term::Var(Var::Global(vid)))
                    };
                    self.type_param_vars.insert(key, var_tid);
                    return var_tid;
                }
                // WI-302/WI-313: a name resolving to a VALUE in a type slot is
                // value-in-type — `Modify[c]`, `Modify[result]`, `Modify[kb]`
                // (kb a zero-arg accessor). Lower it to `denoted(value: Ref(sym))`
                // so it reads as a value indexing the type, not a `sort_ref`. The
                // faithful occurrence form lands with the effects→occurrences
                // change; the term-form `Ref` is adequate for the current
                // `Vec<TermId>` effect representation.
                //
                // The split is VALUE vs TYPE:
                //   - Param / Field        → a value binding      → denoted  (WI-302)
                //   - Operation            → value-producing       → denoted
                //     (e.g. reflect's `kb()` ambient-KB accessor; an operation
                //     reference in a type slot denotes the value it yields).
                //   - Entity               → a TYPE: a standalone entity is sugar
                //     for a single-constructor sort (kernel-language §6.3), so its
                //     bare name names that sort → `sort_ref`. (WI-313: entities are
                //     NOT value-in-type; the motivating `kb` is properly an op.)
                //   - Sort / Namespace     → a type                → `sort_ref`
                let is_value = matches!(
                    self.kb.symbols.get(sort_sym),
                    crate::intern::SymbolDef::Resolved {
                        kind: SymbolKind::Param | SymbolKind::Field | SymbolKind::Operation, ..
                    }
                );
                if is_value {
                    let value = self.kb.alloc(Term::Ref(sort_sym));
                    return self.kb.make_denoted(value);
                }
                self.kb.make_sort_ref(sort_sym)
            }
            TypeExpr::Parameterized { name, bindings } => {
                let sort_sym = self.remap_name(name);
                let base = self.kb.make_sort_ref(sort_sym);
                // Look up the sort's declared type-parameter names in
                // source order so positional bindings (e.g. `Map[String,
                // Int]` for `sort Map { sort K = ?; sort V = ? }`) can
                // map index 0 → "K", index 1 → "V".
                let declared_params = self.kb.type_params_of_sort(sort_sym);
                let mut type_bindings: Vec<(Symbol, TermId)> = Vec::new();
                let mut positional_index: usize = 0;
                for b in bindings {
                    let bound_term = self.type_expr_to_term(&b.bound);
                    let param_sym = if let Some(p) = &b.param {
                        // Named binding wins over positional cursor.
                        Some(self.reintern(p.last()))
                    } else if positional_index < declared_params.len() {
                        let param_name = &declared_params[positional_index];
                        positional_index += 1;
                        Some(self.kb.intern(param_name))
                    } else {
                        // More positional bindings than declared params
                        // — silently drop. The typer will surface this
                        // via parameter-mismatch errors when the sort
                        // is consumed.
                        None
                    };
                    if let Some(sym) = param_sym {
                        type_bindings.push((sym, bound_term));
                    }
                }
                self.kb.make_parameterized_type(base, &type_bindings)
            }
            TypeExpr::Variable { term_id, descriptions } => {
                let kb_id = self.convert_term(*term_id);
                for desc_text in descriptions {
                    self.emit_desc_fact(kb_id, desc_text, self.current_scope);
                }
                // Keep as Term::Var — entity facts need variables for unification.
                // The typing pass creates type_var() terms when needed for inference.
                kb_id
            }
            TypeExpr::Tuple(fields) => {
                let type_fields: Vec<(Symbol, TermId)> = fields.iter().map(|(sym, ty)| {
                    let key = self.reintern(*sym);
                    let val = self.type_expr_to_term(ty);
                    (key, val)
                }).collect();
                self.kb.make_named_tuple_type(&type_fields)
            }
            TypeExpr::Arrow { params, return_type, effects } => {
                // For single-param arrows, use param directly.
                // For multi-param, build a named_tuple of param types — keyed
                // by the param's declared name when present (spec §5.4), else
                // the 1-based positional name `_1`, `_2`, … (spec §4.5,
                // matching plain tuples, see `convert.rs` positional naming).
                let param_type = if params.len() == 1 {
                    self.type_expr_to_term(&params[0].1)
                } else {
                    let param_fields: Vec<(Symbol, TermId)> = params.iter().enumerate().map(|(i, (name, p))| {
                        // `name` is a parse-IR symbol; resolve to text and
                        // re-intern into the KB symbol table.
                        let key = match name {
                            Some(sym) => {
                                let nm = self.parsed.symbols.name(*sym).to_owned();
                                self.kb.intern(&nm)
                            }
                            None => self.kb.intern(&format!("_{}", i + 1)),
                        };
                        let val = self.type_expr_to_term(p);
                        (key, val)
                    }).collect();
                    self.kb.make_named_tuple_type(&param_fields)
                };
                let result_type = self.type_expr_to_term(return_type);
                let effect_terms: Vec<TermId> = effects.iter()
                    .map(|e| self.type_expr_to_term(e))
                    .collect();
                self.kb.make_arrow_type(param_type, result_type, &effect_terms)
            }
            TypeExpr::Denoted(t) => {
                // WI-302: value-in-type. Lower the value to its term-form via the
                // non-re-entrant `convert_term`. NOT `convert_expr_term`: this arm
                // runs *inside* a `convert_expr_term` walk when a value-in-type
                // appears as a body call type-arg (`g[3](y)`, build_call_type_args)
                // or a `let : T` annotation, and `convert_expr_term` is not
                // re-entrant — it clears the occurrence stacks at entry. The
                // faithful occurrence form lands with the effects→occurrences change.
                let value_term = self.convert_term(*t);
                self.kb.make_denoted(value_term)
            }
            // WI-327: `-E` lowers to the `absent(E)` EffectExpression atom.
            // Only meaningful in effects positions — `build_canonical_effects_
            // rows` recognizes the wrapper and threads it through the
            // canonical row form. In any other position the canonicalizer
            // never sees the atom, so the wrapped term behaves like an
            // opaque tag in the diagnostics path; the typer treats it as
            // a non-label entry.
            TypeExpr::EffectAbsent(inner) => {
                let inner_term = self.type_expr_to_term(inner);
                self.kb.make_effect_expression_absent(inner_term)
            }
        }
    }

    /// WI-342 — lower a `TypeExpr` to a carrier-agnostic [`Value`], honoring the
    /// carrier rule: a type whose structure transitively contains a `denoted`
    /// (`Modify[c]`, a value-in-type field) is minted as a `Value::Node`
    /// occurrence; a fully-ground type rides as `Value::Term` (the hash-consed
    /// form). The dual-carrier peer of [`Self::type_expr_to_term`]. Used for
    /// operation effect labels (E2) and entity field types; the remaining
    /// `TermId`-only loader positions (params/return/let) flip incrementally as
    /// their storage gains a `Value` carrier.
    fn type_expr_to_value(&mut self, ty: &TypeExpr) -> crate::eval::value::Value {
        let span = self.type_expr_span(ty);
        let owner = self.current_owner;
        match self.type_expr_to_child(ty, span, owner) {
            node_occurrence::TypeChild::Ground(t) => crate::eval::value::Value::Term(t),
            node_occurrence::TypeChild::Node(n) => crate::eval::value::Value::Node(n),
        }
    }

    /// Span for a lowered type's occurrence — its leading `Name` span when
    /// available, else a synthetic span on the current source. Occurrence spans
    /// here feed diagnostics only.
    fn type_expr_span(&self, ty: &TypeExpr) -> SourceSpan {
        match ty {
            TypeExpr::Simple(n) | TypeExpr::Parameterized { name: n, .. } => {
                SourceSpan::from_span(self.source_id, n.span)
            }
            _ => SourceSpan::new(self.source_id, 0, 0),
        }
    }

    /// Dual-carrier peer of the relevant [`Self::type_expr_to_term`] arms,
    /// returning a [`node_occurrence::TypeChild`]: `Ground(TermId)` when the
    /// sub-tree is fully ground (reusing the hash-consed builder verbatim), or
    /// `Node(Rc<NodeOccurrence>)` when it carries a `denoted`. The carrier of a
    /// `parameterized` follows its bindings — any `Node` binding poisons the
    /// whole type to `Node`. Only the value-in-type shapes are Node-aware
    /// (`Simple`-as-value, `Parameterized`); every other shape (arrow, tuple, …)
    /// stays ground via `type_expr_to_term` (no denoted ⇒ no carrier obligation).
    fn type_expr_to_child(
        &mut self,
        ty: &TypeExpr,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> node_occurrence::TypeChild {
        match ty {
            TypeExpr::Simple(name) => {
                let sort_sym = self.remap_name(name);
                let short_name = self.kb.resolve_sym(sort_sym).to_owned();
                // A type-param name is a ground logic Var — defer to the
                // hash-consed builder (no denoted).
                if self.kb.symbols.is_type_param(self.current_scope.raw(), &short_name) {
                    return node_occurrence::TypeChild::Ground(self.type_expr_to_term(ty));
                }
                // WI-302/WI-313: a name resolving to a VALUE in a type slot is
                // value-in-type (`Modify[c]`) — the `denoted` source. Mint it as
                // a `Value::Node` occurrence rather than the ground `make_denoted`.
                let is_value = matches!(
                    self.kb.symbols.get(sort_sym),
                    SymbolDef::Resolved {
                        kind: SymbolKind::Param | SymbolKind::Field | SymbolKind::Operation, ..
                    }
                );
                if is_value {
                    node_occurrence::TypeChild::Node(
                        self.kb.make_denoted_occ_ref(sort_sym, span, owner),
                    )
                } else {
                    node_occurrence::TypeChild::Ground(self.kb.make_sort_ref(sort_sym))
                }
            }
            TypeExpr::Parameterized { name, bindings } => {
                let sort_sym = self.remap_name(name);
                let base_term = self.kb.make_sort_ref(sort_sym);
                // Same positional→declared-param-name mapping as the
                // `type_expr_to_term` Parameterized arm, so a label's binding
                // symbols match across the two builders (the display-name
                // comparison in the op-boundary check relies on this).
                let declared_params = self.kb.type_params_of_sort(sort_sym);
                let mut child_bindings: Vec<(Symbol, node_occurrence::TypeChild)> = Vec::new();
                let mut positional_index: usize = 0;
                let mut any_node = false;
                for b in bindings {
                    let bound_child = self.type_expr_to_child(&b.bound, span, owner);
                    if matches!(bound_child, node_occurrence::TypeChild::Node(_)) {
                        any_node = true;
                    }
                    let param_sym = if let Some(p) = &b.param {
                        Some(self.reintern(p.last()))
                    } else if positional_index < declared_params.len() {
                        let param_name = declared_params[positional_index].clone();
                        positional_index += 1;
                        Some(self.kb.intern(&param_name))
                    } else {
                        None
                    };
                    if let Some(sym) = param_sym {
                        child_bindings.push((sym, bound_child));
                    }
                }
                if any_node {
                    node_occurrence::TypeChild::Node(self.kb.make_parameterized_occ(
                        node_occurrence::TypeChild::Ground(base_term),
                        child_bindings,
                        span,
                        owner,
                    ))
                } else {
                    // No denoted binding ⇒ the ground hash-consed form is
                    // faithful; rebuild it via the canonical builder.
                    node_occurrence::TypeChild::Ground(self.type_expr_to_term(ty))
                }
            }
            // No denoted obligation for any other label shape (sort_ref,
            // arrow, tuple, bare denoted, `-E`): build the hash-consed form.
            // A bare top-level `denoted` effect label is not minted by any
            // current producer; if one appears it rides as a ground `Term`
            // denoted (the pre-E2 behavior), which the deferred non-effect
            // loader-flip slice will Node-ify.
            _ => node_occurrence::TypeChild::Ground(self.type_expr_to_term(ty)),
        }
    }

    /// Convert a TypeExpr to a sort instantiation term (SortView) for `requires` clauses.
    /// Unlike type_expr_to_term, this preserves operation bindings alongside type bindings.
    fn sort_inst_to_term(&mut self, ty: &TypeExpr) -> TermId {
        match ty {
            TypeExpr::Simple(name) => self.name_to_sort_term(name),
            TypeExpr::Parameterized { name, bindings } => {
                let name_term = self.name_to_sort_term(name);
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::from_elem(name_term, 1);
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for b in bindings {
                    let bound_term = self.sort_inst_to_term(&b.bound);
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
            _ => self.type_expr_to_term(ty),
        }
    }

    /// Load items (top-level or within a domain), tracking scope.
    fn load_items(&mut self, items: &[Item], domain: Option<TermId>) {
        let prev_scope = self.current_scope;
        let domain = domain.unwrap_or_else(|| self.kb.make_name_term("_global"));
        self.current_scope = domain;

        // WI-233: per-item-kind timing/count, gated by
        // ANTHILL_ITEM_TIMING=1. Aggregated across all `load_items`
        // invocations into thread-local counters; printed by the
        // outermost caller at end-of-pass.
        let timing = std::env::var("ANTHILL_ITEM_TIMING").map(|v| v == "1").unwrap_or(false);

        for item in items {
            let t0 = if timing { Some(std::time::Instant::now()) } else { None };
            let kind = match item {
                Item::Namespace(n) => { self.load_namespace(n); "Namespace" }
                Item::AbstractSort(s) => { self.load_abstract_sort(s, domain); "AbstractSort" }
                Item::SortWithBody(s) => { self.load_sort_with_body(s, domain); "SortWithBody" }
                Item::Rule(r) => { self.load_rule(r, domain); "Rule" }
                Item::Operation(o) => { self.load_operation(o, domain); "Operation" }
                Item::RequiresDecl(r) => { self.load_requires_decl(r, domain); "RequiresDecl" }
                Item::Entity(e) => { self.load_entity(e, domain); "Entity" }
                Item::Fact(f) => { self.load_fact(f, domain); "Fact" }
                Item::Constraint(c) => { self.load_constraint(c, domain); "Constraint" }
                Item::OperationBlock(ob) => {
                    for op in &ob.entries {
                        self.load_operation(op, domain);
                    }
                    "OperationBlock"
                }
                Item::RuleBlock(rb) => {
                    for rule in &rb.entries {
                        self.load_rule(rule, domain);
                    }
                    "RuleBlock"
                }
                Item::Describe(d) => { self.load_describe(d, domain); "Describe" }
                Item::Proof(p) => { self.load_proof(p, domain); "Proof" }
                Item::ProvidesClause(pc) => { self.load_provides_clause(pc, domain); "ProvidesClause" }
                Item::ProvidesBlock(pb) => { self.load_provides_block(pb, domain); "ProvidesBlock" }
            };
            if let Some(t0) = t0 {
                let dt = t0.elapsed();
                ITEM_TIMINGS.with(|m| {
                    let mut m = m.borrow_mut();
                    let entry = m.entry(kind).or_insert((0u32, std::time::Duration::ZERO));
                    entry.0 += 1;
                    entry.1 += dt;
                });
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

        // Skip re-registration if this AbstractSort has already been
        // loaded — load_sort_with_body's pre-pass calls us early so
        // SortAlias is in place before entity FieldInfo builds; the
        // later load_items pass would otherwise allocate a *second*
        // SortAlias with a fresh target Var, leaving each type-param
        // backed by two distinct Vars (`find_sort_alias_var` then
        // returns the first by `by_functor` order, which may differ
        // from the Var the entity field already captured).
        let alias_sym = self.kb.resolve_symbol("SortAlias");
        for rid in self.kb.by_functor(alias_sym) {
            if !self.kb.is_fact(rid) { continue; }
            let head = self.kb.rule_head(rid);
            if let Term::Fn { pos_args, .. } = self.kb.get_term(head) {
                if pos_args.len() >= 2 && pos_args[0] == sort_term {
                    return;
                }
            }
        }

        self.kb.register_sort(sort_term, SortKind::Sort);

        // Both variable (sort T = ?Element) and alias (sort T = Int) emit SortAlias.
        // For variables, use convert_term directly to avoid double-emitting descriptions
        // (AbstractSort.descriptions already covers them via the loop below).
        let target_term = match &s.definition {
            TypeExpr::Variable { term_id, .. } => self.convert_term(*term_id),
            _ => self.type_expr_to_term(&s.definition),
        };
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
        self.defined_sorts.push(sort_term);
        let sort_sort = self.kb.make_name_term("Sort");

        let has_entities = s.items.iter().any(|item| matches!(item, Item::Entity(_)));
        let (sort_kind, kind_str) = match s.kind {
            SortDeclKind::Enum => (SortKind::Enum, "enum"),
            SortDeclKind::Sort => (SortKind::Sort, "sort"),
        };
        self.kb.register_sort(sort_term, sort_kind);

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

        // Pre-load nested `sort X = ?` declarations so their SortAlias
        // is in place before entity FieldInfo build calls
        // `type_expr_to_term` on field types that reference them. Without
        // this, `entity foo(x: T)` runs before `sort T = ?` in source
        // order, hits `type_expr_to_term`'s fallback (no SortAlias yet),
        // and allocates a fresh `Var(name="T")` — a different Var than
        // the SortAlias's `Var(name="_")` registered later. The two Vars
        // never unify, so pattern substitution misses and the typer
        // sees `head: Var(...)` where it should see `head: String`.
        // `load_abstract_sort` dedupes on already-asserted SortAlias,
        // so `load_items` below safely re-encounters these and no-ops.
        // Pass `sort_term` (the enclosing sort's own domain) so the
        // SortAlias fact lives in the same domain the second pass
        // would have used.
        for item in &s.items {
            if let Item::AbstractSort(abs) = item {
                self.load_abstract_sort(abs, sort_term);
            }
        }

        // Register direct entity children (entity → parent sort)
        for item in &s.items {
            if let Item::Entity(e) = item {
                let ctor_term = self.name_to_sort_term(&e.name);
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
                    let req_term = self.sort_inst_to_term(&r.type_expr);
                    req_terms.push(req_term);
                }
                _ => {}
            }
        }

        self.emit_sort_info(sort_functor, has_entities, kind_str,
            &ctor_refs, &op_refs, &param_refs, &req_terms,
            sort_sort, parent_domain);

        // Auto-emit the induction principle for any sort with constructors,
        // including parameterised ones. The body uses positional fresh vars
        // (?head, ?tail, ...) in value position; it never references the
        // type parameter ?T, so polymorphism does not affect the rule
        // shape. (An earlier exclusion claimed cpp-gen would collide, but
        // cpp-gen iterates rules only via specific functor queries —
        // Implementation, SortInfo, OperationInfo, etc. — and never
        // enumerates `<Sort>.induction` rules.)
        if has_entities {
            self.emit_induction_rule(s, sort_term, sort_functor, parent_domain);
        }

        self.current_scope = prev_scope;
    }

    /// Emit `<Sort>.induction(?P) :- ho_apply(?P, ctor_1(...)), ...` —
    /// case analysis with one body goal per constructor. For ctors
    /// with recursive fields (a field whose type is the sort itself),
    /// the goal is wrapped in `forall_impl` carrying the inductive
    /// hypothesis: `(forall(?f1, ..., ?fN), ho_apply(?P, ?fr) -: ho_apply(?P, ctor(...)))`
    /// where `?fr` is each recursive-position binder. The IH form
    /// is consumed at proof time by the SLD nested-impl resolver
    /// (WI-108) and the Z3 induction tactic (WI-101).
    fn emit_induction_rule(
        &mut self,
        s: &SortWithBody,
        sort_term: TermId,
        sort_functor: Symbol,
        parent_domain: TermId,
    ) {
        let entities: Vec<&Entity> = s.items.iter()
            .filter_map(|i| if let Item::Entity(e) = i { Some(e) } else { None })
            .collect();
        if entities.is_empty() { return; }

        let p_sym = self.kb.intern("P");
        let p_var = self.kb.fresh_var(p_sym);
        let p_term = self.kb.alloc(Term::Var(Var::Global(p_var)));

        let sort_name = match self.kb.symbols.get(sort_functor) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        let induction_name = format!("{sort_name}.induction");
        // Scope the `induction` short-name to the SORT (not parent_domain).
        // Top-level sorts otherwise all share `_global`, where the first
        // call registers `induction → Symbol(N)` and subsequent calls
        // reuse that without inserting their qualified name into
        // `by_qualified_name` — making each subsequent <Sort>.induction
        // unreachable by qualified-name lookup.
        let induction_sym = if let Some(&existing) = self.kb.symbols.by_qualified_name.get(&induction_name) {
            existing
        } else {
            self.kb.symbols.define(
                "induction", &induction_name, SymbolKind::Goal, sort_term.raw(),
            )
        };

        let head = self.kb.alloc(Term::Fn {
            functor: induction_sym,
            pos_args: SmallVec::from_slice(&[p_term]),
            named_args: SmallVec::new(),
        });

        // Use the resolved qualified-name symbol so the builtin tag
        // (BuiltinTag::HoApply registered against `anthill.reflect.Expr.ho_apply`)
        // recognises auto-generated induction rule bodies. Falling back
        // to bare intern would create an unresolved symbol disconnected
        // from the builtin tag.
        let ho_apply_sym = self.kb.symbols
            .by_qualified_name
            .get("anthill.reflect.Expr.ho_apply")
            .copied()
            .unwrap_or_else(|| self.kb.intern("ho_apply"));
        let tuple_sym = self.kb.intern("tuple");
        let forall_impl_sym = self.kb.intern("forall_impl");

        let mut body: Vec<TermId> = Vec::new();
        for e in entities {
            let ctor_sym = self.remap_name(&e.name);
            if e.fields.is_empty() {
                let ctor_term = self.kb.alloc(Term::Ref(ctor_sym));
                body.push(self.alloc_pos_fn(ho_apply_sym, &[p_term, ctor_term]));
                continue;
            }

            // Build binder vars per field, classifying recursive positions.
            let mut field_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            let mut binder_vars: SmallVec<[TermId; 4]> = SmallVec::new();
            let mut recursive_vars: SmallVec<[TermId; 2]> = SmallVec::new();
            for f in &e.fields {
                let f_name_str = self.parsed.symbols.name(f.name).to_owned();
                let f_sym = self.kb.intern(&f_name_str);
                let var = self.kb.fresh_var(f_sym);
                let var_term = self.kb.alloc(Term::Var(Var::Global(var)));
                field_args.push((f_sym, var_term));
                binder_vars.push(var_term);
                if self.field_is_recursive(&f.ty, sort_functor) {
                    recursive_vars.push(var_term);
                }
            }

            let ctor_term = self.kb.alloc(Term::Fn {
                functor: ctor_sym,
                pos_args: SmallVec::new(),
                named_args: field_args,
            });
            let consequent_goal = self.alloc_pos_fn(ho_apply_sym, &[p_term, ctor_term]);

            if recursive_vars.is_empty() {
                body.push(consequent_goal);
                continue;
            }

            // Inductive case: wrap in forall_impl(binders, ihs, [consequent]).
            let ihs: Vec<TermId> = recursive_vars.iter()
                .map(|&rv| self.alloc_pos_fn(ho_apply_sym, &[p_term, rv]))
                .collect();
            let binders_tuple = self.alloc_pos_fn(tuple_sym, &binder_vars);
            let ihs_tuple = self.alloc_pos_fn(tuple_sym, &ihs);
            let consequent_tuple = self.alloc_pos_fn(tuple_sym, &[consequent_goal]);
            body.push(self.alloc_pos_fn(
                forall_impl_sym,
                &[binders_tuple, ihs_tuple, consequent_tuple],
            ));
        }

        let rule_sort = self.kb.make_name_term("Rule");
        self.kb.assert_rule_debruijn(head, body, rule_sort, parent_domain, None);
    }

    /// True if `ty` is a `Simple` type whose remapped symbol equals the
    /// containing sort. Parameterised self-references aren't reached here
    /// because parameterised sorts skip induction emission upstream.
    fn field_is_recursive(&mut self, ty: &TypeExpr, sort_functor: Symbol) -> bool {
        match ty {
            TypeExpr::Simple(n) => self.remap_name(n) == sort_functor,
            _ => false,
        }
    }

    /// Allocate `Term::Fn { functor, pos_args, named_args: empty }`.
    fn alloc_pos_fn(&mut self, functor: Symbol, pos_args: &[TermId]) -> TermId {
        self.kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_slice(pos_args),
            named_args: SmallVec::new(),
        })
    }

    /// Emit a SortInfo fact with the given components.
    fn emit_sort_info(
        &mut self,
        sort_functor: Symbol,
        has_entities: bool,
        kind_str: &str,
        ctor_refs: &[TermId],
        op_refs: &[TermId],
        param_refs: &[TermId],
        req_terms: &[TermId],
        sort_sort: TermId,
        parent_domain: TermId,
    ) {
        let sort_info_sym = self.kb.resolve_symbol("anthill.reflect.SortInfo");
        let name_sym = self.kb.intern("name");
        let kind_field_sym = self.kb.intern("kind");
        let definition_sym = self.kb.intern("definition");
        let constructors_sym = self.kb.intern("constructors");
        let operations_sym = self.kb.intern("operations");
        let parameters_sym = self.kb.intern("parameters");
        let requires_sym = self.kb.intern("requires");

        let field_order = vec![
            name_sym, kind_field_sym, definition_sym, constructors_sym,
            operations_sym, parameters_sym, requires_sym,
        ];
        self.kb.register_entity_fields(sort_info_sym, field_order.clone());

        let name_ref = self.kb.alloc(Term::Ref(sort_functor));
        let kind_sym = self.kb.intern(kind_str);
        let kind_term = self.kb.alloc(Term::Ident(kind_sym));

        let definition_term = if has_entities {
            self.kb.make_name_term_from_sym(sort_functor)
        } else {
            let anon_sym = self.kb.intern("?");
            let vid = self.kb.fresh_var(anon_sym);
            self.kb.alloc(Term::Var(Var::Global(vid)))
        };

        let ctors_list = build_list(self.kb, ctor_refs);
        let ops_list = build_list(self.kb, op_refs);
        let params_list = build_list(self.kb, param_refs);
        let requires_list = build_list(self.kb, req_terms);

        // Sort by declared field-list order so rule-body partial-named-arg
        // queries (which use the same order via convert_term) unify against
        // these facts. Sorting by Symbol::index() looks canonical but isn't —
        // the field names get interned in arbitrary order, so the index
        // sort silently diverges from the convert_term-side sort.
        let mut si_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
            (constructors_sym, ctors_list),
            (definition_sym, definition_term),
            (kind_field_sym, kind_term),
            (name_sym, name_ref),
            (operations_sym, ops_list),
            (parameters_sym, params_list),
            (requires_sym, requires_list),
        ]);
        let order: HashMap<Symbol, usize> = field_order.iter().enumerate().map(|(i, &s)| (s, i)).collect();
        si_args.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
        let fact_term = self.kb.alloc(Term::Fn {
            functor: sort_info_sym,
            pos_args: SmallVec::new(),
            named_args: si_args,
        });
        self.kb.assert_fact(fact_term, sort_sort, parent_domain, None);
    }

    fn load_entity(&mut self, e: &Entity, domain: TermId) {
        let entity_sort = self.kb.make_name_term("Entity");
        let functor = self.remap_name(&e.name);

        // WI-342: lower each field type ONCE, carrier-agnostically — a value-in-
        // type field (`Modify[c]`-shaped / dependent) is carried as `Value::Node`,
        // a ground field type as `Value::Term`. The reflect `Entity` fact needs
        // the hash-consed `TermId` form, derived below via `as_term` (entity field
        // types are ground today — no value-in-type field — so this never `None`s;
        // a future denoted field would re-ground here). Lowering once avoids
        // double-firing per-field side effects like `emit_desc_fact` (a described
        // type-var field type).
        let field_types: Vec<(Symbol, crate::eval::value::Value)> = e.fields
            .iter()
            .map(|f| (self.reintern(f.name), self.type_expr_to_value(&f.ty)))
            .collect();
        let named_args: SmallVec<[(Symbol, TermId); 2]> = field_types
            .iter()
            .map(|(s, v)| {
                (*s, v.as_term().expect("entity field type is ground (no value-in-type field)"))
            })
            .collect();

        // Register entity field names for partial named-arg expansion.
        // Register under both the qualified symbol (from remap_name) and
        // the short name, so that sugar-generated facts (which use unqualified
        // functor names like "WorkItem") can also look up entity fields.
        let field_names: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
        self.kb.register_entity_fields(functor, field_names.clone());
        self.kb.register_entity_field_types(functor, field_types.clone());
        let short_name = if e.name.segments.len() == 1 {
            self.parsed.symbols.name(e.name.segments[0]).to_owned()
        } else {
            // For multi-segment names, use the last segment as short name
            self.parsed.symbols.name(*e.name.segments.last().unwrap()).to_owned()
        };
        let short_sym = self.kb.intern(&short_name);
        if short_sym != functor {
            self.kb.register_entity_fields(short_sym, field_names);
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
        // Record the fact's top-level term span on the side-tables so
        // typing.rs error formatting can resolve it back to a span.
        self.create_occurrence(f.term, term);

        let meta = f.meta.as_ref().map(|mb| self.load_meta_block(mb));
        let rule_id = self.kb.assert_fact(term, fact_sort, domain, meta);
        self.fact_rule_ids.push(rule_id);

        // WI-210: when `fact Spec[bindings]` appears inside a sort body
        // and Spec is itself a parameterized sort, also emit a
        // SortProvidesInfo so dispatch (and proposal-030 specialization
        // witnesses) can find the impl. Mirrors load_provides_clause.
        // Brings the loader in line with kernel-language §1418.
        self.maybe_emit_fact_provides_info(term, domain);

        self.current_owner = prev_owner;
    }

    /// If `fact_term` is `Spec[bindings]` claiming spec satisfaction,
    /// emit a `SortProvidesInfo(sort_ref=<carrier>, spec=SortView(Spec,
    /// <named bindings>))` alongside the bare fact. Two recognised
    /// shapes (kernel-language §1418 + the stdlib namespace-level
    /// convention):
    /// - **Sort-body**: `current_scope` is a sort. The carrier is
    ///   `current_scope` itself; bindings come from the fact.
    /// - **Namespace-level**: `current_scope` is a namespace.
    ///   The carrier is derived from the fact's first binding value
    ///   (the type that satisfies the spec).
    ///
    /// Positional bindings are translated to named bindings via
    /// `type_params_of_sort` — `fact Ring[Float]` and
    /// `fact Ring[T = Float]` produce equivalent `SortView` records.
    fn maybe_emit_fact_provides_info(&mut self, fact_term: TermId, domain: TermId) {
        // fact_term must be `Fn { functor, … }` where functor is a Sort
        // with at least one type parameter (i.e. a spec).
        let (fact_functor, fact_pos_args, fact_named_args) =
            match self.kb.get_term(fact_term) {
                Term::Fn { functor, pos_args, named_args } => {
                    (*functor, pos_args.clone(), named_args.clone())
                }
                _ => return,
            };
        if !matches!(self.kb.kind_of(fact_functor), Some(SymbolKind::Sort)) {
            return;
        }
        let spec_params = self.kb.type_params_of_sort(fact_functor);
        if spec_params.is_empty() {
            return;
        }

        // Translate positional bindings → named, using the spec's
        // declared parameter order. type_params_of_sort returns short
        // names; positional[i] binds to params[i].
        let mut named: SmallVec<[(Symbol, TermId); 2]> = fact_named_args.clone();
        for (i, pos_val) in fact_pos_args.iter().enumerate() {
            let param_name = match spec_params.get(i) {
                Some(n) => n.clone(),
                None => continue,
            };
            let param_sym = self.kb.intern(&param_name);
            // Skip if user already supplied this name explicitly.
            if named.iter().any(|(s, _)| *s == param_sym) {
                continue;
            }
            named.push((param_sym, *pos_val));
        }

        // Determine sort_ref (the carrier). For sort-body facts, it's
        // the enclosing sort. For namespace-level facts, it's the
        // first binding value's underlying sort symbol.
        let domain_functor = match self.kb.get_term(domain) {
            Term::Fn { functor, .. } => *functor,
            _ => return,
        };
        let sort_ref_term = match self.kb.kind_of(domain_functor) {
            Some(SymbolKind::Sort) => domain,
            Some(SymbolKind::Namespace) => {
                // Derive carrier from the first binding's value.
                let carrier_sym = named
                    .first()
                    .and_then(|(_, val)| self.fact_value_to_sort_sym(*val));
                match carrier_sym {
                    Some(sym) => self.kb.make_name_term_from_sym(sym),
                    None => return,
                }
            }
            _ => return,
        };

        // Build SortView(spec_name_term, …named bindings).
        let sort_view_sym = self.kb.resolve_symbol("anthill.reflect.SortView");
        let spec_name_term = self.kb.make_name_term_from_sym(fact_functor);
        let sort_view_term = self.kb.alloc(Term::Fn {
            functor: sort_view_sym,
            pos_args: SmallVec::from_elem(spec_name_term, 1),
            named_args: named,
        });

        // Build SortProvidesInfo(sort_ref, spec).
        let provides_sym = self.kb.resolve_symbol("anthill.reflect.SortProvidesInfo");
        let sort_ref_arg = self.kb.intern("sort_ref");
        let spec_arg = self.kb.intern("spec");
        self.kb.register_entity_fields(provides_sym, vec![sort_ref_arg, spec_arg]);
        let provides_term = self.kb.alloc(Term::Fn {
            functor: provides_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (sort_ref_arg, sort_ref_term),
                (spec_arg, sort_view_term),
            ]),
        });

        let provides_sort = self.kb.make_name_term("Requirement");
        self.kb.assert_fact(provides_term, provides_sort, domain, None);
    }

    /// Extract the underlying sort symbol from a fact-binding value
    /// term. Handles `Ref`, `Ident`, and nullary `Fn` shapes — the
    /// forms `convert_term` produces for plain sort references.
    fn fact_value_to_sort_sym(&self, value: TermId) -> Option<Symbol> {
        match self.kb.get_term(value) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            Term::Fn { functor, .. } => {
                if matches!(self.kb.kind_of(*functor), Some(SymbolKind::Sort)) {
                    Some(*functor)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn load_rule(&mut self, r: &Rule, domain: TermId) {
        let rule_sort = self.kb.make_name_term("Rule");

        let prev_owner = self.current_owner;
        if let Some(ref label) = r.label {
            self.current_owner = Some(self.remap_name(label));
        }

        // Single pass: build positive heads, detect any `⊥` head.
        let mut positive_heads: Vec<TermId> = Vec::with_capacity(r.heads.len());
        let mut has_bottom = false;
        for h in &r.heads {
            match h {
                RuleHead::Term(tid) => positive_heads.push(self.convert_term(*tid)),
                RuleHead::Bottom => has_bottom = true,
            }
        }

        // ⊥ does not combine with positive heads.
        if has_bottom && r.heads.len() > 1 {
            self.errors.push(LoadError::Other {
                message: "denial heads (`⊥`) cannot be combined with positive heads in a multi-head rule".to_string(),
            });
            self.current_owner = prev_owner;
            return;
        }

        // WI-246: build the rule's native occurrence body — the sole body
        // representation now that the term body is dropped. Each atom is walked
        // from the parse IR straight to a `NodeOccurrence`
        // (`build_body_atom_occurrence`), which seeds `self.var_map` itself for
        // shared var identity across the body atoms and the (already-converted)
        // head, so `assert_rule_debruijn_with_nodes` can collect the rule's vars
        // from head + occurrences and close both to De Bruijn — no term body.
        let mut body_nodes: Vec<Rc<NodeOccurrence>> = Vec::new();
        if let Some(terms) = r.body.as_ref() {
            for &tid in terms {
                body_nodes.push(self.build_body_atom_occurrence(tid));
            }
        }
        let meta = r.meta.as_ref().map(|mb| self.load_meta_block(mb));

        // Proposal 032: head IS the rule's claim. Labeled rules
        // remain citable through `RuleEntry.label` + `rules_by_label`.
        // Multi-head labeled rules (`rule X: H1, H2 :- B`) desugar
        // into N rules sharing label X, each with head H_i and the
        // same body B — `using X` fans out to all of them via
        // `rules_by_label[X]`.
        let label_sym = r.label.as_ref().map(|l| self.remap_name(l));

        let kb_heads: Vec<TermId> = match (&r.label, has_bottom, positive_heads.len()) {
            // Denial: head = ⊥. (Labeled cites via label index;
            // unlabeled denial is citable only by pattern.)
            (_, true, _) => vec![self.kb.alloc(Term::Bottom)],

            // Labeled — single or multi-head; each head becomes its
            // own rule sharing the label.
            (Some(_), false, _) => positive_heads,

            // Unlabeled single-head: head term IS the KB identity.
            (None, false, 1) => positive_heads,

            // Unlabeled multi-head: no unique citation handle.
            (None, false, _) => {
                self.errors.push(LoadError::Other {
                    message: "multi-head rule requires a label so the rule has a unique citation handle (e.g. `rule my_law: H1, H2 :- B`)".to_string(),
                });
                self.current_owner = prev_owner;
                return;
            }
        };

        for kb_head in kb_heads {
            let rid = self.kb.assert_rule_debruijn_with_nodes(
                kb_head, body_nodes.clone(), rule_sort, domain, meta);
            if let Some(label) = label_sym {
                self.kb.set_rule_label(rid, label);
            }
            // WI-139: equational rules are cite-required by default.
            if is_equational_head(self.kb, kb_head)
                && !meta_has_flag(self.kb, meta, "simp")
                && !meta_has_flag(self.kb, meta, "unfold")
            {
                self.kb.unindex_functor(rid);
            }
        }

        self.current_owner = prev_owner;
    }

    fn load_operation(&mut self, o: &Operation, domain: TermId) {
        let op_sort = self.kb.make_name_term("Operation");
        let functor = self.remap_name(&o.name);

        // Set owner for expression occurrences
        let prev_owner = self.current_owner;
        self.current_owner = Some(functor);

        // Always enter the operation scope (scope created during scanning).
        // Even paramless operations have an op scope so that the reserved
        // `result` name is resolvable in effects / ensures positions
        // (proposal 041).
        let prev_scope = self.current_scope;
        let op_scope = self.kb.make_name_term_from_sym(functor);
        self.current_scope = op_scope;

        let op_qualified = self.kb.qualified_name_of(functor).to_owned();

        // `result` as a parameter name collides with the reserved
        // return-value name; one diagnostic per operation suffices.
        if o.params.iter().any(|p| self.parsed.symbols.name(p.name) == "result") {
            self.errors.push(LoadError::Other {
                message: format!(
                    "operation '{}': parameter name 'result' is reserved for the return value; rename the parameter",
                    op_qualified
                ),
            });
        }

        // Pre-allocate type-param Vars and seed the per-scope cache so
        // later `type_expr_to_term` calls reuse them, and we can publish
        // the list on OperationInfo. Skipping the `find_sort_alias_var`
        // branch is intentional: an op type-param is its own logical
        // variable, distinct from any same-named outer SortAlias.
        let mut type_param_var_terms: Vec<TermId> = Vec::with_capacity(o.type_params.len());
        for tp in &o.type_params {
            let tp_name = self.parsed.symbols.name(tp.name).to_owned();
            let tp_sym = self.kb.intern(&tp_name);
            let cache_key = (op_scope.raw(), tp_name.clone());
            let var_tid = if let Some(&cached) = self.type_param_vars.get(&cache_key) {
                cached
            } else {
                let vid = self.kb.fresh_var(tp_sym);
                let tid = self.kb.alloc(Term::Var(Var::Global(vid)));
                self.type_param_vars.insert(cache_key, tid);
                tid
            };
            type_param_var_terms.push(var_tid);
        }

        let return_term = self.type_expr_to_term(&o.return_type);

        // Build FieldInfo list for params
        let field_info_sym = self.kb.resolve_symbol("anthill.reflect.FieldInfo");
        let fi_name_sym = self.kb.intern("name");
        let fi_type_sym = self.kb.intern("type_name");
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

        // WI-348 (value-fact payoff): effect labels are carrier-agnostic
        // `Value`s and ride directly in the `OperationInfo` fact built below —
        // no `op_effects` side-table. A `Modify[c]` label is a `Value::Node` (a
        // `denoted` cannot be a hash-consed term); a ground label (`Error`) is a
        // `Value::Term`. When any label is non-`Term` the fact is built as a
        // *value fact* (Node-carrying head, `assert_fact_value`); when all are
        // `Term` it stays a hash-consed fact. Either way `lookup_operation_info`
        // reads these same labels back from the fact.
        let effect_values: Vec<crate::eval::value::Value> = o.effects
            .iter()
            .map(|e| self.type_expr_to_value(&e.type_expr))
            .collect();

        // Build requires and ensures lists. Auto-requires inference
        // (WI-320 / proposal 045 §6 Phase 0) extends the user-written
        // requires with one `EffectsRuntime[Effects = E_i]` per free row
        // variable in the effects clause — see `infer_effects_row_requires`
        // for the row-variable heuristic and the spec examples.
        let auto_requires_terms = self.infer_effects_row_requires(o);
        let requires_list = self.convert_clause_list_with_extra(&o.requires, &auto_requires_terms);
        let ensures_list = self.convert_clause_list(&o.ensures);

        // Convert expression body if present. WI-305: discard the term handle;
        // the occurrence is the sole stored body (op_body_node side-table). The
        // handle is no longer kept in any fact field (OperationInfo/OperationImpl
        // body fields dropped). The term is still built transiently inside
        // `convert_expr_term` because the native node-build reads it.
        let has_body = match o.body {
            Some(body_tid) => {
                let (_handle, node) = self.convert_expr_term(body_tid);
                self.kb.set_op_body_node(functor, node);
                true
            }
            None => false,
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
        let type_params_sym = self.kb.intern("type_params");

        // name: Ref to operation symbol
        let name_ref = self.kb.alloc(Term::Ref(functor));
        let type_params_list = build_list(self.kb, &type_param_var_terms);

        // WI-348: assemble the OperationInfo named args ONCE, carrier-agnostically.
        // Only `effects` varies by carrier: when every label is a ground
        // `Value::Term` the effects fit a hash-consed `TermId` cons-list and the
        // whole head stays a hash-consed term (the universal, dedup-able case);
        // when any label is a `Value::Node` (a `denoted` like `Modify[c]`) the
        // effects ride as a value cons-list and the head must be a value fact.
        // Every other field is always a ground `Value::Term`.
        use crate::eval::value::Value;
        let all_ground = effect_values
            .iter()
            .all(|v| matches!(v, Value::Term(_)));
        let effects_field = if all_ground {
            let effect_terms: Vec<TermId> = effect_values
                .iter()
                .map(|v| match v {
                    Value::Term(t) => *t,
                    _ => unreachable!("all_ground guard guarantees Value::Term"),
                })
                .collect();
            Value::Term(build_list(self.kb, &effect_terms))
        } else {
            build_value_list(self.kb, effect_values)
        };
        // Single source of truth for the field set / order. Readers resolve by
        // key (functor + `NamedKey(sym)`), so order is not load-bearing.
        let named: Vec<(Symbol, Value)> = vec![
            (name_sym, Value::Term(name_ref)),
            (params_sym, Value::Term(params_list)),
            (return_type_sym, Value::Term(return_term)),
            (effects_sym, effects_field),
            (requires_sym, Value::Term(requires_list)),
            (ensures_sym, Value::Term(ensures_list)),
            (type_params_sym, Value::Term(type_params_list)),
        ];
        if all_ground {
            // Ground head → hash-consed `Term::Fn` (dedup, structural sharing).
            // Every field is a `Value::Term` here, so the extraction is total.
            let named_args: SmallVec<[(Symbol, TermId); 2]> = named
                .iter()
                .map(|(s, v)| match v {
                    Value::Term(t) => (*s, *t),
                    _ => unreachable!("all_ground ⇒ every OperationInfo field is Value::Term"),
                })
                .collect();
            let op_info = self.kb.alloc(Term::Fn {
                functor: op_info_sym,
                pos_args: SmallVec::new(),
                named_args,
            });
            self.kb.assert_fact(op_info, op_sort, domain, None);
        } else {
            // A `denoted`-bearing effect forces a `Value::Node` somewhere in the
            // head, which a hash-consed `Term` cannot hold → value fact.
            let head = Value::Entity {
                functor: op_info_sym,
                pos: std::rc::Rc::from(Vec::<Value>::new()),
                named: std::rc::Rc::from(named),
            };
            self.kb.assert_fact_value(head, op_sort, domain, None);
        }

        // Emit OperationImpl fact for operations with expression bodies. WI-305:
        // the body field is dropped — the occurrence lives in op_body_node and is
        // reached via anthill.reflect.operation_body.
        if has_body {
            if let Some(op_impl_sym) = self.kb.try_resolve_symbol("anthill.realization.OperationImpl") {
                let impl_sort = self.kb.make_name_term("OperationImpl");
                let operation_key = self.kb.intern("operation");
                let params_key = self.kb.intern("params");

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
                    ]),
                });
                self.kb.assert_fact(op_impl, impl_sort, domain, None);
            }
        }

        if let Some(body_parse_id) = o.body {
            self.emit_operation_equation(o, functor, body_parse_id, domain);
        }
    }

    /// Build `eq(<op>(?p1, ?p2, ...), body[params -> ?p_i])` and
    /// assert it as a rule with empty body, so SLD can apply operation
    /// definitions as rewrite rules during proof search.
    fn emit_operation_equation(
        &mut self,
        o: &Operation,
        op_functor: Symbol,
        body_parse_id: TermId,
        domain: TermId,
    ) {
        let body_kb = self.convert_term(body_parse_id);

        let mut param_vars: Vec<(Symbol, VarId)> = Vec::new();
        for p in &o.params {
            let pname = self.parsed.symbols.name(p.name).to_owned();
            let kb_sym = self.kb.intern(&pname);
            let var = self.kb.fresh_var(kb_sym);
            param_vars.push((kb_sym, var));
        }

        let body_with_vars = self.rewrite_param_refs(body_kb, &param_vars);

        let call_pos: SmallVec<[TermId; 4]> = param_vars.iter()
            .map(|(_, vid)| self.kb.alloc(Term::Var(Var::Global(*vid))))
            .collect();
        let call = self.kb.alloc(Term::Fn {
            functor: op_functor,
            pos_args: call_pos,
            named_args: SmallVec::new(),
        });

        let eq_sym = self.kb.try_resolve_symbol("anthill.prelude.Eq.eq")
            .unwrap_or_else(|| self.kb.intern("eq"));
        let head = self.kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[call, body_with_vars]),
            named_args: SmallVec::new(),
        });

        let eq_sort = self.kb.make_name_term("anthill.prelude.Eq");
        self.kb.assert_rule_debruijn(head, vec![], eq_sort, domain, None);
    }

    /// Replace `Ident(s)`/`Ref(s)` matching a parameter symbol with the
    /// corresponding `Var::Global`. Doesn't alpha-rename inside lambda
    /// or let bodies — shadowing param names is unsupported.
    fn rewrite_param_refs(&mut self, term: TermId, param_vars: &[(Symbol, VarId)]) -> TermId {
        match self.kb.get_term(term).clone() {
            Term::Ident(s) | Term::Ref(s) => {
                if let Some((_, vid)) = param_vars.iter().find(|(p, _)| *p == s) {
                    self.kb.alloc(Term::Var(Var::Global(*vid)))
                } else {
                    term
                }
            }
            Term::Fn { functor, pos_args, named_args } => {
                let mut new_pos: SmallVec<[TermId; 4]> = SmallVec::new();
                for &t in pos_args.iter() {
                    new_pos.push(self.rewrite_param_refs(t, param_vars));
                }
                let mut new_named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for &(n, t) in named_args.iter() {
                    new_named.push((n, self.rewrite_param_refs(t, param_vars)));
                }
                self.kb.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
            }
            _ => term,
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
        let type_term = self.sort_inst_to_term(&r.type_expr);

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

    /// Encode a `ProofStrategy` IR node into a `ProofStrategyKind` (or
    /// `ProofStrategyOpen`) Term. Shared by ProofRecord.strategy and
    /// the per-step / concluding-clause tactic fields of structured
    /// proofs (proposal 031).
    fn encode_strategy(&mut self, s: &ProofStrategy) -> TermId {
        let sname_sym = self.kb.alloc(Term::Const(
            super::term::Literal::String(self.parsed.symbols.name(s.name).to_string())
        ));
        let strat_sym = self.kb.resolve_symbol("anthill.realization.ProofStrategyKind");
        let arg_ids: Vec<TermId> = s.args.iter().map(|&t| self.convert_term(t)).collect();
        let args_list = build_list(self.kb, &arg_ids);
        let name_arg = self.kb.symbols.intern("name");
        let args_arg = self.kb.symbols.intern("args");
        self.kb.alloc(Term::Fn {
            functor: strat_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (name_arg, sname_sym),
                (args_arg, args_list),
            ]),
        })
    }

    /// Resolve a structured-proof cite name to its qualified rule QN.
    /// Step-local labels (matching one of `step_labels`) resolve to
    /// `<parent_proof_qn>.<label>` — phase-b dispatch will look up
    /// the synthesized step rule under that QN. External cites fall
    /// back to scope-aware resolution against the loader's current
    /// scope (same path the parent proof's `using` clause uses).
    /// Names that don't resolve are encoded as their source-side
    /// segment join so the dispatcher can surface a clear error
    /// rather than silently dropping the cite.
    fn resolve_step_cite(
        &mut self,
        name: &Name,
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> String {
        let source = join_segments(&self.parsed.symbols, &name.segments);
        if step_labels.contains(&source) {
            return format!("{parent_proof_qn}.{source}");
        }
        let sym = self.remap_name(name);
        match self.kb.symbols.get(sym) {
            crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            crate::intern::SymbolDef::Unresolved { .. } => source,
        }
    }

    /// Encode a structured-proof cite-list as a cons-list of String
    /// literals carrying each cite's resolved qualified rule QN
    /// (step-local labels become `<parent_proof_qn>.<label>`; external
    /// names go through scope-aware resolution).
    fn encode_step_using_list(
        &mut self,
        using: &[Name],
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> TermId {
        let strs: Vec<TermId> = using.iter()
            .map(|n| {
                let qn = self.resolve_step_cite(n, parent_proof_qn, step_labels);
                self.kb.alloc(Term::Const(super::term::Literal::String(qn)))
            })
            .collect();
        build_list(self.kb, &strs)
    }

    /// Encode one structured-proof step rule into a ProofStep Term.
    /// The step's head is taken as the first positive head of the
    /// rule (proposal 031 v0 supports single-head steps); multi-head
    /// or denial steps are encoded with `Bottom` as a placeholder so
    /// the dispatcher can reject them at runtime with a clear error.
    fn encode_proof_step(
        &mut self,
        step: &ProofStep,
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> TermId {
        let label_str = step.rule.label.as_ref()
            .map(|n| join_segments(&self.parsed.symbols, &n.segments))
            .unwrap_or_default();
        let label_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(label_str)
        ));

        let head_term = match step.rule.heads.first() {
            Some(RuleHead::Term(tid)) => self.convert_term(*tid),
            _ => self.kb.alloc(Term::Bottom),
        };

        let body_ids: Vec<TermId> = step.rule.body.as_ref()
            .map(|terms| terms.iter().map(|&t| self.convert_term(t)).collect())
            .unwrap_or_default();
        let body_list = build_list(self.kb, &body_ids);

        let using_list = self.encode_step_using_list(&step.using, parent_proof_qn, step_labels);
        let tactic_term = self.encode_strategy(&step.strategy);

        let s_sym = self.kb.resolve_symbol("anthill.realization.ProofStep");
        let label_arg = self.kb.symbols.intern("label");
        let head_arg = self.kb.symbols.intern("head_term");
        let body_arg = self.kb.symbols.intern("body_terms");
        let using_arg = self.kb.symbols.intern("using_names");
        let tactic_arg = self.kb.symbols.intern("tactic");
        self.kb.alloc(Term::Fn {
            functor: s_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (label_arg, label_term),
                (head_arg, head_term),
                (body_arg, body_list),
                (using_arg, using_list),
                (tactic_arg, tactic_term),
            ]),
        })
    }

    fn encode_proof_conclude(
        &mut self,
        c: &ConcludeClause,
        parent_proof_qn: &str,
        step_labels: &std::collections::BTreeSet<String>,
    ) -> TermId {
        let using_list = self.encode_step_using_list(&c.using, parent_proof_qn, step_labels);
        let tactic_term = self.encode_strategy(&c.strategy);
        let c_sym = self.kb.resolve_symbol("anthill.realization.ProofConcludeClause");
        let using_arg = self.kb.symbols.intern("using_names");
        let tactic_arg = self.kb.symbols.intern("tactic");
        self.kb.alloc(Term::Fn {
            functor: c_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (using_arg, using_list),
                (tactic_arg, tactic_term),
            ]),
        })
    }

    /// Lower a `proof <target> by <strategy> ... end` declaration into a
    /// ProofRecord fact. The target's qualified name and a term
    /// encoding of strategy/body are written so an external driver
    /// (CLI, IDE) can dispatch without reparsing the source.
    fn load_proof(&mut self, p: &ProofDecl, domain: TermId) {
        let target_sym = self.remap_name(&p.target);

        let strategy_term = match &p.strategy {
            None => {
                let open_sym = self.kb.resolve_symbol("anthill.realization.ProofStrategyOpen");
                self.kb.alloc(Term::Fn {
                    functor: open_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                })
            }
            Some(s) => self.encode_strategy(s),
        };

        let body_term = match &p.body {
            None => {
                let none_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyNone");
                self.kb.alloc(Term::Fn {
                    functor: none_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::new(),
                })
            }
            Some(ProofBody::Hints(hints)) => {
                let hint_ids: Vec<TermId> = hints.iter().map(|&t| self.convert_term(t)).collect();
                let list = build_list(self.kb, &hint_ids);
                let h_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyHints");
                let hints_arg = self.kb.symbols.intern("hints");
                self.kb.alloc(Term::Fn {
                    functor: h_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (hints_arg, list),
                    ]),
                })
            }
            Some(ProofBody::Structured { steps, conclude }) => {
                // Collect step labels first so step-internal cites
                // (`using h1, h2, ...` referencing other steps in
                // this same body) resolve to `<parent_proof_qn>.<label>`
                // rather than going through scope-aware lookup. The
                // parent_proof_qn is the qualified name of the rule
                // being proved (`rule_text`, computed below before
                // ProofRecord construction).
                let parent_proof_qn: String = match self.kb.symbols.get(target_sym) {
                    crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                    crate::intern::SymbolDef::Unresolved { name } => name.clone(),
                };
                let step_labels: std::collections::BTreeSet<String> = steps.iter()
                    .filter_map(|s| s.rule.label.as_ref()
                        .map(|n| join_segments(&self.parsed.symbols, &n.segments)))
                    .collect();
                let step_terms: Vec<TermId> = steps.iter()
                    .map(|s| self.encode_proof_step(s, &parent_proof_qn, &step_labels))
                    .collect();
                let steps_list = build_list(self.kb, &step_terms);
                let conclude_term = match conclude {
                    Some(c) => self.encode_proof_conclude(c, &parent_proof_qn, &step_labels),
                    None => self.kb.alloc(Term::Bottom),
                };
                let s_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyStructured");
                let steps_arg = self.kb.symbols.intern("steps");
                let conclude_arg = self.kb.symbols.intern("conclude");
                self.kb.alloc(Term::Fn {
                    functor: s_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (steps_arg, steps_list),
                        (conclude_arg, conclude_term),
                    ]),
                })
            }
            Some(ProofBody::Query { text, mapping }) => {
                let text_term = self.kb.alloc(Term::Const(
                    super::term::Literal::String(text.clone())
                ));
                let mapping_term = match mapping {
                    None => {
                        let nil_sym = self.kb.resolve_symbol("anthill.prelude.List.nil");
                        self.kb.alloc(Term::Fn {
                            functor: nil_sym,
                            pos_args: SmallVec::new(),
                            named_args: SmallVec::new(),
                        })
                    }
                    Some(mb) => {
                        let pair_sym = self.kb.resolve_symbol("anthill.realization.MappingEntry");
                        let s_arg = self.kb.symbols.intern("source");
                        let t_arg = self.kb.symbols.intern("target");
                        let entries: Vec<TermId> = mb.entries.iter().map(|e| {
                            let src = self.kb.alloc(Term::Const(
                                super::term::Literal::String(join_segments(&self.parsed.symbols, &e.source.segments))
                            ));
                            let tgt = self.kb.alloc(Term::Const(
                                super::term::Literal::String(e.target.clone())
                            ));
                            self.kb.alloc(Term::Fn {
                                functor: pair_sym,
                                pos_args: SmallVec::new(),
                                named_args: SmallVec::from_slice(&[
                                    (s_arg, src),
                                    (t_arg, tgt),
                                ]),
                            })
                        }).collect();
                        build_list(self.kb, &entries)
                    }
                };
                let q_sym = self.kb.resolve_symbol("anthill.realization.ProofBodyQuery");
                let text_arg = self.kb.symbols.intern("text");
                let map_arg = self.kb.symbols.intern("mapping");
                self.kb.alloc(Term::Fn {
                    functor: q_sym,
                    pos_args: SmallVec::new(),
                    named_args: SmallVec::from_slice(&[
                        (text_arg, text_term),
                        (map_arg, mapping_term),
                    ]),
                })
            }
        };

        let record_sym = self.kb.resolve_symbol("anthill.realization.ProofRecord");
        let rule_arg = self.kb.symbols.intern("rule");
        let strategy_arg = self.kb.symbols.intern("strategy");
        let body_arg = self.kb.symbols.intern("body");
        let result_arg = self.kb.symbols.intern("result");
        let deps_arg = self.kb.symbols.intern("dependencies");
        let using_arg = self.kb.symbols.intern("using");
        // Phase α.2 — proposal 030: witness, state_hash, parametric_context.
        // At load time these are placeholders; the prove driver will
        // populate them when a successful discharge produces a witness
        // (phase α.3+). Until then a Pending record carries a
        // TrustedAxiom placeholder so the field is always populated.
        let witness_arg = self.kb.symbols.intern("witness");
        let state_hash_arg = self.kb.symbols.intern("state_hash");
        let parametric_context_arg = self.kb.symbols.intern("parametric_context");

        let rule_text = match self.kb.symbols.get(target_sym) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        let rule_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(rule_text)
        ));
        let pending_sym = self.kb.resolve_symbol("anthill.realization.ObligationStatus.Pending");
        let pending_term = self.kb.alloc(Term::Fn {
            functor: pending_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let nil_sym = self.kb.resolve_symbol("anthill.prelude.List.nil");
        let nil_term = self.kb.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });

        // `using` clause: each cited name is resolved against the
        // proof block's enclosing scope (so `using lemma_a` works
        // bare, and `using anthill.x.lemma_a` also works). Resolved
        // qualified names land as String consts in a cons-list, so
        // the CLI driver can read them without re-parsing.
        let using_qns: Vec<TermId> = p.using.iter().map(|n| {
            let sym = self.remap_name(n);
            let qn = match self.kb.symbols.get(sym) {
                SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
                SymbolDef::Unresolved { name } => name.clone(),
            };
            self.kb.alloc(Term::Const(super::term::Literal::String(qn)))
        }).collect();
        let using_list = build_list(self.kb, &using_qns);

        // Phase α.2 placeholder values for witness, state_hash, and
        // parametric_context. A Pending ProofRecord carries
        // TrustedAxiom(reason: "pending — not yet discharged") as its
        // witness placeholder so the field is always populated. The
        // prove driver overwrites this when a tactic returns a real
        // witness (phase α.3+).
        let trusted_axiom_sym =
            self.kb.resolve_symbol("anthill.realization.witness.ProofWitness.TrustedAxiom");
        let reason_arg = self.kb.symbols.intern("reason");
        let pending_reason_term = self.kb.alloc(Term::Const(
            super::term::Literal::String("pending — not yet discharged".to_string())
        ));
        let placeholder_witness = self.kb.alloc(Term::Fn {
            functor: trusted_axiom_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(reason_arg, pending_reason_term)]),
        });
        let empty_state_hash = self.kb.alloc(Term::Const(
            super::term::Literal::String(String::new())
        ));

        let record_term = self.kb.alloc(Term::Fn {
            functor: record_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (rule_arg, rule_term),
                (strategy_arg, strategy_term),
                (body_arg, body_term),
                (result_arg, pending_term),
                (deps_arg, nil_term),
                (using_arg, using_list),
                (witness_arg, placeholder_witness),
                (state_hash_arg, empty_state_hash),
                (parametric_context_arg, nil_term),
            ]),
        });
        let record_sort = self.kb.make_name_term("anthill.realization.ProofRecord");
        self.kb.assert_fact(record_term, record_sort, domain, None);
    }

    /// `provides Spec[...]` inside a sort body. Emits a
    /// `SortProvidesInfo` fact recording the user's intent ("this
    /// sort claims to satisfy the named spec at the given binding").
    /// The verification pass `register_provides_specializations`
    /// (proposal 030 phase α.8 / WI-119 Variant 3) walks these
    /// facts after α.6/α.7 have registered the requires-clause
    /// witnesses; for each it checks that every requires-law has
    /// a Discharged ProofRecord at the substitution and emits
    /// `Specialization` ProofRecords pointing at the supporting
    /// proofs.
    fn load_provides_clause(&mut self, pc: &ProvidesClause, domain: TermId) {
        let provides_sort = self.kb.make_name_term("Requirement");
        let provides_sym = self.kb.resolve_symbol("anthill.reflect.SortProvidesInfo");
        let spec_term = self.sort_inst_to_term(&pc.spec);

        let sort_ref_sym = self.kb.intern("sort_ref");
        let spec_sym = self.kb.intern("spec");
        self.kb.register_entity_fields(provides_sym, vec![sort_ref_sym, spec_sym]);
        let provides_term = self.kb.alloc(Term::Fn {
            functor: provides_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (sort_ref_sym, domain),
                (spec_sym, spec_term),
            ]),
        });
        self.kb.assert_fact(provides_term, provides_sort, domain, None);
    }

    /// Standalone `provides Spec language X ... end`. Proposal 038.
    ///
    /// Inner facts/rules/proofs are loaded against the spec sort as their
    /// domain — so a `fact Eq[T = Int]` inside `provides Int language rust`
    /// triggers Phase 1's SortProvidesInfo auto-emit through the sort-body
    /// path, recording the carrier as the spec sort symbol (not a namespace
    /// doppelgänger). For non-anthill languages, additionally emit an
    /// `Implementation` fact (anthill.realization.Implementation) carrying
    /// the carrier/artifact/namespace-map metadata so codegen and
    /// interpreters can locate the host bindings by `(language, profile)`.
    fn load_provides_block(&mut self, pb: &ProvidesBlock, _domain: TermId) {
        let spec_term = self.sort_inst_to_term(&pb.spec);
        let prev_scope = self.current_scope;
        self.current_scope = spec_term;

        for item in &pb.items {
            match item {
                ProvidesItem::Rule(r) => self.load_rule(r, spec_term),
                ProvidesItem::RuleBlock(rb) => {
                    for r in &rb.entries { self.load_rule(r, spec_term); }
                }
                ProvidesItem::Fact(f) => self.load_fact(f, spec_term),
                ProvidesItem::Proof(p) => self.load_proof(p, spec_term),
                ProvidesItem::Artifact(_)
                | ProvidesItem::Carrier(_)
                | ProvidesItem::NamespaceMap(_) => {}
            }
        }

        self.current_scope = prev_scope;

        if self.parsed.symbols.name(pb.language) != "anthill" {
            self.emit_implementation_fact(pb, spec_term);
        }
    }

    /// Build and assert an `anthill.realization.Implementation` fact from
    /// a `provides Spec language X ... end` block. Populates target,
    /// artifact, language, profile, carrier, and namespace_map fields per
    /// the entity definition in stdlib/anthill/realization/realization.anthill.
    fn emit_implementation_fact(&mut self, pb: &ProvidesBlock, spec_term: TermId) {
        // target: qualified name of the spec sort, as a String literal.
        let spec_functor = match self.kb.get_term(spec_term) {
            Term::Fn { functor, .. } => *functor,
            _ => return,
        };
        let target_qn = match self.kb.symbols.get(spec_functor) {
            SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            SymbolDef::Unresolved { name } => name.clone(),
        };
        let target_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(target_qn.clone())));

        // language: from pb.language (parsed-symbol → string).
        let language_str = self.parsed.symbols.name(pb.language).to_string();
        let language_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(language_str)));

        // artifact: first Artifact item, defaulting to "" if absent.
        let artifact_str = pb.items.iter().find_map(|item| match item {
            ProvidesItem::Artifact(s) => Some(s.clone()),
            _ => None,
        }).unwrap_or_default();
        let artifact_term = self.kb.alloc(Term::Const(
            super::term::Literal::String(artifact_str)));

        // profile and description default to none (Option[T = String]).
        let none_sym = self.kb.resolve_symbol("anthill.prelude.Option.none");
        let none_term = self.kb.alloc(Term::Fn {
            functor: none_sym, pos_args: SmallVec::new(), named_args: SmallVec::new(),
        });

        // carrier: cons-list of CarrierBinding terms collected from each
        // `carrier` clause inside the block.
        let cb_sym = self.kb.resolve_symbol("anthill.realization.CarrierBinding");
        let sort_name_arg = self.kb.intern("sort_name");
        let host_type_arg = self.kb.intern("host_type");
        let mut carrier_terms: Vec<TermId> = Vec::new();
        for item in &pb.items {
            if let ProvidesItem::Carrier(bindings) = item {
                for b in bindings {
                    let sort_name = self.parsed.symbols.name(b.anthill_param).to_string();
                    let sort_name_term = self.kb.alloc(Term::Const(
                        super::term::Literal::String(sort_name)));
                    let host_type_term = self.host_type_to_string_term(b.host_type);
                    carrier_terms.push(self.kb.alloc(Term::Fn {
                        functor: cb_sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (sort_name_arg, sort_name_term),
                            (host_type_arg, host_type_term),
                        ]),
                    }));
                }
            }
        }
        let carrier_list = build_list(self.kb, &carrier_terms);

        // namespace_map: cons-list of NamespaceMapping terms.
        let nm_sym = self.kb.resolve_symbol("anthill.realization.NamespaceMapping");
        let ns_arg = self.kb.intern("namespace");
        let host_module_arg = self.kb.intern("host_module");
        let mut nm_terms: Vec<TermId> = Vec::new();
        for item in &pb.items {
            if let ProvidesItem::NamespaceMap(entries) = item {
                for e in entries {
                    let ns_name = self.parsed.symbols.name(e.anthill_namespace).to_string();
                    let ns_name_term = self.kb.alloc(Term::Const(
                        super::term::Literal::String(ns_name)));
                    let host_mod_term = self.host_type_to_string_term(e.host_module);
                    nm_terms.push(self.kb.alloc(Term::Fn {
                        functor: nm_sym,
                        pos_args: SmallVec::new(),
                        named_args: SmallVec::from_slice(&[
                            (ns_arg, ns_name_term),
                            (host_module_arg, host_mod_term),
                        ]),
                    }));
                }
            }
        }
        let nm_list = build_list(self.kb, &nm_terms);

        // Assemble the Implementation fact.
        let impl_sym = self.kb.resolve_symbol("anthill.realization.Implementation");
        let target_arg = self.kb.intern("target");
        let artifact_arg = self.kb.intern("artifact");
        let language_arg = self.kb.intern("language");
        let profile_arg = self.kb.intern("profile");
        let description_arg = self.kb.intern("description");
        let carrier_arg = self.kb.intern("carrier");
        let nm_field = self.kb.intern("namespace_map");

        let impl_term = self.kb.alloc(Term::Fn {
            functor: impl_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (target_arg, target_term),
                (artifact_arg, artifact_term),
                (language_arg, language_term),
                (profile_arg, none_term),
                (description_arg, none_term),
                (carrier_arg, carrier_list),
                (nm_field, nm_list),
            ]),
        });
        let impl_sort = self.kb.make_name_term("anthill.realization.Implementation");
        self.kb.assert_fact(impl_term, impl_sort, spec_term, None);
    }

    /// Convert a parsed host_type term (typically a `Term::Const(String)`
    /// like `"i64"`) into a String-literal KB term. Falls back to
    /// stringifying via `convert_term` for non-literal forms.
    fn host_type_to_string_term(&mut self, parse_id: TermId) -> TermId {
        if let Term::Const(super::term::Literal::String(s)) = self.parsed.terms.get(parse_id) {
            let s = s.clone();
            return self.kb.alloc(Term::Const(super::term::Literal::String(s)));
        }
        self.convert_term(parse_id)
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
        self.convert_clause_list_with_extra(clauses, &[])
    }

    /// Like `convert_clause_list`, plus a tail of additional kb-space clause
    /// terms to append after the user-written clauses. The `extra_terms` are
    /// already-built kb TermIds (one term per clause, no conjunction wrap),
    /// used by WI-320's auto-requires inference to append synthesized
    /// `EffectsRuntime[Effects = E_i]` clauses to a user's requires list.
    fn convert_clause_list_with_extra(
        &mut self,
        clauses: &[Vec<TermId>],
        extra_terms: &[TermId],
    ) -> TermId {
        let mut clause_terms: Vec<TermId> = clauses
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
        clause_terms.extend_from_slice(extra_terms);
        build_list(self.kb, &clause_terms)
    }

    /// WI-320 / proposal 045 §6 Phase 0 — auto-requires inference for an
    /// operation's `effects <expr>` clause.
    ///
    /// Walks the operation's effects and emits one `EffectsRuntime[Effects = E_i]`
    /// kb term per distinct free row variable. The OperationInfo.requires list
    /// then contains the synthesized clauses alongside user-written ones —
    /// avoiding boilerplate at every operation declaration that mentions a
    /// row variable.
    ///
    /// **Heuristic for "free row variable":** the current `_effect_set`
    /// grammar admits `simple_type | application | variable_term`. Only the
    /// bare `simple_type` form (`effects E`) can name a row variable; both
    /// `application` (`Modify[T]` — closed) and `variable_term` (`?x` —
    /// reserved for term-level variables, not row vars at the type level)
    /// short-circuit. A bare name qualifies as a row variable when its
    /// resolved symbol participates in a `SortAlias(<sym>, Var)` fact —
    /// shorthand for "declared as `sort X = ?`", which is exactly the shape
    /// the `effects X` sugar (this WI's `effects_sort_item`) desugars to and
    /// the shape pre-existing migration sites (Function.E, Stream.E, etc.)
    /// already had. Concrete effect sorts like `Suspension`/`Branch` lack
    /// the SortAlias fact and are rightly excluded.
    ///
    /// **Per-spec examples:**
    ///   - `effects E`                  → one requires
    ///   - `effects merge(E1, E2)`      → two requires  (forward-looking;
    ///                                     the current grammar's
    ///                                     `_effect_set` does not yet admit
    ///                                     row-combinator applications, so
    ///                                     this case is a no-op today)
    ///   - `effects { E, -Modify[kb] }` → one requires  (E only)
    ///   - `effects { Modify[c] }`      → none          (closed row)
    ///
    /// The kb term emitted per row variable is the SortAlias-backed Var
    /// shape that `type_expr_to_term` returns for the effect — the same
    /// Term that goes into OperationInfo.effects, keeping the row var's
    /// identity consistent across effects/requires. This is structurally
    /// distinct from what a hand-written `requires EffectsRuntime[Effects = E]`
    /// lowers to (which routes through convert_instantiation_term →
    /// convert_type_value and produces a `Term::Ref(E_sym)` value, not the
    /// SortAlias Var). Both shapes happen to unify against the bridge fact
    /// head `EffectsRuntime[Effects = effects_rows(?expr)]` — the Var/Ref
    /// query-side binds to the effects_rows subterm via the discrim tree's
    /// standard Var-skip path — but they are NOT interchangeable Terms,
    /// despite the symmetry the surface syntax suggests.
    fn infer_effects_row_requires(&mut self, o: &Operation) -> Vec<TermId> {
        // EffectsRuntime is unconditionally pre-registered by
        // `register_stdlib_scopes` (and the bridge fact emission at
        // `emit_effects_runtime_bridge_fact` `.expect()`s the same symbol).
        // A missing symbol here is the same bootstrap regression as the
        // bridge-fact path — surface it loudly rather than silently dropping
        // every operation's auto-requires (which would mask the upstream
        // failure behind confusing per-operation 'requires unmet' errors).
        // Matches code-review #9's policy from commit 9ed183d.
        let er_sym = self.kb.try_resolve_symbol("anthill.prelude.EffectsRuntime").expect(
            "WI-320 bootstrap invariant: anthill.prelude.EffectsRuntime symbol \
             pre-registered by register_stdlib_scopes — see kb/load.rs",
        );
        let effects_param_sym = self.kb.intern("Effects");

        let mut seen: HashSet<Symbol> = HashSet::new();
        let mut result: Vec<TermId> = Vec::new();
        for eff in &o.effects {
            let TypeExpr::Simple(name) = &eff.type_expr else {
                continue;
            };
            // Cache the resolved sym to avoid pushing duplicate UnresolvedName
            // diagnostics: `remap_name` errors-on-miss, so calling it once
            // here AND again via `type_expr_to_term` (~7067) would double a
            // legitimate error. We resolve once, dedup-by-sym, then reuse the
            // SortAlias Var directly without re-routing through remap_name.
            let sym = self.remap_name(name);
            if !seen.insert(sym) {
                continue;
            }
            // Row-variable test: must be backed by a SortAlias fact. Skipping
            // here also skips the second `remap_name` call below for non-row
            // effects (concrete sorts like `Suspension`).
            let Some(row_var_term) = self.find_sort_alias_var(sym) else {
                continue;
            };
            let er_term = self.kb.alloc(Term::Fn {
                functor: er_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(effects_param_sym, row_var_term)]),
            });
            result.push(er_term);
        }
        result
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
                    let kind = if s.kind == SortDeclKind::Enum { "Enum" } else { "Sort" };
                    self.emit_member_fact(sym, kind, parent);
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
