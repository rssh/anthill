/// Rust code generation from anthill parse IR.
///
/// Walks a `ParsedFile` and emits Rust skeleton code (traits, structs, enums,
/// function signatures). All generated code is bodyless — users provide
/// implementations separately.
///
/// See `docs/rust-forward-mapping.md` for the full mapping specification.

use std::collections::{HashMap, HashSet};

use crate::intern::{SymbolTable, Symbol};
use crate::kb::term::{Term, Literal, TermId};
use crate::parse::ir::*;

// ── Codegen error ───────────────────────────────────────────────

/// Error produced during Rust code generation.
#[derive(Debug, Clone)]
pub struct CodegenError {
    pub message: String,
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for CodegenError {}

// ── Codegen configuration ───────────────────────────────────────

/// Configuration for code generation output mode.
///
/// Default produces skeleton output (existing behavior).
/// Non-default values produce compilable output for STL generation.
pub struct CodegenConfig {
    /// Skip the outer `pub mod name { }` wrapper (file IS the module).
    pub flatten_top_namespace: bool,
    /// Emit `{ todo!() }` for free functions and impl methods (compilable output).
    pub emit_fn_bodies: bool,
    /// CarrierBindings: opaque sort name → host type path.
    /// E.g. "Term" → "anthill_core::kb::term::TermId"
    pub carrier_bindings: HashMap<String, String>,
    /// NamespaceMappings: anthill namespace prefix → host module prefix.
    /// E.g. "anthill" → "crate" for intra-crate generation.
    pub namespace_map: HashMap<String, String>,
    /// Derive macros for structs/enums. E.g. ["Clone", "Debug"].
    pub derives: Vec<String>,
    /// Make all items public (for compilable library output).
    pub default_pub: bool,
}

impl Default for CodegenConfig {
    fn default() -> Self {
        Self {
            flatten_top_namespace: false,
            emit_fn_bodies: false,
            carrier_bindings: HashMap::new(),
            namespace_map: HashMap::new(),
            derives: Vec::new(),
            default_pub: false,
        }
    }
}

/// Generate Rust skeleton code from a parsed anthill file.
pub fn generate_rust(parsed: &ParsedFile) -> Result<String, Vec<CodegenError>> {
    generate_rust_with_context(parsed, &HashSet::new())
}

/// Generate Rust code with cross-file sort classification context.
///
/// `global_trait_sorts` contains sort names known to be traits from other files.
/// This allows correct `impl Trait` wrapping for return types defined elsewhere.
pub fn generate_rust_with_context(
    parsed: &ParsedFile,
    global_trait_sorts: &HashSet<String>,
) -> Result<String, Vec<CodegenError>> {
    let config = CodegenConfig::default();
    generate_rust_with_config(parsed, global_trait_sorts, &config)
}

/// Generate Rust code with full configuration control.
///
/// Used by build scripts to produce compilable output with import remapping,
/// carrier bindings, derive macros, etc.
pub fn generate_rust_with_config(
    parsed: &ParsedFile,
    global_trait_sorts: &HashSet<String>,
    config: &CodegenConfig,
) -> Result<String, Vec<CodegenError>> {
    let mut cg = RustCodegen::with_context(&parsed.symbols, &parsed.terms, global_trait_sorts, config);
    cg.emit_items(&parsed.items, None);
    if cg.errors.is_empty() {
        Ok(cg.output)
    } else {
        Err(cg.errors)
    }
}

/// Collect trait sort names across multiple parsed files.
///
/// A sort is a trait if it has operations and no entities (same heuristic
/// used during single-file codegen). This pre-pass enables cross-file
/// `impl Trait` wrapping.
pub fn collect_trait_sorts(files: &[&ParsedFile]) -> HashSet<String> {
    let mut traits = HashSet::new();
    for file in files {
        collect_trait_sorts_from_items(&file.items, &file.symbols, &mut traits);
    }
    traits
}

fn collect_trait_sorts_from_items(
    items: &[Item],
    symbols: &SymbolTable,
    traits: &mut HashSet<String>,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let has_ops = s.items.iter().any(|i| matches!(i,
                    Item::Operation(_) | Item::OperationBlock(_)));
                let has_entities = s.items.iter().any(|i| matches!(i, Item::Entity(_)));
                if !has_entities && has_ops {
                    traits.insert(symbols.name(s.name.last()).to_owned());
                }
                // Recurse into nested items (sub-namespaces, nested sorts)
                collect_trait_sorts_from_items(&s.items, symbols, traits);
            }
            Item::Namespace(ns) => {
                collect_trait_sorts_from_items(&ns.items, symbols, traits);
            }
            _ => {}
        }
    }
}

// ── Sort analysis ────────────────────────────────────────────────

struct SortInfo<'a> {
    type_params: Vec<String>,
    supertraits: Vec<String>,
    entities: Vec<&'a Entity>,
    operations: Vec<&'a Operation>,
    rules: Vec<&'a Rule>,
    constraints: Vec<&'a Constraint>,
    consts: Vec<&'a Const>,
    sub_namespaces: Vec<&'a Namespace>,
}

impl<'a> SortInfo<'a> {
    fn from_items(items: &'a [Item], symbols: &SymbolTable, terms: &SimpleTermStore) -> Self {
        let mut info = SortInfo {
            type_params: Vec::new(),
            supertraits: Vec::new(),
            entities: Vec::new(),
            operations: Vec::new(),
            rules: Vec::new(),
            constraints: Vec::new(),
            consts: Vec::new(),
            sub_namespaces: Vec::new(),
        };

        for item in items {
            match item {
                Item::AbstractSort(s) => {
                    info.type_params.push(symbols.name(s.name.last()).to_owned());
                }
                Item::RequiresDecl(r) => {
                    let name = type_expr_name(symbols, &r.type_expr);
                    info.supertraits.push(name);
                }
                Item::Fact(f) => {
                    if let Some(name) = extract_fact_sort_name(symbols, terms, f) {
                        info.supertraits.push(name);
                    }
                }
                Item::Entity(e) => {
                    info.entities.push(e);
                }
                Item::Operation(o) => {
                    info.operations.push(o);
                }
                Item::OperationBlock(ob) => {
                    for o in &ob.entries {
                        info.operations.push(o);
                    }
                }
                Item::Rule(r) => {
                    info.rules.push(r);
                }
                Item::RuleBlock(rb) => {
                    for r in &rb.entries {
                        info.rules.push(r);
                    }
                }
                Item::Constraint(c) => {
                    info.constraints.push(c);
                }
                Item::Const(c) => {
                    info.consts.push(c);
                }
                Item::Namespace(n) => {
                    info.sub_namespaces.push(n);
                }
                _ => {}
            }
        }

        info
    }
}

// ── Codegen struct ───────────────────────────────────────────────

struct RustCodegen<'a> {
    symbols: &'a SymbolTable,
    terms: &'a SimpleTermStore,
    output: String,
    indent: usize,
    /// Sort names that generate as traits (not enums/structs).
    /// Used to wrap return types with `impl` when returning a trait.
    trait_sorts: HashSet<String>,
    config: &'a CodegenConfig,
    errors: Vec<CodegenError>,
}

impl<'a> RustCodegen<'a> {
    fn with_context(
        symbols: &'a SymbolTable,
        terms: &'a SimpleTermStore,
        global_traits: &HashSet<String>,
        config: &'a CodegenConfig,
    ) -> Self {
        Self {
            symbols,
            terms,
            output: String::new(),
            indent: 0,
            trait_sorts: global_traits.clone(),
            config,
            errors: Vec::new(),
        }
    }

    // ── Output helpers ───────────────────────────────────────────

    fn line(&mut self, text: &str) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
        self.output.push_str(text);
        self.output.push('\n');
    }

    fn blank(&mut self) {
        self.output.push('\n');
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    // ── Name resolution helpers ──────────────────────────────────

    fn resolve(&self, name: &Name) -> String {
        self.symbols.name(name.last()).to_owned()
    }

    /// Find a binding by named param, falling back to positional index.
    fn find_binding<'b>(&self, bindings: &'b [SortBinding], param_name: &str, positional_index: usize) -> Option<&'b SortBinding> {
        bindings.iter()
            .find(|b| b.param.as_ref().map(|p| self.symbols.name(p.last()) == param_name).unwrap_or(false))
            .or_else(|| bindings.iter().filter(|b| b.param.is_none()).nth(positional_index))
    }

    fn resolve_sym(&self, sym: Symbol) -> String {
        self.symbols.name(sym).to_owned()
    }

    fn visibility_prefix(&self, vis: Option<Visibility>) -> &'static str {
        match vis {
            Some(Visibility::Public) => "pub ",
            _ => {
                if self.config.default_pub { "pub " } else { "" }
            }
        }
    }

    // ── Trait return wrapping ─────────────────────────────────────

    /// If the outermost type of a return type is a known trait sort,
    /// wrap it with `impl` (e.g. `Stream<T>` → `impl Stream<T>`).
    fn wrap_trait_return(&self, ret: &str) -> String {
        // Extract the outermost type name (before '<' if generic)
        let base = ret.split('<').next().unwrap_or(ret).trim();
        if self.trait_sorts.contains(base) {
            format!("impl {ret}")
        } else {
            ret.to_owned()
        }
    }

    /// Emit `#[derive(...)]` attribute if configured.
    fn emit_derive_attr(&mut self) {
        if !self.config.derives.is_empty() {
            let derives = self.config.derives.join(", ");
            self.line(&format!("#[derive({derives})]"));
        }
    }

    // ── Term-level constants (proposal 039 / WI-084, codegen = WI-533) ──

    /// Lower a const's value term (in the ParsedFile term store) to a Rust
    /// constant expression. The Rust backend is a skeleton generator with no
    /// expression lowering, so only LITERAL bodies are supported; a bodyless
    /// host const or a non-literal body is a loud codegen error (the const is
    /// dropped and the error surfaces — never a silent skip, per the repo rule).
    /// Lower a const's value to a Rust constant expression. A bodied const must
    /// have a LITERAL body (the skeleton generator has no expression lowering);
    /// a bodyless const is host-supplied, so the known Float IEEE specials
    /// (WI-532) map to their `f64` expressions (keeping `float.anthill` Rust
    /// codegen working and matching cpp-gen). Anything else is a loud codegen
    /// error — dropped and diagnosed, never a silent skip, per the repo rule.
    fn lower_const_value(&mut self, name: &str, rust_ty: &str, value: Option<TermId>) -> Option<String> {
        let Some(tid) = value else {
            if rust_ty == "f64" {
                if let Some(expr) = host_float_const_rust(name) {
                    return Some(expr.to_string());
                }
            }
            self.errors.push(CodegenError {
                message: format!(
                    "const `{name}`: bodyless host-supplied const has no Rust value \
                     source (only the Float IEEE specials infinity/negativeInfinity/nan \
                     are mapped)"
                ),
            });
            return None;
        };
        match self.terms.get(tid) {
            // A handle (FactId/OccurrenceId) has no const-expressible literal form.
            Term::Const(Literal::Handle(..)) => {
                self.errors.push(CodegenError {
                    message: format!(
                        "const `{name}`: a handle literal is not a valid Rust const value"
                    ),
                });
                None
            }
            Term::Const(lit) => Some(lower_literal_rust(lit, rust_ty)),
            other => {
                self.errors.push(CodegenError {
                    message: format!(
                        "const `{name}`: only literal bodies are supported by Rust \
                         codegen, got {other:?}"
                    ),
                });
                None
            }
        }
    }

    /// Rust type for a const place. Like `type_to_rust`, but a `String` const
    /// becomes `&str`: `String` is not a valid `const` type (not const-
    /// constructible from a string literal), whereas `&'static str` is.
    fn const_rust_type(&self, ty: &TypeExpr) -> String {
        let t = self.type_to_rust(ty);
        if t == "String" { "&str".to_string() } else { t }
    }

    /// Emit a term-level const as `[pub] const NAME: T = value;`. A trait
    /// associated const takes no visibility (it is public with the trait);
    /// free-standing and inherent-impl consts follow the configured visibility.
    fn emit_const(&mut self, c: &Const, in_trait: bool) {
        let name = self.resolve(&c.name);
        let ty = self.const_rust_type(&c.ty);
        if let Some(val) = self.lower_const_value(&name, &ty, c.value) {
            let vis = if in_trait { "" } else { self.visibility_prefix(c.visibility) };
            self.line(&format!("{vis}const {name}: {ty} = {val};"));
        }
    }

    // ── Type expression mapping ──────────────────────────────────

    fn type_to_rust(&self, ty: &TypeExpr) -> String {
        match ty {
            TypeExpr::Simple(name) => {
                let n = self.resolve(name);
                map_primitive_type(&n)
            }
            TypeExpr::Variable { .. } => "T".to_owned(),
            TypeExpr::Tuple(fields) => {
                let parts: Vec<String> = fields.iter()
                    .map(|(_, ty)| self.type_to_rust(ty))
                    .collect();
                format!("({})", parts.join(", "))
            }
            TypeExpr::Parameterized { name, bindings } => {
                let n = self.resolve(name);
                match n.as_str() {
                    "List" => {
                        let inner = self.find_binding(bindings, "T", 0)
                            .map(|b| self.type_to_rust(&b.bound))
                            .unwrap_or_else(|| "T".to_owned());
                        format!("Vec<{inner}>")
                    }
                    "Option" => {
                        let inner = self.find_binding(bindings, "T", 0)
                            .map(|b| self.type_to_rust(&b.bound))
                            .unwrap_or_else(|| "T".to_owned());
                        format!("Option<{inner}>")
                    }
                    _ => {
                        let args: Vec<String> = bindings.iter()
                            .map(|b| self.type_to_rust(&b.bound))
                            .collect();
                        let mapped = map_primitive_type(&n);
                        format!("{mapped}<{}>", args.join(", "))
                    }
                }
            }
            TypeExpr::Arrow { params, return_type, .. } => {
                let param_types: Vec<String> = params.iter()
                    .map(|(_, p)| self.type_to_rust(p))
                    .collect();
                let ret = self.type_to_rust(return_type);
                format!("fn({}) -> {ret}", param_types.join(", "))
            }
            // WI-302: value-in-type (value-dependent) has no direct Rust type;
            // emit unit as a placeholder. (Codegen of dependent types is unsupported.)
            TypeExpr::Denoted(_) => "()".to_owned(),
            // WI-327: `-E` absence-form. Effect-position-only construct;
            // codegen of effect rows is not implemented, so emit `()`
            // identically to Denoted/effect-bearing arrows.
            TypeExpr::EffectAbsent(_) => "()".to_owned(),
            // WI-375: a written effect-row (`{}` / `{Modify[c]}`). An effect
            // annotation, not a value-carrying Rust type — emit `()` like the
            // effect-bearing arrow / absence forms above.
            TypeExpr::EffectRow(_) => "()".to_owned(),
        }
    }

    /// Map a type, but if the type name matches the enclosing sort name,
    /// replace with `Self`.
    fn type_to_rust_in_sort(&self, ty: &TypeExpr, sort_name: &str, type_params: &[String], collapse_type_params: bool) -> String {
        match ty {
            TypeExpr::Simple(name) => {
                let n = self.resolve(name);
                if n == sort_name {
                    return "Self".to_owned();
                }
                if collapse_type_params && type_params.iter().any(|p| p == &n) {
                    return "Self".to_owned();
                }
                map_primitive_type(&n)
            }
            TypeExpr::Variable { .. } => "T".to_owned(),
            TypeExpr::Tuple(fields) => {
                let parts: Vec<String> = fields.iter()
                    .map(|(_, ty)| self.type_to_rust_in_sort(ty, sort_name, type_params, collapse_type_params))
                    .collect();
                format!("({})", parts.join(", "))
            }
            TypeExpr::Parameterized { name, bindings } => {
                let n = self.resolve(name);
                if n == sort_name {
                    return "Self".to_owned();
                }
                match n.as_str() {
                    "List" => {
                        let inner = self.find_binding(bindings, "T", 0)
                            .map(|b| self.type_to_rust_in_sort(&b.bound, sort_name, type_params, collapse_type_params))
                            .unwrap_or_else(|| "T".to_owned());
                        format!("Vec<{inner}>")
                    }
                    "Option" => {
                        let inner = self.find_binding(bindings, "T", 0)
                            .map(|b| self.type_to_rust_in_sort(&b.bound, sort_name, type_params, collapse_type_params))
                            .unwrap_or_else(|| "T".to_owned());
                        format!("Option<{inner}>")
                    }
                    _ => {
                        let args: Vec<String> = bindings.iter()
                            .map(|b| self.type_to_rust_in_sort(&b.bound, sort_name, type_params, collapse_type_params))
                            .collect();
                        let mapped = map_primitive_type(&n);
                        format!("{mapped}<{}>", args.join(", "))
                    }
                }
            }
            TypeExpr::Arrow { params, return_type, .. } => {
                let param_types: Vec<String> = params.iter()
                    .map(|(_, p)| self.type_to_rust_in_sort(p, sort_name, type_params, collapse_type_params))
                    .collect();
                let ret = self.type_to_rust_in_sort(return_type, sort_name, type_params, collapse_type_params);
                format!("fn({}) -> {ret}", param_types.join(", "))
            }
            TypeExpr::Denoted(_) => "()".to_owned(),
            TypeExpr::EffectAbsent(_) => "()".to_owned(),
            // WI-375: written effect-row — an annotation, not a Rust type.
            TypeExpr::EffectRow(_) => "()".to_owned(),
        }
    }

    // ── Top-level dispatch ───────────────────────────────────────

    fn emit_items(&mut self, items: &[Item], _enclosing_ns: Option<&Namespace>) {
        let mut first = true;
        let mut last_entity: Option<String> = None;
        for item in items {
            match item {
                Item::Namespace(n) => {
                    if !first { self.blank(); }
                    self.emit_namespace(n);
                    last_entity = None;
                }
                Item::SortWithBody(s) => {
                    if !first { self.blank(); }
                    self.emit_sort(s);
                    last_entity = None;
                }
                Item::Entity(e) => {
                    if !first { self.blank(); }
                    self.emit_standalone_entity(e, _enclosing_ns);
                    last_entity = Some(self.resolve(&e.name));
                }
                Item::Operation(o) => {
                    let op_name = self.resolve(&o.name);
                    self.errors.push(CodegenError {
                        message: format!("operation `{op_name}` has no enclosing namespace for module trait"),
                    });
                }
                Item::Fact(f) => {
                    self.emit_namespace_fact(f, last_entity.as_deref());
                }
                Item::Rule(_) => {
                    // Collected later for test module
                }
                Item::RuleBlock(_) => {
                    // Collected later for test module
                }
                Item::Constraint(c) => {
                    if !first { self.blank(); }
                    self.emit_constraint(c);
                }
                Item::AbstractSort(_) => {
                    // Skip — only meaningful inside sort bodies
                }
                // WI-533: a free-standing const → `pub const NAME: T = value;`.
                Item::Const(c) => {
                    if !first { self.blank(); }
                    self.emit_const(c, false);
                    last_entity = None;
                }
                Item::OperationBlock(_) | Item::RequiresDecl(_)
                | Item::Describe(_)
                | Item::Proof(_) | Item::ProvidesClause(_) | Item::ProvidesBlock(_) => {}
            }
            first = false;
        }

        // Collect all rules for test module
        let rules = collect_rules(items);
        if !rules.is_empty() {
            self.blank();
            self.emit_test_module(&rules);
        }
    }

    // ── Namespace → mod ──────────────────────────────────────────

    fn emit_namespace(&mut self, ns: &Namespace) {
        let name = to_snake_case(&self.resolve(&ns.name));
        let flatten = self.config.flatten_top_namespace && self.indent == 0;

        if !flatten {
            self.line(&format!("pub mod {name} {{"));
            self.indent();
        }

        // Imports
        for imp in &ns.imports {
            self.emit_import(imp);
        }
        if !ns.imports.is_empty() && !ns.items.is_empty() {
            self.blank();
        }

        // Pre-pass: collect sort names and build aggregation maps
        // Only sorts with a body should receive aggregated operations
        let body_sort_names = self.collect_body_sort_names(&ns.items);
        let sort_names = self.collect_sort_names(&ns.items);
        let _entity_names = self.collect_entity_names(&ns.items);

        // Map: sort_name → Vec<&Operation> for namespace-level ops
        let mut sort_ops: std::collections::HashMap<String, Vec<&Operation>> =
            std::collections::HashMap::new();
        let mut consumed_ops: std::collections::HashSet<usize> =
            std::collections::HashSet::new();

        // Map: sort_name → Vec<String> for namespace-level facts as supertraits
        // Associate each fact with the most recent preceding sort
        let mut sort_supertraits: std::collections::HashMap<String, Vec<String>> =
            std::collections::HashMap::new();
        let mut consumed_facts: std::collections::HashSet<usize> =
            std::collections::HashSet::new();

        // Track the most recently seen sort name for fact association
        let mut current_sort: Option<String> = None;

        for (idx, item) in ns.items.iter().enumerate() {
            match item {
                Item::AbstractSort(s) => {
                    current_sort = Some(self.resolve(&s.name));
                }
                Item::SortWithBody(s) => {
                    current_sort = Some(self.resolve(&s.name));
                }
                Item::Entity(_) | Item::Namespace(_) => {
                    // Entities and namespaces break the sort-fact association
                    current_sort = None;
                }
                Item::Operation(op) => {
                    if let Some(first_param) = op.params.first() {
                        let first_type = self.type_expr_short_name(&first_param.ty);
                        if body_sort_names.contains(&first_type) {
                            sort_ops.entry(first_type).or_default().push(op);
                            consumed_ops.insert(idx);
                        }
                    }
                }
                Item::Fact(f) => {
                    // If preceded by a sort, associate as supertrait
                    if let Some(ref sname) = current_sort {
                        if let Some(trait_name) = extract_fact_sort_name(
                            self.symbols, self.terms, f
                        ) {
                            // Only associate if the fact name is a known sort
                            // (not an entity-level fact like `fact BulkStore`)
                            if sort_names.contains(&trait_name) {
                                sort_supertraits
                                    .entry(sname.clone())
                                    .or_default()
                                    .push(trait_name);
                                consumed_facts.insert(idx);
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        // Emit items, handling sorts with aggregated operations and supertraits
        let mut first = true;
        let mut last_entity: Option<String> = None;
        let mut orphan_ops: Vec<&Operation> = Vec::new();
        for (idx, item) in ns.items.iter().enumerate() {
            if consumed_ops.contains(&idx) || consumed_facts.contains(&idx) {
                continue;
            }
            match item {
                Item::SortWithBody(s) => {
                    if !first { self.blank(); }
                    let sname = self.resolve(&s.name);
                    let extra_ops = sort_ops.remove(&sname).unwrap_or_default();
                    let extra_supers = sort_supertraits.remove(&sname).unwrap_or_default();
                    self.emit_sort_with_extras(s, &extra_ops, &extra_supers);
                    last_entity = None;
                }
                Item::AbstractSort(s) => {
                    let sname = self.resolve(&s.name);
                    let extra_ops = sort_ops.remove(&sname);
                    let extra_supers = sort_supertraits.remove(&sname).unwrap_or_default();
                    if let Some(host_type) = self.config.carrier_bindings.get(&sname) {
                        // Carrier binding: emit type alias instead of struct/trait
                        if !first { self.blank(); }
                        let vis = self.visibility_prefix(s.visibility);
                        self.line(&format!("{vis}type {sname} = {host_type};"));
                    } else if let Some(ops) = extra_ops {
                        if !first { self.blank(); }
                        self.emit_abstract_sort_as_trait(s, &ops, &extra_supers);
                    } else {
                        // No operations → emit as unit struct
                        if !first { self.blank(); }
                        let vis = self.visibility_prefix(s.visibility);
                        self.line(&format!("{vis}struct {sname};"));
                    }
                    last_entity = None;
                }
                Item::Namespace(n) => {
                    if !first { self.blank(); }
                    self.emit_namespace(n);
                    last_entity = None;
                }
                Item::Entity(e) => {
                    if !first { self.blank(); }
                    self.emit_standalone_entity(e, Some(ns));
                    last_entity = Some(self.resolve(&e.name));
                }
                Item::Operation(o) => {
                    // Collect orphan ops for module trait emission
                    orphan_ops.push(o);
                }
                Item::Fact(f) => {
                    self.emit_namespace_fact(f, last_entity.as_deref());
                }
                Item::Rule(_) | Item::RuleBlock(_) => {
                    // Collected later for test module
                }
                Item::Constraint(c) => {
                    if !first { self.blank(); }
                    self.emit_constraint(c);
                }
                Item::Const(c) => {
                    if !first { self.blank(); }
                    self.emit_const(c, false);
                }
                _ => {}
            }
            first = false;
        }

        // Emit module trait for orphan operations (compilable mode only)
        if !orphan_ops.is_empty() {
            self.blank();
            self.emit_module_trait(ns, &orphan_ops);
        }

        // Test module for namespace-level rules
        let rules = collect_rules(&ns.items);
        if !rules.is_empty() {
            self.blank();
            self.emit_test_module(&rules);
        }

        if !flatten {
            self.dedent();
            self.line("}");
        }
    }

    fn collect_sort_names(&self, items: &[Item]) -> Vec<String> {
        items.iter().filter_map(|item| {
            match item {
                Item::SortWithBody(s) => Some(self.resolve(&s.name)),
                Item::AbstractSort(s) => Some(self.resolve(&s.name)),
                _ => None,
            }
        }).collect()
    }

    fn collect_body_sort_names(&self, items: &[Item]) -> Vec<String> {
        items.iter().filter_map(|item| {
            if let Item::SortWithBody(s) = item { Some(self.resolve(&s.name)) } else { None }
        }).collect()
    }

    fn collect_entity_names(&self, items: &[Item]) -> Vec<String> {
        items.iter().filter_map(|item| {
            if let Item::Entity(e) = item { Some(self.resolve(&e.name)) } else { None }
        }).collect()
    }

    /// Emit an abstract sort (no body) as a trait with aggregated namespace-level operations.
    fn emit_abstract_sort_as_trait(
        &mut self,
        sort: &AbstractSort,
        ops: &[&Operation],
        supertraits: &[String],
    ) {
        let vis = self.visibility_prefix(sort.visibility);
        let sort_name = self.resolve(&sort.name);
        self.trait_sorts.insert(sort_name.clone());

        let supertrait_clause = if supertraits.is_empty() {
            String::new()
        } else {
            format!(": {}", supertraits.join(" + "))
        };

        self.line(&format!("{vis}trait {sort_name}{supertrait_clause} {{"));
        self.indent();

        let mut first_op = true;
        for op in ops {
            if !first_op { self.blank(); }
            self.emit_trait_method(op, &sort_name, &[], false);
            first_op = false;
        }

        self.dedent();
        self.line("}");
    }

    /// Emit a sort with body plus extra namespace-level operations and supertraits.
    fn emit_sort_with_extras(
        &mut self,
        sort: &SortWithBody,
        extra_ops: &[&Operation],
        extra_supers: &[String],
    ) {
        // Emit sort-level imports (if the sort has its own imports)
        for imp in &sort.imports {
            self.emit_import(imp);
        }
        if !sort.imports.is_empty() {
            self.blank();
        }

        let sort_name = self.resolve(&sort.name);
        let mut info = SortInfo::from_items(&sort.items, self.symbols, self.terms);

        // Add extra namespace-level operations and supertraits
        for op in extra_ops {
            info.operations.push(op);
        }
        for s in extra_supers {
            if !info.supertraits.contains(s) {
                info.supertraits.push(s.clone());
            }
        }

        if !info.entities.is_empty() {
            self.emit_sort_as_enum(sort, &sort_name, &info);
        } else if !info.operations.is_empty() {
            self.emit_sort_as_trait(sort, &sort_name, &info);
        }

        // Emit sub-namespaces
        for sub_ns in &info.sub_namespaces {
            self.blank();
            self.emit_namespace(sub_ns);
        }
    }

    fn emit_import(&mut self, imp: &Import) {
        let mut segments: Vec<String> = imp.path.segments.iter()
            .map(|s| to_snake_case(&self.resolve_sym(*s)))
            .collect();

        // Apply namespace_map: if the first segment matches a key, replace it
        if let Some(first) = segments.first() {
            if let Some(replacement) = self.config.namespace_map.get(first.as_str()) {
                segments[0] = replacement.clone();
            }
        }

        if self.config.emit_fn_bodies {
            self.line("#[allow(unused_imports)]");
        }

        match &imp.kind {
            ImportKind::Plain => {
                let path = segments.join("::");
                self.line(&format!("use {path};"));
            }
            ImportKind::Selective(names) => {
                let path = segments.join("::");
                let selected: Vec<String> = names.iter()
                    .map(|n| self.resolve(n))
                    .collect();
                self.line(&format!("use {}::{{{}}};", path, selected.join(", ")));
            }
            ImportKind::Wildcard => {
                let path = segments.join("::");
                self.line(&format!("use {path}::*;"));
            }
        }
    }

    // ── Standalone entity → struct ───────────────────────────────

    fn emit_standalone_entity(&mut self, entity: &Entity, _enclosing_ns: Option<&Namespace>) {
        let vis = self.visibility_prefix(entity.visibility);
        let name = self.resolve(&entity.name);

        self.emit_derive_attr();
        if entity.fields.is_empty() {
            self.line(&format!("{vis}struct {name};"));
        } else {
            self.line(&format!("{vis}struct {name} {{"));
            self.indent();
            for field in &entity.fields {
                let fname = to_snake_case(&self.resolve_sym(field.name));
                let ftype = self.type_to_rust(&field.ty);
                self.line(&format!("pub {fname}: {ftype},"));
            }
            self.dedent();
            self.line("}");
        }
    }

    // ── Sort → enum or trait ─────────────────────────────────────

    fn emit_sort(&mut self, sort: &SortWithBody) {
        // Emit sort-level imports (e.g. from `sort a.b.C` with imports inside)
        for imp in &sort.imports {
            self.emit_import(imp);
        }
        if !sort.imports.is_empty() {
            self.blank();
        }

        let sort_name = self.resolve(&sort.name);
        let info = SortInfo::from_items(&sort.items, self.symbols, self.terms);

        if !info.entities.is_empty() {
            self.emit_sort_as_enum(sort, &sort_name, &info);
        } else if !info.operations.is_empty() {
            self.emit_sort_as_trait(sort, &sort_name, &info);
        } else if !info.consts.is_empty() {
            // WI-533: a const-only sort (no entities, no operations) has no enum
            // or trait to carry its consts — emit a unit struct + inherent impl
            // rather than silently dropping them.
            self.emit_sort_as_const_holder(sort, &sort_name, &info);
        }
        // Sort with no constructors, operations, or consts — skip
        // (abstract sort used as trait name by other sorts)

        // Emit sub-namespaces (nested namespaces inside sorts)
        for sub_ns in &info.sub_namespaces {
            self.blank();
            self.emit_namespace(sub_ns);
        }
    }

    /// A sort whose only members are term-level consts (WI-533): no entities
    /// (not an enum) and no operations (not a trait). Emit a unit struct plus
    /// an inherent impl carrying the associated consts.
    fn emit_sort_as_const_holder(&mut self, sort: &SortWithBody, sort_name: &str, info: &SortInfo) {
        let vis = self.visibility_prefix(sort.visibility);
        self.line(&format!("{vis}struct {sort_name};"));
        self.blank();
        self.line(&format!("impl {sort_name} {{"));
        self.indent();
        for c in &info.consts {
            self.emit_const(c, false);
        }
        self.dedent();
        self.line("}");
    }

    fn emit_sort_as_enum(&mut self, sort: &SortWithBody, sort_name: &str, info: &SortInfo) {
        let vis = self.visibility_prefix(sort.visibility);

        // Generic parameters
        let generics = if info.type_params.is_empty() {
            String::new()
        } else {
            format!("<{}>", info.type_params.join(", "))
        };

        self.emit_derive_attr();
        self.line(&format!("{vis}enum {sort_name}{generics} {{"));
        self.indent();

        for entity in &info.entities {
            let ename = to_pascal_case(&self.resolve(&entity.name));
            if entity.fields.is_empty() {
                self.line(&format!("{ename},"));
            } else {
                self.line(&format!("{ename} {{"));
                self.indent();
                for field in &entity.fields {
                    let fname = to_snake_case(&self.resolve_sym(field.name));
                    let ftype = self.type_to_rust_for_enum_field(
                        &field.ty, sort_name, &info.type_params,
                    );
                    self.line(&format!("{fname}: {ftype},"));
                }
                self.dedent();
                self.line("},");
            }
        }

        self.dedent();
        self.line("}");

        // WI-533: sort-body consts on an enum sort → inherent `impl` associated
        // consts (an enum has no trait body to hang them on).
        if !info.consts.is_empty() {
            self.blank();
            self.line(&format!("impl{generics} {sort_name}{generics} {{"));
            self.indent();
            for c in &info.consts {
                self.emit_const(c, false);
            }
            self.dedent();
            self.line("}");
        }

        // If there are operations, emit an impl block (skeleton mode only).
        // In compilable mode, impl methods need hand-written implementations.
        if !info.operations.is_empty() && !self.config.emit_fn_bodies {
            self.blank();
            self.line(&format!("impl{generics} {sort_name}{generics} {{"));
            self.indent();
            let mut first_op = true;
            for op in &info.operations {
                if !first_op { self.blank(); }
                self.emit_method_signature(op, sort_name, &info.type_params, true);
                first_op = false;
            }
            self.dedent();
            self.line("}");
        }

        // Rules → test module
        if !info.rules.is_empty() {
            self.blank();
            self.emit_test_module(&info.rules);
        }

        // Constraints
        for c in &info.constraints {
            self.blank();
            self.emit_constraint(c);
        }
    }

    fn emit_sort_as_trait(&mut self, sort: &SortWithBody, sort_name: &str, info: &SortInfo) {
        self.trait_sorts.insert(sort_name.to_owned());
        let vis = self.visibility_prefix(sort.visibility);

        // Self-collapse heuristic: if exactly one type param and every op's
        // first param type matches it → collapse to Self, don't emit generic
        let collapse_self = should_collapse_self(info, self.symbols);

        // Determine trait generics (non-collapsed type params)
        let trait_generics = if collapse_self {
            String::new()
        } else if info.type_params.is_empty() {
            String::new()
        } else {
            format!("<{}>", info.type_params.join(", "))
        };

        // Supertraits
        let supertrait_clause = if info.supertraits.is_empty() {
            String::new()
        } else {
            format!(": {}", info.supertraits.join(" + "))
        };

        self.line(&format!("{vis}trait {sort_name}{trait_generics}{supertrait_clause} {{"));
        self.indent();

        // WI-533: sort-body consts become trait associated consts, emitted
        // before the methods (matching source order, where a sentinel const
        // precedes the operations).
        for c in &info.consts {
            self.emit_const(c, true);
        }
        if !info.consts.is_empty() && !info.operations.is_empty() {
            self.blank();
        }

        let mut first_op = true;
        for op in &info.operations {
            if !first_op { self.blank(); }
            self.emit_trait_method(op, sort_name, &info.type_params, collapse_self);
            first_op = false;
        }

        self.dedent();
        self.line("}");

        // Rules → test module
        if !info.rules.is_empty() {
            self.blank();
            self.emit_test_module(&info.rules);
        }

        // Constraints
        for c in &info.constraints {
            self.blank();
            self.emit_constraint(c);
        }
    }

    /// Map a type for an enum field, boxing self-referential fields.
    fn type_to_rust_for_enum_field(
        &self,
        ty: &TypeExpr,
        sort_name: &str,
        type_params: &[String],
    ) -> String {
        let rust_type = self.type_to_rust(ty);
        let type_name = self.type_expr_short_name(ty);
        if type_name == sort_name {
            // Self-referential → Box
            let generics = if type_params.is_empty() {
                String::new()
            } else {
                format!("<{}>", type_params.join(", "))
            };
            format!("Box<{sort_name}{generics}>")
        } else {
            // Map type params to their names as-is (they are generic)
            if type_params.contains(&type_name) {
                type_name
            } else {
                rust_type
            }
        }
    }

    // ── Method/function signature emission ────────────────────────

    fn emit_trait_method(
        &mut self,
        op: &Operation,
        sort_name: &str,
        type_params: &[String],
        collapse_self: bool,
    ) {
        let op_name = to_snake_case(&self.resolve(&op.name));
        let effects = analyze_effects(&op.effects, self.symbols, type_params);

        // Determine self-arg
        let (has_self, is_mut) = self.check_self_arg(op, sort_name, type_params, &effects, collapse_self);

        let mut params_str = String::new();

        if has_self {
            if is_mut {
                params_str.push_str("&mut self");
            } else {
                params_str.push_str("&self");
            }
        }

        // Remaining params (skip first if it became self)
        let skip = if has_self { 1 } else { 0 };
        for param in op.params.iter().skip(skip) {
            if !params_str.is_empty() {
                params_str.push_str(", ");
            }
            let pname = to_snake_case(&self.resolve_sym(param.name));
            let ptype = self.type_to_rust_in_sort(&param.ty, sort_name, type_params, collapse_self);
            // Non-self params of sort type or type-param type get &-ref
            let ptype = if should_ref_param(&ptype) {
                format!("&{ptype}")
            } else {
                ptype
            };
            params_str.push_str(&format!("{pname}: {ptype}"));
        }

        // Return type
        let raw_ret = self.type_to_rust_in_sort(&op.return_type, sort_name, type_params, collapse_self);
        let raw_ret = self.wrap_trait_return(&raw_ret);
        let ret = wrap_return_type(&raw_ret, &effects);

        self.line(&format!("fn {op_name}({params_str}) -> {ret};"));
    }

    fn emit_method_signature(
        &mut self,
        op: &Operation,
        sort_name: &str,
        type_params: &[String],
        in_impl: bool,
    ) {
        let vis = if in_impl { self.visibility_prefix(op.visibility) } else { "" };
        let op_name = to_snake_case(&self.resolve(&op.name));
        let effects = analyze_effects(&op.effects, self.symbols, type_params);

        let (has_self, is_mut) = self.check_self_arg(op, sort_name, type_params, &effects, false);

        let mut params_str = String::new();

        if has_self {
            if is_mut {
                params_str.push_str("&mut self");
            } else {
                params_str.push_str("&self");
            }
        }

        let skip = if has_self { 1 } else { 0 };
        for param in op.params.iter().skip(skip) {
            if !params_str.is_empty() {
                params_str.push_str(", ");
            }
            let pname = to_snake_case(&self.resolve_sym(param.name));
            let ptype = self.type_to_rust_in_sort(&param.ty, sort_name, type_params, false);
            params_str.push_str(&format!("{pname}: {ptype}"));
        }

        let raw_ret = self.type_to_rust_in_sort(&op.return_type, sort_name, type_params, false);
        let raw_ret = self.wrap_trait_return(&raw_ret);
        let ret = wrap_return_type(&raw_ret, &effects);

        self.line(&format!("{vis}fn {op_name}({params_str}) -> {ret};"));
    }

    /// Emit a module trait collecting orphan operations.
    ///
    /// Operations that don't match any sort/entity for self-arg (Rule 3) are
    /// collected into a trait named `{Namespace}Ops` with `&self` on each method.
    fn emit_module_trait(&mut self, ns: &Namespace, ops: &[&Operation]) {
        let ns_name = self.resolve(&ns.name);
        let trait_name = format!("{}Ops", to_pascal_case(&ns_name));
        let vis = self.visibility_prefix(None);

        self.line(&format!("{vis}trait {trait_name} {{"));
        self.indent();

        let mut first = true;
        for op in ops {
            if !first { self.blank(); }
            self.emit_module_trait_method(op);
            first = false;
        }

        self.dedent();
        self.line("}");
    }

    /// Emit a single method inside a module trait.
    ///
    /// Like `emit_trait_method` but always adds `&self` as receiver and keeps
    /// all original params (no sort-name matching for self-collapse).
    fn emit_module_trait_method(&mut self, op: &Operation) {
        let op_name = to_snake_case(&self.resolve(&op.name));
        let effects = analyze_effects(&op.effects, self.symbols, &[]);

        let mut params_str = String::from("&self");

        for param in &op.params {
            params_str.push_str(", ");
            let pname = to_snake_case(&self.resolve_sym(param.name));
            let ptype = self.type_to_rust(&param.ty);
            params_str.push_str(&format!("{pname}: {ptype}"));
        }

        let raw_ret = self.type_to_rust(&op.return_type);
        let raw_ret = self.wrap_trait_return(&raw_ret);
        let ret = wrap_return_type(&raw_ret, &effects);

        self.line(&format!("fn {op_name}({params_str}) -> {ret};"));
    }

    /// Check if the first param should become self.
    fn check_self_arg(
        &self,
        op: &Operation,
        sort_name: &str,
        type_params: &[String],
        effects: &EffectInfo,
        collapse_type_params: bool,
    ) -> (bool, bool) {
        if op.params.is_empty() {
            return (false, false);
        }

        let first_type_name = self.type_expr_short_name(&op.params[0].ty);

        // Check if first param type matches the sort name or a type param
        let is_self = first_type_name == sort_name
            || (collapse_type_params && type_params.iter().any(|p| p == &first_type_name));

        if !is_self {
            return (false, false);
        }

        // Check if the first param is the target of a Modifies effect
        let first_param_name = self.resolve_sym(op.params[0].name);
        let is_mut = effects.modifies_targets.iter().any(|t| t == &first_param_name);

        (true, is_mut)
    }

    fn type_expr_short_name(&self, ty: &TypeExpr) -> String {
        type_expr_name(self.symbols, ty)
    }

    // ── Namespace fact → impl marker comment ─────────────────────

    fn emit_namespace_fact(&mut self, fact: &Fact, preceding_entity: Option<&str>) {
        let entity_name = match preceding_entity {
            Some(name) => name,
            None => return,
        };

        let trait_name = match extract_fact_sort_name(self.symbols, self.terms, fact) {
            Some(n) => n,
            None => return,
        };

        self.line(&format!("// impl {trait_name} for {entity_name}"));
    }

    // ── Constraint → check function ──────────────────────────────

    fn emit_constraint(&mut self, constraint: &Constraint) {
        if let Some(label) = &constraint.label {
            let label_name = to_snake_case(&self.resolve(label));
            self.line(&format!("fn check_{label_name}() -> bool {{"));
            self.indent();
            self.line(&format!("todo!(\"invariant: {label_name}\")"));
            self.dedent();
            self.line("}");
        }
    }

    // ── Rules → test module ──────────────────────────────────────

    fn emit_test_module(&mut self, rules: &[&Rule]) {
        let labeled: Vec<_> = rules.iter()
            .filter(|r| r.label.is_some())
            .collect();

        if labeled.is_empty() {
            return;
        }

        self.line("#[cfg(test)]");
        self.line("mod tests {");
        self.indent();
        self.line("use super::*;");

        for rule in &labeled {
            self.blank();
            let label = rule.label.as_ref().unwrap();
            let label_name = to_snake_case(&self.resolve(label));
            self.line("#[test]");
            self.line(&format!("fn prop_{label_name}() {{"));
            self.indent();
            self.line(&format!("todo!(\"property: {label_name}\")"));
            self.dedent();
            self.line("}");
        }

        self.dedent();
        self.line("}");
    }
}

// ── Effect analysis ──────────────────────────────────────────────

struct EffectInfo {
    modifies_targets: Vec<String>,
    errors_type: Option<String>,
}

fn analyze_effects(effects: &[Effect], symbols: &SymbolTable, type_params: &[String]) -> EffectInfo {
    let mut info = EffectInfo {
        modifies_targets: Vec::new(),
        errors_type: None,
    };

    for effect in effects {
        match &effect.type_expr {
            TypeExpr::Parameterized { name, bindings } => {
                let kind = symbols.name(name.last());
                // Extract target from first binding's bound value
                let target = if let Some(b) = bindings.first() {
                    match &b.bound {
                        TypeExpr::Simple(n) => symbols.name(n.last()).to_owned(),
                        _ => continue,
                    }
                } else {
                    continue;
                };

                match kind {
                    "Modify" => {
                        info.modifies_targets.push(target);
                    }
                    "Error" => {
                        info.errors_type = Some(map_primitive_type(&target));
                    }
                    _ => {}
                }
            }
            TypeExpr::Simple(name) => {
                let kind = symbols.name(name.last());
                match kind {
                    "Error" => {
                        // Bare Error (no type param) → Result<R, Error>
                        info.errors_type = Some("Error".to_owned());
                    }
                    _ => {
                        // Abstract effect: if the name is a type parameter of the
                        // enclosing sort, treat it as an abstract error type.
                        // E.g. `effects (E)` where `sort E = ?` → Result<R, E>
                        if type_params.contains(&kind.to_owned()) {
                            info.errors_type = Some(kind.to_owned());
                        }
                    }
                }
            }
            TypeExpr::Variable { .. } => {}
            TypeExpr::Tuple(_) => {}
            TypeExpr::Arrow { .. } => {}
            TypeExpr::Denoted(_) => {}
            // WI-327: `-E` doesn't contribute Modify/Error analysis.
            TypeExpr::EffectAbsent(_) => {}
            // WI-375: a written effect-row in a type-arg slot is not an
            // operation effects-clause — no Modify/Error contribution here.
            TypeExpr::EffectRow(_) => {}
        }
    }

    info
}

fn wrap_return_type(raw: &str, effects: &EffectInfo) -> String {
    if let Some(err_type) = &effects.errors_type {
        format!("Result<{raw}, {err_type}>")
    } else {
        raw.to_owned()
    }
}

// ── Self-collapse heuristic ──────────────────────────────────────

fn should_collapse_self(info: &SortInfo, symbols: &SymbolTable) -> bool {
    if info.type_params.len() != 1 {
        return false;
    }

    let param_name = &info.type_params[0];

    // Check every operation: its first param type must match the type param
    if info.operations.is_empty() {
        return false;
    }

    for op in &info.operations {
        if op.params.is_empty() {
            // Operations with no params can still be in a collapsed trait
            // (like zero_val() -> T)
            continue;
        }

        let first_type = match &op.params[0].ty {
            TypeExpr::Simple(name) => symbols.name(name.last()).to_owned(),
            TypeExpr::Parameterized { name, .. } => symbols.name(name.last()).to_owned(),
            TypeExpr::Variable { .. } => "T".to_owned(),
            TypeExpr::Tuple(_) => "Tuple".to_owned(),
            TypeExpr::Arrow { .. } => "Fn".to_owned(),
            TypeExpr::Denoted(_) => "Denoted".to_owned(),
            TypeExpr::EffectAbsent(_) => "EffectAbsent".to_owned(),
            TypeExpr::EffectRow(_) => "EffectRow".to_owned(),
        };

        if first_type != *param_name {
            return false;
        }
    }

    true
}

// ── Utility functions ────────────────────────────────────────────

/// Rust expression for a bodyless host-supplied Float const (WI-532). Mirrors
/// cpp-gen's `render_as_float_special`. Matched by short name (rust.rs runs on
/// the raw ParsedFile, before name resolution), gated by the caller on an `f64`
/// declared type so a non-Float same-named const can't collide.
fn host_float_const_rust(name: &str) -> Option<&'static str> {
    match name {
        "infinity" => Some("f64::INFINITY"),
        "negativeInfinity" => Some("f64::NEG_INFINITY"),
        "nan" => Some("f64::NAN"),
        _ => None,
    }
}

/// Render a literal term as a Rust constant expression of type `rust_ty`
/// (WI-533). A value that would read as an integer but whose const is `f64`
/// gets a `.0` suffix so it keeps the float type (anthill admits an integer
/// literal for a `Float` const; Rust does not coerce). String literals use
/// Rust's debug escaping.
fn lower_literal_rust(lit: &Literal, rust_ty: &str) -> String {
    let float_target = rust_ty == "f64" || rust_ty == "f32";
    let with_point = |s: String| -> String {
        if float_target && !(s.contains('.') || s.contains('e') || s.contains('E')) {
            format!("{s}.0")
        } else {
            s
        }
    };
    match lit {
        Literal::Int(n) => with_point(n.to_string()),
        Literal::BigInt(n) => with_point(n.to_string()),
        Literal::Float(f) => with_point(f.into_inner().to_string()),
        Literal::Bool(b) => b.to_string(),
        Literal::String(s) => format!("{s:?}"),
        Literal::Handle(kind, id) => format!("/* handle {kind:?}:{id} */"),
    }
}

fn map_primitive_type(name: &str) -> String {
    match name {
        "Int64" => "i64".to_owned(),
        "Float" => "f64".to_owned(),
        "Bool" => "bool".to_owned(),
        "String" => "String".to_owned(),
        "Duration" => "std::time::Duration".to_owned(),
        "Timestamp" => "String".to_owned(),
        "Term" => "Term".to_owned(),
        "Meta" => "Meta".to_owned(),
        "FactId" => "FactId".to_owned(),
        _ => name.to_owned(),
    }
}

fn to_snake_case(s: &str) -> String {
    let mut result = String::with_capacity(s.len() + 4);
    let mut prev_was_upper = false;
    let mut prev_was_sep = false;

    for (i, c) in s.chars().enumerate() {
        if c == '-' || c == '_' {
            if !result.is_empty() {
                result.push('_');
            }
            prev_was_sep = true;
            prev_was_upper = false;
            continue;
        }

        if c.is_uppercase() {
            if i > 0 && !prev_was_upper && !prev_was_sep {
                result.push('_');
            }
            result.push(c.to_lowercase().next().unwrap());
            prev_was_upper = true;
        } else {
            result.push(c);
            prev_was_upper = false;
        }
        prev_was_sep = false;
    }

    escape_rust_keyword(result)
}

/// Wrap a generated identifier as a raw identifier (`r#name`) when it collides
/// with a Rust keyword, so codegen output stays compilable (e.g. an anthill
/// field named `type`). The few keywords that can't be raw (`crate` / `self` /
/// `super` / `Self`) get a trailing underscore instead.
fn escape_rust_keyword(name: String) -> String {
    const RESERVED: &[&str] = &[
        "as", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern", "false", "fn",
        "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
        "return", "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe",
        "use", "where", "while", "async", "await", "abstract", "become", "box", "do", "final",
        "macro", "override", "priv", "typeof", "unsized", "virtual", "yield", "try",
    ];
    match name.as_str() {
        "crate" | "self" | "super" | "Self" => format!("{name}_"),
        n if RESERVED.contains(&n) => format!("r#{name}"),
        _ => name,
    }
}

/// Extract a sort name from a fact term (for fact-as-supertrait pattern).
fn extract_fact_sort_name(symbols: &SymbolTable, terms: &SimpleTermStore, fact: &Fact) -> Option<String> {
    match terms.get(fact.term) {
        Term::Ident(sym) => Some(symbols.name(*sym).to_owned()),
        Term::Fn { functor, .. } => {
            Some(symbols.name(*functor).to_owned())
        }
        _ => None,
    }
}

/// Get the short name from a TypeExpr.
fn type_expr_name(symbols: &SymbolTable, ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Simple(name) => symbols.name(name.last()).to_owned(),
        TypeExpr::Parameterized { name, .. } => symbols.name(name.last()).to_owned(),
        TypeExpr::Variable { .. } => "T".to_owned(),
        TypeExpr::Tuple(_) => "Tuple".to_owned(),
        TypeExpr::Arrow { .. } => "Fn".to_owned(),
        TypeExpr::Denoted(_) => "Denoted".to_owned(),
        TypeExpr::EffectAbsent(_) => "EffectAbsent".to_owned(),
        TypeExpr::EffectRow(_) => "EffectRow".to_owned(),
    }
}

/// Collect all rules from a list of items.
fn collect_rules(items: &[Item]) -> Vec<&Rule> {
    let mut rules = Vec::new();
    for item in items {
        match item {
            Item::Rule(r) => rules.push(r),
            Item::RuleBlock(rb) => {
                for r in &rb.entries {
                    rules.push(r);
                }
            }
            _ => {}
        }
    }
    rules
}

/// Whether a parameter type should be passed by reference.
fn should_ref_param(ty: &str) -> bool {
    matches!(ty, "Self")
}

fn to_pascal_case(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut capitalize_next = true;
    for c in s.chars() {
        if c == '-' || c == '_' {
            capitalize_next = true;
            continue;
        }
        if capitalize_next {
            for uc in c.to_uppercase() {
                result.push(uc);
            }
            capitalize_next = false;
        } else {
            result.push(c);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_snake_case() {
        assert_eq!(to_snake_case("WorkStatus"), "work_status");
        assert_eq!(to_snake_case("FileStore"), "file_store");
        assert_eq!(to_snake_case("zero-val"), "zero_val");
        assert_eq!(to_snake_case("sqlDialect"), "sql_dialect");
        assert_eq!(to_snake_case("already_snake"), "already_snake");
        assert_eq!(to_snake_case("simple"), "simple");
    }

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("stage0"), "Stage0");
        assert_eq!(to_pascal_case("by_namespace"), "ByNamespace");
        assert_eq!(to_pascal_case("flat"), "Flat");
        assert_eq!(to_pascal_case("kb"), "Kb");
        assert_eq!(to_pascal_case("Postgresql"), "Postgresql");
        assert_eq!(to_pascal_case("kebab-case"), "KebabCase");
    }

    #[test]
    fn test_map_primitive_type() {
        assert_eq!(map_primitive_type("Int64"), "i64");
        assert_eq!(map_primitive_type("Float"), "f64");
        assert_eq!(map_primitive_type("Bool"), "bool");
        assert_eq!(map_primitive_type("String"), "String");
        assert_eq!(map_primitive_type("Duration"), "std::time::Duration");
        assert_eq!(map_primitive_type("Timestamp"), "String");
        assert_eq!(map_primitive_type("MyType"), "MyType");
    }
}
