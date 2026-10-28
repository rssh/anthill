/// Rust code generation from anthill parse IR.
///
/// Walks a `ParsedFile` and emits Rust skeleton code (traits, structs, enums,
/// function signatures). All generated code is bodyless — users provide
/// implementations separately.
///
/// See `docs/rust-forward-mapping.md` for the full mapping specification.
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use super::type_template::{parse_type_template, TypeTemplatePart};
use crate::intern::{Symbol, SymbolTable};
use crate::kb::term::{Literal, Term, TermId};
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
#[derive(Clone)]
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
    /// Render a trait-typed position as a trait OBJECT rather than `impl Trait`
    /// (WI-540): a return / field becomes `Box<dyn Trait<…>>` and a non-receiver
    /// parameter `&dyn Trait`, instead of `impl Trait` (returns) or a bare trait
    /// name (params, which is invalid Rust). This keeps a generated trait
    /// object-safe — required for a host `&dyn KB` and for a recursive `Stream`
    /// (`tail -> Stream`) or a trait-typed enum field (`Solution.definite(subst:
    /// Substitution)`). Off by default → existing skeleton output is unchanged.
    pub boxed_trait_objects: bool,
    /// Emit ONLY the named top-level items (WI-540): when `Some`, a sort / enum /
    /// entity whose short name is not in the set is skipped, and the synthesized
    /// namespace-level free-op "module trait" is omitted entirely. Used to
    /// generate just the KB-bridge subset of `reflect.anthill` (the `KB` /
    /// `Substitution` traits + `Solution` / `LogicalQuery` / introspection data
    /// types) without the occurrence IR or the free reflect ops. `None` →
    /// everything is emitted (existing behavior).
    pub emit_only: Option<Vec<String>>,
    /// Skip emitting `use` statements for the source's `import`s. The codegen is
    /// signature-only (no expression lowering), so an anthill sort's body/rule
    /// imports — value constructors (`Option.{some, none}`), arithmetic
    /// (`Numeric.{sub, add}`), or marker sorts (`Iterable`/`Modify`) — are
    /// vestigial in the generated interface and may not even resolve to a host
    /// item (e.g. `crate::prelude::option`). Set this when the including module
    /// supplies the few imports the signatures actually need (the `Stream`
    /// shim provides `Pair`). Off by default → imports emitted as before.
    pub suppress_imports: bool,
}

impl CodegenConfig {
    /// Whether a top-level item named `name` should be emitted under
    /// [`Self::emit_only`] (always true when the filter is `None`).
    fn emits(&self, name: &str) -> bool {
        match &self.emit_only {
            None => true,
            Some(names) => names.iter().any(|n| n == name),
        }
    }
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
            boxed_trait_objects: false,
            emit_only: None,
            suppress_imports: false,
        }
    }
}

/// Generate Rust skeleton code from a parsed anthill file.
pub fn generate_rust(parsed: &ParsedFile) -> Result<String, Vec<CodegenError>> {
    generate_rust_with_context(parsed, &collect_sorts(&[parsed]))
}

/// Generate Rust code for one file of a run whose files declare `catalog`
/// ([`collect_sorts`] over all of them).
pub fn generate_rust_with_context(
    parsed: &ParsedFile,
    catalog: &SortCatalog,
) -> Result<String, Vec<CodegenError>> {
    let config = CodegenConfig::default();
    generate_rust_with_config(parsed, catalog, &config)
}

/// Generate Rust code with full configuration control.
///
/// Used by build scripts to produce compilable output with import remapping,
/// carrier bindings, derive macros, etc.
pub fn generate_rust_with_config(
    parsed: &ParsedFile,
    catalog: &SortCatalog,
    config: &CodegenConfig,
) -> Result<String, Vec<CodegenError>> {
    let mut cg = RustCodegen::with_context(&parsed.symbols, &parsed.terms, catalog, config);
    cg.push_scope(String::new(), &parsed.imports, Vec::new());
    // WI-853: a file's TOP-LEVEL imports emit their `use` lines here, where a
    // namespace body's are emitted by `emit_namespace`. Both spell one anthill
    // `import` as one Rust `use`; dropping the top-level ones would generate a
    // module whose names silently do not resolve.
    let mut wrote_use = false;
    for imp in &parsed.imports {
        wrote_use |= cg.emit_import(imp);
    }
    if wrote_use && !parsed.items.is_empty() {
        cg.blank();
    }
    cg.emit_items(&parsed.items, None);
    let errors = cg.errors.into_inner();
    if errors.is_empty() {
        Ok(cg.output)
    } else {
        Err(errors)
    }
}

/// Every sort the files generated together declare, by qualified name: what a written
/// type name resolves to when it is not a type parameter, and how its arguments are
/// ordered and wrapped.
///
/// A file of the run sees the sorts of every other: `sort Api` in one file returning a
/// `Boom` declared in another renders `Boom` with `Boom`'s own parameter order. A sort
/// declared in no file of the run has no order to render its arguments in.
#[derive(Clone, Default)]
pub struct SortCatalog {
    sorts: HashMap<String, CatalogSort>,
}

#[derive(Clone)]
struct CatalogSort {
    /// The sort's type parameters, in declaration order.
    params: Vec<String>,
    /// Whether the sort generates as a trait: it has operations and no entities (the
    /// same heuristic single-file emission uses), so a reference to it from another
    /// file is wrapped as one (`impl Trait`).
    is_trait: bool,
}

/// Collect the sorts the files of one run declare ([`SortCatalog`]).
pub fn collect_sorts(files: &[&ParsedFile]) -> SortCatalog {
    let mut catalog = SortCatalog::default();
    for file in files {
        collect_sorts_from_items(&file.items, &file.symbols, "", false, &mut catalog);
    }
    catalog
}

/// `in_sort` — `items` are a sort's body, whose `sort T = ?` members are its type
/// parameters rather than sorts.
fn collect_sorts_from_items(
    items: &[Item],
    symbols: &SymbolTable,
    prefix: &str,
    in_sort: bool,
    catalog: &mut SortCatalog,
) {
    for item in items {
        match item {
            Item::SortWithBody(s) => {
                let qualified = qualify(prefix, &name_text(symbols, &s.name));
                let params = s
                    .items
                    .iter()
                    .filter_map(|i| match i {
                        Item::AbstractSort(p) => Some(symbols.local_name(p.name.last()).to_owned()),
                        _ => None,
                    })
                    .collect();
                let has_ops = s
                    .items
                    .iter()
                    .any(|i| matches!(i, Item::Operation(_) | Item::OperationBlock(_)));
                let has_entities = s.items.iter().any(|i| matches!(i, Item::Entity(_)));
                catalog.sorts.insert(
                    qualified.clone(),
                    CatalogSort {
                        params,
                        is_trait: has_ops && !has_entities,
                    },
                );
                // Nested items: sub-namespaces and nested sorts.
                collect_sorts_from_items(&s.items, symbols, &qualified, true, catalog);
            }
            // A sort declared at namespace level without a body. One written inside a
            // sort's body is a type parameter of that sort, and was read above.
            Item::AbstractSort(_) if in_sort => {}
            Item::AbstractSort(s) => {
                let qualified = qualify(prefix, &name_text(symbols, &s.name));
                catalog.sorts.insert(
                    qualified,
                    CatalogSort {
                        params: Vec::new(),
                        is_trait: false,
                    },
                );
            }
            // A free-standing entity is a struct, and a type.
            Item::Entity(e) => {
                let qualified = qualify(prefix, &name_text(symbols, &e.name));
                catalog.sorts.insert(
                    qualified,
                    CatalogSort {
                        params: Vec::new(),
                        is_trait: false,
                    },
                );
            }
            Item::Namespace(ns) => {
                let qualified = qualify(prefix, &name_text(symbols, &ns.name));
                collect_sorts_from_items(&ns.items, symbols, &qualified, false, catalog);
            }
            _ => {}
        }
    }
}

/// `name` as written, every segment joined with `.`.
fn name_text(symbols: &SymbolTable, name: &Name) -> String {
    name.segments
        .iter()
        .map(|s| symbols.local_name(*s))
        .collect::<Vec<_>>()
        .join(".")
}

/// `name` qualified by the scope `prefix` it is declared in (`""` at a file's top).
fn qualify(prefix: &str, name: &str) -> String {
    if prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{prefix}.{name}")
    }
}

/// How a sort of the standard library's prelude is written in Rust: the table
/// [`RUST_STDLIB_TYPES`] is the whole of what this generator knows about a prelude
/// sort, and a prelude sort it does not list is refused where a type names it.
struct RustStdlibType {
    qualified: &'static str,
    /// The anthill sort's type parameters, in its declaration order — what a written
    /// application's positional arguments are placed against.
    params: &'static [&'static str],
    /// The Rust type, as a template over `params` (`type_template`): each `$Name` is the
    /// argument that places `Name`, so `Result[E, T]` is `Result<$T, $E>`, and a
    /// parameter the Rust item does not take is left out (`LogicalStream<$T>`).
    template: &'static str,
    rendering: StdlibRendering,
}

enum StdlibRendering {
    /// A host type. The generated code names it and never the anthill sort, so no
    /// `use` is emitted for the sort or for a member of it.
    Host,
    /// A type the support crate's `prelude` exports under the sort's own name; `use`d
    /// like a sort of the program.
    Support { is_trait: bool },
}

/// The prelude sorts this generator writes, and how. The support crate is `anthill-stl`
/// (`anthill-stl/src/prelude/mod.rs` for the `Support` names).
///
/// `Duration` and `Timestamp` are host types here although `primitives.anthill`
/// declares them as sorts with constructors: that is what this generator has always
/// emitted for them, and `rust_std.anthill` says the same.
#[rustfmt::skip]
const RUST_STDLIB_TYPES: &[RustStdlibType] = &[
    stdlib_host("anthill.prelude.Int64", &[], "i64"),
    stdlib_host("anthill.prelude.BigInt", &[], "num_bigint::BigInt"),
    stdlib_host("anthill.prelude.Float", &[], "f64"),
    stdlib_host("anthill.prelude.Bool", &[], "bool"),
    stdlib_host("anthill.prelude.String", &[], "String"),
    stdlib_host("anthill.prelude.Unit", &[], "()"),
    stdlib_host("anthill.prelude.Duration", &[], "std::time::Duration"),
    stdlib_host("anthill.prelude.Timestamp", &[], "String"),
    stdlib_host("anthill.prelude.List", &["T"], "Vec<$T>"),
    stdlib_host("anthill.prelude.Option", &["T"], "Option<$T>"),
    stdlib_host("anthill.prelude.Result", &["E", "T"], "Result<$T, $E>"),
    stdlib_support("anthill.prelude.Pair", &["A", "B"], "Pair<$A, $B>", false),
    stdlib_support("anthill.prelude.Stream", &["T", "E"], "Stream<$T, $E>", true),
    stdlib_support("anthill.prelude.LogicalStream", &["T", "E"], "LogicalStream<$T>", true),
    stdlib_support("anthill.prelude.Meta.Meta", &[], "Meta", false),
    stdlib_support("anthill.prelude.Modifiable", &["T"], "Modifiable", true),
    stdlib_support("anthill.prelude.Type", &[], "Type", false),
    stdlib_support("anthill.prelude.TypeExtractor", &[], "TypeExtractor", false),
    stdlib_support("anthill.prelude.FieldOf", &["T", "Name"], "FieldOf", false),
];

const fn stdlib_host(
    qualified: &'static str,
    params: &'static [&'static str],
    template: &'static str,
) -> RustStdlibType {
    RustStdlibType {
        qualified,
        params,
        template,
        rendering: StdlibRendering::Host,
    }
}

const fn stdlib_support(
    qualified: &'static str,
    params: &'static [&'static str],
    template: &'static str,
    is_trait: bool,
) -> RustStdlibType {
    RustStdlibType {
        qualified,
        params,
        template,
        rendering: StdlibRendering::Support { is_trait },
    }
}

/// The namespace a bare name reaches without an import, and whose sorts this generator
/// writes only through [`RUST_STDLIB_TYPES`].
const PRELUDE: &str = "anthill.prelude";

fn stdlib_type(qualified: &str) -> Option<&'static RustStdlibType> {
    RUST_STDLIB_TYPES.iter().find(|t| t.qualified == qualified)
}

/// What a written type name denotes where it is written.
enum Denoted {
    /// The reserved `Self`.
    SelfType,
    /// A type parameter in scope: a sort's member, an operation's own, or one read off a
    /// value parameter (`s.T`).
    Param(String),
    /// A sort declared in a file of this run, by qualified name.
    Declared(String),
    /// A prelude sort [`RUST_STDLIB_TYPES`] lists.
    Stdlib(&'static RustStdlibType),
    /// A sort outside the prelude that no file of this run declares, by qualified name.
    External(String),
    /// A prelude sort the table does not list, by qualified name.
    UnmappedPrelude(String),
    /// A bare name nothing in scope declares or imports, which as a `public` prelude
    /// name (its qualified reading here) the table does not list either.
    NotFound(String),
}

/// The qualified name of the `Error` effect label, which a type position writes as its
/// payload (`Error[P]` is `P`).
const ERROR_LABEL: &str = "anthill.prelude.Error";

/// The qualified name of the `Modify` effect label.
const MODIFY_LABEL: &str = "anthill.prelude.Modify";

/// The `Error` payload an effects clause gives a signature: a written type, or a name
/// the generator writes as it is (bare `Error`, a sort's type parameter).
enum ErrorPayload<'t> {
    Type(&'t TypeExpr),
    Named(String),
}

/// A type rendered inside the sort being emitted ([`RustCodegen::type_to_rust_in_sort`]).
struct InSort<'p> {
    type_params: &'p [String],
    /// The single type parameter collapses to `Self` (`should_collapse_self`).
    collapse: bool,
}

/// The last segment of a qualified name.
fn short_of(qualified: &str) -> &str {
    qualified.rsplit('.').next().unwrap_or(qualified)
}

impl Denoted {
    /// The qualified name of the sort this resolves to, when it is one.
    fn qualified(&self) -> Option<&str> {
        match self {
            Denoted::Declared(q)
            | Denoted::External(q)
            | Denoted::UnmappedPrelude(q)
            | Denoted::NotFound(q) => Some(q),
            Denoted::Stdlib(t) => Some(t.qualified),
            Denoted::SelfType | Denoted::Param(_) => None,
        }
    }
}

/// One scope a name is resolved in, innermost last on [`RustCodegen::scopes`]: the file's
/// top level, a namespace, a sort, or an operation's signature.
struct Scope {
    /// The scope's qualified name (`""` at a file's top level, and an operation's
    /// signature adds none).
    prefix: String,
    /// Short name → the qualified name it imports.
    imports: HashMap<String, String>,
    /// Paths imported with `.*`.
    wildcards: Vec<String>,
    /// Type parameters declared here.
    params: Vec<String>,
    /// An operation's value parameters, whose members a type may name (`s.T`).
    value_params: Vec<String>,
}

// ── Sort analysis ────────────────────────────────────────────────

struct SortInfo<'a> {
    type_params: Vec<String>,
    /// Each of `type_params`' declared default (proposal 069 §1.4), in the same order.
    type_param_defaults: Vec<Option<&'a TypeExpr>>,
    supertraits: Vec<String>,
    entities: Vec<&'a Entity>,
    operations: Vec<&'a Operation>,
    rules: Vec<&'a Rule>,
    constraints: Vec<&'a Constraint>,
    consts: Vec<&'a Const>,
    sub_namespaces: Vec<&'a Namespace>,
}

impl<'a> SortInfo<'a> {
    fn from_items(items: &'a [Item], symbols: &SymbolTable) -> Self {
        let mut info = SortInfo {
            type_params: Vec::new(),
            type_param_defaults: Vec::new(),
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
                    info.type_params
                        .push(symbols.local_name(s.name.last()).to_owned());
                    info.type_param_defaults.push(s.default.as_ref());
                }
                Item::RequiresDecl(r) => {
                    // `effects E = ?` desugars to `requires
                    // anthill.prelude.EffectsRuntime[Effects=E]`, an effect-runtime
                    // kind-anchor with no host trait. Emitting it as a Rust supertrait
                    // (`trait Stream: EffectsRuntime`) would never resolve, so drop it;
                    // every other `requires` becomes a real supertrait. Match by the
                    // CANONICAL qualified name, not the short name — a user sort merely
                    // NAMED `EffectsRuntime` in another namespace must still become a
                    // supertrait (WI-703).
                    if type_expr_qualified_name(symbols, &r.type_expr)
                        != "anthill.prelude.EffectsRuntime"
                    {
                        info.supertraits.push(type_expr_name(symbols, &r.type_expr));
                    }
                }
                // WI-862 (058 §4) / WI-20260917-S8JYF — A SORT'S PROVISION IS WHAT A
                // SUPERTRAIT BOUND RENDERS, AND `provides` IS THE ONLY SPELLING OF ONE.
                // An `Item::Fact` arm stood beside this one and pushed a supertrait for
                // `sort NonMonotonicStore { fact Store }`; WI-862 added this arm because
                // migrating that line to `provides Store` had silently dropped `trait
                // NonMonotonicStore: Store` to a bare `trait NonMonotonicStore`
                // (`codegen_test::full_persistence_store_hierarchy`). The retirement
                // deletes the fact arm: a `fact` inside a sort is an ordinary fact and
                // asserts no is-a, so rendering one as a bound would be the mapper
                // asserting in Rust a relation the loader does not record.
                //
                // BARE SPECS ONLY, AND THE PARAMETERIZED CASE IS A KNOWN GAP — **WI-1108**.
                // A parameterized provision would render as the bare bound `: Iterable`,
                // dropping every binding. That is wrong Rust and it does not compile:
                // MEASURED by widening this arm to every provision, which made `stdlib`'s
                // pre-existing `sort Stream { provides Iterable[C = Stream, …] }` emit
                // `pub trait Stream<T, E>: Iterable` into a `suppress_imports: true`
                // file — whose whole premise (`anthill-stl/build.rs`, WI-553) is that
                // "the signature-only output never references" `Iterable` — and broke
                // the workspace build. The defect is the generator's, not the
                // retirement's. Rendering a parameterized supertrait needs its type
                // arguments AND its import, which is WI-587's territory, so it gets a
                // ticket rather than a guess here.
                // A CONDITIONAL provision is excluded for the same reason and under the
                // same ticket: `provides Store :- Backed[T = …]` (WI-869's tail) is not
                // an unconditional is-a, and `trait X: Store` asserts one — rendering it
                // would need a `where` clause the generator has no notion of.
                Item::ProvidesClause(pc)
                    if matches!(pc.spec, TypeExpr::Simple(_)) && pc.conditions.is_empty() =>
                {
                    info.supertraits.push(type_expr_name(symbols, &pc.spec));
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
    /// The sorts of the run's files, which written type names resolve to.
    catalog: &'a SortCatalog,
    /// Qualified names of the sorts that generate as traits (not enums/structs): the
    /// catalog's, and each one emitted as a trait. Used to wrap a trait-typed position
    /// (`impl Trait`, `Box<dyn Trait>`).
    trait_sorts: HashSet<String>,
    /// The scopes a written name is resolved in, innermost last.
    scopes: Vec<Scope>,
    /// The qualified name of the sort being emitted: a written name that resolves to it
    /// is the sort itself (`Self`).
    current_sort: Option<String>,
    config: &'a CodegenConfig,
    /// Collected rather than returned at each site: a type is rendered through `&self`.
    errors: RefCell<Vec<CodegenError>>,
    /// Names already `use`d into THIS file, keyed by `(path, name)`.
    ///
    /// ANTHILL IMPORTS ARE PER-DECLARATION AND RUST `use` IS PER-MODULE, and this
    /// is where the two currencies are reconciled. A generated file is one Rust
    /// scope, so two declarations that both `import anthill.prelude.{List}` emit
    /// two `use crate::prelude::{List};` and the file does not compile —
    /// E0252, "the name `List` is defined multiple times". Measured on
    /// `reflect.anthill` the moment `LoadFailed` joined the emitted set: its
    /// `import anthill.prelude.{List, String}` collided with the `{List}` an
    /// earlier declaration had already emitted.
    imported: HashSet<(String, String)>,
}

impl<'a> RustCodegen<'a> {
    fn with_context(
        symbols: &'a SymbolTable,
        terms: &'a SimpleTermStore,
        catalog: &'a SortCatalog,
        config: &'a CodegenConfig,
    ) -> Self {
        Self {
            symbols,
            terms,
            output: String::new(),
            indent: 0,
            catalog,
            trait_sorts: catalog
                .sorts
                .iter()
                .filter(|(_, s)| s.is_trait)
                .map(|(q, _)| q.clone())
                .collect(),
            scopes: Vec::new(),
            current_sort: None,
            config,
            errors: RefCell::new(Vec::new()),
            imported: HashSet::new(),
        }
    }

    fn error(&self, message: String) {
        self.errors.borrow_mut().push(CodegenError { message });
    }

    // ── Scopes and name resolution ───────────────────────────────

    /// Enter the scope `prefix`, which declares `imports` and the type parameters
    /// `params`. Left with [`Self::pop_scope`].
    fn push_scope(&mut self, prefix: String, imports: &[Import], params: Vec<String>) {
        let mut scope = Scope {
            prefix,
            imports: HashMap::new(),
            wildcards: Vec::new(),
            params,
            value_params: Vec::new(),
        };
        for imp in imports {
            let path = name_text(self.symbols, &imp.path);
            match &imp.kind {
                ImportKind::Plain => {
                    let short = self.symbols.local_name(imp.path.last()).to_owned();
                    scope.imports.insert(short, path);
                }
                ImportKind::Selective(names) => {
                    for n in names {
                        let short = self.symbols.local_name(n.last()).to_owned();
                        scope
                            .imports
                            .insert(short, qualify(&path, &name_text(self.symbols, n)));
                    }
                }
                ImportKind::Wildcard => scope.wildcards.push(path),
            }
        }
        self.scopes.push(scope);
    }

    /// Enter an operation's signature: its own type parameters and its value
    /// parameters, whose members a type may name.
    fn push_operation_scope(&mut self, op: &Operation) {
        let prefix = self
            .scopes
            .last()
            .map(|s| s.prefix.clone())
            .unwrap_or_default();
        let params = op
            .type_params
            .iter()
            .map(|tp| self.local_name_of(tp.name))
            .collect();
        self.push_scope(prefix, &[], params);
        let value_params = op
            .params
            .iter()
            .map(|p| self.local_name_of(p.name))
            .collect();
        if let Some(scope) = self.scopes.last_mut() {
            scope.value_params = value_params;
        }
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// The qualified name of the scope being emitted.
    fn scope_prefix(&self) -> String {
        self.scopes
            .last()
            .map(|s| s.prefix.clone())
            .unwrap_or_default()
    }

    /// What `name` denotes where it is written: innermost scope first, each scope's type
    /// parameters, then the sorts it declares, then its imports; then the prelude's
    /// `public` names.
    fn denote(&self, name: &Name) -> Denoted {
        let written = name_text(self.symbols, name);
        if written == crate::intern::SELF_TYPE_NAME {
            return Denoted::SelfType;
        }
        let first = self.symbols.local_name(name.segments[0]);
        let rest: Vec<&str> = name.segments[1..]
            .iter()
            .map(|s| self.symbols.local_name(*s))
            .collect();
        for (depth, scope) in self.scopes.iter().enumerate().rev() {
            if rest.is_empty() && scope.params.iter().any(|p| p == first) {
                return Denoted::Param(first.to_owned());
            }
            // `s.T`: the member `T` of the value parameter `s`'s type, which this
            // generator writes as the parameter `T` of the sort being emitted.
            if rest.len() == 1 && scope.value_params.iter().any(|p| p == first) {
                return Denoted::Param(rest[0].to_owned());
            }
            // The scope's own declarations, then those of the namespaces its dotted
            // name passes through (`sort anthill.prelude.Stream` sits in
            // `anthill.prelude`) down to the next scope out.
            let outer = depth
                .checked_sub(1)
                .map(|d| self.scopes[d].prefix.as_str())
                .unwrap_or("");
            let mut prefix = scope.prefix.as_str();
            loop {
                let declared = qualify(prefix, &written);
                if self.catalog.sorts.contains_key(&declared) {
                    return Denoted::Declared(declared);
                }
                if prefix == outer || prefix.is_empty() {
                    break;
                }
                prefix = prefix.rsplit_once('.').map_or("", |(p, _)| p);
            }
            if let Some(imported) = scope.imports.get(first) {
                let mut qualified = imported.clone();
                for r in &rest {
                    qualified = qualify(&qualified, r);
                }
                return self.denote_qualified(qualified);
            }
            for path in &scope.wildcards {
                let candidate = qualify(path, &written);
                if self.catalog.sorts.contains_key(&candidate) || stdlib_type(&candidate).is_some()
                {
                    return self.denote_qualified(candidate);
                }
            }
        }
        // A bare name nothing in scope declares or imports is read as a `public` name
        // of the prelude (`Error`, `Modify`), which every scope reaches without an
        // import (kernel-language.md §8.6) — unless this generator does not know that
        // prelude name and a wildcard import of another namespace is in scope, which
        // brings the name in, and Rust's `use path::*` with it. A dotted one is read
        // from the root.
        if !rest.is_empty() {
            return self.denote_qualified(written);
        }
        let in_prelude = qualify(PRELUDE, &written);
        let known = stdlib_type(&in_prelude).is_some()
            || self.catalog.sorts.contains_key(&in_prelude)
            || in_prelude == ERROR_LABEL
            || in_prelude == MODIFY_LABEL;
        if !known {
            let wildcard = self
                .scopes
                .iter()
                .rev()
                .flat_map(|s| s.wildcards.iter())
                .find(|p| p.as_str() != PRELUDE);
            if let Some(path) = wildcard {
                return Denoted::External(qualify(path, &written));
            }
        }
        match self.denote_qualified(in_prelude) {
            Denoted::UnmappedPrelude(q) => Denoted::NotFound(q),
            other => other,
        }
    }

    /// What the qualified name `qualified` denotes. The table answers for a prelude sort
    /// before the catalog does, so a reference to `Int64` is `i64` in `int64.anthill`
    /// too, which declares `sort Int64`.
    fn denote_qualified(&self, qualified: String) -> Denoted {
        if let Some(t) = stdlib_type(&qualified) {
            return Denoted::Stdlib(t);
        }
        if self.catalog.sorts.contains_key(&qualified) {
            return Denoted::Declared(qualified);
        }
        if qualified.starts_with(&format!("{PRELUDE}.")) {
            return Denoted::UnmappedPrelude(qualified);
        }
        Denoted::External(qualified)
    }

    /// Is `name` the reserved word `Self` as written (THIS instance, never an open one)?
    fn denotes_self_word(&self, name: &Name) -> bool {
        matches!(self.denote(name), Denoted::SelfType)
    }

    /// Does the head of `ty` name the sort being emitted — `Self`, or a name that
    /// resolves to it? `Self` (proposal 070 §1.2) is still the word the author wrote in
    /// the parse tree this generator reads, so every place that asks "is this the sort
    /// itself" — the `Self` rendering, the boxed recursive field, the receiver — asks
    /// here. Without it `entity cons(head: T, tail: Self)` was not boxed and
    /// `length(l: Self)` was no method.
    fn names_current_sort(&self, ty: &TypeExpr) -> bool {
        match ty {
            TypeExpr::Simple(name) | TypeExpr::Parameterized { name, .. } => {
                self.is_current_sort(&self.denote(name))
            }
            _ => false,
        }
    }

    /// [`Self::names_current_sort`] for a name already resolved.
    fn is_current_sort(&self, denoted: &Denoted) -> bool {
        matches!(denoted, Denoted::SelfType)
            || denoted
                .qualified()
                .is_some_and(|q| self.current_sort.as_deref() == Some(q))
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
        self.symbols.local_name(name.last()).to_owned()
    }

    /// Proposal 070 §1.3 — the first reference in `ty`, at any depth, to the sort being
    /// generated that leaves one of its type parameters OPEN, as it is written: the sort's
    /// bare name (`o: Cell` inside `sort Cell`, which declares `V`), an application that
    /// leaves a parameter out, or one that writes the anonymous `?` into it (`Cell[V = ?]`).
    /// `None` for a sort that declares no parameter — it has one instance, and its name is
    /// that. A NAMED variable in the slot (`LogicalStream[T = ?A]`) is not this: it is one
    /// unknown the signature can share, and is rendered as it was.
    ///
    /// Such a reference is ANY instance of the sort, inside its own definition as outside
    /// it; THIS instance is written `Self`. This generator used to render both as Rust's
    /// `Self` — the implicit tie, on the emission side: `both(a: Self, b: Chain) -> Int64`
    /// came out `fn both(&self, b: Self)`, and a field `next: Chain` as `Box<Chain<T>>`,
    /// each claiming the receiver's instance for a value that may be any. Rust has no type
    /// for "any `Chain`" in a field or a return, and in a parameter only through a generic
    /// this generator does not mint, so the declaration is REFUSED
    /// ([`Self::refuse_open_own_reference`]) rather than emitted with the old meaning.
    ///
    /// An effect row is not walked: a label's own name is compared by identity, not
    /// expanded (kernel-language.md §8.1), so it is no reference to the sort.
    fn open_own_reference(
        &self,
        ty: &TypeExpr,
        sort_name: &str,
        type_params: &[String],
    ) -> Option<String> {
        if type_params.is_empty() {
            return None;
        }
        match ty {
            TypeExpr::Simple(name) => (!self.denotes_self_word(name)
                && self.names_current_sort(ty))
            .then(|| sort_name.to_owned()),
            TypeExpr::Parameterized { name, bindings } => {
                if !self.denotes_self_word(name) && self.names_current_sort(ty) {
                    // Slot by slot, as the loader places them: a parameter takes the binding
                    // that NAMES it, else the next positional one — so `Pair[L = Int64,
                    // String]` writes both slots.
                    let named = |p: &str| {
                        bindings.iter().find(|b| {
                            b.param
                                .as_ref()
                                .is_some_and(|n| self.symbols.local_name(n.last()) == p)
                        })
                    };
                    let mut positional = bindings.iter().filter(|b| b.param.is_none());
                    let leaves_open = type_params.iter().any(|p| {
                        named(p)
                            .or_else(|| positional.next())
                            .is_none_or(|b| self.is_anonymous_variable(&b.bound))
                    });
                    if leaves_open {
                        return Some(format!("{sort_name}[…]"));
                    }
                }
                bindings
                    .iter()
                    .find_map(|b| self.open_own_reference(&b.bound, sort_name, type_params))
            }
            TypeExpr::Tuple(fields) => fields
                .iter()
                .find_map(|(_, t)| self.open_own_reference(t, sort_name, type_params)),
            TypeExpr::Arrow {
                params,
                return_type,
                ..
            } => params
                .iter()
                .map(|(_, t)| t)
                .chain(std::iter::once(&**return_type))
                .find_map(|t| self.open_own_reference(t, sort_name, type_params)),
            _ => None,
        }
    }

    /// Is `ty` the anonymous `?` — the variable the converter mints under the name `_`
    /// (`convert_variable_node`), fresh at each occurrence?
    fn is_anonymous_variable(&self, ty: &TypeExpr) -> bool {
        let TypeExpr::Variable { term_id, .. } = ty else {
            return false;
        };
        matches!(
            self.terms.get(*term_id),
            Term::Var(crate::kb::term::Var::Global(vid)) if self.symbols.local_name(vid.name()) == "_"
        )
    }

    /// Record the refusal of `what` — a parameter, a return or a field of the sort being
    /// generated — where its type leaves the sort's own parameter open
    /// ([`Self::open_own_reference`]). The error makes `generate_rust` answer `Err`, so
    /// what is rendered for the declaration afterwards is never returned.
    fn refuse_open_own_reference(
        &mut self,
        what: &str,
        ty: &TypeExpr,
        sort_name: &str,
        type_params: &[String],
    ) {
        if let Some(written) = self.open_own_reference(ty, sort_name, type_params) {
            // ONLY `Self` IS OFFERED. The typer's refusal of the same spelling also offers a
            // name for the other instance's parameter (`[X]`, `Cell[V = X]`), and this
            // generator must not: it renders an application of the enclosing sort as `Self`
            // whatever its arguments (older than proposal 070, and recorded there), so that
            // advice would lead straight to the emission this refusal exists to prevent.
            self.errors.borrow_mut().push(CodegenError {
                message: format!(
                    "{what}: `{written}` is the enclosing sort `{sort_name}` with a type \
                     parameter left open — inside its own definition a sort's bare name is \
                     ANY instance of it (proposal 070 §1.3), and this generator has no Rust \
                     spelling for that. `{self_word}` is this instance",
                    self_word = crate::intern::SELF_TYPE_NAME,
                ),
            });
        }
    }

    /// [`Self::refuse_open_own_reference`] over an operation's signature: every parameter —
    /// the one that becomes the receiver included — and the return.
    fn refuse_open_own_references_in(
        &mut self,
        op: &Operation,
        sort_name: &str,
        type_params: &[String],
    ) {
        let op_name = self.resolve(&op.name);
        for param in &op.params {
            let pname = self.local_name_of(param.name);
            self.refuse_open_own_reference(
                &format!("operation `{op_name}`, parameter `{pname}`"),
                &param.ty,
                sort_name,
                type_params,
            );
        }
        self.refuse_open_own_reference(
            &format!("operation `{op_name}`, return type"),
            &op.return_type,
            sort_name,
            type_params,
        );
    }

    fn local_name_of(&self, sym: Symbol) -> String {
        self.symbols.local_name(sym).to_owned()
    }

    fn visibility_prefix(&self, vis: Option<Visibility>) -> &'static str {
        match vis {
            Some(Visibility::Public) => "pub ",
            _ => {
                if self.config.default_pub {
                    "pub "
                } else {
                    ""
                }
            }
        }
    }

    // ── Trait return wrapping ─────────────────────────────────────

    /// True when `ty`'s head resolves to a sort that generates as a trait. Drives the
    /// WI-540 trait-object wrapping; a `Self` collapse is handled at the call site (it is
    /// a trait by construction inside a trait method).
    fn is_trait_type(&self, ty: &TypeExpr) -> bool {
        let name = match ty {
            TypeExpr::Simple(name) | TypeExpr::Parameterized { name, .. } => name,
            _ => return false,
        };
        // The sort being emitted renders `Self` inside its own body, and is wrapped (or
        // not) by the `Self` handling at each site.
        let denoted = self.denote(name);
        if self.is_current_sort(&denoted) {
            return false;
        }
        match denoted {
            Denoted::Declared(q) => self.trait_sorts.contains(&q),
            Denoted::Stdlib(t) => {
                matches!(t.rendering, StdlibRendering::Support { is_trait: true })
            }
            _ => false,
        }
    }

    /// Whether the sort being emitted generates as a trait.
    fn current_sort_is_trait(&self) -> bool {
        self.current_sort
            .as_ref()
            .is_some_and(|q| self.trait_sorts.contains(q))
    }

    /// If `ty`, rendered `ret`, is of a trait sort, wrap it: `Box<dyn Stream<T>>` when
    /// [`CodegenConfig::boxed_trait_objects`] (keeps the trait object-safe), else
    /// `impl Stream<T>` (the original skeleton form).
    fn wrap_trait_return(&self, ret: &str, ty: &TypeExpr) -> String {
        if self.is_trait_type(ty) {
            if self.config.boxed_trait_objects {
                format!("Box<dyn {ret}>")
            } else {
                format!("impl {ret}")
            }
        } else {
            ret.to_owned()
        }
    }

    /// Return-position wrapping that also resolves a `Self` collapse (WI-540).
    /// `type_to_rust_in_sort` renders the enclosing sort's own type as `"Self"`;
    /// in a trait method a `Self` return breaks object-safety, so under
    /// `boxed_trait_objects` it becomes `Box<dyn <SortName>>`. A non-trait
    /// enclosing sort (enum impl method) keeps `Self` (delegates to
    /// [`Self::wrap_trait_return`], which leaves non-trait types untouched).
    fn wrap_trait_return_in_sort(
        &self,
        ret: &str,
        ty: &TypeExpr,
        sort_name: &str,
        type_params: &[String],
    ) -> String {
        if self.config.boxed_trait_objects && self.current_sort_is_trait() {
            // The enclosing trait sort renders as `Self` (see `type_to_rust_in_sort`).
            // A `Self` return — bare OR nested (e.g. `Option<Pair<T, Self>>` from
            // `splitFirst`) — breaks object-safety, so replace EVERY whole-word
            // `Self` with the boxed trait-object form, carrying the trait's own
            // type args (`Box<dyn Stream<T, E>>`) so the reference is well-formed.
            let args = if type_params.is_empty() {
                String::new()
            } else {
                format!("<{}>", type_params.join(", "))
            };
            let boxed = format!("Box<dyn {sort_name}{args}>");
            let replaced = replace_word(ret, "Self", &boxed);
            if replaced != ret {
                return replaced;
            }
        }
        self.wrap_trait_return(ret, ty)
    }

    /// Parameter-position wrapping (WI-540). A non-receiver parameter of a trait
    /// type must be a trait object reference under `boxed_trait_objects`: the
    /// enclosing trait's own type (`"Self"`) → `&dyn <SortName>`, a different
    /// trait → `&dyn Trait`. Off / non-trait carriers keep the original
    /// `should_ref_param` behaviour (`&Self`, or the bare type).
    fn wrap_trait_param(&self, ptype: &str, ty: &TypeExpr, sort_name: &str) -> String {
        if self.config.boxed_trait_objects {
            if ptype == "Self" && self.current_sort_is_trait() {
                return format!("&dyn {sort_name}");
            }
            if self.is_trait_type(ty) {
                return format!("&dyn {ptype}");
            }
        }
        if should_ref_param(ptype) {
            format!("&{ptype}")
        } else {
            ptype.to_owned()
        }
    }

    /// Field-position wrapping (WI-540): a struct/enum field of trait type
    /// becomes `Box<dyn Trait<…>>` under `boxed_trait_objects` (e.g.
    /// `Solution.definite(subst: Substitution)` → `subst: Box<dyn Substitution>`).
    /// A non-trait field (or the flag off) is unchanged.
    fn wrap_trait_field(&self, rendered: &str, ty: &TypeExpr) -> String {
        if self.config.boxed_trait_objects && self.is_trait_type(ty) {
            format!("Box<dyn {rendered}>")
        } else {
            rendered.to_owned()
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
    fn lower_const_value(
        &mut self,
        name: &str,
        rust_ty: &str,
        value: Option<TermId>,
    ) -> Option<String> {
        let Some(tid) = value else {
            if rust_ty == "f64" {
                if let Some(expr) = host_float_const_rust(name) {
                    return Some(expr.to_string());
                }
            }
            self.errors.borrow_mut().push(CodegenError {
                message: format!(
                    "const `{name}`: bodyless host-supplied const has no Rust value \
                     source (only the Float IEEE specials infinity/negativeInfinity/nan \
                     are mapped)"
                ),
            });
            return None;
        };
        match self.terms.get(tid) {
            Term::Const(lit) => Some(lower_literal_rust(lit, rust_ty)),
            other => {
                self.errors.borrow_mut().push(CodegenError {
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
        if t == "String" {
            "&str".to_string()
        } else {
            t
        }
    }

    /// Emit a term-level const as `[pub] const NAME: T = value;`. A trait
    /// associated const takes no visibility (it is public with the trait);
    /// free-standing and inherent-impl consts follow the configured visibility.
    fn emit_const(&mut self, c: &Const, in_trait: bool) {
        let name = self.resolve(&c.name);
        let ty = self.const_rust_type(&c.ty);
        if let Some(val) = self.lower_const_value(&name, &ty, c.value) {
            let vis = if in_trait {
                ""
            } else {
                self.visibility_prefix(c.visibility)
            };
            self.line(&format!("{vis}const {name}: {ty} = {val};"));
        }
    }

    /// WI-540: a struct/enum with a trait-object field (`Box<dyn Trait>`, under
    /// `boxed_trait_objects`) cannot `derive(Clone, Debug)` — a trait object is
    /// neither unless the trait requires it. Such a type (e.g.
    /// `Solution.definite(subst: Substitution)`) must skip the derive attr.
    /// Only ever true under `boxed_trait_objects`, so default output is
    /// unaffected. (Outer-name check — a trait *inside* a `List`/`Option` is not
    /// flagged; the reflect subset has none.)
    fn has_trait_object_field<'b>(&self, tys: impl Iterator<Item = &'b TypeExpr>) -> bool {
        self.config.boxed_trait_objects && tys.into_iter().any(|ty| self.is_trait_type(ty))
    }

    /// A sort's generic parameter list as its DECLARATION writes it (`enum Box<T = i64>`):
    /// each parameter with its declared default (proposal 069 §1.4), so a written `Box` that
    /// leaves `T` out is `Box<i64>` to Rust as to anthill. Rust takes a default only on a
    /// trailing run of parameters, so the defaults are emitted from the last parameter that
    /// declares none onward; an `impl` header takes none at all, and is written without.
    fn declared_generics(&self, info: &SortInfo) -> String {
        if info.type_params.is_empty() {
            return String::new();
        }
        let trailing_from = info
            .type_param_defaults
            .iter()
            .rposition(|d| d.is_none())
            .map_or(0, |i| i + 1);
        let params: Vec<String> = info
            .type_params
            .iter()
            .enumerate()
            .map(|(i, name)| match info.type_param_defaults.get(i).copied().flatten() {
                Some(default) if i >= trailing_from => {
                    format!("{name} = {}", self.type_to_rust(default))
                }
                _ => name.clone(),
            })
            .collect();
        format!("<{}>", params.join(", "))
    }

    // ── Type expression mapping ──────────────────────────────────

    fn type_to_rust(&self, ty: &TypeExpr) -> String {
        self.render_type(ty, None)
    }

    /// Map a type written in the sort being emitted: a name of that sort is `Self`, and
    /// with `collapse_type_params` so is one of its `type_params`.
    fn type_to_rust_in_sort(
        &self,
        ty: &TypeExpr,
        type_params: &[String],
        collapse_type_params: bool,
    ) -> String {
        self.render_type(
            ty,
            Some(&InSort {
                type_params,
                collapse: collapse_type_params,
            }),
        )
    }

    fn render_type(&self, ty: &TypeExpr, in_sort: Option<&InSort>) -> String {
        match ty {
            TypeExpr::Simple(name) | TypeExpr::Parameterized { name, .. } => {
                let bindings: &[SortBinding] = match ty {
                    TypeExpr::Parameterized { bindings, .. } => bindings,
                    _ => &[],
                };
                let denoted = self.denote(name);
                if let Some(ctx) = in_sort {
                    if self.is_current_sort(&denoted) {
                        return "Self".to_owned();
                    }
                    if let (true, [], Denoted::Param(p)) = (ctx.collapse, bindings, &denoted) {
                        if ctx.type_params.contains(p) {
                            return "Self".to_owned();
                        }
                    }
                }
                self.render_named(name, denoted, bindings, in_sort)
            }
            TypeExpr::Variable { .. } => "T".to_owned(),
            TypeExpr::Tuple(fields) => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(_, ty)| self.render_type(ty, in_sort))
                    .collect();
                // A 1-tuple needs the trailing comma: Rust reads `(T)` as plain `T`,
                // which silently DROPS the tuple. Reachable since WI-766 made a
                // one-component named tuple type writable (`-> (a: Int64)`).
                if parts.len() == 1 {
                    format!("({},)", parts[0])
                } else {
                    format!("({})", parts.join(", "))
                }
            }
            TypeExpr::Arrow {
                params,
                return_type,
                ..
            } => {
                let param_types: Vec<String> = params
                    .iter()
                    .map(|(_, p)| self.render_type(p, in_sort))
                    .collect();
                let ret = self.render_type(return_type, in_sort);
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
            // WI-478: a guarded effect is an effect-position construct, not a Rust
            // type — emit `()` like the other effect forms.
            TypeExpr::EffectGuarded { .. } => "()".to_owned(),
        }
    }

    /// Render the written name `name` applied to `bindings` (none for a bare name), by
    /// what it denotes. A name this generator cannot write is an error naming it.
    fn render_named(
        &self,
        name: &Name,
        denoted: Denoted,
        bindings: &[SortBinding],
        in_sort: Option<&InSort>,
    ) -> String {
        let written = name_text(self.symbols, name);
        if let Denoted::Declared(q) | Denoted::UnmappedPrelude(q) | Denoted::NotFound(q) = &denoted
        {
            if q == ERROR_LABEL {
                // WI-20260911-8Y5BE — an `Error[P]` label in a TYPE-ARGUMENT slot
                // (`Stream[T = …, E = Error[P]]`) strips to `P`, the rule the effects
                // clause already follows (`analyze_effects`: `effects Error[P]` is
                // `Result<_, P>`). Keeping the wrapper here gave one channel two Rust
                // types — `execute`'s own `Err` was `P`, its stream's `E` was
                // `Error<P>` — and the host `Error` takes no generics.
                return match bindings {
                    [] => "Error".to_owned(),
                    _ if leaves_every_slot(bindings) => "Error".to_owned(),
                    [only] => self.render_type(&only.bound, in_sort),
                    _ => {
                        self.error(format!(
                            "`{written}` takes one payload, and is given {}",
                            bindings.len()
                        ));
                        "Error".to_owned()
                    }
                };
            }
        }
        match denoted {
            Denoted::SelfType => "Self".to_owned(),
            Denoted::Param(p) => match bindings {
                [] => p,
                [only] => format!("{p}<{}>", self.render_type(&only.bound, in_sort)),
                _ => {
                    self.error(format!(
                        "`{written}` applies the type parameter `{p}` to {} arguments, and \
                         this generator does not know the order of its parameters",
                        bindings.len()
                    ));
                    p
                }
            },
            Denoted::Declared(q) => {
                let params = self.catalog.sorts[&q].params.clone();
                self.render_applied(&written, short_of(&q), &params, bindings, in_sort)
            }
            Denoted::Stdlib(t) => self.render_template(&written, t, bindings, in_sort),
            Denoted::External(q) => match bindings {
                [] => short_of(&q).to_owned(),
                [only] => format!(
                    "{}<{}>",
                    short_of(&q),
                    self.render_type(&only.bound, in_sort)
                ),
                _ => {
                    self.error(format!(
                        "`{written}` is `{q}`, which no file generated with this one declares, \
                         so the order of its {} arguments is unknown — generate the file that \
                         declares it in the same run",
                        bindings.len()
                    ));
                    short_of(&q).to_owned()
                }
            },
            Denoted::UnmappedPrelude(q) => {
                self.error(format!(
                    "no Rust mapping for the prelude sort '{q}' (written `{written}`) — the \
                     Rust generator writes a prelude sort only through its table \
                     (`RUST_STDLIB_TYPES`), and this one is not in it. A sort declared in \
                     another file is found when that file is generated in the same run"
                ));
                written
            }
            Denoted::NotFound(q) => {
                self.error(format!(
                    "type `{written}` is declared in no file generated in this run and \
                     imported by none, and read as the prelude's `{q}` it has no Rust \
                     mapping — generate the file that declares it in the same run"
                ));
                written
            }
        }
    }

    /// `rust_name` applied to `bindings`, placed against the sort's declared `params`
    /// and written in that order — Rust's generics are positional. Parameters left out
    /// at the end are left to their defaults; one left out before a written one is an
    /// error, as Rust has no way to skip it.
    fn render_applied(
        &self,
        written: &str,
        rust_name: &str,
        params: &[String],
        bindings: &[SortBinding],
        in_sort: Option<&InSort>,
    ) -> String {
        if bindings.is_empty() {
            return rust_name.to_owned();
        }
        let Some(placed) = self.place_bindings(written, params, bindings) else {
            return rust_name.to_owned();
        };
        let Some(last) = placed.iter().rposition(Option::is_some) else {
            return rust_name.to_owned();
        };
        let mut args = Vec::with_capacity(last + 1);
        for (param, binding) in params.iter().zip(&placed).take(last + 1) {
            match binding {
                Some(b) => args.push(self.render_type(&b.bound, in_sort)),
                None => {
                    self.error(format!(
                        "`{written}` leaves out `{param}` and writes a parameter after it, \
                         which Rust's positional generics cannot say"
                    ));
                    args.push("_".to_owned());
                }
            }
        }
        format!("{rust_name}<{}>", args.join(", "))
    }

    /// A prelude sort's Rust template with each `$Name` replaced by the Rust type of the
    /// binding that places the sort's parameter `Name`.
    fn render_template(
        &self,
        written: &str,
        t: &RustStdlibType,
        bindings: &[SortBinding],
        in_sort: Option<&InSort>,
    ) -> String {
        let params: Vec<String> = t.params.iter().map(|p| p.to_string()).collect();
        let Some(placed) = self.place_bindings(written, &params, bindings) else {
            return t.template.to_owned();
        };
        let parts = match parse_type_template(t.template) {
            Ok(parts) => parts,
            Err(what) => {
                self.error(format!("the Rust template of `{}` {what}", t.qualified));
                return t.template.to_owned();
            }
        };
        let mut out = String::new();
        for part in parts {
            match part {
                TypeTemplatePart::Text(text) => out.push_str(&text),
                TypeTemplatePart::Param(name) => {
                    let slot = params.iter().position(|p| *p == name);
                    match slot.and_then(|i| placed[i]) {
                        Some(b) => out.push_str(&self.render_type(&b.bound, in_sort)),
                        None => {
                            self.error(format!(
                                "`{written}` leaves its parameter `{name}` open, and the Rust \
                                 type of `{}` (`{}`) needs it",
                                t.qualified, t.template
                            ));
                            out.push('_');
                        }
                    }
                }
            }
        }
        out
    }

    /// Each of `params` with the binding that places it: the one that NAMES it, else the
    /// next positional one, in declaration order — the loader's rule (`Pair[L = Int64,
    /// String]` writes both slots). `None`, with an error recorded, when a binding places
    /// no parameter.
    fn place_bindings<'b>(
        &self,
        written: &str,
        params: &[String],
        bindings: &'b [SortBinding],
    ) -> Option<Vec<Option<&'b SortBinding>>> {
        let mut placed: Vec<Option<&SortBinding>> = vec![None; params.len()];
        for b in bindings {
            if let Some(n) = &b.param {
                let pname = self.symbols.local_name(n.last());
                let Some(i) = params.iter().position(|p| p == pname) else {
                    self.error(format!(
                        "`{written}` binds `{pname}`, which is no type parameter of it \
                         (it declares {params:?})"
                    ));
                    return None;
                };
                placed[i] = Some(b);
            }
        }
        for b in bindings.iter().filter(|b| b.param.is_none()) {
            let Some(slot) = placed.iter_mut().find(|p| p.is_none()) else {
                self.error(format!(
                    "`{written}` is given more arguments than it declares parameters ({params:?})"
                ));
                return None;
            };
            *slot = Some(b);
        }
        Some(placed)
    }

    /// True if `name` appears in a VALUE-type position within `ty` (a simple/
    /// parameterized name, tuple element, or arrow param/return). Deliberately
    /// does NOT descend into an arrow's effect row — an effect-only type param
    /// (`EffP` in `(…) -> … @ {EffP}`) is therefore reported absent, so it gets
    /// erased rather than emitted as an unconstrained method generic.
    fn type_mentions(&self, ty: &TypeExpr, name: &str) -> bool {
        match ty {
            TypeExpr::Simple(n) => self.resolve(n) == name,
            TypeExpr::Variable { .. } => false,
            TypeExpr::Tuple(fields) => fields.iter().any(|(_, t)| self.type_mentions(t, name)),
            TypeExpr::Parameterized { name: n, bindings } => {
                self.resolve(n) == name
                    || bindings.iter().any(|b| self.type_mentions(&b.bound, name))
            }
            TypeExpr::Arrow {
                params,
                return_type,
                ..
            } => {
                params.iter().any(|(_, p)| self.type_mentions(p, name))
                    || self.type_mentions(return_type, name)
            }
            TypeExpr::Denoted(_)
            | TypeExpr::EffectAbsent(_)
            | TypeExpr::EffectRow(_)
            | TypeExpr::EffectGuarded { .. } => false,
        }
    }

    // ── Top-level dispatch ───────────────────────────────────────

    fn emit_items(&mut self, items: &[Item], _enclosing_ns: Option<&Namespace>) {
        let mut first = true;
        for item in items {
            match item {
                Item::Namespace(n) => {
                    if !first {
                        self.blank();
                    }
                    // WI-20260917-S8JYF — a SECONDARY ENTRY's spec claims, before the
                    // block's own module: `namespace FileStore { provides Modifiable[T =
                    // FileStore] }` is where `// impl Modifiable for FileStore` comes
                    // from now that the `fact Modifiable[T = FileStore]` spelling is
                    // retired. An ordinary namespace has no `provides` (the loader
                    // refuses one, `ProvidesClauseNeedsSort`), so this emits nothing
                    // there.
                    self.emit_secondary_entry_provisions(n);
                    self.emit_namespace(n);
                }
                Item::SortWithBody(s) => {
                    if !first {
                        self.blank();
                    }
                    self.emit_sort(s);
                }
                Item::Entity(e) => {
                    if !first {
                        self.blank();
                    }
                    self.emit_standalone_entity(e, _enclosing_ns);
                }
                Item::Operation(o) => {
                    let op_name = self.resolve(&o.name);
                    self.errors.borrow_mut().push(CodegenError {
                        message: format!(
                            "operation `{op_name}` has no enclosing namespace for module trait"
                        ),
                    });
                }
                // WI-20260917-S8JYF — a top-level `fact` maps to NOTHING in Rust. One
                // used to render `// impl <Trait> for <Carrier>` off its brackets; with
                // the `fact` spelling of a provision retired it asserts no is-a, and the
                // marker comes from a `namespace <Carrier>` secondary entry above.
                Item::Fact(_) => {}
                Item::Rule(_) => {
                    // Collected later for test module
                }
                Item::RuleBlock(_) => {
                    // Collected later for test module
                }
                Item::Constraint(c) => {
                    if !first {
                        self.blank();
                    }
                    self.emit_constraint(c);
                }
                Item::AbstractSort(_) => {
                    // Skip — only meaningful inside sort bodies
                }
                // WI-533: a free-standing const → `pub const NAME: T = value;`.
                Item::Const(c) => {
                    if !first {
                        self.blank();
                    }
                    self.emit_const(c, false);
                }
                Item::OperationBlock(_)
                | Item::RequiresDecl(_)
                | Item::Describe(_)
                | Item::Proof(_)
                | Item::ProvidesClause(_)
                | Item::ProvidesBlock(_) => {}
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
        let prefix = qualify(&self.scope_prefix(), &name_text(self.symbols, &ns.name));
        self.push_scope(prefix.clone(), &ns.imports, Vec::new());
        // A namespace nested in a sort's body is not that sort: a name of the sort in
        // it is the sort's, not `Self`.
        let enclosing_sort = self.current_sort.take();

        if !flatten {
            self.line(&format!("pub mod {name} {{"));
            self.indent();
        }

        // Imports
        let mut wrote_use = false;
        for imp in &ns.imports {
            wrote_use |= self.emit_import(imp);
        }
        if wrote_use && !ns.items.is_empty() {
            self.blank();
        }

        // Pre-pass: collect sort names and build aggregation maps
        // Only sorts with a body should receive aggregated operations
        let body_sort_names = self.collect_body_sort_names(&ns.items);
        let sort_names = self.collect_sort_names(&ns.items);

        // Map: sort_name → Vec<&Operation> for namespace-level ops
        let mut sort_ops: std::collections::HashMap<String, Vec<&Operation>> =
            std::collections::HashMap::new();
        let mut consumed_ops: std::collections::HashSet<usize> = std::collections::HashSet::new();

        // Map: sort_name → Vec<String>, the is-a edges a SECONDARY ENTRY at that sort's
        // address declares. `namespace Type { provides PartialEq[T = Type] }` beside
        // `sort Type = ?` renders `trait Type: PartialEq`, exactly as the same claim
        // written in the sort's own body does (`collect_sort_info`) — 059 R2: what a
        // secondary entry declares enters the sort's own scope.
        //
        // WI-20260917-S8JYF — WHAT REPLACED THE PROXIMITY READING. A namespace-level
        // `fact Spec` used to be folded into the PRECEDING sort's supertrait list, so
        // declaration ORDER decided which type a claim was about — the reading WI-978
        // removed from the loader and WI-933 from the impl-marker path, and this was
        // the last place it survived. The entry's ADDRESS says it now, and nothing is
        // read off a neighbour.
        //
        // AN ENTRY AT A NON-SORT ADDRESS IS NOT CONSUMED HERE: a §6.3 free-standing
        // `entity FileStore(…)` lowers to a STRUCT, which has no supertrait list, so
        // its entry's claims render as `// impl Modifiable for FileStore` markers in
        // [`Self::emit_secondary_entry_provisions`]. One provision, one rendering —
        // the two paths partition on whether the address is trait-lowered.
        let mut sort_supertraits: std::collections::HashMap<String, Vec<String>> =
            std::collections::HashMap::new();
        let mut consumed_entries: std::collections::HashSet<usize> =
            std::collections::HashSet::new();

        for (idx, item) in ns.items.iter().enumerate() {
            match item {
                Item::Operation(op) => {
                    // An operation whose first parameter is of one of this namespace's
                    // sorts joins that sort's methods.
                    let first_sort = op.params.first().and_then(|p| match &p.ty {
                        TypeExpr::Simple(n) | TypeExpr::Parameterized { name: n, .. } => {
                            match self.denote(n) {
                                Denoted::Declared(q) => {
                                    q.strip_prefix(&format!("{prefix}.")).map(str::to_owned)
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    });
                    if let Some(first_type) = first_sort.filter(|t| body_sort_names.contains(t)) {
                        sort_ops.entry(first_type).or_default().push(op);
                        consumed_ops.insert(idx);
                    }
                }
                Item::Namespace(entry) => {
                    let address = self.resolve(&entry.name);
                    if !sort_names.contains(&address) {
                        continue;
                    }
                    // Bare specs only, and unconditional ones — the WI-1108 bound the
                    // in-body reader states, for its reason.
                    let supers: Vec<String> = entry
                        .items
                        .iter()
                        .filter_map(|i| match i {
                            Item::ProvidesClause(pc)
                                if matches!(pc.spec, TypeExpr::Simple(_))
                                    && pc.conditions.is_empty() =>
                            {
                                Some(type_expr_name(self.symbols, &pc.spec))
                            }
                            _ => None,
                        })
                        .collect();
                    if supers.is_empty() {
                        continue;
                    }
                    sort_supertraits.entry(address).or_default().extend(supers);
                    // Consumed only when the entry has NOTHING ELSE in it: an entry that
                    // also declares operations (059 R2) still has to emit its module.
                    if entry
                        .items
                        .iter()
                        .all(|i| matches!(i, Item::ProvidesClause(_)))
                    {
                        consumed_entries.insert(idx);
                    }
                }
                _ => {}
            }
        }

        // Emit items, handling sorts with aggregated operations and supertraits
        let mut first = true;
        let mut orphan_ops: Vec<&Operation> = Vec::new();
        for (idx, item) in ns.items.iter().enumerate() {
            if consumed_ops.contains(&idx) || consumed_entries.contains(&idx) {
                continue;
            }
            // WI-540 `emit_only`: skip a sort/enum/entity not in the subset, and
            // skip namespace-level facts entirely — they map to nothing in Rust.
            if self.config.emit_only.is_some() {
                let skip = match item {
                    Item::SortWithBody(s) => !self.config.emits(&self.resolve(&s.name)),
                    Item::AbstractSort(s) => !self.config.emits(&self.resolve(&s.name)),
                    Item::Entity(e) => !self.config.emits(&self.resolve(&e.name)),
                    Item::Fact(_) => true,
                    _ => false,
                };
                if skip {
                    continue;
                }
            }
            match item {
                Item::SortWithBody(s) => {
                    if !first {
                        self.blank();
                    }
                    let sname = self.resolve(&s.name);
                    let extra_ops = sort_ops.remove(&sname).unwrap_or_default();
                    let extra_supers = sort_supertraits.remove(&sname).unwrap_or_default();
                    self.emit_sort_with_extras(s, &extra_ops, &extra_supers);
                }
                Item::AbstractSort(s) => {
                    let sname = self.resolve(&s.name);
                    let extra_ops = sort_ops.remove(&sname);
                    let extra_supers = sort_supertraits.remove(&sname).unwrap_or_default();
                    let previous = self.current_sort.replace(qualify(&prefix, &sname));
                    if let Some(host_type) = self.config.carrier_bindings.get(&sname) {
                        // Carrier binding: emit type alias instead of struct/trait
                        if !first {
                            self.blank();
                        }
                        let vis = self.visibility_prefix(s.visibility);
                        self.line(&format!("{vis}type {sname} = {host_type};"));
                    } else if let Some(ops) = extra_ops {
                        if !first {
                            self.blank();
                        }
                        self.emit_abstract_sort_as_trait(s, &ops, &extra_supers);
                    } else {
                        // No operations → emit as unit struct. Derive like other
                        // generated types (WI-540) so an opaque sort (e.g.
                        // `NodeOccurrence`) can sit in a `derive(Clone, Debug)`
                        // struct field. (No-op when `derives` is empty.)
                        if !first {
                            self.blank();
                        }
                        self.emit_derive_attr();
                        let vis = self.visibility_prefix(s.visibility);
                        self.line(&format!("{vis}struct {sname};"));
                    }
                    self.current_sort = previous;
                }
                Item::Namespace(n) => {
                    if !first {
                        self.blank();
                    }
                    // A SECONDARY ENTRY whose address is NOT trait-lowered — a §6.3
                    // free-standing `entity`, which becomes a struct and has no
                    // supertrait list. Its claims render as `// impl <Trait> for <X>`
                    // markers.
                    //
                    // GUARDED ON `sort_names`, and the guard is not redundant with the
                    // `consumed_entries` skip above. An entry at a sort's address whose
                    // claims were folded into that sort's supertraits is consumed ONLY
                    // when it holds nothing else; one that also declares an operation
                    // (059 R2) still has to emit its module, and would otherwise arrive
                    // here and render its already-folded claims a SECOND time as
                    // markers — one provision, two renderings.
                    if !sort_names.contains(&self.resolve(&n.name)) {
                        self.emit_secondary_entry_provisions(n);
                    }
                    self.emit_namespace(n);
                }
                Item::Entity(e) => {
                    if !first {
                        self.blank();
                    }
                    self.emit_standalone_entity(e, Some(ns));
                }
                Item::Operation(o) => {
                    // Collect orphan ops for module trait emission
                    orphan_ops.push(o);
                }
                Item::Rule(_) | Item::RuleBlock(_) => {
                    // Collected later for test module
                }
                Item::Constraint(c) => {
                    if !first {
                        self.blank();
                    }
                    self.emit_constraint(c);
                }
                Item::Const(c) => {
                    if !first {
                        self.blank();
                    }
                    self.emit_const(c, false);
                }
                _ => {}
            }
            first = false;
        }

        // Emit module trait for orphan operations (compilable mode only).
        // WI-540 `emit_only`: the free reflect ops are interpreter-only — omit
        // the module trait entirely under the subset filter.
        if !orphan_ops.is_empty() && self.config.emit_only.is_none() {
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
        self.current_sort = enclosing_sort;
        self.pop_scope();
    }

    fn collect_sort_names(&self, items: &[Item]) -> Vec<String> {
        items
            .iter()
            .filter_map(|item| match item {
                Item::SortWithBody(s) => Some(self.resolve(&s.name)),
                Item::AbstractSort(s) => Some(self.resolve(&s.name)),
                _ => None,
            })
            .collect()
    }

    fn collect_body_sort_names(&self, items: &[Item]) -> Vec<String> {
        items
            .iter()
            .filter_map(|item| {
                if let Item::SortWithBody(s) = item {
                    Some(self.resolve(&s.name))
                } else {
                    None
                }
            })
            .collect()
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
        if let Some(q) = &self.current_sort {
            self.trait_sorts.insert(q.clone());
        }

        let supertrait_clause = if supertraits.is_empty() {
            String::new()
        } else {
            format!(": {}", supertraits.join(" + "))
        };

        self.line(&format!("{vis}trait {sort_name}{supertrait_clause} {{"));
        self.indent();

        let mut first_op = true;
        for op in ops {
            if !first_op {
                self.blank();
            }
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
        let mut wrote_use = false;
        for imp in &sort.imports {
            wrote_use |= self.emit_import(imp);
        }
        if wrote_use {
            self.blank();
        }

        let sort_name = self.resolve(&sort.name);
        let mut info = SortInfo::from_items(&sort.items, self.symbols);
        let previous = self.enter_sort(sort, &info);

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
        self.leave_sort(previous);
    }

    /// Enter the scope of `sort`, whose type parameters `info` read, as the sort being
    /// emitted. Returns the sort that was being emitted, for [`Self::leave_sort`].
    fn enter_sort(&mut self, sort: &SortWithBody, info: &SortInfo) -> Option<String> {
        let qualified = qualify(&self.scope_prefix(), &name_text(self.symbols, &sort.name));
        self.push_scope(qualified.clone(), &sort.imports, info.type_params.clone());
        self.current_sort.replace(qualified)
    }

    fn leave_sort(&mut self, previous: Option<String>) {
        self.pop_scope();
        self.current_sort = previous;
    }

    /// Emit the `use` line for `imp`, if it brings in anything the generated code
    /// names. Returns whether a line was written.
    fn emit_import(&mut self, imp: &Import) -> bool {
        if self.config.suppress_imports {
            return false;
        }
        let mut segments: Vec<String> = imp
            .path
            .segments
            .iter()
            .map(|s| to_snake_case(&self.local_name_of(*s)))
            .collect();

        // Apply namespace_map: if the first segment matches a key, replace it
        if let Some(first) = segments.first() {
            if let Some(replacement) = self.config.namespace_map.get(first.as_str()) {
                segments[0] = replacement.clone();
            }
        }

        // Drop what this file has already brought in — see `Self::imported` — and
        // what the generated code never names (`Self::import_is_written`). The
        // filter runs BEFORE the `#[allow(unused_imports)]` line so a fully
        // redundant import emits nothing at all, attribute included.
        let path = segments.join("::");
        let anthill_path = name_text(self.symbols, &imp.path);
        let names: Vec<String> = match &imp.kind {
            // A whole-path or wildcard import names one thing for this purpose: the
            // path itself. Repeating either is the same E0252 (or, for a wildcard,
            // a harmless but noisy second glob), and keyed this way both dedup
            // through the one table.
            ImportKind::Plain if !self.import_is_written(&anthill_path) => Vec::new(),
            ImportKind::Plain | ImportKind::Wildcard => vec![String::new()],
            ImportKind::Selective(names) => names
                .iter()
                .filter(|n| {
                    self.import_is_written(&qualify(&anthill_path, &name_text(self.symbols, n)))
                })
                .map(|n| self.resolve(n))
                .collect(),
        };
        let fresh: Vec<String> = names
            .into_iter()
            .filter(|n| self.imported.insert((path.clone(), n.clone())))
            .collect();
        if fresh.is_empty() {
            return false;
        }

        if self.config.emit_fn_bodies {
            self.line("#[allow(unused_imports)]");
        }

        match &imp.kind {
            ImportKind::Plain => {
                self.line(&format!("use {path};"));
            }
            ImportKind::Selective(_) => {
                self.line(&format!("use {}::{{{}}};", path, fresh.join(", ")));
            }
            ImportKind::Wildcard => {
                self.line(&format!("use {path}::*;"));
            }
        }
        true
    }

    /// Does the generated code name what the import of `qualified` brings in? Not a
    /// prelude sort written as a host type (`Int64` is `i64`, `Result` is std's), nor a
    /// member of one (`Option.{some}`): the support crate exports neither. In the
    /// prelude, only what the support crate exports ([`StdlibRendering::Support`]) and
    /// what a file of this run declares are written; a prelude sort neither covers is
    /// refused where a type names it, and its `use` would not resolve.
    fn import_is_written(&self, qualified: &str) -> bool {
        let parent = qualified.rsplit_once('.').map(|(p, _)| p);
        let host =
            |q: &str| stdlib_type(q).is_some_and(|t| matches!(t.rendering, StdlibRendering::Host));
        if host(qualified) || parent.is_some_and(host) {
            return false;
        }
        if !qualified.starts_with(&format!("{PRELUDE}.")) {
            return true;
        }
        stdlib_type(qualified).is_some()
            || self.catalog.sorts.contains_key(qualified)
            || parent
                .is_some_and(|p| self.catalog.sorts.contains_key(p) && stdlib_type(p).is_none())
    }

    // ── Standalone entity → struct ───────────────────────────────

    fn emit_standalone_entity(&mut self, entity: &Entity, _enclosing_ns: Option<&Namespace>) {
        let vis = self.visibility_prefix(entity.visibility);
        let name = self.resolve(&entity.name);

        if !self.has_trait_object_field(entity.fields.iter().map(|f| &f.ty)) {
            self.emit_derive_attr();
        }
        if entity.fields.is_empty() {
            self.line(&format!("{vis}struct {name};"));
        } else {
            self.line(&format!("{vis}struct {name} {{"));
            self.indent();
            for field in &entity.fields {
                let fname = to_snake_case(&self.local_name_of(field.name));
                let ftype = self.wrap_trait_field(&self.type_to_rust(&field.ty), &field.ty);
                self.line(&format!("pub {fname}: {ftype},"));
            }
            self.dedent();
            self.line("}");
        }
    }

    // ── Sort → enum or trait ─────────────────────────────────────

    fn emit_sort(&mut self, sort: &SortWithBody) {
        // Emit sort-level imports (e.g. from `sort a.b.C` with imports inside)
        let mut wrote_use = false;
        for imp in &sort.imports {
            wrote_use |= self.emit_import(imp);
        }
        if wrote_use {
            self.blank();
        }

        let sort_name = self.resolve(&sort.name);
        let info = SortInfo::from_items(&sort.items, self.symbols);
        let previous = self.enter_sort(sort, &info);

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
        self.leave_sort(previous);
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

        // Generic parameters: the declaration's carry their defaults, the `impl`s' cannot.
        let generics = if info.type_params.is_empty() {
            String::new()
        } else {
            format!("<{}>", info.type_params.join(", "))
        };
        let declared_generics = self.declared_generics(info);

        if !self.has_trait_object_field(
            info.entities
                .iter()
                .flat_map(|e| e.fields.iter().map(|f| &f.ty)),
        ) {
            self.emit_derive_attr();
        }
        self.line(&format!("{vis}enum {sort_name}{declared_generics} {{"));
        self.indent();

        for entity in &info.entities {
            let ename = to_pascal_case(&self.resolve(&entity.name));
            if entity.fields.is_empty() {
                self.line(&format!("{ename},"));
            } else {
                self.line(&format!("{ename} {{"));
                self.indent();
                for field in &entity.fields {
                    let fname = to_snake_case(&self.local_name_of(field.name));
                    self.refuse_open_own_reference(
                        &format!("entity `{ename}`, field `{fname}`"),
                        &field.ty,
                        sort_name,
                        &info.type_params,
                    );
                    let ftype =
                        self.type_to_rust_for_enum_field(&field.ty, sort_name, &info.type_params);
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
                if !first_op {
                    self.blank();
                }
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
        if let Some(q) = &self.current_sort {
            self.trait_sorts.insert(q.clone());
        }
        let vis = self.visibility_prefix(sort.visibility);

        // Self-collapse heuristic: if exactly one type param and every op's
        // first param type matches it → collapse to Self, don't emit generic
        let collapse_self = should_collapse_self(info, self.symbols);

        // Determine trait generics (non-collapsed type params)
        let trait_generics = if collapse_self {
            String::new()
        } else {
            self.declared_generics(info)
        };

        // Supertraits
        let supertrait_clause = if info.supertraits.is_empty() {
            String::new()
        } else {
            format!(": {}", info.supertraits.join(" + "))
        };

        self.line(&format!(
            "{vis}trait {sort_name}{trait_generics}{supertrait_clause} {{"
        ));
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
            if !first_op {
                self.blank();
            }
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
        if self.names_current_sort(ty) {
            // Self-referential → Box
            let generics = if type_params.is_empty() {
                String::new()
            } else {
                format!("<{}>", type_params.join(", "))
            };
            format!("Box<{sort_name}{generics}>")
        } else {
            // WI-540: a trait-typed enum field becomes `Box<dyn Trait>`.
            self.wrap_trait_field(&self.type_to_rust(ty), ty)
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
        self.push_operation_scope(op);
        self.refuse_open_own_references_in(op, sort_name, type_params);
        let op_name = to_snake_case(&self.resolve(&op.name));
        let effects = self.analyze_effects(&op.effects, type_params);

        // Per-op type params (`operation foldLeft[EffP, Acc]`) → method generics,
        // but ONLY the ones that surface in a value-type position (a param/return
        // type). An effect-only param (`EffP`, used solely in `@ {EffP}` / `effects`)
        // has no Rust witness — emitting it as an unconstrained generic would break
        // call-site inference — so it is erased.
        let method_type_params: Vec<String> = op
            .type_params
            .iter()
            .map(|tp| self.local_name_of(tp.name))
            .filter(|name| {
                op.params.iter().any(|p| self.type_mentions(&p.ty, name))
                    || self.type_mentions(&op.return_type, name)
            })
            .collect();
        let method_generics = if method_type_params.is_empty() {
            String::new()
        } else {
            format!("<{}>", method_type_params.join(", "))
        };

        // Determine self-arg
        let (has_self, is_mut) = self.check_self_arg(op, type_params, &effects, collapse_self);

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
            let pname = to_snake_case(&self.local_name_of(param.name));
            let ptype = self.type_to_rust_in_sort(&param.ty, type_params, collapse_self);
            let ptype = self.wrap_trait_param(&ptype, &param.ty, sort_name);
            params_str.push_str(&format!("{pname}: {ptype}"));
        }

        // Return type
        let raw_ret = self.type_to_rust_in_sort(&op.return_type, type_params, collapse_self);
        let raw_ret =
            self.wrap_trait_return_in_sort(&raw_ret, &op.return_type, sort_name, type_params);
        let ret = wrap_return_type(&raw_ret, &effects);

        // Object-safety: a self-less method (a factory like `kb() -> Box<dyn KB>`)
        // OR a generic method (`fold_left<Acc>`) makes the trait non-`dyn`-compatible.
        // Under `boxed_trait_objects` — where the trait IS used as `&dyn Trait` —
        // bound such methods on `Self: Sized` so they are excluded from the vtable
        // and the trait stays object-safe. Gated by the flag to keep default output
        // unchanged.
        let where_clause =
            if self.config.boxed_trait_objects && (!has_self || !method_type_params.is_empty()) {
                " where Self: Sized"
            } else {
                ""
            };
        self.line(&format!(
            "fn {op_name}{method_generics}({params_str}) -> {ret}{where_clause};"
        ));
        self.pop_scope();
    }

    fn emit_method_signature(
        &mut self,
        op: &Operation,
        sort_name: &str,
        type_params: &[String],
        in_impl: bool,
    ) {
        self.push_operation_scope(op);
        self.refuse_open_own_references_in(op, sort_name, type_params);
        let vis = if in_impl {
            self.visibility_prefix(op.visibility)
        } else {
            ""
        };
        let op_name = to_snake_case(&self.resolve(&op.name));
        let effects = self.analyze_effects(&op.effects, type_params);

        let (has_self, is_mut) = self.check_self_arg(op, type_params, &effects, false);

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
            let pname = to_snake_case(&self.local_name_of(param.name));
            let ptype = self.type_to_rust_in_sort(&param.ty, type_params, false);
            // Preserve the original bare-param emission when the flag is off;
            // only trait-object wrapping is opt-in (WI-540).
            let ptype = if self.config.boxed_trait_objects {
                self.wrap_trait_param(&ptype, &param.ty, sort_name)
            } else {
                ptype
            };
            params_str.push_str(&format!("{pname}: {ptype}"));
        }

        let raw_ret = self.type_to_rust_in_sort(&op.return_type, type_params, false);
        let raw_ret =
            self.wrap_trait_return_in_sort(&raw_ret, &op.return_type, sort_name, type_params);
        let ret = wrap_return_type(&raw_ret, &effects);

        self.line(&format!("{vis}fn {op_name}({params_str}) -> {ret};"));
        self.pop_scope();
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
            if !first {
                self.blank();
            }
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
        self.push_operation_scope(op);
        let op_name = to_snake_case(&self.resolve(&op.name));
        let effects = self.analyze_effects(&op.effects, &[]);

        let mut params_str = String::from("&self");

        for param in &op.params {
            params_str.push_str(", ");
            let pname = to_snake_case(&self.local_name_of(param.name));
            let ptype = self.type_to_rust(&param.ty);
            params_str.push_str(&format!("{pname}: {ptype}"));
        }

        let raw_ret = self.type_to_rust(&op.return_type);
        let raw_ret = self.wrap_trait_return(&raw_ret, &op.return_type);
        let ret = wrap_return_type(&raw_ret, &effects);

        self.line(&format!("fn {op_name}({params_str}) -> {ret};"));
        self.pop_scope();
    }

    /// Check if the first param should become self.
    fn check_self_arg(
        &self,
        op: &Operation,
        type_params: &[String],
        effects: &EffectInfo,
        collapse_type_params: bool,
    ) -> (bool, bool) {
        if op.params.is_empty() {
            return (false, false);
        }

        let first_type = &op.params[0].ty;

        // Check if first param type is the sort itself or a type param
        let is_self = self.names_current_sort(first_type)
            || (collapse_type_params
                && matches!(first_type, TypeExpr::Simple(n)
                    if matches!(self.denote(n), Denoted::Param(p) if type_params.contains(&p))));

        if !is_self {
            return (false, false);
        }

        // Check if the first param is the target of a Modifies effect
        let first_param_name = self.local_name_of(op.params[0].name);
        let is_mut = effects
            .modifies_targets
            .iter()
            .any(|t| t == &first_param_name);

        (true, is_mut)
    }

    /// What an operation's effects clause asks of its Rust signature: the parameters a
    /// `Modify` mutates (receiver by `&mut`) and the `Error` payload (`Result<R, P>`).
    /// A label is read by what its name resolves to, and only the payload that decides
    /// the signature is rendered.
    fn analyze_effects(&self, effects: &[Effect], type_params: &[String]) -> EffectInfo {
        let mut modifies_targets = Vec::new();
        let mut payload = None;
        for effect in effects {
            self.read_effect(
                &effect.type_expr,
                false,
                type_params,
                &mut modifies_targets,
                &mut payload,
            );
        }
        EffectInfo {
            modifies_targets,
            errors_type: payload.map(|p| match p {
                ErrorPayload::Type(ty) => self.type_to_rust(ty),
                ErrorPayload::Named(name) => name,
            }),
        }
    }

    /// [`Self::analyze_effects`] for one label. A later label's payload replaces an
    /// earlier one, except that a GUARDED label only fills an empty slot.
    fn read_effect<'t>(
        &self,
        label: &'t TypeExpr,
        guarded: bool,
        type_params: &[String],
        modifies_targets: &mut Vec<String>,
        payload: &mut Option<ErrorPayload<'t>>,
    ) {
        let mut set = |p: ErrorPayload<'t>| {
            if !guarded || payload.is_none() {
                *payload = Some(p);
            }
        };
        match label {
            TypeExpr::Parameterized { name, bindings } if !leaves_every_slot(bindings) => {
                let Some(b) = bindings.first() else {
                    return;
                };
                match self.denoted_qualified(name).as_deref() {
                    // `Modify[c]` names the parameter `c` it mutates.
                    Some(MODIFY_LABEL) => {
                        if let TypeExpr::Simple(n) = &b.bound {
                            modifies_targets.push(self.symbols.local_name(n.last()).to_owned());
                        }
                    }
                    Some(ERROR_LABEL) if !matches!(b.bound, TypeExpr::Variable { .. }) => {
                        set(ErrorPayload::Type(&b.bound));
                    }
                    _ => {}
                }
            }
            // A label written bare, or applied with every slot left open.
            TypeExpr::Simple(name) | TypeExpr::Parameterized { name, .. } => {
                match self.denote(name) {
                    // Bare Error (no type param) → Result<R, Error>
                    Denoted::Declared(q) | Denoted::UnmappedPrelude(q) | Denoted::NotFound(q)
                        if q == ERROR_LABEL =>
                    {
                        set(ErrorPayload::Named("Error".to_owned()));
                    }
                    // Abstract effect: a type parameter of the enclosing sort is an
                    // abstract error type. E.g. `effects (E)` where `sort E = ?` →
                    // Result<R, E>
                    Denoted::Param(p) if type_params.contains(&p) => {
                        set(ErrorPayload::Named(p));
                    }
                    _ => {}
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
            // WI-478: a guarded effect is CONSERVATIVELY PRESENT (phase 1 — discharge
            // is WI-067), so it contributes the SAME Modify/Error analysis its bare
            // label would (a `Error[X] :- g` still yields the `Error[X]` Result, not a
            // silent drop).
            TypeExpr::EffectGuarded { label, .. } => {
                self.read_effect(label, true, type_params, modifies_targets, payload);
            }
        }
    }

    /// The qualified name `name` resolves to, when it resolves to a sort.
    fn denoted_qualified(&self, name: &Name) -> Option<String> {
        self.denote(name).qualified().map(str::to_owned)
    }

    // ── Secondary entry's `provides` → impl marker comment ───────

    /// A SECONDARY ENTRY's spec claims → the `impl <Trait> for <Carrier>` marker
    /// comments. `namespace FileStore { provides Modifiable[T = FileStore] }` renders
    /// `// impl Modifiable for FileStore`.
    ///
    /// THE CARRIER IS THE ADDRESS (WI-20260917-S8JYF), which is the whole reason this
    /// replaced `emit_namespace_fact`. That function read a namespace-level `fact
    /// QueryableStore[SqlStore]` and took the carrier from the BRACKETS — itself a
    /// WI-933 repair of an earlier reading that took the entity PRECEDING the fact
    /// (measured: `entity SqlStore(…) entity ColumnDef(…) fact QueryableStore[SqlStore]`
    /// emitted `// impl QueryableStore for ColumnDef`, discarding the author's carrier).
    /// The retirement removes the question: a `fact` at namespace level is an ordinary
    /// fact and names no carrier at all, while a provision names its provider by WHERE
    /// it is written, so the enclosing block's own name IS the carrier and nothing is
    /// derived, guessed or read out of a binding.
    ///
    /// NO DATA-SORT GATE, and it is not needed. `emit_namespace_fact` carried one
    /// (WI-1106), because `fact Polynom[Coeff]` — an ordinary instantiation fact over a
    /// parametric DATA sort — is shaped exactly like a claim and used to emit `// impl
    /// Polynom for Coeff`. A `provides` clause has no second reading, and the loader
    /// refuses one naming a data sort outright (`ProvidesNamesDataSort`).
    ///
    /// THE BLOCK'S OWN CONTENT still emits as a module: a secondary entry may also
    /// declare operations (059 R2), and this reads only its `provides` items.
    fn emit_secondary_entry_provisions(&mut self, ns: &Namespace) {
        let carrier = self.resolve(&ns.name);
        // The LOCAL segment: a secondary entry may be written `namespace anthill.prelude.Int64`.
        let carrier = carrier.rsplit('.').next().unwrap_or(&carrier).to_string();
        for item in &ns.items {
            if let Item::ProvidesClause(pc) = item {
                let trait_name = type_expr_name(self.symbols, &pc.spec);
                self.line(&format!("// impl {trait_name} for {carrier}"));
            }
        }
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
        let labeled: Vec<_> = rules.iter().filter(|r| r.label.is_some()).collect();

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

/// Is every binding written `?` alone — the application its bare name is (`Error[T = ?]` is
/// `Error`, kernel-language §8.1)? Read for the `Error` label, which maps by its spelling.
fn leaves_every_slot(bindings: &[SortBinding]) -> bool {
    !bindings.is_empty()
        && bindings
            .iter()
            .all(|b| matches!(b.bound, TypeExpr::Variable { fresh: true, .. }))
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
            TypeExpr::Simple(name) => symbols.local_name(name.last()).to_owned(),
            TypeExpr::Parameterized { name, .. } => symbols.local_name(name.last()).to_owned(),
            TypeExpr::Variable { .. } => "T".to_owned(),
            TypeExpr::Tuple(_) => "Tuple".to_owned(),
            TypeExpr::Arrow { .. } => "Fn".to_owned(),
            TypeExpr::Denoted(_) => "Denoted".to_owned(),
            TypeExpr::EffectAbsent(_) => "EffectAbsent".to_owned(),
            TypeExpr::EffectRow(_) => "EffectRow".to_owned(),
            TypeExpr::EffectGuarded { .. } => "EffectGuarded".to_owned(),
        };

        if first_type != *param_name {
            return false;
        }
    }

    true
}

// ── Utility functions ────────────────────────────────────────────

/// Rust SOURCE expression for a bodyless host-supplied Float const (WI-532):
/// `infinity`/`negativeInfinity`/`nan`. Matched by short name (rust.rs runs on the
/// raw ParsedFile, before name resolution), gated by the caller on an `f64` declared
/// type so a non-Float same-named const can't collide.
///
/// WI-889 — this table STAYS hardcoded while the rust RUNTIME (`register_const_mappings`)
/// and cpp-gen (`HostConstTable`) went data-driven off `const_map` / `ConstMapping`
/// facts, for two reasons that are specific to the rust source-GENERATOR: it lowers
/// the raw `ParsedFile` before the KB exists, so there are no resolved facts to read;
/// and even if there were, the value it needs is a Rust SOURCE spelling (`f64::INFINITY`),
/// NOT the runtime registry key (`float_infinity`) the `lang == "rust"` `const_map`
/// carries — the interpreter and the source generator are two different "rust" consumers
/// that need different host spellings for the same const, which `lang` alone cannot
/// distinguish. Making this path data-driven is a wider question (a source-spelling
/// channel, e.g. a distinct `lang`) than WI-889's, whose line was the two hardcoded
/// lists the ticket named. `operation_map` has the same untaken step for rust codegen.
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
        "as", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern", "false",
        "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub",
        "ref", "return", "self", "Self", "static", "struct", "super", "trait", "true", "type",
        "unsafe", "use", "where", "while", "async", "await", "abstract", "become", "box", "do",
        "final", "macro", "override", "priv", "typeof", "unsized", "virtual", "yield", "try",
    ];
    match name.as_str() {
        "crate" | "self" | "super" | "Self" => format!("{name}_"),
        n if RESERVED.contains(&n) => format!("r#{name}"),
        _ => name,
    }
}

/// Get the short name from a TypeExpr.
fn type_expr_name(symbols: &SymbolTable, ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Simple(name) => symbols.local_name(name.last()).to_owned(),
        TypeExpr::Parameterized { name, .. } => symbols.local_name(name.last()).to_owned(),
        TypeExpr::Variable { .. } => "T".to_owned(),
        TypeExpr::Tuple(_) => "Tuple".to_owned(),
        TypeExpr::Arrow { .. } => "Fn".to_owned(),
        TypeExpr::Denoted(_) => "Denoted".to_owned(),
        TypeExpr::EffectAbsent(_) => "EffectAbsent".to_owned(),
        TypeExpr::EffectRow(_) => "EffectRow".to_owned(),
        TypeExpr::EffectGuarded { .. } => "EffectGuarded".to_owned(),
    }
}

/// The FULLY-QUALIFIED name of a named type expression's head — every segment
/// joined, not just the last one (`type_expr_name` returns the short name).
/// Used where recognition must key on the CANONICAL symbol rather than a short
/// name: matching the `anthill.prelude.EffectsRuntime` kind-anchor by short name
/// alone would also fire for a user sort merely NAMED `EffectsRuntime` in another
/// namespace. Non-named variants fall back to `type_expr_name`.
fn type_expr_qualified_name(symbols: &SymbolTable, ty: &TypeExpr) -> String {
    let segments = match ty {
        TypeExpr::Simple(name) => &name.segments,
        TypeExpr::Parameterized { name, .. } => &name.segments,
        _ => return type_expr_name(symbols, ty),
    };
    segments
        .iter()
        .map(|s| symbols.local_name(*s))
        .collect::<Vec<_>>()
        .join(".")
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

/// Replace every whole-word occurrence of `word` in `s` with `replacement`.
/// "Whole-word" = not flanked by an identifier character, so `Self` inside a
/// larger identifier is left intact. Used to box a `Self` token (bare or nested,
/// e.g. inside `Option<Pair<T, Self>>`) into the object-safe trait-object form.
fn replace_word(s: &str, word: &str, replacement: &str) -> String {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_';
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(pos) = rest.find(word) {
        let (before, after) = rest.split_at(pos);
        let after_word = &after[word.len()..];
        let prev_ok = before.chars().last().map_or(true, |c| !is_ident(c));
        let next_ok = after_word.chars().next().map_or(true, |c| !is_ident(c));
        out.push_str(before);
        out.push_str(if prev_ok && next_ok {
            replacement
        } else {
            word
        });
        rest = after_word;
    }
    out.push_str(rest);
    out
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
}
