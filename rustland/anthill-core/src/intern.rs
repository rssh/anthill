/// Symbol table — maps strings to compact `Symbol(u32)` handles,
/// with optional resolution metadata (kind, scope, qualified name).
///
/// Symbols can be **Unresolved** (just a name, deduplicated) or
/// **Resolved** (local name + qualified name + kinds + parent scope).
/// The scan-then-load pipeline defines symbols during scanning, then
/// resolves references during loading.

use std::collections::{HashMap, HashSet};
use smallvec::SmallVec;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Symbol(u32);

impl Symbol {
    pub fn index(self) -> u32 {
        self.0
    }

    /// Create from raw index. Used for synthetic VarIds (de Bruijn). `const` so
    /// a fixed symbol can be a `const` (e.g. a test's stable functor id).
    pub const fn from_raw(raw: u32) -> Self {
        Symbol(raw)
    }
}

// ── ScopeId ─────────────────────────────────────────────────────

/// WI-984 — A SCOPE, AS A TYPE. The lexical scope a `namespace`, a `sort` body,
/// an operation frame or the top-level `_global` opens, identified by THE SYMBOL
/// THAT OWNS IT.
///
/// IT WRAPS THE SYMBOL, NOT THE TERM, and that is the whole design. Scope keys
/// used to be the `TermId` raw of the owner's nullary name term, which made the
/// owner projection a QUERY — fetch the term, match a nullary `Term::Fn`, answer
/// `Option` — and that query is not total: [`crate::kb::KnowledgeBase::alloc`]
/// rewrites a CONSTRUCTOR symbol's nullary `Fn` to a `Term::Ref` (WI-511), so
/// every scope owned by a constructor answered `None`. MEASURED over a stdlib
/// load before this change: 227 of 2602 resolved symbols — every entity FIELD,
/// whose declaring scope is its constructor — got `None` from
/// `declaring_scope_symbol`, and `scope(?sym, ?r)` failed on each. Off the
/// symbol the projection is TOTAL and no representation can make it fail.
///
/// WHAT THIS TYPE CLOSES: a scope can no longer be built from a bare integer, a
/// `TermId`, or an arbitrary index — [`SymbolTable::scope_id`] is the only
/// constructor and it takes a `Symbol`. "This raw is a scope" stopped being a
/// promise each caller carries.
///
/// AND THE LOADER CARRIES IT, not just the table (WI-1028). WI-984 typed the
/// `SymbolTable` API but left the loader holding scope TERMS and projecting back at
/// 89 sites; the `ScopePass` spine, `ScopeSite.enclosing`, `Loader::current_scope`
/// and the scope finders are all `ScopeId` now, so a value in a scope position names
/// a scope AT THE WRITE. What that buys is not throughput (measured at ~0.5% of a
/// debug load, immaterial) — it is that the derivation was hiding a decision:
/// `load_provides_block` assigned an APPLIED spec term as its scope, and "what scope
/// does that name?" surfaced only when the projection aborted, 22 reads later.
///
/// GOING BACK THE OTHER WAY IS NOT FREE, and the rule reads as if it were.
/// `make_name_term_from_sym(scope.owner())` is the same call that built the term the
/// spine used to carry, so it yields the same hash-consed `TermId` — but it routes
/// through the WI-511 canon, which spells a CONSTRUCTOR owner `Term::Ref` and every
/// other owner `Term::Fn`. A caller that then matches the term's SHAPE is reading
/// `is_constructor_symbol` without naming it — which is what `load::is_sort_scope`
/// did until WI-1029, and what WI-926 leans on. Derive the term only to PUT it where
/// a term goes; to ask a question about the scope, ask the owner.
///
/// WHAT IT DOES NOT CLOSE, stated rather than implied. TWO HOLES, both about
/// PROVENANCE — nothing here says WHERE the owning symbol came from.
///
///  1. WHICH TABLE issued it (WI-1004). The loader threads two symbol tables — the
///     KB's and the parse-side `ParsedFile`'s — and a `Symbol` carries no table of
///     its own (the term store and the discrimination tree key on it and have no
///     table to speak of). Scala closes this with a path-dependent `opaque type`
///     member; Rust has no path-dependent types, so the mint's range check is all
///     that is available here, and it catches only the direction where the foreign
///     table is the LARGER one. Asserted, not papered over — see
///     `scope_id_refuses_a_symbol_this_table_never_issued`. Closing it properly
///     needs the symbol TAGGED with its table, which is WI-1004's question, not
///     this type's.
///  2. [`Symbol::from_raw`] is `pub const`, so `st.scope_id(Symbol::from_raw(3))`
///     compiles and, in range, succeeds. The compile errors below say a scope
///     cannot be built from an integer *in a scope position*; they do not say an
///     integer can never reach one, and that hop is one call long.
///
/// THE REFUSALS, AS COMPILE ERRORS — WI-984's acceptance criterion, spelled so a
/// change that re-admits any of them fails the build instead of passing quietly.
///
/// A raw integer is not a scope:
/// ```compile_fail
/// use anthill_core::intern::{SymbolTable, SymbolKind};
/// let mut st = SymbolTable::new();
/// st.define("x", "A.x", SymbolKind::Operation, 10u32);
/// ```
///
/// Nor a term's raw id — the same rejection as above, since `TermId::raw()` IS a
/// `u32`, kept because "a scope is not a term" is the half of the criterion a
/// reader comes here to check:
/// ```compile_fail
/// use anthill_core::kb::KnowledgeBase;
/// use anthill_core::intern::SymbolKind;
/// let mut kb = KnowledgeBase::new();
/// let t = kb.make_name_term("_global");
/// kb.define_symbol("x", "A.x", SymbolKind::Operation, t.raw());
/// ```
///
/// And one cannot be conjured without a table to issue its owner:
/// ```compile_fail
/// use anthill_core::intern::{ScopeId, Symbol};
/// let _ = ScopeId(Symbol::from_raw(3));
/// ```
///
/// What DOES work is the one mint:
/// ```
/// use anthill_core::intern::{SymbolTable, SymbolKind};
/// let mut st = SymbolTable::new();
/// let owner = st.intern("A");
/// let scope = st.scope_id(owner);
/// let x = st.define("x", "A.x", SymbolKind::Operation, scope);
/// assert_eq!(st.declaring_scope(x).map(|s| s.owner()), Some(owner));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ScopeId(Symbol);

impl ScopeId {
    /// The symbol that OWNS this scope — `Tank` for the scope `Tank.fill` is
    /// declared in. A TOTAL projection: no fetch, no match, no `Option`. The
    /// reason this newtype wraps the symbol.
    pub fn owner(self) -> Symbol {
        self.0
    }
}

// ── Symbol metadata ─────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolKind {
    Sort,
    Entity,
    Operation,
    /// A term-level named constant (proposal 039 / WI-084) — `const NAME: T [=
    /// EXPR]`. A nullary, carrier-independent value identity: value-denoting in
    /// TERM position (the typer's `check_bare_ref` reads its declared type; eval
    /// materializes its memoized value). NOT in `is_value_place()` — that set is
    /// for frame-relative value PLACES within a binder's scope (value-in-TYPE
    /// lowering); a `Const` is a global identity, gated separately at the
    /// term-position sites. Distinct from `Operation`: a const is value-denoting
    /// where an operation (until first-class operations land) is not.
    Const,
    Namespace,
    Fact,
    Rule,
    Constraint,
    /// An operation parameter — the `input` place of the operation frame
    /// (proposal 046 / WI-352). Also the implicit dataflow `provenance` of the
    /// name: an op param IS its input.
    Param,
    Field,
    /// A RELATION: the head functor of a predicate rule (`adult(?x) :- …`), and
    /// the `<Sort>.induction` schema. Its clauses are indexed UNDER THIS NAME, so
    /// `rule_ids_by_qn` finds them — which is what makes it a first-class
    /// `Relation[T]` value at the WI-714 citation positions (bare, applied, and
    /// as an argument).
    ///
    /// SEE [`SymbolKind::EquationFunctor`] BEFORE ADDING A READER: the two are
    /// both "a name a rule introduced" and were one kind until WI-898, but only
    /// this one owns clauses.
    Goal,
    /// WI-898 — the subject of a bodyless EQUATION (`ite(true, ?t, ?_) = ?t`):
    /// a function DEFINED BY REWRITING, whose call sites reduce (`[simp]`) rather
    /// than dispatch. Minted by `load::scan_rule_goal` alongside [`SymbolKind::Goal`],
    /// from the same head walk, because both are names a rule introduces.
    ///
    /// IT IS NOT A RELATION, and that is the whole reason it is a separate kind.
    /// An equation's clauses are indexed under the `eq`/`unify` CONNECTIVE, not
    /// under this functor — so every WI-714 reader (`relation_columns_across_clauses`
    /// and friends) finds ZERO clauses for it and reports "unresolved name" about a
    /// name that resolved perfectly well. Borrowing `Goal` for it made that
    /// misdiagnosis reachable from the spelling WI-894 recommends.
    EquationFunctor,
    // ── Operation-frame places (WI-352) ─────────────────────────────
    // The reserved result and callback-derived binders introduced by an
    // operation signature. WI-351 mis-tagged these as `Param` (a result is
    // not a parameter) and kept the real classification in an external
    // `place_roles` side-table; WI-352 moves the truth onto the symbol's
    // kind, so `provenance` and `is_result_binder` are functions of it. These
    // route as values and stay scope-encapsulated exactly like `Param`.
    /// The operation's reserved return-value name `<op>.result` (and its
    /// tuple-field projections) — proposal 041. `provenance = op_result`;
    /// `is_result_binder(sym) == (kind == OpResult)`.
    OpResult,
    /// A parameter of a callback-typed op parameter — `<op>.f.a`. A flow
    /// *target* (the op feeds it); carries no `provenance` of its own.
    CallbackParam,
    /// A callback-typed op parameter's result — `<op>.f.result`.
    /// `provenance = fresh_output` (the callback mints it inside the op).
    CallbackResult,
    /// A `let`-bound local in an operation body. `provenance = local`.
    /// (WI-352 reserves the kind; *tagging* let-locals with it — interning
    /// them as scoped symbols during body lowering — is deferred.)
    LocalLet,
}

impl SymbolKind {
    /// True for the frame-/instance-relative VALUE-PLACE kinds — an operation or
    /// callback parameter, a result binder, an entity field, or a `let`-local.
    /// These name a place WITHIN some binder's scope, NOT a global identity
    /// (`Sort`/`Entity`/`Operation`/…), so a reference to one is binder-relative:
    /// meaningful only up to binder alignment. The single source of truth for that
    /// classification — used by the loader's value-in-type lowering
    /// (`symbol_is_value_place`) and the typer's value-in-type groundness gate
    /// (`denoted_value_is_closed`, WI-470), which must agree on the set.
    pub fn is_value_place(self) -> bool {
        matches!(
            self,
            SymbolKind::Param
                | SymbolKind::Field
                | SymbolKind::LocalLet
                | SymbolKind::OpResult
                | SymbolKind::CallbackParam
                | SymbolKind::CallbackResult
        )
    }

    /// The kind's REFLECT NAME — the string `kind(?sym, ?k)` binds, in the
    /// resolver's builtin and in the `anthill-stl` eval bridge alike. One table
    /// (WI-898): the two readers each carried their own exhaustive copy, so adding
    /// a kind meant editing both and a program could see `"Goal"` from one and a
    /// compile error from the other.
    ///
    /// RESOLVED kinds only. The two readers still part ways on an UNRESOLVED symbol —
    /// the resolver builtin FAILS the goal, the eval bridge answers `"Unresolved"` —
    /// and that difference is theirs to own (a builtin failing a goal is not a string
    /// it could have returned), so do not read this table as unifying it.
    pub fn reflect_name(self) -> &'static str {
        match self {
            SymbolKind::Sort => "Sort",
            SymbolKind::Entity => "Entity",
            SymbolKind::Operation => "Operation",
            SymbolKind::Const => "Const",
            SymbolKind::Namespace => "Namespace",
            SymbolKind::Fact => "Fact",
            SymbolKind::Rule => "Rule",
            SymbolKind::Constraint => "Constraint",
            SymbolKind::Param => "Param",
            SymbolKind::Field => "Field",
            SymbolKind::Goal => "Goal",
            SymbolKind::EquationFunctor => "EquationFunctor",
            SymbolKind::OpResult => "OpResult",
            SymbolKind::CallbackParam => "CallbackParam",
            SymbolKind::CallbackResult => "CallbackResult",
            SymbolKind::LocalLet => "LocalLet",
        }
    }
}

#[derive(Clone, Debug)]
pub enum SymbolDef {
    Unresolved {
        name: String,
    },
    Resolved {
        local_name: String,
        qualified_name: String,
        /// The categories this name PLAYS, in declaration order — a set, not a
        /// single value, because one written name can genuinely be more than one
        /// thing. §6.3's eponymous constructor IS its sort: `sort Project { entity
        /// Project(…) }` writes one name that is both a `Sort` and an `Entity`,
        /// and so does the sugar `entity Project(…)` it desugars from.
        ///
        /// It used to be one `SymbolKind`, so a name that plays two roles could
        /// record only the one that got there first, and the same two declarations
        /// in the opposite order produced a different `kind` (measured, WI-926).
        /// That is not a category; it is an accident of source order.
        ///
        /// The loser was not always dropped in the same place, which is why the
        /// categories are written from the DECLARATION rather than left to
        /// whichever code path minted the symbol: `define` reuses an existing
        /// symbol on a repeated short name, and the loader has two further arms
        /// (an eponymous constructor reusing its sort's symbol, and a
        /// by-qualified-name reuse) that never reach `define` at all. See
        /// `scan_items_pass1`'s `Item::Entity` arm.
        ///
        /// Order is kept (not a bitset) because it is the one real piece of
        /// information beyond membership: the head is the keyword the declaration
        /// actually opened with, which is what [`Self::primary_kind`] — and hence
        /// `kind_of` — reports, exactly as the single field did.
        ///
        /// Ask [`Self::has_kind`] for "does this name play role X" — that is the
        /// question most readers mean, and it is order-free. [`Self::primary_kind`]
        /// is right for exactly two things: DISPLAY (a diagnostic, reflect's `kind`
        /// string), and a genuinely EXCLUSIVE discriminator, where "any role
        /// qualifies" would be the wrong question — the loader's
        /// `symbol_is_value_place` is one, since its caller branches on the false
        /// case. Asking `primary_kind() == Sort` to decide whether a name is USABLE
        /// as a sort is the misuse: it re-creates the source-order dependence this
        /// field exists to remove.
        ///
        /// Not yet uniform: many `kind_of` call sites predate the set and still
        /// compare it to a single kind. Each is only correct where the exclusive
        /// reading is intended; they were left alone rather than swept, because the
        /// two readings coincide for every symbol carrying ONE category and only a
        /// site-by-site judgement can tell which was meant.
        kinds: SmallVec<[SymbolKind; 2]>,
        /// The scope this name was DECLARED IN. A [`ScopeId`] since WI-984 — it
        /// was a bare `u32` (the owner's name-term raw), which made it one type
        /// with an arbitrary term and an arbitrary index.
        scope: ScopeId,
        /// WI-352 — for a *callable* place (an operation, or a callback-typed
        /// parameter), the ordered argument-place symbols it binds: an op's
        /// param places (`reduce.xs`, `reduce.z`, `reduce.f`) or a callback's
        /// own param places (`reduce.f.a`, `reduce.f.t`). Empty for everything
        /// else. This makes the higher-order structure self-describing on the
        /// symbol, so a body's `apply(F, args)` maps `args[i]` to `F`'s i-th
        /// place purely from symbol data — what the flow-derivation pass keys
        /// on, for the op (self-recursion) and callbacks alike. The result
        /// place is `<F>.result`, found by name, so it is not stored here.
        arg_places: Vec<Symbol>,
    },
}

impl SymbolTable {
    /// Record that `sym` also plays `kind`. Idempotent, order-preserving: the
    /// first-declared category stays the head, so `primary_kind` (and `kind_of`)
    /// keep reporting the keyword the declaration opened with.
    ///
    /// The explicit companion to `define`'s accumulation, for the case where a
    /// second role is discovered WITHOUT a second `define` call — §6.3's eponymous
    /// constructor, which reuses the enclosing sort's symbol rather than defining
    /// a nested one, so nothing would otherwise record that the name also
    /// constructs.
    pub fn add_kind(&mut self, sym: Symbol, kind: SymbolKind) {
        if let Some(SymbolDef::Resolved { kinds, .. }) = self.defs.get_mut(sym.0 as usize) {
            if !kinds.contains(&kind) {
                kinds.push(kind);
            }
        }
    }
}

impl SymbolDef {
    /// The categories this name plays, declaration order. Empty for `Unresolved`.
    pub fn kinds(&self) -> &[SymbolKind] {
        match self {
            SymbolDef::Resolved { kinds, .. } => kinds,
            SymbolDef::Unresolved { .. } => &[],
        }
    }

    /// Does this name play role `kind`? THE question almost every caller means.
    pub fn has_kind(&self, kind: SymbolKind) -> bool {
        self.kinds().contains(&kind)
    }

    /// The keyword the declaration opened with — for DISPLAY only (diagnostics,
    /// reflect's `kind` string). Not a test for what the name can be used as:
    /// see [`Self::has_kind`].
    pub fn primary_kind(&self) -> Option<SymbolKind> {
        self.kinds().first().copied()
    }
}

/// A scope's link to a parent scope — an enclosing body, a `requires`, an import.
///
/// WI-994: `PartialEq` is what makes [`SymbolTable::add_parent`] idempotent — a
/// scope's parents are a SET.
///
/// WI-984 removed a third field, `instantiation_term_raw: u32`: the `TermId` raw
/// of the type expression a `requires` was written with. It was written by 18
/// sites and read by NOTHING except this derived `PartialEq`, where it split
/// `requires Eq[T = Int]` and `requires Eq[T = String]` on one scope into two
/// links. That split was never observable — [`SymbolTable::resolve_in_scope`] and
/// [`SymbolTable::internal_visible_from`] read only `parent_scope` and
/// `is_enclosing`, so both links resolve identically — so the field's departure
/// merges them and leaves every resolution answer alone. The faithful
/// instantiation still rides on the `SortRequiresInfo` / `SortProvidesInfo` value
/// facts, which is where a reader should look for it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScopeInclusion {
    pub parent_scope: ScopeId,
    /// If true, this is an enclosing-scope relationship (sort/namespace body)
    /// and the variant-exposure (`exposed`-set) filter is bypassed.
    pub is_enclosing: bool,
}

// ── Resolution result ───────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveResult {
    Found(Symbol),
    Ambiguous(Vec<Symbol>),
    NotFound,
}

impl ResolveResult {
    /// Does the name DENOTE something here — one symbol or several? The negation of
    /// `NotFound`, named, because that is the question the name ladder is built on:
    /// `Found` and `Ambiguous` are both ANSWERS, and only `NotFound` licenses trying a
    /// lower rung (kernel-language.md §8.6, WI-907).
    ///
    /// Asked directly by the positions that need the verdict and not the symbol — the
    /// rule-head mint guard (`load::name_denotes_for_rule_head`) and the dot-call
    /// re-route gate (`Loader::qualified_name_resolves`).
    pub fn denotes(&self) -> bool {
        !matches!(self, ResolveResult::NotFound)
    }

    /// THE LADDER STEP: this answer if it [`denotes`](Self::denotes) anything, else the
    /// next rung's. One spelling of "an ambiguity ends the ladder" for every ladder in
    /// the tree — before WI-917 gave the dotted rung this vocabulary the rule was
    /// re-derived per site, and the site that re-derived it WRONG (silently standing an
    /// ambiguity down as if it were a miss) is what that ticket was.
    pub fn or_else(self, next: impl FnOnce() -> ResolveResult) -> ResolveResult {
        if self.denotes() { self } else { next() }
    }
}

// ── Scope ───────────────────────────────────────────────────────

/// All per-scope data consolidated into one struct.
#[derive(Debug, Default)]
pub struct Scope {
    /// Definitions in this scope: local_name → Symbol
    pub locals: HashMap<String, Symbol>,
    /// Imported aliases: local_name → original Symbol
    pub imports: HashMap<String, Symbol>,
    /// Names this scope exposes to the enclosing scope through a
    /// (non-enclosing) variant-exposure parent link — populated from a sort's
    /// entity-variant short names ONLY. An empty set disables the filter (the
    /// scope is reachable only via `requires`/wildcard, which see everything).
    /// Names are visible by default (proposal 044); the `export` statement that
    /// once restricted this was removed in WI-291.
    pub exposed: HashSet<String>,
    /// Parent scope inclusions (enclosing + requires + imports)
    pub parents: Vec<ScopeInclusion>,
    /// Type parameter names (excluded from parent lookups)
    pub type_params: HashSet<String>,
    /// Type parameter names in declaration order. Parallel to
    /// `type_params` for membership tests; this is what positional
    /// sort bindings (e.g. `Map[String, Int]` for a `sort Map { sort
    /// K = ?; sort V = ? }`) consult to map index 0 → "K", index 1 →
    /// "V". Insertion-order preserves the source-text declaration
    /// order, which is the binding contract.
    pub type_params_ordered: Vec<String>,
}

// ── SymbolTable ─────────────────────────────────────────────────

#[derive(Debug, Default)]
pub struct SymbolTable {
    defs: Vec<SymbolDef>,
    /// Dedup map for Unresolved symbols: name → Symbol
    pub(crate) intern_map: HashMap<String, Symbol>,
    /// Qualified name → unique resolved Symbol
    pub by_qualified_name: HashMap<String, Symbol>,
    /// All per-scope data, keyed by the scope's owning symbol.
    scopes: HashMap<ScopeId, Scope>,
    /// WI-369: symbols declared `internal` — hidden from cross-scope resolution
    /// (kernel-language.md §8.6). A name is visible by default; only `internal`
    /// hides it. Recorded by raw symbol index; the empty set is the all-visible
    /// default, so `public`/unspecified declarations cost nothing here.
    internal_syms: HashSet<u32>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// WI-984 — mint the [`ScopeId`] of the scope `owner` opens. THE ONLY
    /// constructor: a scope cannot be built from a raw integer, a `TermId`, or an
    /// arbitrary index, and that refusal is a compile error rather than a comment.
    ///
    /// The bound check is the one provenance guard Rust affords here, and it is
    /// LOAD-BEARING rather than defensive: every reader indexes `defs` by the
    /// owner, so a symbol this table never issued reaches a raw index panic in a
    /// display path with no hint of where it came from. It catches only the
    /// direction where the FOREIGN table is the larger one — see [`ScopeId`] for
    /// what that leaves open and why Rust cannot close it.
    pub fn scope_id(&self, owner: Symbol) -> ScopeId {
        assert!(
            (owner.index() as usize) < self.defs.len(),
            "scope_id: Symbol({}) was never issued by this SymbolTable (it holds {} \
             symbols) — a scope owner from another table cannot name a scope here",
            owner.index(),
            self.defs.len(),
        );
        ScopeId(owner)
    }

    /// Intern a name, returning a Symbol. Creates an Unresolved entry
    /// if the name hasn't been seen before (deduplicated).
    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(&sym) = self.intern_map.get(s) {
            return sym;
        }
        let sym = Symbol(self.defs.len() as u32);
        self.defs.push(SymbolDef::Unresolved {
            name: s.to_owned(),
        });
        self.intern_map.insert(s.to_owned(), sym);
        sym
    }

    /// Mint a FRESH, distinct Unresolved symbol carrying `name` as its display
    /// name — bypassing the `intern_map` dedup, so two calls with the same `name`
    /// return two *different* symbols. Used to alpha-rename a local binder
    /// (`let`/lambda/match-arm) to a per-binding-site identity (WI-550): the
    /// symbol still prints / resolves-by-name as `name` (so eval's name-based
    /// `find_local` and the printer are unaffected), but `let x = 0; let x = 1`
    /// now mint distinct symbols, keeping their flow facts (`x ≡ 0`, `x ≡ 1`)
    /// collision-free under shadowing in Γ (proposal 050). It is intentionally
    /// NOT inserted into `intern_map` / any scope: a binder is resolved only via
    /// the loader's local-name frame, never scope-resolution, so leaving the
    /// dedup map pointing at the original `intern(name)` symbol is correct.
    pub fn intern_unique(&mut self, name: &str) -> Symbol {
        let sym = Symbol(self.defs.len() as u32);
        self.defs.push(SymbolDef::Unresolved {
            name: name.to_owned(),
        });
        sym
    }

    /// Look up an existing symbol by name without allocating one if it
    /// isn't present. Returns `None` when no one has interned the name.
    /// Used by read-only paths (e.g. the loader looking for parse-side
    /// `"type_name"` / `"type_args"` named args without forcing them
    /// into existence).
    pub fn lookup(&self, s: &str) -> Option<Symbol> {
        self.intern_map.get(s).copied()
    }

    /// Define a new resolved symbol in a scope. If the same local_name
    /// already exists in the scope, returns the existing symbol (merge
    /// behavior — e.g. `namespace X` extends an existing `sort X`).
    /// Otherwise creates a new entry and indexes it.
    pub fn define(
        &mut self,
        local_name: &str,
        qualified_name: &str,
        kind: SymbolKind,
        scope: ScopeId,
    ) -> Symbol {
        let scope_data = self.scopes.entry(scope).or_default();
        if let Some(&existing) = scope_data.locals.get(local_name) {
            // Re-declaring a name already bound in this scope RECORDS the added
            // category instead of discarding it. The early return is unchanged —
            // one name in one scope is still one symbol — but the second
            // declaration's role is no longer lost, which is what made `kind`
            // depend on which of two declarations came first (WI-926).
            self.add_kind(existing, kind);
            return existing;
        }
        let sym = Symbol(self.defs.len() as u32);
        self.defs.push(SymbolDef::Resolved {
            local_name: local_name.to_owned(),
            qualified_name: qualified_name.to_owned(),
            kinds: SmallVec::from_elem(kind, 1),
            scope,
            arg_places: Vec::new(),
        });
        scope_data.locals.insert(local_name.to_owned(), sym);
        self.by_qualified_name
            .insert(qualified_name.to_owned(), sym);
        sym
    }

    /// Define a resolved symbol addressable ONLY by its qualified name — it is
    /// intentionally NOT inserted into any scope's `locals`, so scope-aware
    /// resolution (`resolve_in_scope`) never surfaces it as a candidate.
    ///
    /// Used for loader-internal fact functors (the reflection `member`
    /// constructor, the `meta` / `SortAlias` functors) that the loader emits
    /// into the KB and only ever looks up by qualified name via
    /// `resolve_symbol`. Registering them as bare global locals (`define`)
    /// leaked them into user name resolution, where a `requires`-induced scope
    /// link could resurface e.g. the kernel `member` as a phantom rival to a
    /// user's `import …List.{member}` alias (WI-422). Idempotent: returns the
    /// existing symbol if the qualified name is already taken.
    pub fn define_qualified_only(
        &mut self,
        local_name: &str,
        qualified_name: &str,
        kind: SymbolKind,
        scope: ScopeId,
    ) -> Symbol {
        if let Some(&existing) = self.by_qualified_name.get(qualified_name) {
            // Same accumulation as `define`: a repeated declaration ADDS its role
            // rather than losing it.
            self.add_kind(existing, kind);
            return existing;
        }
        let sym = Symbol(self.defs.len() as u32);
        self.defs.push(SymbolDef::Resolved {
            local_name: local_name.to_owned(),
            qualified_name: qualified_name.to_owned(),
            kinds: SmallVec::from_elem(kind, 1),
            scope,
            arg_places: Vec::new(),
        });
        self.by_qualified_name
            .insert(qualified_name.to_owned(), sym);
        sym
    }

    /// WI-352 — record the ordered argument-place symbols of a *callable*
    /// place (an operation, or a callback-typed parameter). See
    /// [`SymbolDef::Resolved::arg_places`]. Idempotent overwrite; a no-op on
    /// an unresolved symbol.
    pub fn set_arg_places(&mut self, sym: Symbol, places: Vec<Symbol>) {
        if let Some(SymbolDef::Resolved { arg_places, .. }) = self.defs.get_mut(sym.0 as usize) {
            *arg_places = places;
        }
    }

    /// WI-352 — the ordered argument-place symbols of `sym` (empty when `sym`
    /// is not a callable place, or unresolved). The result place is `<sym>.result`
    /// (found by name), not included here.
    pub fn arg_places(&self, sym: Symbol) -> &[Symbol] {
        match self.defs.get(sym.0 as usize) {
            Some(SymbolDef::Resolved { arg_places, .. }) => arg_places,
            _ => &[],
        }
    }

    /// WI-369: record that `sym` was declared `internal`, so cross-scope
    /// resolution hides it (kernel-language.md §8.6). No-op-safe to call more
    /// than once.
    pub fn mark_internal(&mut self, sym: Symbol) {
        self.internal_syms.insert(sym.0);
    }

    /// WI-369: whether `sym` was declared `internal`.
    pub fn is_internal(&self, sym: Symbol) -> bool {
        self.internal_syms.contains(&sym.0)
    }

    /// WI-369: is `sym` visible from `from_scope`? A non-`internal` symbol
    /// is visible everywhere (the default). An `internal` symbol is visible only
    /// within its declaring scope and that scope's lexical descendants — i.e.
    /// `from_scope` is the declaring scope, or reaches it by following
    /// `is_enclosing` parent links (the sort/namespace body chain). Crossing any
    /// non-enclosing edge (`import`/`requires`/wildcard/variant exposure) leaves
    /// the lexical scope, so the internal name is hidden there.
    pub fn internal_visible_from(&self, sym: Symbol, from_scope: ScopeId) -> bool {
        if !self.is_internal(sym) {
            return true;
        }
        // Unresolved/unknown — nothing to hide.
        let Some(decl_scope) = self.declaring_scope(sym) else { return true };
        // Walk the enclosing-parent chain up from `from_scope`.
        let mut stack = vec![from_scope];
        let mut visited = HashSet::new();
        while let Some(s) = stack.pop() {
            if s == decl_scope {
                return true;
            }
            if !visited.insert(s) {
                continue;
            }
            if let Some(scope) = self.scopes.get(&s) {
                for p in &scope.parents {
                    if p.is_enclosing {
                        stack.push(p.parent_scope);
                    }
                }
            }
        }
        false
    }

    /// Mark a name as exposed from a scope to its enclosing scope via the
    /// variant-exposure parent link (populated from entity variants only).
    pub fn add_exposed(&mut self, scope: ScopeId, name: &str) {
        self.scopes
            .entry(scope)
            .or_default()
            .exposed
            .insert(name.to_owned());
    }

    /// Check if a name is a type parameter of the given scope.
    pub fn is_type_param(&self, scope: ScopeId, name: &str) -> bool {
        self.scopes.get(&scope)
            .map_or(false, |s| s.type_params.contains(name))
    }

    /// Record a type parameter name for a scope (excluded from parent lookups).
    pub fn add_type_param(&mut self, scope: ScopeId, name: &str) {
        let data = self.scopes.entry(scope).or_default();
        if data.type_params.insert(name.to_owned()) {
            data.type_params_ordered.push(name.to_owned());
        }
    }

    /// Record an imported name alias in a scope.
    /// Makes `local_name` resolve to `sym` locally in the given scope.
    pub fn add_import(&mut self, scope: ScopeId, local_name: &str, sym: Symbol) {
        self.scopes
            .entry(scope)
            .or_default()
            .imports
            .insert(local_name.to_owned(), sym);
    }

    /// Record a parent scope inclusion (from `requires` or `import`).
    ///
    /// IDEMPOTENT (WI-994) — a scope's parents are a SET, and an exact repeat adds
    /// nothing that [`Self::resolve_in_scope_recursive`] can observe: it walks under
    /// a `visited` set and dedups matches by symbol, so a second copy of one link
    /// only lengthens the list every failed local lookup scans.
    ///
    /// Load-bearing since the variant-exposure link stopped being gated on the
    /// symbol being FRESH: `load_incremental` re-scanning files already in the KB
    /// re-runs every declaration, so without this each reload would push another
    /// copy of every such link — `anthill.prelude` 28 → 56 exposure parents on the
    /// second load, and unbounded in the number of loads. `is_new` had been
    /// suppressing that as a side effect of answering a different question.
    ///
    /// The dedup is on the WHOLE inclusion — since WI-984 that is `(parent_scope,
    /// is_enclosing)`, exactly the pair [`Self::resolve_in_scope_recursive`] and
    /// [`Self::internal_visible_from`] read, so two links this call cannot tell
    /// apart are two no walk could tell apart either. O(P) per push against P in
    /// the tens, paid at load, against an O(P) every lookup pays forever.
    pub fn add_parent(&mut self, scope: ScopeId, inclusion: ScopeInclusion) {
        let parents = &mut self.scopes.entry(scope).or_default().parents;
        if !parents.contains(&inclusion) {
            parents.push(inclusion);
        }
    }

    /// Get a scope's data.
    pub fn scope(&self, scope: ScopeId) -> Option<&Scope> {
        self.scopes.get(&scope)
    }

    /// Get or create a scope's data.
    pub fn scope_mut(&mut self, scope: ScopeId) -> &mut Scope {
        self.scopes.entry(scope).or_default()
    }

    /// Resolve a name within a scope. Resolution order:
    /// 1. Local: find symbol defined directly in this scope
    /// 1b. Imports: check imported name aliases
    /// 2. Parent scopes: check parent inclusions (exposed variants only across
    ///    a variant-exposure link, excluding type params)
    /// 3. NotFound if nothing matches
    pub fn resolve_in_scope(&self, name: &str, scope: ScopeId) -> ResolveResult {
        // WI-369: resolve IGNORING `internal`, then drop any matched symbol not
        // visible from the ENTRY scope (kernel-language.md §8.6). Visibility is
        // applied as a post-filter on the resolved symbol(s), not as a per-hop
        // parent filter, because it is a property of the symbol relative to the
        // entry scope — an internal name reached transitively (through a
        // non-enclosing parent's enclosing grandparent) or re-exported via a
        // descendant's imports must be hidden the same as a direct member.
        // Filtering at collection time also keeps internal names from polluting
        // the candidate set with a spurious ambiguity (the spec's step-3 intent).
        let raw = self.resolve_in_scope_ignoring_internal(name, scope);
        self.filter_internal_visibility(raw, scope)
    }

    /// WI-369 diagnostic twin of [`Self::resolve_in_scope`] that does NOT apply
    /// the `internal` visibility filter — so a name hidden only by visibility
    /// still resolves here. Used to tell a genuine missing-name (unresolved)
    /// apart from a forbidden access to an `internal` symbol, so the loader can
    /// emit a precise `ForbiddenInternalAccess` rather than a bare
    /// `UnresolvedName`.
    pub fn resolve_in_scope_ignoring_internal(&self, name: &str, scope: ScopeId) -> ResolveResult {
        let mut visited = std::collections::HashSet::new();
        self.resolve_in_scope_recursive(name, scope, &mut visited)
    }

    /// WI-369: drop matched symbols not visible from `from_scope` (the entry
    /// scope of the resolution). A hidden `internal` symbol becomes `NotFound`
    /// (the loader then probes [`Self::resolve_in_scope_ignoring_internal`] to
    /// emit a precise `ForbiddenInternalAccess`); an ambiguity keeps only its
    /// visible candidates, so an `internal` name never shadows a visible peer.
    fn filter_internal_visibility(&self, r: ResolveResult, from_scope: ScopeId) -> ResolveResult {
        match r {
            ResolveResult::Found(sym) => {
                if self.internal_visible_from(sym, from_scope) {
                    ResolveResult::Found(sym)
                } else {
                    ResolveResult::NotFound
                }
            }
            ResolveResult::Ambiguous(cands) => {
                let kept: Vec<Symbol> = cands
                    .into_iter()
                    .filter(|&s| self.internal_visible_from(s, from_scope))
                    .collect();
                match kept.len() {
                    0 => ResolveResult::NotFound,
                    1 => ResolveResult::Found(kept[0]),
                    _ => ResolveResult::Ambiguous(kept),
                }
            }
            ResolveResult::NotFound => ResolveResult::NotFound,
        }
    }

    fn resolve_in_scope_recursive(
        &self,
        name: &str,
        scope: ScopeId,
        visited: &mut std::collections::HashSet<ScopeId>,
    ) -> ResolveResult {
        if !visited.insert(scope) {
            return ResolveResult::NotFound; // cycle
        }

        // Collect eligible parent scopes (filter + extract) while holding
        // the borrow on self.scopes, then drop it before recursing.
        let eligible_parents: SmallVec<[ScopeId; 4]> = if let Some(data) = self.scopes.get(&scope) {
            // 1. Local: check locals defined in this scope — O(1) lookup
            if let Some(&sym) = data.locals.get(name) {
                return ResolveResult::Found(sym);
            }

            // 1b. Imported name aliases (from selective/plain imports)
            if let Some(&sym) = data.imports.get(name) {
                return ResolveResult::Found(sym);
            }

            // 2. Filter parent scopes by type_params and the `exposed` set.
            // `internal` visibility is NOT filtered per-hop here — it is applied
            // as a post-filter on the matched symbol in `resolve_in_scope` (so a
            // transitively-reached or re-exported internal name is hidden too).
            // `exposed` holds a sort's entity variants (proposal 044 job 2): a
            // non-empty set leaks only those variants to the enclosing scope; an
            // empty set (specs, namespaces) is fully visible via requires/wildcard.
            data.parents.iter().filter_map(|p| {
                if !p.is_enclosing {
                    if let Some(parent) = self.scopes.get(&p.parent_scope) {
                        if parent.type_params.contains(name) {
                            return None;
                        }
                        if !parent.exposed.is_empty() && !parent.exposed.contains(name) {
                            return None;
                        }
                    }
                }
                Some(p.parent_scope)
            }).collect()
        } else {
            return ResolveResult::NotFound;
        };
        // Borrow on self.scopes is dropped — safe to recurse.

        let mut matches = Vec::new();
        for parent_scope in eligible_parents {
            match self.resolve_in_scope_recursive(name, parent_scope, visited) {
                ResolveResult::Found(sym) => matches.push(sym),
                ResolveResult::Ambiguous(mut candidates) => matches.append(&mut candidates),
                ResolveResult::NotFound => {}
            }
        }

        // Deduplicate matches (same symbol may be reachable via multiple paths)
        matches.sort_by_key(|s| s.0);
        matches.dedup();

        match matches.len() {
            0 => ResolveResult::NotFound,
            1 => ResolveResult::Found(matches[0]),
            _ => ResolveResult::Ambiguous(matches),
        }
    }

    /// `sym`'s name WITHIN THE SCOPE THAT DECLARES IT — the key it is filed under in
    /// that scope's `locals`, and the raw name for an unresolved symbol.
    ///
    /// LOCAL, not SHORT. It is one segment for the ordinary case (`fill` for
    /// `Tank.fill`), but a WI-341 callback place is declared in the OPERATION's scope
    /// under its path relative to that operation — see [`SymbolTable::define`]'s
    /// callers in `load::register_callback_places` — so `<op>.f._1` is filed under
    /// `f._1`. The dot is load-bearing: it is what keeps `f._1` distinct from a
    /// sibling callback's `g._1` in one flat map. MEASURED over stdlib + anthill-stl,
    /// 53 of 2598 symbols answer with a dotted name, all of that shape.
    ///
    /// Callers wanting the LAST SEGMENT must slice — `typing::short_name_of`, or the
    /// language-level `anthill.reflect.short_name`, both of which `rsplit` for exactly
    /// this reason. Named `name` (and aliased `resolve`) until WI-956.
    pub fn local_name(&self, sym: Symbol) -> &str {
        match &self.defs[sym.0 as usize] {
            SymbolDef::Unresolved { name } => name,
            SymbolDef::Resolved { local_name, .. } => local_name,
        }
    }

    /// Get the full SymbolDef for a symbol.
    pub fn get(&self, sym: Symbol) -> &SymbolDef {
        &self.defs[sym.0 as usize]
    }

    /// Check if a symbol is resolved (has kind, scope, qualified name).
    pub fn is_resolved(&self, sym: Symbol) -> bool {
        matches!(&self.defs[sym.0 as usize], SymbolDef::Resolved { .. })
    }

    /// WI-984 — THE SCOPE `sym` WAS DECLARED IN. `None` only for an unresolved
    /// symbol, which has no scope at all; there is no second way to fail, because
    /// [`ScopeId::owner`] is total. The stored-representation reader every caller
    /// wanting the declaring scope (or its owner) should go through.
    pub fn declaring_scope(&self, sym: Symbol) -> Option<ScopeId> {
        match self.defs.get(sym.0 as usize) {
            Some(SymbolDef::Resolved { scope, .. }) => Some(*scope),
            _ => None,
        }
    }


}

// ── Backward-compatible type alias ──────────────────────────────

/// Alias: old code that uses `Interner` keeps compiling.
pub type Interner = SymbolTable;

// ── Positional field labels (WI-790) ────────────────────────────

/// The synthetic field label for source index `index` — `_1`, `_2`, `_3`, …
///
/// ONE-based: `docs/kernel-language.md` §4.5 states that positional syntax is
/// sugar for auto-generated names `_1`, `_2`, `_3`, so index 0 is `_1`.
///
/// This function, [`positional_label_index`] and [`is_positional_label_at`] are
/// the SOLE owners of the FIELD-LABEL convention. Every producer (tuple literals
/// and tuple TYPES in `parse/convert.rs`, unnamed arrow params and param-list
/// types in `kb/load.rs`, the tuple/arrow type builders in `kb/typing.rs`, the
/// JSON serializer in `persistence/term_ser.rs`) mints through here, and every
/// consumer that asks "which slot does this label name?" reads through the
/// inverse. They lived as nine hand-written `format!`/literal mints and five
/// hand-spelled `strip_prefix('_')` tests before WI-790, and had drifted:
/// `term_ser` was ZERO-based, so a serialized mixed positional/named `Term::Fn`
/// carried keys off by one from every reader, and three of the five recognizers
/// admitted leading zeros while WI-786's classifier (correctly) did not. Routing
/// both directions through one pair makes such a divergence a compile-time
/// impossibility rather than a silent textual one.
///
/// NOT this convention, despite the spelling: `anthill-stl`'s
/// `reflect/reader.rs` renders a de Bruijn VARIABLE as `_{n}` — 0-based, a
/// variable rather than a field label, and deliberately left alone. A `format!
/// ("_{`  sweep finds it; it is not a survivor.
pub fn positional_label(index: usize) -> String {
    format!("_{}", index + 1)
}

/// The source index `label` names, or `None` when `label` is not one
/// [`positional_label`] could have minted — i.e. its exact inverse.
///
/// Refuses everything outside the image, which is what makes it usable as a
/// classifier and not just a parser:
///
///  * no `_` prefix (`x`, `a1`) — an ordinary name;
///  * `_` alone, or `_` + non-digits (`_b`, `_id`) — a user label that merely
///    starts with an underscore. `strip_prefix('_')` + `parse` already rejected
///    these, but a bare `starts_with('_')` test did not, and WI-786 was the bug
///    that caused (`_b` re-slotted positionally, DISCARDING the name);
///  * a LEADING ZERO (`_0`, `_01`) — `_0` is outside the 1-based image entirely,
///    and `_01` is a distinct string from the `_1` this would mint, so it is a
///    USER label. `parse::<usize>()` alone accepts both, which is how three
///    recognizers came to disagree with WI-786's classifier
///    (`leading_zero_label_is_not_synthetic`);
///  * a `+` sign (`_+1`) — accepted by `usize::from_str`, refused here.
pub fn positional_label_index(label: &str) -> Option<usize> {
    let digits = label.strip_prefix('_')?;
    if digits.starts_with('0') || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    // The parse rejects the two remaining non-labels: the empty `_`, and overflow.
    // Past it, `digits` is non-empty with no leading zero, so `n >= 1` and the
    // decrement cannot underflow.
    Some(digits.parse::<usize>().ok()? - 1)
}

/// Is `label` the synthetic label for source index `index` — i.e. exactly
/// `positional_label(index)`?
///
/// The question three of the five recognizers actually ask.
/// [`positional_label_index`] alone was not enough of an owner: the raw inverse
/// had one home while the PREDICATE built on it — the part carrying the index,
/// and so the part that decides anything — was re-spelled at each site, which is
/// the same drift one level up. `eval`'s `classify_ctor_arg` asks it of a
/// constructor argument, `kb::typing`'s `is_positional_tuple_names` of a
/// parameter list, and `persistence::print` of a tuple-type component.
pub fn is_positional_label_at(label: &str, index: usize) -> bool {
    positional_label_index(label) == Some(index)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_dedup() {
        let mut st = SymbolTable::new();
        let a = st.intern("foo");
        let b = st.intern("foo");
        assert_eq!(a, b);
        assert_eq!(st.local_name(a), "foo");
    }

    #[test]
    fn define_creates_new_entry_different_scopes() {
        let mut st = SymbolTable::new();
        let a = scope(&mut st, "A");
        let b = scope(&mut st, "B");
        let s1 = st.define("foo", "A.foo", SymbolKind::Operation, a);
        let s2 = st.define("foo", "B.foo", SymbolKind::Operation, b);
        assert_ne!(s1, s2);
        assert_eq!(st.local_name(s1), "foo");
        assert_eq!(st.local_name(s2), "foo");
        assert!(st.is_resolved(s1));
        assert!(st.is_resolved(s2));
    }

    /// The scope `owner` opens. Tests used to pass bare integers here — the very
    /// thing WI-984 makes impossible.
    fn scope(st: &mut SymbolTable, owner: &str) -> ScopeId {
        let sym = st.intern(owner);
        st.scope_id(sym)
    }

    #[test]
    fn define_same_scope_reuses() {
        let mut st = SymbolTable::new();
        let a = scope(&mut st, "A");
        let s1 = st.define("Foo", "A.Foo", SymbolKind::Sort, a);
        let s2 = st.define("Foo", "A.Foo", SymbolKind::Namespace, a);
        assert_eq!(s1, s2, "same local_name in same scope should reuse");
    }

    #[test]
    fn resolve_in_scope_local() {
        let mut st = SymbolTable::new();
        let eq = scope(&mut st, "Eq");
        let s = st.define("eq", "Eq.eq", SymbolKind::Operation, eq);
        match st.resolve_in_scope("eq", eq) {
            ResolveResult::Found(found) => assert_eq!(found, s),
            other => panic!("expected Found, got {:?}", other),
        }
    }

    #[test]
    fn resolve_in_scope_parent() {
        let mut st = SymbolTable::new();
        let eq = scope(&mut st, "Eq");
        let ordered = scope(&mut st, "Ordered");
        let eq_sym = st.define("eq", "Eq.eq", SymbolKind::Operation, eq);
        st.add_exposed(eq, "eq");

        // `Ordered` includes `Eq`
        st.add_parent(ordered, ScopeInclusion { parent_scope: eq, is_enclosing: false });

        match st.resolve_in_scope("eq", ordered) {
            ResolveResult::Found(found) => assert_eq!(found, eq_sym),
            other => panic!("expected Found, got {:?}", other),
        }
    }

    #[test]
    fn resolve_excludes_type_params() {
        let mut st = SymbolTable::new();
        let eq = scope(&mut st, "Eq");
        let ordered = scope(&mut st, "Ordered");
        // "T" is a type param of `Eq`
        st.define("T", "Eq.T", SymbolKind::Sort, eq);
        st.add_exposed(eq, "T");
        st.add_type_param(eq, "T");

        let eq_sym = st.define("eq", "Eq.eq", SymbolKind::Operation, eq);
        st.add_exposed(eq, "eq");

        st.add_parent(ordered, ScopeInclusion { parent_scope: eq, is_enclosing: false });

        // "T" should NOT resolve from parent (it's a type param)
        match st.resolve_in_scope("T", ordered) {
            ResolveResult::NotFound => {}
            other => panic!("expected NotFound for type param, got {:?}", other),
        }

        // "eq" should resolve normally
        match st.resolve_in_scope("eq", ordered) {
            ResolveResult::Found(found) => assert_eq!(found, eq_sym),
            other => panic!("expected Found, got {:?}", other),
        }
    }

    #[test]
    fn resolve_ambiguous() {
        let mut st = SymbolTable::new();
        let a = scope(&mut st, "A");
        let b = scope(&mut st, "B");
        let c = scope(&mut st, "C");
        st.define("foo", "A.foo", SymbolKind::Operation, a);
        st.add_exposed(a, "foo");
        st.define("foo", "B.foo", SymbolKind::Operation, b);
        st.add_exposed(b, "foo");

        st.add_parent(c, ScopeInclusion { parent_scope: a, is_enclosing: false });
        st.add_parent(c, ScopeInclusion { parent_scope: b, is_enclosing: false });

        match st.resolve_in_scope("foo", c) {
            ResolveResult::Ambiguous(candidates) => assert_eq!(candidates.len(), 2),
            other => panic!("expected Ambiguous, got {:?}", other),
        }
    }

    #[test]
    fn local_shadows_parent() {
        let mut st = SymbolTable::new();
        let a = scope(&mut st, "A");
        let b = scope(&mut st, "B");
        st.define("foo", "A.foo", SymbolKind::Operation, a);
        st.add_exposed(a, "foo");

        let local_foo = st.define("foo", "B.foo", SymbolKind::Operation, b);
        st.add_parent(b, ScopeInclusion { parent_scope: a, is_enclosing: false });

        // Local should win
        match st.resolve_in_scope("foo", b) {
            ResolveResult::Found(found) => assert_eq!(found, local_foo),
            other => panic!("expected Found (local), got {:?}", other),
        }
    }

    // ── positional labels (WI-790) ──────────────────────────────

    /// The convention itself: index 0 is `_1`, per spec §4.5. Spelled as literals
    /// rather than derived, so a change to `positional_label` has to disagree with
    /// the spec HERE rather than silently in eight call sites.
    #[test]
    fn positional_label_is_one_based() {
        assert_eq!(positional_label(0), "_1");
        assert_eq!(positional_label(1), "_2");
        assert_eq!(positional_label(2), "_3");
    }

    /// The pair is a genuine round trip, not two independently-plausible rules —
    /// this is the property the eight minters and five recognizers now share.
    #[test]
    fn positional_label_index_inverts_positional_label() {
        for i in 0..64 {
            assert_eq!(positional_label_index(&positional_label(i)), Some(i), "index {i}");
        }
    }

    /// Everything outside the image is refused. `_0` and `_01` are the two that a
    /// bare `parse::<usize>()` used to admit — the drift WI-790 closes.
    #[test]
    fn non_synthetic_labels_have_no_index() {
        for label in ["_0", "_01", "_00", "_007", "_", "_b", "_id", "_1a", "_+1", "x", "1", ""] {
            assert_eq!(positional_label_index(label), None, "{label:?} is not synthetic");
        }
    }

    /// The predicate is index-SENSITIVE: a synthetic label at the wrong slot is
    /// not synthetic THERE. That is the whole reason it takes an index rather
    /// than being `positional_label_index(..).is_some()` — a `_2` written first
    /// is a user label that must keep its name (WI-786's
    /// `synthetic_name_for_the_wrong_index_stays_named`).
    #[test]
    fn is_positional_label_at_is_index_sensitive() {
        assert!(is_positional_label_at("_1", 0));
        assert!(is_positional_label_at("_2", 1));
        assert!(!is_positional_label_at("_2", 0), "`_2` in slot 0 is a user label");
        assert!(!is_positional_label_at("_1", 1), "`_1` in slot 1 is a user label");
        assert!(!is_positional_label_at("_01", 0), "leading zero is a user label");
        assert!(!is_positional_label_at("_b", 0));
    }

    /// WI-994 — a scope's parents are a SET. Re-declaring one link must not grow
    /// the list: `load_incremental` re-scans files already in the KB, and the
    /// variant-exposure link is no longer gated on the symbol being fresh, so
    /// every reload re-offers every such link. Measured control: delete the
    /// `contains` guard in `add_parent` and the first assertion below reads 3.
    #[test]
    fn add_parent_is_idempotent_per_distinct_inclusion() {
        let mut syms = SymbolTable::new();
        let child = scope(&mut syms, "Child");
        let parent = scope(&mut syms, "Parent");
        let link = ScopeInclusion { parent_scope: parent, is_enclosing: false };
        syms.add_parent(child, link.clone());
        syms.add_parent(child, link.clone());
        syms.add_parent(child, link.clone());
        assert_eq!(syms.scope(child).unwrap().parents.len(), 1, "one link, offered thrice");

        // …and the dedup is on the WHOLE inclusion, so the same parent scope reached
        // by an ENCLOSING edge is a SECOND link, not a repeat of the first. Without
        // this row the guard could be narrowed to `parent_scope` and nothing here
        // would notice.
        syms.add_parent(child, ScopeInclusion { is_enclosing: true, ..link });
        assert_eq!(syms.scope(child).unwrap().parents.len(), 2, "two DISTINCT links");
    }

    /// WI-984's rider, said as an assertion rather than left silent: dropping
    /// `instantiation_term_raw` MERGED a distinction `add_parent` used to keep. One
    /// spec `requires`d at two instantiations — `Eq[T = Int]` and `Eq[T = String]`
    /// on one scope — offered two links that differed only in that field and now
    /// offers one. Nothing observes the loss: `resolve_in_scope` and
    /// `internal_visible_from` read `parent_scope` and `is_enclosing` only, so the
    /// two links always resolved identically. Before WI-984 this read 2.
    #[test]
    fn two_instantiations_of_one_spec_are_one_link() {
        let mut syms = SymbolTable::new();
        let child = scope(&mut syms, "Stack");
        let eq = scope(&mut syms, "Eq");
        syms.add_parent(child, ScopeInclusion { parent_scope: eq, is_enclosing: false });
        syms.add_parent(child, ScopeInclusion { parent_scope: eq, is_enclosing: false });
        assert_eq!(syms.scope(child).unwrap().parents.len(), 1);
    }

    /// WI-984 — the mint refuses a symbol its table never issued. This is the ONLY
    /// provenance check Rust affords (Scala closes it with a path-dependent member,
    /// WI-1004), and it catches only the direction where the FOREIGN table is the
    /// larger one — a symbol from a SMALLER table is in range and passes silently.
    /// Asserted rather than implied, so the hole is on the record.
    #[test]
    fn scope_id_refuses_a_symbol_this_table_never_issued() {
        let mut small = SymbolTable::new();
        let mut large = SymbolTable::new();
        small.intern("only");
        for n in ["a", "b", "c", "d"] {
            large.intern(n);
        }
        let foreign_from_large = large.intern("d");
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                small.scope_id(foreign_from_large)
            }))
            .is_err(),
            "a symbol past the end of this table's `defs` is refused",
        );

        // THE HOLE, driven: the foreign symbol is in range, so it passes — and names
        // whatever `small` happens to hold at that index.
        let foreign_from_small = small.intern("only");
        let _accepted: ScopeId = large.scope_id(foreign_from_small);
    }
}
