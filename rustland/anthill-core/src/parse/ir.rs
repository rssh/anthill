/// Parse IR — typed AST produced by tree-sitter conversion.
///
/// This is the intermediate representation between the tree-sitter CST
/// and the KnowledgeBase. All AST nodes live here.
///
/// Terms at parse time use `TermId` into `SimpleTermStore` (a plain Vec,
/// no hash-consing). During loading into the KB, terms are re-allocated
/// into the hash-consed store.

use std::collections::HashMap;

use smallvec::SmallVec;

use crate::intern::{SymbolTable, Symbol};
use crate::span::Span;
use crate::kb::term::{Term, TermId};

// ── Simple term store (parse-time only) ─────────────────────────

/// A plain term store for parse time — no hash-consing or refcounting.
#[derive(Debug, Default)]
pub struct SimpleTermStore {
    terms: Vec<Term>,
    /// Inline description blocks attached to variables: TermId → description texts.
    pub descriptions: HashMap<TermId, Vec<String>>,
    /// Byte-offset spans for terms.
    /// Populated by the converter for each term node that has a source position.
    pub spans: HashMap<TermId, Span>,
}

impl SimpleTermStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc(&mut self, term: Term) -> TermId {
        let id = TermId::from_raw(self.terms.len() as u32);
        self.terms.push(term);
        id
    }

    pub fn get(&self, id: TermId) -> &Term {
        &self.terms[id.index()]
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }
}

// ── Parsed file (root) ─────────────────────────────────────────

#[derive(Debug)]
pub struct ParsedFile {
    pub items: Vec<Item>,
    pub symbols: SymbolTable,
    pub terms: SimpleTermStore,
}

// ── Name (qualified, with span) ─────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name {
    pub segments: SmallVec<[Symbol; 2]>,
    pub span: Span,
}

impl Name {
    pub fn simple(sym: Symbol, span: Span) -> Self {
        Self {
            segments: SmallVec::from_elem(sym, 1),
            span,
        }
    }

    pub fn qualified(segments: SmallVec<[Symbol; 2]>, span: Span) -> Self {
        Self { segments, span }
    }

    pub fn last(&self) -> Symbol {
        *self.segments.last().expect("Name must have at least one segment")
    }

    pub fn is_simple(&self) -> bool {
        self.segments.len() == 1
    }
}

// ── Type expressions ────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq)]
pub enum TypeExpr {
    /// Simple type: `Account`, `Int`
    Simple(Name),
    /// Parameterized type: `List[T=Int]`
    Parameterized {
        name: Name,
        bindings: Vec<SortBinding>,
    },
    /// Type variable: `?` or `?name`, with zero or more inline descriptions.
    Variable {
        term_id: TermId,
        descriptions: Vec<String>,
    },
    /// Tuple type: `(Int, String)` or `(name: String, age: Int)`.
    /// Always named; converter fills _1, _2 for positional.
    Tuple(Vec<(Symbol, TypeExpr)>),
    /// Arrow type: `(A) -> B` or `(A, B) -> C @ E`.
    Arrow {
        params: Vec<TypeExpr>,
        return_type: Box<TypeExpr>,
        effect: Option<Box<TypeExpr>>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct SortBinding {
    /// Named binding: `Some(name)` for `T = Int`, `None` for positional `Int`.
    pub param: Option<Name>,
    pub bound: TypeExpr,
}

// ── Literal (parse-time, with plain f64) ────────────────────────

#[derive(Clone, Debug, PartialEq)]
pub enum ParseLiteral {
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
}

// ── Items ───────────────────────────────────────────────────────

#[derive(Debug)]
pub enum Item {
    // Kernel
    Namespace(Namespace),
    AbstractSort(AbstractSort),
    SortWithBody(SortWithBody),
    Rule(Rule),
    Operation(Operation),
    RequiresDecl(RequiresDecl),
    // Sugar
    Entity(Entity),
    Fact(Fact),
    Constraint(Constraint),
    OperationBlock(OperationBlock),
    RuleBlock(RuleBlock),
    Describe(Describe),
    Proof(ProofDecl),
    ProvidesClause(ProvidesClause),
    ProvidesBlock(ProvidesBlock),
}

// ── Namespace ───────────────────────────────────────────────────

#[derive(Debug)]
pub struct Namespace {
    pub name: Name,
    pub imports: Vec<Import>,
    pub exports: Vec<Name>,
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Import {
    pub path: Name,
    pub kind: ImportKind,
}

#[derive(Debug, PartialEq)]
pub enum ImportKind {
    /// `import anthill.prelude.List` — import a specific name
    Plain,
    /// `import anthill.prelude.{List, Option}` — import selected names
    Selective(Vec<Name>),
    /// `import anthill.prelude.*` — import everything from namespace
    Wildcard,
}

// ── Sort ────────────────────────────────────────────────────────

#[derive(Debug)]
pub struct AbstractSort {
    pub visibility: Option<Visibility>,
    pub name: Name,
    pub definition: TypeExpr,
    pub descriptions: Vec<String>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

/// Sort or enum declaration kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortDeclKind {
    Sort,
    Enum,
}

#[derive(Debug)]
pub struct SortWithBody {
    pub kind: SortDeclKind,
    pub visibility: Option<Visibility>,
    pub name: Name,
    pub descriptions: Vec<String>,
    pub imports: Vec<Import>,
    pub exports: Vec<Name>,
    pub items: Vec<Item>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

/// Backwards-compatible alias.
pub type EnumDecl = SortWithBody;

#[derive(Debug)]
pub struct FieldDecl {
    pub name: Symbol,
    pub ty: TypeExpr,
}

// ── Rule ────────────────────────────────────────────────────────

#[derive(Debug)]
pub struct Rule {
    pub label: Option<Name>,
    /// One or more positive head terms, or a single `RuleHead::Bottom`
    /// for denial. Mixing `Bottom` with positive heads is rejected at
    /// load time. Multi-head desugars conjunctively (proposal 032).
    pub heads: Vec<RuleHead>,
    pub body: Option<Vec<TermId>>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub enum RuleHead {
    Term(TermId),
    Bottom,
}

// ── Operation ───────────────────────────────────────────────────

#[derive(Debug)]
pub struct Operation {
    pub visibility: Option<Visibility>,
    pub name: Name,
    pub params: Vec<Param>,
    pub return_type: TypeExpr,
    pub requires: Vec<Vec<TermId>>,
    pub ensures: Vec<Vec<TermId>>,
    pub effects: Vec<Effect>,
    pub body: Option<TermId>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Param {
    pub name: Symbol,
    pub ty: TypeExpr,
}

// ── Requires declaration ────────────────────────────────────────

#[derive(Debug)]
pub struct RequiresDecl {
    pub type_expr: TypeExpr,
    pub span: Span,
}

// ── Sugar: entity, fact, constraint ─────────────────────────────

#[derive(Debug)]
pub struct Entity {
    pub visibility: Option<Visibility>,
    pub name: Name,
    pub fields: Vec<FieldDecl>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Fact {
    pub term: TermId,
    /// Optional sort hint for the KB. Stage0 sugar (workitem, tool, etc.)
    /// desugars to facts with a specific sort (e.g. "WorkItem") rather than
    /// the generic "Fact" sort. `None` means sort "Fact".
    pub sort: Option<String>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Constraint {
    pub label: Option<Name>,
    pub head: Vec<TermId>,
    pub guard: Option<Vec<TermId>>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

// ── Sugar: blocks ───────────────────────────────────────────────

#[derive(Debug)]
pub struct OperationBlock {
    pub entries: Vec<Operation>,
    pub span: Span,
}

#[derive(Debug)]
pub struct RuleBlock {
    pub entries: Vec<Rule>,
    pub span: Span,
}

// ── Describe ────────────────────────────────────────────────────

#[derive(Debug)]
pub struct Describe {
    pub target: Name,
    pub contents: Vec<String>,
    pub span: Span,
}

// ── Common ──────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility {
    Internal,
    Export,
    Public,
}

#[derive(Debug)]
pub struct Effect {
    pub type_expr: TypeExpr,
}

#[derive(Debug)]
pub struct MetaBlock {
    pub entries: Vec<MetaEntry>,
}

#[derive(Debug)]
pub struct MetaEntry {
    pub key: Name,
    pub value: TermId,
}

// ── Proof construct (proposal 025) ──────────────────────────────

#[derive(Debug)]
pub struct ProofDecl {
    /// Name of the rule (or operation contract clause) being proved.
    pub target: Name,
    pub strategy: Option<ProofStrategy>,
    pub body: Option<ProofBody>,
    /// Cited-lemma rule names from the optional `using <name-list>`
    /// clause. The prove driver resolves each to a rule QN, renders
    /// the cited rule's body, and injects the result as
    /// `ProofConfig.assumptions` clauses for the discharge of this
    /// proof. Empty when the clause is absent.
    pub using: Vec<Name>,
    pub span: Span,
}

#[derive(Debug)]
pub struct ProofStrategy {
    /// "derivation" | "z3" | "test" | tool name
    pub name: Symbol,
    /// Optional tool args, named or positional. Each TermId points into
    /// the file's SimpleTermStore. Named args are stored as
    /// `Term::FnArg::Named { name, value }` already.
    ///
    /// Legacy field. New consumers should read `tactic` (proposal 025.1
    /// Phase 2 IR). Kept for backwards compat with anthill-cli's
    /// dispatch path.
    pub args: Vec<TermId>,
    /// Typed tactic term (proposal 025.1). Populated for `by z3(...)`
    /// blocks. For other strategies (derivation, test, ...) this is
    /// `None`. The conversion treats `by z3(logic: "LRA")` as the
    /// shorthand `by z3(tactic: smt(logic: "LRA"))`, so the field is
    /// always populated for `z3` even on the legacy syntax.
    pub tactic: Option<Tactic>,
    pub span: Span,
}

// ── Tactic IR (proposal 025.1 Phase 2) ──────────────────────────

/// A tactic term. Tactic terms are either bare identifiers (`smt`,
/// `simplify`), function applications (`smt(logic: "LRA")`,
/// `then(smt, qe)`), the `raw(...)` escape, or a `mapping` block.
#[derive(Debug, Clone)]
pub enum Tactic {
    /// Bare identifier — equivalent to a no-arg application.
    Bare(Symbol),
    /// `name(arg1, arg2, ...)` — covers `smt(...)`, `then(...)`,
    /// `or_else(...)`, `repeat(t, times: N)`, `induction(over: ...)`,
    /// `ranking(...)` and any pass-through Z3 tactic. The interpreter
    /// (Phase 3+) inspects the name and shape.
    App(Symbol, Vec<TacticArg>),
    /// `raw("(tactic-expr)")` — verbatim splice into Z3 input.
    Raw(String),
    /// `mapping { src -> tgt, ... }`.
    Mapping(MappingBlock),
}

#[derive(Debug, Clone)]
pub struct TacticArg {
    /// `Some(name)` for named args (`logic:`, `times:`, `over:`),
    /// `None` for positional args (combinator children, `raw`'s string).
    pub name: Option<Symbol>,
    pub value: TacticArgValue,
}

#[derive(Debug, Clone)]
pub enum TacticArgValue {
    Tactic(Box<Tactic>),
    String(String),
    Int(i64),
    Bool(bool),
    /// A `name`-shaped reference (e.g. `over: TransponderState`).
    /// Resolution happens at tactic-execution time.
    Name(Name),
}

#[derive(Debug)]
pub enum ProofBody {
    /// `:- hint1, hint2` — guided search hints (rule-name terms).
    Hints(Vec<TermId>),
    /// `query "..."` (+ optional mapping block) — explicit external query.
    Query {
        text: String,
        mapping: Option<MappingBlock>,
    },
    /// Structured proof body (proposal 031): a sequence of inner step
    /// rules each carrying its own discharge tactic, plus an optional
    /// concluding `using ... by ...` clause that discharges the
    /// enclosing lemma's head under the accumulated step hypotheses.
    Structured {
        steps: Vec<ProofStep>,
        conclude: Option<ConcludeClause>,
    },
}

/// One step inside a structured proof body. The step is structurally
/// a single-arrow rule (proposal 032) plus optional `using` cites and
/// a mandatory `by <tactic>` discharge.
#[derive(Debug)]
pub struct ProofStep {
    pub rule: Rule,
    pub using: Vec<Name>,
    pub strategy: ProofStrategy,
    pub span: Span,
}

/// The trailing `[using ...] by <tactic>` clause that discharges the
/// enclosing proof's lemma under accumulated step hypotheses.
#[derive(Debug)]
pub struct ConcludeClause {
    pub using: Vec<Name>,
    pub strategy: ProofStrategy,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct MappingBlock {
    pub entries: Vec<MappingEntry>,
}

#[derive(Debug, Clone)]
pub struct MappingEntry {
    pub source: Name,
    /// rendered as a string in tool space (operator, identifier, etc.)
    pub target: String,
}

// ── Provides construct (proposal 025) ───────────────────────────

/// `provides Spec[T = X]` inside a sort/enum body.
/// Declares the enclosing sort satisfies the spec.
#[derive(Debug)]
pub struct ProvidesClause {
    pub spec: TypeExpr,
    pub span: Span,
}

/// Standalone `provides Spec language <lang> ... end` block.
#[derive(Debug)]
pub struct ProvidesBlock {
    pub spec: TypeExpr,
    pub language: Symbol,
    pub items: Vec<ProvidesItem>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ProvidesItem {
    Rule(Rule),
    RuleBlock(RuleBlock),
    Fact(Fact),
    Proof(ProofDecl),
    Artifact(String),
    Carrier(Vec<CarrierBinding>),
    NamespaceMap(Vec<NamespaceMapEntry>),
}

#[derive(Debug)]
pub struct CarrierBinding {
    pub anthill_param: Symbol,
    pub host_type: TermId,
}

#[derive(Debug)]
pub struct NamespaceMapEntry {
    pub anthill_namespace: Symbol,
    pub host_module: TermId,
}

// ── Stage 0: import tools ───────────────────────────────────────
