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
    /// Parameterized type: `List{T=Int}`
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
    // Stage 0
    Project(Project),
    Tool(Tool),
    WorkItem(WorkItem),
    Feedback(Feedback),
    ImportTools(ImportTools),
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

#[derive(Debug)]
pub struct SortWithBody {
    pub visibility: Option<Visibility>,
    pub name: Name,
    pub descriptions: Vec<String>,
    pub imports: Vec<Import>,
    pub exports: Vec<Name>,
    pub items: Vec<Item>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub struct FieldDecl {
    pub name: Symbol,
    pub ty: TypeExpr,
}

// ── Rule ────────────────────────────────────────────────────────

#[derive(Debug)]
pub struct Rule {
    pub label: Option<Name>,
    pub head: RuleHead,
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

// ── Stage 0: project ────────────────────────────────────────────

#[derive(Debug)]
pub struct Project {
    pub name: Name,
    pub structure: ProjectStructure,
    pub import_tools: Vec<ImportTools>,
    pub tools: Vec<Name>,
    pub domains: Vec<Name>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ProjectStructure {
    Simple(SimpleProjectFields),
    Modules(Vec<ModuleDecl>),
    ToolsOnly,
}

#[derive(Debug)]
pub struct SimpleProjectFields {
    pub language: String,
    pub build: Option<String>,
    pub sources: Vec<SourceRoot>,
}

#[derive(Debug)]
pub struct ModuleDecl {
    pub name: Name,
    pub root: String,
    pub language: String,
    pub build: Option<String>,
    pub sources: Vec<SourceRoot>,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub struct SourceRoot {
    pub path: String,
    pub language: Option<String>,
    pub scope: SourceScope,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceScope {
    Main,
    Test,
    Generated,
    Docs,
}

// ── Stage 0: import tools ───────────────────────────────────────

#[derive(Debug)]
pub struct ImportTools {
    pub names: Vec<Name>,
    pub span: Span,
}

// ── Stage 0: tool ───────────────────────────────────────────────

#[derive(Debug)]
pub struct Tool {
    pub name: Name,
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub timeout: Option<String>,
    pub success: SuccessCriterion,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub enum SuccessCriterion {
    ExitZero,
    ExitCode(i64),
    OutputMatches(String),
    Custom(TermId),
}

// ── Stage 0: workitem ───────────────────────────────────────────

#[derive(Debug)]
pub struct WorkItem {
    pub id: Name,
    pub description: Option<TermId>,
    pub context: Vec<ContextRef>,
    pub acceptance: Vec<AcceptanceCriterion>,
    pub depends_on: Vec<Name>,
    pub generates: Vec<TermId>,
    pub requires_capability: Vec<Capability>,
    pub status: WorkStatus,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ContextRef {
    FileRef {
        path: String,
        lines: Option<(i64, i64)>,
    },
    FactRef {
        name: Name,
        term: TermId,
    },
    WorkItemRef(Name),
}

#[derive(Debug)]
pub enum AcceptanceCriterion {
    ToolPasses {
        tool: Name,
        bindings: Option<Vec<(String, TermId)>>,
    },
    FactHolds {
        name: Name,
        term: TermId,
    },
    Compiles(CompileTarget),
    Constraint(TermId),
}

#[derive(Debug)]
pub enum CompileTarget {
    SourceRoot(SourceRoot),
    Module(Name),
}

#[derive(Debug)]
pub enum Capability {
    Code { languages: Vec<String> },
    Test,
    Refine,
    Review,
    Decompose,
    Architect,
    HumanJudgment,
}

#[derive(Debug)]
pub enum WorkStatus {
    Draft,
    Open,
    Claimed { agent: String, since: String },
    Delivered { agent: String, at: String },
    Verified { at: String },
    Rejected { reason: String, at: String },
    ProposalRejected { reason: String, at: String },
    Stale { reason: String, since: String },
}

// ── Stage 0: feedback ───────────────────────────────────────────

#[derive(Debug)]
pub struct Feedback {
    pub workitem: Name,
    pub author: String,
    pub content: TermId,
    pub at: String,
    pub meta: Option<MetaBlock>,
    pub span: Span,
}
