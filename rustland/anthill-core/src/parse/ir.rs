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

// ── Stage 0: import tools ───────────────────────────────────────
