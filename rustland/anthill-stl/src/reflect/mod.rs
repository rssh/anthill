#![allow(unused_imports)]

pub mod bridge;

use crate::prelude::{List, Pair, Bool, Stream};

// ── Opaque types bridging to anthill-core ───────────────────────

pub type Term = anthill_core::kb::term::TermId;
pub type FactId = anthill_core::kb::RuleId;

#[derive(Clone, Debug)]
pub struct Error(pub String);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for Error {}

// ── KB trait ────────────────────────────────────────────────────

pub trait KB {
    fn reify(&self, t: Term) -> TermRepr;

    fn reflect(&self, r: TermRepr) -> Term;

    fn sorts(&self, namespace: Option<String>) -> Vec<SortInfo>;

    fn operations(&self, sort_name: &str) -> Vec<OperationInfo>;

    fn constructors(&self, sort_name: &str) -> Vec<String>;

    fn fields(&self, name: &str) -> Vec<FieldInfo>;

    fn rules(&self, sort_name: &str) -> Vec<TermRepr>;

    fn descriptions(&self, target: Option<&str>) -> Vec<DescriptionInfo>;

    fn nonvar(&self, x: Term) -> bool;

    fn ground(&self, x: Term) -> bool;

    /// Apply a core substitution to a term. Infrastructure for Substitution::apply.
    fn apply_core_subst(&self, t: Term, subst: &anthill_core::kb::subst::Substitution) -> Term;

    fn execute(&self, query: LogicalQuery) -> Result<Box<dyn Stream<SubstBridge, Error>>, Error>;

    fn sort_template(&self, sort_name: String) -> LogicalQuery;

    fn instantiation_query(&self, sort_name: String, bindings: &dyn Substitution) -> LogicalQuery;
}

// ── LiteralRepr ─────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum LiteralRepr {
    IntLiteral(i64),
    FloatLiteral(f64),
    StringLiteral(String),
    BoolLiteral(bool),
}

// ── TermRepr ────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum TermRepr {
    ConstRepr {
        value: LiteralRepr,
    },
    VarRepr {
        name: String,
    },
    FnRepr {
        name: Term,
        args: Vec<TermRepr>,
    },
    RefRepr {
        name: Term,
    },
    QuotedRepr {
        language: String,
        source: String,
    },
}

// ── SortInfo ────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct SortInfo {
    pub name: Term,
    pub definition: Term,
    pub constructors: Vec<Term>,
    pub operations: Vec<Term>,
    pub parameters: Vec<Term>,
    pub requires: Vec<Term>,
}

// ── OperationInfo ───────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct OperationInfo {
    pub name: Term,
    pub sort_context: Option<Term>,
    pub params: Vec<FieldInfo>,
    pub return_type: Term,
    pub effects: Vec<Term>,
}

// ── FieldInfo ───────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct FieldInfo {
    pub name: String,
    pub type_name: Term,
}

// ── DescriptionInfo ─────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct DescriptionInfo {
    pub target: Term,
    pub content: String,
}

// ── Substitution trait ──────────────────────────────────────────

pub trait Substitution {
    fn apply(&self, t: Term, kb: &dyn KB) -> Term;
    fn compose(&self, s2: &dyn Substitution, kb: &dyn KB) -> Box<dyn Substitution>;
}

// ── SubstBridge ─────────────────────────────────────────────────

pub struct SubstBridge {
    pub inner: anthill_core::kb::subst::Substitution,
}

impl SubstBridge {
    pub fn new() -> Self {
        Self { inner: anthill_core::kb::subst::Substitution::new() }
    }

    pub fn from_core(s: anthill_core::kb::subst::Substitution) -> Self {
        Self { inner: s }
    }
}

// ── LogicalQuery ────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum LogicalQuery {
    EmptyQuery,
    PatternQuery {
        term: Term,
    },
    SortQuery {
        sort_name: String,
    },
    Conjunction {
        left: Box<LogicalQuery>,
        right: Box<LogicalQuery>,
    },
    Disjunction {
        left: Box<LogicalQuery>,
        right: Box<LogicalQuery>,
    },
    Negation {
        query: Box<LogicalQuery>,
    },
    Guarded {
        query: Box<LogicalQuery>,
        condition: Term,
    },
    Projected {
        query: Box<LogicalQuery>,
        vars: Vec<String>,
    },
    Limited {
        query: Box<LogicalQuery>,
        count: i64,
    },
}
