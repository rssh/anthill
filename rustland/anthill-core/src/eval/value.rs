//! Runtime value representation for the evaluator.
//!
//! Per proposal 026 §Values: scalars stay unboxed, transient tuples/entities
//! hold inline payloads, and `Value::Term(TermId)` wraps KB-resident data
//! that's already hash-consed. Promotion to `TermId` happens only at KB
//! boundaries (assert_fact, Modify writes, SharedStream caching).

use std::rc::Rc;

use crate::intern::Symbol;
use crate::kb::node_occurrence::NodeOccurrence;
use crate::kb::term::{TermId, Var};

pub use super::cell_arena::CellHandle;
pub use super::closure::ClosureHandle;
pub use super::map_arena::MapHandle;
pub use super::requirement_arena::RequirementHandle;
pub use super::stream::StreamHandle;
pub use super::subst_arena::SubstHandle;

#[derive(Clone, Debug)]
pub enum Value {
    // Unboxed scalars — zero alloc, zero hash lookup.
    Int(i64),
    /// Arbitrary-precision integer. Lives outside the hash-consed TermStore
    /// so in-flight arithmetic doesn't pay the alloc+refcount tax per
    /// intermediate value. Only promoted to `Value::Term(TermId)` at KB
    /// boundaries.
    BigInt(num_bigint::BigInt),
    Float(f64),
    Bool(bool),
    Str(String),
    Unit,

    // Anonymous tuple (no functor). Payloads are `Rc<[…]>` for the same
    // O(1)-clone reason as `Entity` below (and to avoid a self-referential
    // layout cycle).
    Tuple {
        pos: Rc<[Value]>,
        named: Rc<[(Symbol, Value)]>,
    },

    // Constructed entity (has a functor), transient until persisted. Zero
    // TermStore allocation unless/until it crosses a KB boundary.
    //
    // Invariant: `named` is sorted canonically (declared field order when
    // the functor is registered, `Symbol::index()` otherwise) — matches
    // the KB-side `Term::Fn { named_args }` invariant. Enforced at
    // construction in `finish_constructor`; `structural_eq` relies on it
    // for positional compare.
    // Payloads are `Rc<[…]>` rather than `Vec<…>` so `Value::clone` is an
    // O(1) refcount bump instead of a deep copy. This matters because an
    // anthill list is a chain of `cons(head, tail)` entities: with `Vec`
    // payloads, cloning a list `Value` (on every arg-bind and variable
    // read) deep-copies the whole spine — O(N) per clone, O(N²) for a
    // recursive op threading a list. With `Rc<[…]>` the tail is shared, so
    // the clone is O(1). Read access is transparent via `Deref` to `[…]`;
    // build the `Vec` first (sorting `named` canonically) then `.into()`.
    Entity {
        functor: Symbol,
        pos: Rc<[Value]>,
        named: Rc<[(Symbol, Value)]>,
    },

    // Interpreter-owned handles. Each is an arena-refcounted smart
    // pointer — Clone bumps the slot's refcount, Drop decrements. The
    // lazy arena is not yet built; `LazyHandle` stays a plain u32 newtype
    // until M5 lands it.
    Closure(ClosureHandle),
    /// WI-275 — a top-level operation referenced as a first-class function
    /// value (eta-expansion). A bare reference to an operation of arity ≥ 1 in
    /// value position (e.g. passing `inc` / `lt_int` to a `Function`-typed
    /// parameter) carries the operation symbol; applying it (`f(x)` / the
    /// closure-dispatch path) calls the operation, spreading a single tuple
    /// argument across a multi-parameter operation to match the
    /// `Function[(A, B), R]` ⇒ `op(a, b)` convention. Unlike a `Closure` it
    /// captures no environment — a global operation needs none.
    OpRef(Symbol),
    Stream(StreamHandle),
    Lazy(LazyHandle),
    /// First-class substitution — reference into an arena owned by the
    /// interpreter. Yielded by stream `splitFirst` and constructed by
    /// `Substitution.compose`; passed to `Substitution.apply`.
    Substitution(SubstHandle),
    /// First-class map — arena-refcounted handle into the per-interpreter
    /// MapArena. Type parameters are erased at runtime; the type checker
    /// guards against heterogeneous keys/values (proposal 035).
    Map(MapHandle),
    /// Mutable typed cell — arena-refcounted handle into the
    /// per-interpreter CellArena. Identity is the slot index (allocation-
    /// time uid); each `Cell.new` returns a fresh handle. The held value
    /// is mutated in place via `Cell.set`. Cycles are inexpressible:
    /// the typer's `may_contain_cell` rule rejects `Cell[T]` whenever T
    /// transitively contains Cell, so the runtime never has to detect
    /// cycles. See proposal 037 §"Cell[V]" + `docs/design/cell-runtime.md`.
    Cell(CellHandle),
    /// First-class requirement value — arena-refcounted handle into the
    /// per-interpreter RequirementArena. Materializes a resolved spec
    /// impl: the slot stores `(functor, sub-requirements)` so bodies
    /// can dispatch through it via `requirement_at_current(i, op_short)`
    /// and project sub-deps via `requirement_at_sort(chain, k)`.
    /// Constructed by the IR's `construct_requirement(impl, [...])`
    /// form; carried in `frame.requirements` and `closure.requirements`
    /// channels. See `docs/design/operation-call-model.md` §"Runtime:
    /// frame, requirement value, closure".
    Requirement(RequirementHandle),

    // KB-sourced or already-committed data (hash-consed).
    Term(TermId),

    /// WI-109 — a logic variable at the value level (flex `Global`,
    /// `DeBruijn`, or `Rigid`). Makes the `Term` ↔ `Value` round-trip
    /// lossless for variable-bearing terms: a `Term::Var` lifts to
    /// `Value::Var(var)` (kind-typed, structurally reconstructible) rather
    /// than surviving only as `Value::Term(tid)` or the lossy
    /// `Value::Entity { var_repr, name: "?x" }` reflect encoding. Arithmetic
    /// and comparison over a `Value::Var` is an error ("cannot evaluate over
    /// a variable"); `structural_eq` compares by `Var` equality;
    /// `alloc_from_value` routes it back to `Term::Var`.
    Var(Var),

    /// WI-242 — positional content binding (operation body, rule head,
    /// or other NodeOccurrence). Reflection ops like `body_of`, `head_of`,
    /// `args_of` produce this; consumers walk the `Rc<NodeOccurrence>`
    /// tree directly. Atomic refcount on clone — no deep copy.
    /// See `docs/design/occurrence-as-value-type.md`.
    Node(Rc<NodeOccurrence>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LazyHandle(pub(crate) u32);

/// A hash-consed `TermId` is the universal `Value::Term` carrier (WI-373). Lets
/// the carrier-agnostic rule-assertion entries take `head: impl Into<Value>`
/// while every existing `TermId` caller passes its term unchanged.
impl From<TermId> for Value {
    fn from(t: TermId) -> Self {
        Value::Term(t)
    }
}

impl Value {
    /// Scalar-leaf equality. Tuples / Entities / Closures / Streams / Lazies
    /// compare as unequal here — for shape-aware compare on Value-to-Value
    /// see [`Self::structural_eq`]; for cross-lineage compare (Value vs
    /// `(&KB, TermId)`) see 026.1 Q2's `TermView` work.
    pub fn scalar_eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Int(x), Value::Int(y)) => x == y,
            (Value::BigInt(x), Value::BigInt(y)) => x == y,
            (Value::Float(x), Value::Float(y)) => x == y,
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Str(x), Value::Str(y)) => x == y,
            (Value::Unit, Value::Unit) => true,
            (Value::Term(x), Value::Term(y)) => x == y,
            // WI-109: two value-level logic variables are equal iff they are
            // the same variable (kind + id; `VarId` compares by id only).
            (Value::Var(x), Value::Var(y)) => x == y,
            _ => false,
        }
    }

    /// Structural equality over `Value` — scalars compare by value, Entities
    /// and Tuples recurse on positional and named children. Named args
    /// compare by position, relying on the canonical-order invariant on
    /// `Value::Entity::named`. Opaque handles (Closure / Stream / Lazy)
    /// remain unequal. Cross-lineage comparisons (e.g. `Value::Term` vs
    /// `Value::Entity`) are conservatively false; unifying those is
    /// 026.1 Q2's `TermView` job.
    pub fn structural_eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Tuple { pos: p1, named: n1 }, Value::Tuple { pos: p2, named: n2 }) => {
                children_eq(p1, n1, p2, n2)
            }
            (
                Value::Entity { functor: f1, pos: p1, named: n1 },
                Value::Entity { functor: f2, pos: p2, named: n2 },
            ) => f1 == f2 && children_eq(p1, n1, p2, n2),
            // WI-246: two occurrence sub-parts compare structurally (the
            // resolver's non-linear-pattern consistency check binds a head var
            // to occurrence goals at two positions; distinct `Rc`s of the same
            // structure must be equal).
            (Value::Node(a), Value::Node(b)) => {
                crate::kb::node_occurrence::occurrence_structural_eq(a, b)
            }
            _ => self.scalar_eq(other),
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        if let Value::Int(n) = self { Some(*n) } else { None }
    }

    /// Unwrap the hash-consed `Value::Term` variant. The occurrence-native
    /// resolver (WI-246) carries goals as `Value`; this is the unwrap at the
    /// shrinking term-only boundary where a builtin still needs a `TermId`.
    /// `Value::Node` goals (rule-body occurrences) return `None`.
    pub fn as_term(&self) -> Option<TermId> {
        if let Value::Term(t) = self { Some(*t) } else { None }
    }

    pub fn as_bool(&self) -> Option<bool> {
        if let Value::Bool(b) = self { Some(*b) } else { None }
    }

    pub fn as_str(&self) -> Option<&str> {
        if let Value::Str(s) = self { Some(s.as_str()) } else { None }
    }

    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Int(_) => "Int",
            Value::BigInt(_) => "BigInt",
            Value::Float(_) => "Float",
            Value::Bool(_) => "Bool",
            Value::Str(_) => "String",
            Value::Unit => "Unit",
            Value::Tuple { .. } => "Tuple",
            Value::Entity { .. } => "Entity",
            Value::Closure(_) => "Closure",
            Value::OpRef(_) => "OpRef",
            Value::Stream(_) => "Stream",
            Value::Lazy(_) => "Lazy",
            Value::Substitution(_) => "Substitution",
            Value::Map(_) => "Map",
            Value::Cell(_) => "Cell",
            Value::Requirement(_) => "Requirement",
            Value::Term(_) => "Term",
            Value::Node(_) => "Node",
            Value::Var(_) => "Var",
        }
    }
}

fn children_eq(
    p1: &[Value],
    n1: &[(Symbol, Value)],
    p2: &[Value],
    n2: &[(Symbol, Value)],
) -> bool {
    p1.len() == p2.len()
        && n1.len() == n2.len()
        && p1.iter().zip(p2).all(|(a, b)| a.structural_eq(b))
        && n1.iter().zip(n2).all(|((k1, v1), (k2, v2))| k1 == k2 && v1.structural_eq(v2))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalars_unboxed() {
        assert_eq!(Value::Int(42).as_int(), Some(42));
        assert_eq!(Value::Bool(true).as_bool(), Some(true));
        assert_eq!(Value::Int(1).type_name(), "Int");
    }

    #[test]
    fn tuple_builds() {
        let t = Value::Tuple {
            pos: vec![Value::Int(1), Value::Int(2)].into(),
            named: Vec::new().into(),
        };
        match t {
            Value::Tuple { pos, .. } => assert_eq!(pos.len(), 2),
            _ => panic!(),
        }
    }

    // WI-109: value-level logic variables.
    mod var {
        use super::*;
        use crate::intern::Symbol;
        use crate::kb::term::VarId;

        fn global(id: u32, name: u32) -> Value {
            Value::Var(Var::Global(VarId::new(id, Symbol::from_raw(name))))
        }

        #[test]
        fn type_name_is_var() {
            assert_eq!(global(0, 0).type_name(), "Var");
            assert_eq!(Value::Var(Var::DeBruijn(0)).type_name(), "Var");
        }

        #[test]
        fn same_var_is_equal_name_irrelevant() {
            // VarId compares by id only — display name is irrelevant.
            assert!(global(7, 1).structural_eq(&global(7, 2)));
            assert!(global(7, 1).scalar_eq(&global(7, 1)));
        }

        #[test]
        fn distinct_vars_and_kinds_differ() {
            assert!(!global(1, 0).structural_eq(&global(2, 0)));
            // Same numeric payload, different kind ⇒ not equal.
            assert!(!global(0, 0).structural_eq(&Value::Var(Var::DeBruijn(0))));
            assert!(Value::Var(Var::DeBruijn(3)).structural_eq(&Value::Var(Var::DeBruijn(3))));
        }

        #[test]
        fn var_not_equal_to_non_var() {
            assert!(!global(0, 0).structural_eq(&Value::Int(0)));
            assert!(!Value::Int(0).structural_eq(&global(0, 0)));
        }
    }
}
