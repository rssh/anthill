//! Runtime value representation for the evaluator.
//!
//! Per proposal 026 §Values: scalars stay unboxed, transient tuples/entities
//! hold inline payloads, and `Value::Term(TermId)` wraps KB-resident data
//! that's already hash-consed. Promotion to `TermId` happens only at KB
//! boundaries (assert_fact, Modify writes, SharedStream caching).

use crate::intern::Symbol;
use crate::kb::term::TermId;

pub use super::cell_arena::CellHandle;
pub use super::closure::ClosureHandle;
pub use super::map_arena::MapHandle;
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

    // Anonymous tuple (no functor). `Vec` rather than `SmallVec<[Value; N]>`
    // to avoid a self-referential layout cycle.
    Tuple {
        pos: Vec<Value>,
        named: Vec<(Symbol, Value)>,
    },

    // Constructed entity (has a functor), transient until persisted. Zero
    // TermStore allocation unless/until it crosses a KB boundary.
    //
    // Invariant: `named` is sorted canonically (declared field order when
    // the functor is registered, `Symbol::index()` otherwise) — matches
    // the KB-side `Term::Fn { named_args }` invariant. Enforced at
    // construction in `finish_constructor`; `structural_eq` relies on it
    // for positional compare.
    Entity {
        functor: Symbol,
        pos: Vec<Value>,
        named: Vec<(Symbol, Value)>,
    },

    // Interpreter-owned handles. Each is an arena-refcounted smart
    // pointer — Clone bumps the slot's refcount, Drop decrements. The
    // lazy arena is not yet built; `LazyHandle` stays a plain u32 newtype
    // until M5 lands it.
    Closure(ClosureHandle),
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

    // KB-sourced or already-committed data (hash-consed).
    Term(TermId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LazyHandle(pub(crate) u32);

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
            _ => self.scalar_eq(other),
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        if let Value::Int(n) = self { Some(*n) } else { None }
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
            Value::Stream(_) => "Stream",
            Value::Lazy(_) => "Lazy",
            Value::Substitution(_) => "Substitution",
            Value::Map(_) => "Map",
            Value::Cell(_) => "Cell",
            Value::Term(_) => "Term",
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
            pos: vec![Value::Int(1), Value::Int(2)],
            named: Vec::new(),
        };
        match t {
            Value::Tuple { pos, .. } => assert_eq!(pos.len(), 2),
            _ => panic!(),
        }
    }
}
