//! Runtime value representation for the evaluator.
//!
//! Per proposal 026 §Values: scalars stay unboxed, transient tuples/entities
//! hold inline payloads, and `Value::Term(TermId)` wraps KB-resident data
//! that's already hash-consed. Promotion to `TermId` happens only at KB
//! boundaries (assert_fact, Modify writes, SharedStream caching).

use std::rc::Rc;

use crate::intern::Symbol;
use crate::kb::node_occurrence::NodeOccurrence;
use crate::kb::term::{TermId, Var, VarId};

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
    // construction in `finish_constructor`; `views_structurally_equal` relies
    // on it for positional named-arg compare.
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
    // pointer — Clone bumps the slot's refcount, Drop decrements.
    Closure(ClosureHandle),
    /// WI-275 — a top-level operation referenced as a first-class function
    /// value (eta-expansion). A bare reference to an operation of arity ≥ 1 in
    /// value position (e.g. passing `inc` / `lt_int` to a `Function`-typed
    /// parameter) carries the operation symbol; applying it (`f(x)` / the
    /// closure-dispatch path) calls the operation, spreading a single tuple
    /// argument across a multi-parameter operation to match the
    /// `Function[(A, B), R]` ⇒ `op(a, b)` convention. WI-420: a `requires`-
    /// carrying op also captures the requirement dictionary it needs (`dict`),
    /// snapshotted at mint like a `Closure` snapshots `requirements`.
    OpRef {
        op: Symbol,
        /// WI-420: the dispatching requirement dict the op needs, evaluated at
        /// MINT in the eta-site frame (so an abstract requirement reads the
        /// enclosing `__req_*` and a concrete one builds from its `fact`), then
        /// installed into the callee frame at apply instead of forwarding the
        /// caller's. `None` only for a requires-free op (enclosing sort has no
        /// `requires`) or a namespace-level op; a requires-carrying eta captures
        /// a dict, INCLUDING a same-sort eta (its sort's `__req_self`) — an eta'd
        /// `OpRef` escapes to a foreign apply frame, so it cannot inherit.
        dict: Option<RequirementHandle>,
    },
    Stream(StreamHandle),
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
    /// impl: the slot stores `(functor, sub-requirements)`. A body reads
    /// the dictionary by name (`var_ref` of an inserted `__req_*` param,
    /// the names model — WI-237 retired the positional
    /// `requirement_at_current` read) and projects sub-deps via
    /// `requirement_at_sort(chain, k)`.
    /// Constructed by the IR's `construct_requirement(impl, [...])`
    /// form; carried in `frame.requirements` and `closure.requirements`
    /// channels. See `docs/design/operation-call-model.md` §"Runtime:
    /// frame, requirement value, closure".
    Requirement(RequirementHandle),

    // KB-sourced or already-committed data (hash-consed).
    //
    // A struct variant (not the old `Term(TermId)` tuple). Construct via
    // [`Value::term`] (also usable as a function value, e.g. `.map(Value::term)`);
    // match as `Value::Term { id, .. }`.
    Term {
        id: TermId,
    },

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

    /// WI-714 (proposal 052) — a rule cited by name as a first-class,
    /// composable query value: the typed, intensional face of a `LogicalQuery`.
    ///
    /// Why a dedicated variant (not a `Value::Entity`): `Relation` is an
    /// **abstract sort with no data constructor** — the same situation as
    /// `Stream`(`LogicalStream`) / `Map` / `Cell`. Nothing *builds* a `Relation`
    /// entity, so its values ride a **native carrier** variant that
    /// [`runtime_carrier_sort`] maps to `Relation` by fiat (exactly as
    /// `Value::Stream`→`LogicalStream`), and it is `Opaque` in the term view for
    /// the same reason those are — a native carrier is not structural data. (It is
    /// NOT "a handle for live state": a relation's content is a `LogicalQuery`,
    /// which is data. The load-bearing fact is only "constructor-less abstract
    /// sort → native carrier".) The one thing it carries that `Stream` lacks is the
    /// query; everything else (`splitFirst`/`takeN`/`find`/…) is inherited through
    /// `provides LogicalStream`.
    ///
    /// Two payloads:
    /// - `query` — a reflect `LogicalQuery` value (`pattern_query(head_atom)` for
    ///   a bare rule reference; the algebra increments wrap it in
    ///   `conjunction`/`guarded`/`disjunction`/… — the constructors of the same
    ///   ADT). Reaches [`crate::kb::KnowledgeBase::execute_logical_query`] verbatim.
    /// - `columns` — the relation's free variables `(column name, VarId)` in head
    ///   declaration order: the schema `T`'s projection targets. The `VarId`s are
    ///   the fresh globals embedded in `query`'s goal atom, so an answer
    ///   substitution binds exactly them; `materialize_solution` reads each column
    ///   through these ids (1-collapsing to the element for one, `Unit` for zero).
    ///
    /// A `Relation` `provides LogicalStream[T, E]`, so it is consumed through the
    /// ordinary Stream API: [`runtime_carrier_sort`] maps it to `Relation`, and
    /// `Relation.splitFirst` (a host builtin) runs the query and pumps a
    /// [`crate::eval::stream::StreamSource::MaterializedResolver`] over `columns`.
    /// `Rc` payloads keep `clone` O(1) (an arg-bind / var-read cost).
    Relation {
        query: Rc<Value>,
        columns: Rc<[(Symbol, VarId)]>,
    },
}

/// A hash-consed `TermId` is the universal `Value::Term` carrier (WI-373). Lets
/// the carrier-agnostic rule-assertion entries take `head: impl Into<Value>`
/// while every existing `TermId` caller passes its term unchanged.
impl From<TermId> for Value {
    fn from(t: TermId) -> Self {
        Value::term(t)
    }
}

impl Value {
    /// Construct a `Value::Term` — the universal hash-consed carrier. Also the way
    /// to use the `Term` constructor as a function value (`.map(Value::term)`),
    /// which the struct variant `Value::Term { .. }` cannot be.
    pub fn term(id: TermId) -> Value {
        Value::Term { id }
    }

    /// WI-714 — the normalizing constructor for the `Value::Node` carrier. A
    /// carrier must not redundantly wrap another, so an occurrence that already
    /// IS a value-carrier collapses instead of nesting: `node(Spliced(v)) = v`
    /// (a value wrapped in a node wrapped in a value is just the value), and
    /// `node(Var(x)) = Value::Var(x)` (a bare variable occurrence is a value-level
    /// variable). The carrier algebra then cancels — `Spliced(Node(occ))` and
    /// `node(Spliced(v))` undo each other — so no view or walker ever meets a
    /// doubly-wrapped carrier. Prefer this over a raw `Value::Node(occ)`.
    pub fn node(occ: Rc<NodeOccurrence>) -> Value {
        use crate::kb::node_occurrence::Expr;
        match occ.as_expr() {
            Some(Expr::Spliced(v)) => return v.clone(),
            Some(Expr::Var(var)) => return Value::Var(*var),
            _ => {}
        }
        Value::Node(occ)
    }

    /// Scalar-leaf equality. Tuples / Entities / Closures / Streams
    /// compare as unequal here. For shape-aware, CARRIER-AGNOSTIC structural
    /// compare on any two `Value`s — including the cross-carrier `Value::Term`
    /// vs `Value::Node`/`Entity` case — use
    /// [`crate::kb::term_view::views_structurally_equal`] (needs `&KnowledgeBase`
    /// to decode a `Value::Term`). WI-486 removed the carrier-blind
    /// `Value::structural_eq` that silently called every cross-carrier pair
    /// unequal; `scalar_eq` survives only as the leaf primitive that comparator
    /// and a few ground-label dedups build on.
    pub fn scalar_eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Int(x), Value::Int(y)) => x == y,
            (Value::BigInt(x), Value::BigInt(y)) => x == y,
            (Value::Float(x), Value::Float(y)) => x == y,
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Str(x), Value::Str(y)) => x == y,
            (Value::Unit, Value::Unit) => true,
            (Value::Term { id: x, .. }, Value::Term { id: y, .. }) => x == y,
            // WI-109: two value-level logic variables are equal iff they are
            // the same variable (kind + id; `VarId` compares by id only).
            (Value::Var(x), Value::Var(y)) => x == y,
            _ => false,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        if let Value::Int(n) = self { Some(*n) } else { None }
    }

    /// Unwrap the hash-consed `Value::Term` variant, panicking LOUDLY on any
    /// other carrier. WI-477: this replaces the old silent `as_term() ->
    /// Option<TermId>`, whose `None` on a `Value::Node`/`Entity`/scalar was read
    /// as "no term" and silently dropped the carrier (the binding-erasure class).
    /// Use this ONLY where a `Term` carrier is *guaranteed* (a branch already
    /// narrowed by `matches!(v, Value::Term(_))`, a fact head known hash-consed)
    /// or genuinely DEMANDED (a term-only boundary that cannot proceed otherwise)
    /// — so a stray non-`Term` is a bug that fails loud, never a silent skip. A
    /// caller that legitimately handles a non-`Term` carrier narrows explicitly
    /// (`if let Value::Term(t) = …`) or reads carrier-agnostically via `TermView`.
    pub fn expect_term(&self) -> TermId {
        match self {
            Value::Term { id, .. } => *id,
            other => panic!(
                "expect_term: expected a hash-consed Value::Term, got Value::{}",
                other.type_name(),
            ),
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        if let Value::Bool(b) = self { Some(*b) } else { None }
    }

    pub fn as_str(&self) -> Option<&str> {
        if let Value::Str(s) = self { Some(s.as_str()) } else { None }
    }

    /// WI-787: a tuple's components in SOURCE order, or `None` when this is not
    /// a `Value::Tuple`. THE owning reader for the `pos ++ named` invariant —
    /// read a tuple's components through this, never off one half.
    ///
    /// `classify_ctor_arg` (eval/eval.rs) owns the SPLIT and documents why `pos`
    /// is always a source-order PREFIX and `named` the remainder in order; this
    /// is the reader side of that invariant. Reading one half alone silently
    /// sees a DIFFERENT tuple than was written — a name-keyed tuple presents as
    /// ZERO components to a `pos` reader. That is one bug twice over: WI-785 in
    /// `match_tuple_pattern`, WI-787 in `spread_eta_args`, where it made an
    /// OPERATION and a LAMBDA stop being interchangeable as function values.
    ///
    /// Positional ORDER is the whole content of the correspondence — a named
    /// tuple is an ORDERED PRODUCT, exempted from
    /// `canonicalize_record_named_args` because "source order IS its identity" —
    /// so a consumer that reorders these components is wrong even though it
    /// reads all of them.
    ///
    /// ## Why the two halves stay PUBLIC
    ///
    /// The obvious hardening — make `pos`/`named` private so every half-reader
    /// becomes a COMPILE ERROR — was considered and REFUSED, because legitimate
    /// half-readers exist and it would false-positive on all of them:
    /// `TermView for Value` (kb/term_view.rs) reads `pos` by INDEX in `pos_arg`
    /// and `named` by SYMBOL in `named_arg` / `named_keys`, which is the trait's
    /// contract — it mirrors `Term::Fn { pos_args, named_args }` and must keep
    /// the halves apart. `field_access` (eval/builtins.rs) reads BOTH but
    /// through different access paths (`named` by short name, `pos` by
    /// `positional_label_index`), so a flat component iterator cannot serve it
    /// either. Those reads are SANCTIONED; do not re-litigate them as bugs.
    ///
    /// What is left unenforced is therefore only future readers, which is what
    /// this accessor exists to reach — the invariant was documented in three doc
    /// blocks across two files and the prose demonstrably did not reach a reader
    /// 900 lines away in the same file.
    ///
    /// ## Why this does NOT generalize to `Value::Entity`
    ///
    /// `Entity` has the identical two-half LAYOUT but not the identical
    /// invariant: `finish_constructor` canonicalizes an entity's `named` into
    /// DECLARED FIELD order, while a tuple is exempted from that canonicalization
    /// precisely so its SOURCE order survives. `pos ++ named` therefore means
    /// source order for a `Tuple` and canonical order for an `Entity`, and one
    /// shared accessor would be a single iterator silently meaning two different
    /// things — exporting a source-order guarantee to a carrier that does not
    /// have it. `constructor_sub_values` (eval/pattern.rs) stays separate for
    /// this reason.
    pub fn tuple_components(&self) -> Option<TupleComponents<'_>> {
        match self {
            Value::Tuple { pos, named } => Some(TupleComponents { pos, named }),
            _ => None,
        }
    }

    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Int(_) => "Int64",
            Value::BigInt(_) => "BigInt",
            Value::Float(_) => "Float",
            Value::Bool(_) => "Bool",
            Value::Str(_) => "String",
            Value::Unit => "Unit",
            Value::Tuple { .. } => "Tuple",
            Value::Entity { .. } => "Entity",
            Value::Closure(_) => "Closure",
            Value::OpRef { .. } => "OpRef",
            Value::Stream(_) => "Stream",
            Value::Substitution(_) => "Substitution",
            Value::Map(_) => "Map",
            Value::Cell(_) => "Cell",
            Value::Requirement(_) => "Requirement",
            Value::Term { .. } => "Term",
            Value::Node(_) => "Node",
            Value::Var(_) => "Var",
            Value::Relation { .. } => "Relation",
        }
    }
}

/// WI-787: a borrowed view of a tuple's components as ONE sequence in source
/// order, handed out by [`Value::tuple_components`].
///
/// A handle rather than a bare iterator so the COUNT and the WALK come off the
/// same value. Every consumer tests arity before walking, and `Chain` is not an
/// `ExactSizeIterator`; handing back a bare chain would force a second accessor
/// for the count, and with it a second match on the value plus an unreachable
/// `expect` at each call site. Here [`TupleComponents::len`] is O(1) — the two
/// halves know their own lengths — and cannot be asked about a different value
/// than the one being walked.
pub struct TupleComponents<'a> {
    pos: &'a [Value],
    named: &'a [(Symbol, Value)],
}

impl<'a> TupleComponents<'a> {
    /// How many components the tuple has, counting BOTH halves.
    pub fn len(&self) -> usize {
        self.pos.len() + self.named.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The components in SOURCE order — `pos` then `named`, per the invariant
    /// on [`Value::tuple_components`]. Allocation-free.
    pub fn iter(&self) -> impl Iterator<Item = &'a Value> {
        self.pos.iter().chain(self.named.iter().map(|(_, v)| v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalars_unboxed() {
        assert_eq!(Value::Int(42).as_int(), Some(42));
        assert_eq!(Value::Bool(true).as_bool(), Some(true));
        assert_eq!(Value::Int(1).type_name(), "Int64");
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

        // WI-486: `Value::structural_eq` was removed; structural compare now
        // routes through the carrier-aware `views_structurally_equal` (an empty
        // KB suffices — var values carry no `Value::Term` to decode).
        use crate::kb::term_view::views_structurally_equal;
        use crate::kb::KnowledgeBase;

        #[test]
        fn same_var_is_equal_name_irrelevant() {
            let kb = KnowledgeBase::new();
            // VarId compares by id only — display name is irrelevant.
            assert!(views_structurally_equal(&kb, &global(7, 1), &global(7, 2)));
            assert!(global(7, 1).scalar_eq(&global(7, 1)));
        }

        #[test]
        fn distinct_vars_and_kinds_differ() {
            let kb = KnowledgeBase::new();
            assert!(!views_structurally_equal(&kb, &global(1, 0), &global(2, 0)));
            // Same numeric payload, different kind ⇒ not equal.
            assert!(!views_structurally_equal(
                &kb,
                &global(0, 0),
                &Value::Var(Var::DeBruijn(0))
            ));
            assert!(views_structurally_equal(
                &kb,
                &Value::Var(Var::DeBruijn(3)),
                &Value::Var(Var::DeBruijn(3))
            ));
        }

        #[test]
        fn var_not_equal_to_non_var() {
            let kb = KnowledgeBase::new();
            assert!(!views_structurally_equal(&kb, &global(0, 0), &Value::Int(0)));
            assert!(!views_structurally_equal(&kb, &Value::Int(0), &global(0, 0)));
        }
    }
}
