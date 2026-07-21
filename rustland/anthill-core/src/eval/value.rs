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

    /// WI-803: does this tuple carry component NAMES at all?
    ///
    /// A tuple populates exactly one of its two halves (WI-786), so this splits the
    /// carrier cleanly: a NAME-keyed tuple can be read by label, a POSITIONAL one
    /// cannot — it has no names, and its slot order is the whole of what it says.
    /// That makes it the gate on the by-label destructuring arm.
    ///
    /// A positional carrier is not a degraded named one; reading it by slot is
    /// exact, not a fallback. It is also how a SPREAD call arrives: applying a
    /// two-binder closure as `f(3, 10)` gathers the arguments into
    /// `Tuple { pos: [3, 10], named: [] }` (`gather_closure_arg`) while the
    /// expected type is the named `(acc: Acc, x: Elem)` — so the labels are real
    /// and there is still nothing to key on. That shape is the COMMON one
    /// (`foldLeft` and every other two-binder callback), which makes this the arm
    /// most destructuring executions take, not a corner; a by-label read of it
    /// raised `MatchFailed` on every such program until this gate was added.
    ///
    /// THE INVARIANT THIS RESTS ON, stated because the arm is selected silently: a
    /// positional carrier reaching a LABELLED pattern always holds its components
    /// in the expected type's DECLARED order. It holds because the only producer of
    /// such a carrier is `gather_closure_arg`, which preserves argument order, and
    /// the routes that could permute those arguments are refused at load — a
    /// function value applied with named arguments (`f(b: 10, a: 3)`) is rejected
    /// with "records no parameter names to bind a label to", since an arrow drops
    /// its binder names (WI-783). If arrows ever learn their parameter names, that
    /// barrier goes and this invariant has to be re-established rather than
    /// assumed. See `spread_eta_args` (eval/eval.rs) for the same dependency on the
    /// operation-spelling side.
    pub fn is_name_keyed(&self) -> bool {
        !self.named.is_empty()
    }

    /// WI-803: the component a LABEL names, or `None` when the tuple has no such
    /// component. THE one rule for reading a tuple by name, shared by the two
    /// readers that must agree on it — `field_access` (`t.x`, eval/builtins.rs)
    /// and `match_tuple_pattern`'s by-label arm (eval/pattern.rs), which since
    /// WI-803 destructures by label rather than by slot.
    ///
    /// They MUST agree, and the codebase has already paid twice for two walks over
    /// one tuple diverging: WI-800 found the typer's expected-type threading and
    /// the conformance relation picking different components, and WI-805 found the
    /// relation and `field_access` doing the same on a duplicate label. A
    /// destructuring reader that resolved labels its own way would be the third.
    ///
    /// The rule, in the order `field_access` established:
    ///  1. scan `named` by SHORT name and take the FIRST match — short name, not
    ///     symbol identity, because a component's Symbol may carry a qualified path
    ///     the label does not;
    ///  2. otherwise read the synthetic `_N` convention through its owner
    ///     (`positional_label_index`, WI-790), which maps 1-based `_N` to `pos[N-1]`
    ///     and refuses `_0` / `_01` as USER labels — those are reachable only by (1).
    ///
    /// Both sides are normalized through [`short_name_of`], the WI-672 owner of the
    /// one place short-name matching legitimately survives. Normalizing only the
    /// COMPONENT side (as this first did) is a half-rule: `match_tuple_pattern`
    /// hands over a label read off a TYPE's field list, and those symbols can
    /// arrive qualified — `project_type_component` compares the very same
    /// `named_tuple_fields` symbols with `same_label` rather than `==`, which is
    /// only necessary if they can. A qualified label would then have matched
    /// nothing and raised `MatchFailed` on a correct program.
    ///
    /// Step 2 cannot compete with step 1 for the same tuple, per the one-half
    /// invariant stated on [`Self::is_name_keyed`].
    pub fn by_label(&self, kb: &crate::kb::KnowledgeBase, label: &str) -> Option<&'a Value> {
        self.by_label_index(kb, label).and_then(|i| self.component_at(i))
    }

    /// [`Self::by_label`]'s answer as a component INDEX, in [`Self::iter`] order
    /// (`pos` then `named`) — the owner of the rule, with `by_label` its
    /// value-returning face.
    ///
    /// The index exists because a caller resolving SEVERAL labels against one
    /// tuple has to know whether two of them landed on the SAME component, and a
    /// returned `&Value` cannot answer that. `match_tuple_pattern` needs exactly
    /// that: two binders served the same component is a match that binds one
    /// component twice and never reads another, which is a wrong answer rather
    /// than a failed match. Two labels can collide either by being equal or — since
    /// step 1 compares SHORT names — by being distinct qualified names sharing a
    /// last segment, and an index catches both without the caller re-deriving the
    /// comparison.
    pub fn by_label_index(&self, kb: &crate::kb::KnowledgeBase, label: &str) -> Option<usize> {
        let want = crate::kb::typing::short_name_of(label);
        for (i, (sym, _)) in self.named.iter().enumerate() {
            if crate::kb::typing::short_name_of(kb.resolve_sym(*sym)) == want {
                return Some(self.pos.len() + i);
            }
        }
        // `want`, NOT the raw label. The doc above justifies normalizing because a
        // label read off a TYPE's field list can arrive qualified — and if that is
        // true it is true of a POSITIONAL tuple's `_N` fields too, so reading the
        // raw label here would normalize one branch and not the other and fail to
        // resolve `ns._1`. Asserting the premise on one branch while relying on its
        // negation on the other is the inconsistency this had.
        crate::intern::positional_label_index(want).filter(|i| *i < self.pos.len())
    }

    /// The component at an [`Self::iter`]-order index — the inverse of
    /// [`Self::by_label_index`], over the same `pos ++ named` sequence.
    pub fn component_at(&self, flat: usize) -> Option<&'a Value> {
        match self.pos.get(flat) {
            Some(v) => Some(v),
            None => self.named.get(flat - self.pos.len()).map(|(_, v)| v),
        }
    }

    /// WI-803: are these labels the SYNTHETIC `_1.._n` convention — i.e. does the
    /// expected type say "positional tuple"?
    ///
    /// Read through [`is_positional_label_at`](crate::intern::is_positional_label_at),
    /// WI-790's owner, which requires each label to be the synthetic name for ITS
    /// OWN index — so a USER label like `_0`, `_01`, or a `_2` written first is not
    /// one, and a genuinely name-keyed type is never mistaken for a positional one.
    ///
    /// This gates OUT the by-label arm, because for a positional type a label
    /// carries no information a slot does not: `_i` MEANS slot `i`. Reading such a
    /// type by label is not merely redundant, it FAILS whenever the value is
    /// name-keyed — the named scan finds no component called `_1`, and the `_N`
    /// fallback indexes a `pos` half that a name-keyed carrier leaves empty. The
    /// combination is reachable: a relation ROW is built all-named (see
    /// `spread_eta_args`, eval/eval.rs), so a row destructured against a positional
    /// tuple type has a name-keyed value and synthetic labels at once, and by-label
    /// would raise `MatchFailed` where reading in source order succeeds.
    pub fn labels_are_positional(kb: &crate::kb::KnowledgeBase, labels: &[Symbol]) -> bool {
        !labels.is_empty()
            && labels.iter().enumerate().all(|(i, l)| {
                crate::intern::is_positional_label_at(
                    crate::kb::typing::short_name_of(kb.resolve_sym(*l)),
                    i,
                )
            })
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

    /// WI-803 — the by-label tuple reader, tested at the reader rather than
    /// end-to-end.
    ///
    /// These pin two guards that a /code-review of the first cut found, and that
    /// NO source-level program in this workspace can currently drive: the
    /// end-to-end fixtures written for them were control-run with each guard
    /// removed and PASSED, i.e. they were blind. Rather than ship a test that
    /// asserts nothing, the mechanism is exercised directly here — a tuple carrier
    /// and a label list, built by hand into the shapes the guards exist for.
    ///
    /// Both guards are therefore DEFENSIVE. That is stated, not hidden: the reader
    /// must not depend on a caller never handing it these shapes, because the
    /// carrier/label combinations are legal and the barriers that keep them out of
    /// today's programs are incidental (see `is_name_keyed`' invariant note).
    mod wi803_by_label_reader {
        use super::*;
        use crate::kb::KnowledgeBase;

        fn named_tuple(kb: &mut KnowledgeBase, fields: &[(&str, i64)]) -> Value {
            Value::Tuple {
                pos: Vec::new().into(),
                named: fields.iter().map(|(n, v)| (kb.intern(n), Value::Int(*v))).collect::<Vec<_>>().into(),
            }
        }

        fn positional_tuple(vals: &[i64]) -> Value {
            Value::Tuple {
                pos: vals.iter().map(|v| Value::Int(*v)).collect::<Vec<_>>().into(),
                named: Vec::new().into(),
            }
        }

        /// A QUALIFIED synthetic label resolves against a positional tuple.
        ///
        /// `by_label` normalizes the component side to a short name because a label
        /// read off a TYPE's field list can arrive qualified. If that premise holds
        /// it holds for a positional tuple's `_N` fields too — so the `_N` branch
        /// must normalize as well. It first did not, and `ns._1` resolved to
        /// nothing while `ns.a` resolved fine: one branch asserting the premise and
        /// the other relying on its negation.
        #[test]
        fn qualified_positional_label_resolves_like_a_qualified_named_one() {
            let mut kb = KnowledgeBase::new();
            let t = positional_tuple(&[3, 10]);
            let c = t.tuple_components().expect("tuple");
            assert!(matches!(c.by_label(&kb, "_1"), Some(Value::Int(3))));
            assert!(
                matches!(c.by_label(&kb, "ns._1"), Some(Value::Int(3))),
                "a qualified `_N` must normalize to its short name, as the named scan does",
            );
            // Out of range stays None rather than falling through into `named`.
            assert!(c.by_label(&kb, "_5").is_none());
            let _ = &mut kb;
        }

        /// Synthetic labels cannot be resolved against a NAME-keyed carrier — which
        /// is why `labels_are_positional` gates the by-label arm OFF for them.
        ///
        /// Without that gate a positional tuple TYPE (whose fields ARE `_1.._n`)
        /// meeting a name-keyed value sends every label through a reader that finds
        /// no component called `_1` and then indexes an empty `pos` half, so the
        /// match fails where reading in source order succeeds. An all-named
        /// relation ROW is the shape that makes this reachable in principle.
        #[test]
        fn synthetic_labels_do_not_resolve_against_a_name_keyed_carrier() {
            let mut kb = KnowledgeBase::new();
            let t = named_tuple(&mut kb, &[("x", 1), ("y", 2)]);
            let c = t.tuple_components().expect("tuple");
            assert!(
                c.by_label(&kb, "_1").is_none(),
                "no component is called `_1` and `pos` is empty — this is exactly \
                 why the matcher must not route synthetic labels here",
            );
            let synthetic: Vec<Symbol> = ["_1", "_2"].iter().map(|n| kb.intern(n)).collect();
            assert!(TupleComponents::labels_are_positional(&kb, &synthetic));
        }

        /// `labels_are_positional` must recognize only the SYNTHETIC convention, or
        /// it would switch a genuinely name-keyed type onto the slot reader and
        /// reintroduce WI-788.
        #[test]
        fn only_synthetic_labels_count_as_positional() {
            let mut kb = KnowledgeBase::new();
            let named: Vec<Symbol> = ["a", "b"].iter().map(|n| kb.intern(n)).collect();
            assert!(!TupleComponents::labels_are_positional(&kb, &named));
            // `_2` written FIRST is a USER label (WI-790), not slot 2's synthetic name.
            let out_of_place: Vec<Symbol> = ["_2", "_1"].iter().map(|n| kb.intern(n)).collect();
            assert!(!TupleComponents::labels_are_positional(&kb, &out_of_place));
            // An empty list is not "positional" — it means the typer resolved nothing.
            assert!(!TupleComponents::labels_are_positional(&kb, &[]));
        }

        /// Two labels that collide land on the SAME index, which is what lets
        /// `match_tuple_pattern` refuse a double cover.
        #[test]
        fn colliding_labels_report_the_same_index() {
            let mut kb = KnowledgeBase::new();
            let t = named_tuple(&mut kb, &[("a", 1), ("b", 2)]);
            let c = t.tuple_components().expect("tuple");
            assert_eq!(c.by_label_index(&kb, "a"), c.by_label_index(&kb, "ns.a"));
            assert_ne!(c.by_label_index(&kb, "a"), c.by_label_index(&kb, "b"));
        }
    }
}
