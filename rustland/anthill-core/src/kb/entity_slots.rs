//! **THE DECLARED-FIELD SLOTS AN ENTITY TERM PRESENTS** — completed, ordered, and on
//! whatever carrier the writer is building.
//!
//! Every fact and every pattern of one functor must present the SAME named slots in the
//! SAME order, because the discrimination tree matches structurally: a fact stored as
//! `W(id: 1, name: "a")` and a pattern written `W(id: 1)` do not meet unless the pattern
//! is completed to `W(id: 1, name: ?name)` first. That completion is what this module
//! owns, and it is the whole of what it owns — it is not about queries, and it is not
//! about §8.3 (which is one CALLER of it).
//!
//! ## Two positions, one filler
//!
//! WI-716: the FILL depends on VALUE vs PATTERN position. In a value position (a fact
//! head, an entity-deriving rule head) an absent OPTIONAL field means `none()`, not a
//! var: a var makes the produced entity `forall v. E(field: v)`, which unsoundly unifies
//! a `some(?)` query. In a query/rule-body PATTERN (and for an absent REQUIRED field)
//! the var-fill stays — "matches anything". A `none()` value still unifies a pattern's
//! var (so `E(id: ?)` finds it) but correctly fails `field: some(?)`.
//!
//! WI-20260902-CZJ2N made the filler a FREE function so the sites that expand a bare
//! entity name share ONE of it. Two spellings of §8.3's all-fields-fresh pattern must
//! not have two fillers.
//!
//! ## Two carriers, one filler
//!
//! WI-20260904-J0RM4 made it carrier-parametric, which is what let the QUERY converter
//! join the same filler instead of carrying a fourth hand-rolled copy of the fill-and-
//! sort loop. The asymmetry that makes two carriers right:
//!
//!  * a pattern written in SOURCE — a rule body, or a `Term`-typed field like
//!    `FactHolds(pattern: E(id: ?x))` — is PERSISTENT, and hash-consing it is exactly
//!    what the interner is for ([`Interned`]);
//!  * a pattern built at RUNTIME for one query is TRANSIENT, and interning it leaks: the
//!    `TermStore` is monotone under a scoped-KB layer by design (WI-SPGBP), so nothing
//!    reclaims it ([`Occurrence`]).
//!
//! The carrier decides only how a FILL is minted. The field census, the value/pattern
//! rule and the canonical ORDER are carrier-blind and are written once, here.
//!
//! Naming, since the old names said neither of those things: this was
//! `fill_entity_named_args` and `expand_bare_entity_pattern` inside the 28k-line
//! `kb::load`. The first named its mechanism rather than its purpose; the second said
//! "pattern" while serving the VALUE position through `Loader::expand_bare_entity_subject`
//! — which is the position whose `none()` fill it exists to get right.

use smallvec::SmallVec;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::intern::Symbol;
use crate::kb::node_occurrence::{empty_span, Expr, NodeOccurrence};
use crate::kb::term::{Term, TermId, Var};
use crate::kb::KnowledgeBase;

/// The carrier a completed slot list is built on. The two implementations differ in
/// ONE respect — whether a minted fill enters the hash-consed `TermStore` — and the
/// module doc says why that difference is the right one to parametrize over.
pub(crate) trait SlotCarrier {
    /// What sits in a slot.
    type Node;

    /// WI-716's `none()` fill for an absent OPTIONAL field in a value position.
    fn none(kb: &mut KnowledgeBase) -> Self::Node;

    /// The "matches anything" fill: a fresh logic variable displaying as `field`.
    ///
    /// `KnowledgeBase::fresh_var` on BOTH carriers, and deliberately. The var id is the
    /// KB's global numbering and a transient pattern's variables must be distinct from
    /// every variable the resolver will open, or two unrelated bindings collide. What
    /// the transient carrier avoids is the `kb.alloc` that would put the resulting VAR
    /// TERM — and every `Fn` node above it, whose identity depends on it — in the store
    /// for the KB's lifetime.
    fn fresh_var(kb: &mut KnowledgeBase, field: Symbol) -> Self::Node;
}

/// The PERSISTENT carrier: hash-consed `TermId`s. What the loader builds, for content
/// that lives as long as the KB does.
pub(crate) struct Interned;

impl SlotCarrier for Interned {
    type Node = TermId;

    fn none(kb: &mut KnowledgeBase) -> TermId {
        let none_sym = kb.resolve_symbol("anthill.prelude.Option.none");
        kb.alloc(Term::Fn {
            functor: none_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        })
    }

    fn fresh_var(kb: &mut KnowledgeBase, field: Symbol) -> TermId {
        let fresh = kb.fresh_var(field);
        kb.alloc(Term::Var(Var::Global(fresh)))
    }
}

/// The TRANSIENT carrier: `Rc<NodeOccurrence>` expression nodes, which the
/// discrimination tree and the resolver read through `TermView` exactly as they read
/// their hash-consed twins (`occ_head`'s `Expr::Apply` / `Expr::Ref` / `Expr::Var` arms
/// all route through the same `functor_view_head` / `ViewHead` constructors). Nothing
/// built here enters the `TermStore`.
pub(crate) struct Occurrence;

impl SlotCarrier for Occurrence {
    type Node = Rc<NodeOccurrence>;

    /// **A LOUD REFUSAL, NOT A BODY.** Nothing reaches it: the only transient-carrier
    /// caller is the QUERY converter, which passes `value_position: false` — a query
    /// asks "any account", so WI-716's `none()` fill would narrow it to the facts whose
    /// optional happens to be absent — and `complete_named_slots` computes
    /// `optional_fields` only in a value position, so `C::none` is never called on this
    /// carrier.
    ///
    /// WRITTEN AS A PANIC RATHER THAN AS THE OBVIOUS ONE-LINER, on `/code-review`'s
    /// finding: the obvious body is `expr_node(Expr::Ref(none_sym))`, whose agreement
    /// with the interned twin (`kb.alloc(Fn{none,[],[]})`, folded to `Ref(none)` by
    /// `nullary_canon` because `none` is a sort-nested constructor and carries no
    /// `SymbolKind::Sort`) rests on a chain of reasoning that NOTHING DRIVES. An
    /// undriven body a future caller trusts is worse than a refusal that tells them what
    /// to write and to test. The first transient producer in a VALUE position replaces
    /// this line and brings a row that fires it.
    fn none(_kb: &mut KnowledgeBase) -> Rc<NodeOccurrence> {
        unreachable!(
            "entity_slots::Occurrence::none — the transient carrier has no value-position \
             producer, so WI-716's `none()` fill cannot be reached on it. Adding one means \
             writing this body (`Expr::Ref(Option.none)`, the shape `nullary_canon` folds \
             the interned twin to) AND a test that drives it.",
        )
    }

    fn fresh_var(kb: &mut KnowledgeBase, field: Symbol) -> Rc<NodeOccurrence> {
        let fresh = kb.fresh_var(field);
        expr_node(Expr::Var(Var::Global(fresh)))
    }
}

/// A transient `Expr` occurrence node.
///
/// UNSPANNED, and that is not a loss being papered over. A query pattern is not written
/// in any registered source — `--pattern '<text>'` IS the location, which is why every
/// diagnostic about one is unlocated on purpose (`report_ambiguous_query_dispatch`) —
/// and `materialize_from_handle` gives the same zero span to every node it builds from a
/// term the loader never spanned. Owner is `None` for the same reason: a query belongs
/// to no declaration.
pub(crate) fn expr_node(expr: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(expr, empty_span(), None)
}

/// **COMPLETE `named` TO THE FUNCTOR'S FULL DECLARED FIELD LIST, IN DECLARED ORDER.**
///
/// Positional args also count as "provided" — `ToolPasses("x")` covers `tool` via
/// `pos_args[0]`, so it isn't re-stuffed with a fresh var that would shadow the
/// positional at materialization time. A functor with no declared field schema is left
/// entirely alone — neither filled nor sorted — because there is no declared order to
/// sort into and `named` is then already whatever its producer canonicalized it to.
///
/// `value_position` selects WI-716's fill rule; see the module doc.
pub(crate) fn complete_named_slots<C: SlotCarrier>(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_len: usize,
    value_position: bool,
    named: &mut SmallVec<[(Symbol, C::Node); 2]>,
) {
    let Some(all_fields) = kb.entity_field_names(functor) else {
        return;
    };
    let all_fields = all_fields.to_vec(); // borrow-safe copy

    // Field symbols whose declared type is `Option[..]` — computed only in a value
    // position; patterns keep the uniform var-fill.
    let optional_fields: HashSet<Symbol> = if value_position {
        let fts: Vec<(Symbol, crate::eval::value::Value)> = kb
            .entity_field_types(functor)
            .map(|s| s.to_vec())
            .unwrap_or_default();
        fts.iter()
            .filter(|(_, ty)| crate::kb::typing::is_option_type(&*kb, ty))
            .map(|(s, _)| *s)
            .collect()
    } else {
        HashSet::new()
    };
    if named.len() + pos_len < all_fields.len() {
        let mut provided: HashSet<Symbol> = named.iter().map(|(s, _)| *s).collect();
        for (i, &field_sym) in all_fields.iter().enumerate() {
            if i < pos_len {
                provided.insert(field_sym);
            }
        }
        for &field_sym in &all_fields {
            if !provided.contains(&field_sym) {
                let fill = if optional_fields.contains(&field_sym) {
                    C::none(kb)
                } else {
                    C::fresh_var(kb, field_sym)
                };
                named.push((field_sym, fill));
            }
        }
    }
    let order: HashMap<Symbol, usize> = all_fields
        .iter()
        .enumerate()
        .map(|(i, &s)| (s, i))
        .collect();
    named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
}

/// **§8.3'S EXPANSION OF A BARE ENTITY NAME IN A LOGICAL POSITION** (WI-20260902-CZJ2N):
/// `fact account` IS `fact account()`, the all-fields-fresh pattern. `None` when
/// `functor` is not a registered entity, so a caller keeps its own reading of the name.
///
/// §8.3 already says the expansion applies "whenever the functor is a registered
/// entity", and one level up the spec already reads a bare SPEC name that way — `fact
/// Monoid` IS `fact Monoid[?]` (`unwrap_spec_view` takes a bare `Ref` as no-bindings).
/// F2 makes the VALUE level match. Before this, `fact account` asserted a phantom
/// `account/0` atom that `:- account()` could not see and no other spelling reached
/// either.
///
/// AT THE LOGICAL-POSITION ENTRY POINTS, NOT IN `convert_term_inner`. That arm serves
/// DATA slots too, where `Ref(WorkItem)` must stay the sort-as-value (`facts_of(kb(),
/// WorkItem)`, `typing::check_bare_ref`'s free-standing-entity arm), and `expected: None`
/// cannot tell a goal from a data slot of unknown type. `Loader::convert_subject_term`
/// is the funnel for four of the five positions (rule head, fact head, sort-body
/// pre-scan, proof step); `load::convert_query_term` and the rule-body GOAL arm of
/// `build_body_atom_occurrence_inner` are the other two, and each reaches this.
///
/// WI-20260902-VNWAW: that GOAL arm reaches it down TWO paths, because a dotted
/// paren-less citation is collapsed to its symbol in a branch of its own (719FJ) and so
/// never touches the one-segment `Term::Ref` / `Term::Ident` arms. It called this on the
/// one-segment path only, so `:- ns.account` answered nothing where `:- account`
/// answered — and `not` of it succeeded. The other four positions were never split this
/// way: their dotted branch already funnels back through the same call.
///
/// `value_position` is a PARAMETER rather than a loader field, which is what lets the
/// query pattern say "no" explicitly: a query asks "any account", and filling an absent
/// OPTIONAL with `none()` there would find only the facts whose optional is absent.
///
/// BEFORE INDEXING, necessarily: `Ref(account)` and `account(?, ?)` key differently in
/// the discrimination tree, so a unification-time expansion could not do it.
pub(crate) fn bare_entity_slots<C: SlotCarrier>(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    value_position: bool,
) -> Option<SmallVec<[(Symbol, C::Node); 2]>> {
    kb.entity_field_names(functor)?;
    let mut named: SmallVec<[(Symbol, C::Node); 2]> = SmallVec::new();
    complete_named_slots::<C>(kb, functor, 0, value_position, &mut named);
    Some(named)
}

/// [`bare_entity_slots`] on the INTERNED carrier, applied to a term.
///
/// IDEMPOTENT, which is what lets it sit at a funnel rather than at a branch: a 0-field
/// sort-nested constructor re-canonicalizes to the same `Ref` it arrived as, and an
/// already-applied term is not a `Term::Ref` and is returned untouched.
pub(crate) fn expand_bare_entity_term(
    kb: &mut KnowledgeBase,
    tid: TermId,
    value_position: bool,
) -> TermId {
    let Term::Ref(e) = *kb.get_term(tid) else {
        return tid;
    };
    let Some(named) = bare_entity_slots::<Interned>(kb, e, value_position) else {
        return tid;
    };
    kb.make_entity_term(e, SmallVec::new(), named)
}
