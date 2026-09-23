//! Dispatch diagnostics and arbitration: bare member calls, instance and supplier ties,
//! and the dot-member dispatch decision.

use super::*;

/// WI-866 — which SPEC a dictionary reached through a call to `op_sym` is laid out
/// against ([`DictLayout`]'s spec half), as a decision rather than a fallback.
///
/// The two readers ([`Interpreter::expand_dispatching_dict`] at the frame push and
/// [`dictionary_covers_target`]'s caller) each wrote this as
/// `impl_parent_of_op(op).unwrap_or(provider)`, whose `unwrap_or` conflated three
/// unrelated answers into one. MEASURED, `wi866_dispatch_spec_of_op_answers_by_shape`:
///
///  * a SORT MEMBER (`anthill.prelude.Ord.compare`) — the sort IS the spec, and for a
///    WI-415 parent-bundle dict it is also the provider, which the layout's one-list
///    rule already handles. [`Self::Spec`].
///  * a TOP-LEVEL operation — its canonical name is DOT-LESS (`operation topLevel(…)`
///    at a file's top level gets qn `"topLevel"`), so the `rsplit_once('.')` fails.
///    This is the case the `unwrap_or` actually served, and it names no spec.
///  * a NAMESPACE-LEVEL operation — `impl_parent_of_op` answers `Some(namespace)`, so
///    it NEVER REACHED the `unwrap_or` at all, though the comment there claimed it as
///    the case it covered. It named a namespace as a spec: harmless arithmetically (a
///    namespace declares no `requires`, so the half counts 0 and every slice lands
///    where the one-list reading puts it) and wrong in every diagnostic, which
///    rendered `for spec `some.namespace`'s requires chain`. [`Self::NoSpec`].
///
///  * a DOTTED name whose parent segment resolves to NOTHING —
///    [`Self::UnresolvableParent`]. The ticket expected this to be an inconsistent KB
///    and both readers to raise on it. MEASURED, IT IS NOT: it is the WI-234 Model 1
///    dispatch form, where a synthetic spec-op-like symbol
///    (`test.wi223.dispatch_form.Spec.foo`, whose `Spec` is deliberately never
///    registered) names the SHORT op and the dispatching dict's functor selects the
///    impl. Raising here failed
///    `wi223 apply_within_with_requirement_dispatch_resolves_via_handle_functor`,
///    which is the only thing that distinguishes it from a corrupt KB — nothing at
///    this call can. So it takes the spec-less reading too, and what catches a
///    genuinely wrong one is downstream and already loud: a spec that really did
///    contribute a half makes the dictionary LONGER than the one-list layout counts
///    (`expand_dispatching_dict`'s arity raise), and a frame owner the layout says
///    nothing about is its `slots_for` raise.
///
/// So all three spec-less arms reach the same reading. What changes is that each is
/// now REACHED FOR A STATED REASON, and that a namespace has stopped being named as a
/// spec in the diagnostic a reader gets when those raises fire.
#[derive(Clone, Copy, Debug)]
pub enum DispatchSpec {
    /// `op_sym` is declared by a sort: that sort owns the dictionary's spec half.
    Spec(Symbol),
    /// `op_sym` names no spec — a top-level or namespace-level operation. The
    /// dictionary is the provider's own bundle alone (the layout's one-list rule,
    /// reached by passing the provider as the spec).
    NoSpec,
    /// `op_sym`'s canonical name is dotted but its parent segment is not a registered
    /// symbol — the WI-234 Model 1 form, where the dispatching dict's functor picks
    /// the impl and the synthetic `Spec.foo` name carries only the short name. Spec-
    /// less like [`Self::NoSpec`], and kept apart from it because the REASON differs
    /// and only one of the two is a shape a source file can write.
    UnresolvableParent,
}

impl DispatchSpec {
    /// WI-866 — the symbol to lay the dictionary out against, given the `provider` it
    /// names: the spec where there is one, and the provider itself where there is not
    /// (the layout's one-list rule, [`DictLayout`]).
    ///
    /// ONE OWNER FOR THE COLLAPSE, because the two readers must not come to disagree
    /// about it — [`Interpreter::expand_dispatching_dict`] at the frame push and
    /// [`dictionary_covers_target`]'s caller ask the same question one call apart, and
    /// they each spelled the pre-WI-866 `unwrap_or` for themselves. The `match` is
    /// exhaustive on purpose: a fifth name shape would stop compiling HERE, which is
    /// where the decision belongs, rather than inheriting an arm at two call sites.
    pub fn or_provider(self, provider: Symbol) -> Symbol {
        match self {
            DispatchSpec::Spec(s) => s,
            DispatchSpec::NoSpec | DispatchSpec::UnresolvableParent => provider,
        }
    }
}

/// [`DispatchSpec`] for `op_sym` — see there for the four shapes and what each means.
/// THROUGH [`impl_parent_of_op`], which is THE one reader of "which symbol declares
/// this operation" and says so at length in its own doc — a second `rsplit_once('.')
/// + try_resolve_symbol` here would be that split spelled twice, and the day the one
/// owner changes (its doc weighs exactly such a change) the dictionary's spec would be
/// derived one way at the frame push and another way everywhere else.
///
/// NOT through [`impl_parent_sort_of_op`], which is the same call plus the `Sort`
/// gate: it answers a TWO-valued question (a declaring sort, or nothing) and this one
/// has three answers. Its `None` fuses the namespace parent with the absent one, and
/// the absent one fuses a dot-less name with an unresolvable parent — the very
/// collapse this enum exists to undo. So the gate is applied here, beside the dot
/// test that separates `impl_parent_of_op`'s two ways of answering `None`.
pub fn dispatch_spec_of_op(kb: &KnowledgeBase, op_sym: Symbol) -> DispatchSpec {
    match impl_parent_of_op(kb, op_sym) {
        Some(parent) if kb.has_kind(parent, crate::intern::SymbolKind::Sort) => {
            DispatchSpec::Spec(parent)
        }
        // A NAMESPACE parent: it declares no type params and owns no requirement
        // slots, so it is no more a spec than an absent parent is.
        Some(_) => DispatchSpec::NoSpec,
        // `impl_parent_of_op` answers `None` two ways, and they are not one case: a
        // DOT-LESS canonical name (a `_global` operation — no parent segment at all,
        // so no spec), versus a dotted one whose parent segment resolves to nothing.
        None if kb.qualified_name_of(op_sym).contains('.') => DispatchSpec::UnresolvableParent,
        None => DispatchSpec::NoSpec,
    }
}

/// WI-565: the sorts that declare a MEMBER operation whose SHORT name equals that
/// of the bare, out-of-scope apply functor `fn_sym`. Called only on the Path-3
/// failure edge (`fn_sym` did not resolve to a known free operation): a non-empty
/// result turns the terse `UnknownApplyFunctor` into the scoping hint
/// [`TypeError::BareMemberCall`]. A member's bare name is in scope only within its
/// defining sort; from outside it must be qualified (`Sort.member(…)`) or
/// dot-dispatched (`receiver.member(…)`). The scan walks every registered
/// qualified name (an error-path cost only), keeping a member whose parent
/// resolves to a `Sort`. Deduped by the parent sort's qualified name and sorted by
/// it, so the diagnostic is deterministic across the `by_qualified_name` HashMap's
/// iteration order.
///
/// WI-898 widened "member" from an OPERATION to an operation OR an equation functor,
/// and split off `dot_dispatchable` because the two do not answer the same remedies.
pub(super) fn member_owning_sorts_for_bare(
    kb: &KnowledgeBase,
    fn_sym: Symbol,
) -> BareMemberCandidates {
    let short = kb.local_name_of(fn_sym).to_string();
    // Keyed by the owning sort's qualified name: dedups interned copies and yields
    // the sorts in a deterministic (qualified-name) order via `into_values`.
    let mut by_qn: std::collections::BTreeMap<String, Symbol> = std::collections::BTreeMap::new();
    let mut dot_dispatchable = true;
    for (qn, &sym) in kb.symbols.by_qualified_name.iter() {
        // WI-898: an EQUATION-INTRODUCED functor is a member too — `ite` is `Bool`'s,
        // written as two `@[simp]` clauses instead of an `operation` — and this hint
        // exists for exactly the confusion it causes. It could not be seen while the
        // kind was `Goal`, since a `Goal` is a relation and naming a relation's sort
        // would be nonsense.
        // `has_kind` per role, not `kind_of`: one name can play both (WI-925), and a
        // member that is an operation AND an equation functor must be found as either.
        let is_op = kb.has_kind(sym, crate::intern::SymbolKind::Operation);
        if !is_op && !kb.has_kind(sym, crate::intern::SymbolKind::EquationFunctor) {
            continue;
        }
        let Some((parent_qn, last)) = qn.rsplit_once('.') else {
            continue;
        };
        if last != short {
            continue;
        }
        let Some(parent_sym) = kb.try_resolve_symbol(parent_qn) else {
            continue;
        };
        // `has_kind` here for the same reason as the `is_op` test just above, and
        // WI-956 makes it the same reason at both ends: a §6.3 sort whose ENTITY role
        // registered first still declares members, and dropping it here drops the sort
        // this diagnostic exists to NAME — the author is told nothing owns the member.
        if !kb.has_kind(parent_sym, crate::intern::SymbolKind::Sort) {
            continue;
        }
        // Only an OPERATION answers `receiver.member(…)`: dot dispatch selects a
        // member operation by the receiver's carrier, and an equation functor is not
        // one. Offering that half of the remedy for an equation-only member would
        // send the author to a spelling that fails the same way.
        //
        // ALL, not ANY. The message names the owning sorts JOINTLY, so one remedy has
        // to hold for every one of them: with `any`, a name that is an operation on
        // `A` and an equation functor on `B` still advertised `receiver.foo(…)`, and
        // an author holding a `B` followed it into the same failure — the outcome this
        // flag exists to rule out, reintroduced at multi-sort granularity.
        dot_dispatchable &= is_op;
        by_qn.entry(parent_qn.to_string()).or_insert(parent_sym);
    }
    BareMemberCandidates {
        sorts: by_qn.into_values().collect(),
        dot_dispatchable,
    }
}

/// [`member_owning_sorts_for_bare`]'s answer: the owning sorts, plus whether the
/// receiver spelling is one of the remedies (WI-898 — see the `dot_dispatchable`
/// assignment for why an equation functor does not earn it).
pub(super) struct BareMemberCandidates {
    pub(super) sorts: SmallVec<[Symbol; 2]>,
    pub(super) dot_dispatchable: bool,
}

/// WI-565: the one message body for a bare out-of-scope member-op call, shared by
/// [`TypeError::format`] and [`crate::kb::load::LoadError`]'s renderings so the wording
/// cannot drift. `member` is the bare short name; `owning_sorts` are the owning
/// sorts' short names (already deduped + sorted). Names the sort(s) and the qualified
/// remedy `Sort.member(…)`, plus the dot remedy `receiver.member(…)` when
/// `dot_dispatchable` (WI-898 — an equation functor answers only the first).
pub(crate) fn bare_member_call_message(
    member: &str,
    owning_sorts: &[String],
    dot_dispatchable: bool,
) -> String {
    let (noun, sorts, exemplar) = match owning_sorts {
        [one] => ("sort".to_string(), one.clone(), one.clone()),
        many => ("sorts".to_string(), many.join(", "), "<Sort>".to_string()),
    };
    // WI-898: the receiver spelling is offered only where a member OPERATION answers
    // it. An equation functor (`Bool.ite`) is reached by its qualified name alone, so
    // naming `receiver.ite(…)` would be a remedy that fails the same way.
    let receiver = if dot_dispatchable {
        format!(" or via a receiver `receiver.{member}(…)`")
    } else {
        String::new()
    };
    format!(
        "`{member}` is a member of {noun} {sorts}, not in scope as a bare name here; \
         call it qualified as `{exemplar}.{member}(…)`{receiver}"
    )
}

/// WI-898: the one message body for a citation of an equation-introduced functor that
/// did not rewrite, shared by [`TypeError::format`] and [`crate::kb::load::LoadError`]'s two
/// renderings so the wording cannot drift (the discipline
/// [`bare_member_call_message`] set).
///
/// THREE FAILURES, THREE REPAIRS, and the census tells them apart — which is the whole
/// reason the counts are carried rather than the message being one sentence about all
/// of them. Untagged clauses are INERT (`@[simp]` is the enablement, spec §5.3), so the
/// author has to tag them; tagged clauses that did not match are a PATTERN problem, so
/// the author has to look at what the left-hand sides require; and no clause at all is
/// neither. Telling the author every possibility would be the diagnostic asking them
/// to do the diagnosis.
pub(crate) fn unreduced_equation_functor_message(
    functor: &str,
    census: crate::kb::simp_rewrite::ClauseCensus,
) -> String {
    let head = format!(
        "`{functor}` is defined by equations, not declared as an operation, so a citation \
         of it is answered by REWRITING before dispatch — and this one did not rewrite"
    );
    if census.defining == 0 {
        // Its own sentence rather than a "none of its 0 equations" nonsense — and
        // deliberately WITHOUT a cause. A `retract` (WI-666) can leave the scoped
        // symbol standing with no live clause, but so can an LHS whose stored shape
        // the census cannot key on, and the census establishes neither. Say what was
        // observed; guessing why would send the author looking in the wrong place.
        format!(
            "{head}: no defining equation for it can be found, so there is nothing to \
             rewrite with and no operation to dispatch to"
        )
    } else if census.simp_tagged == 0 {
        format!(
            "{head}: none of its {} defining equation(s) is tagged `@[simp]`, and an \
             untagged equation never fires (spec §5.3 — `@[simp]` is the enablement, not \
             the direction). Tag the defining equation `@[simp]`, or declare `{functor}` \
             as an `operation`",
            census.defining,
        )
    } else {
        // NAMES THE CANDIDATES, ASSERTS NONE. The census knows the tag; it does NOT
        // know why a tagged clause declined, and `try_fire` has three distinct
        // declines — the left-hand pattern not matching, a typed pattern bound the
        // typer refuses to fire unguarded (WI-582), and the type-directed guard
        // (WI-655). An earlier cut asserted the first of the three, which would have
        // sent an author whose clause was skipped for its bound to inspect patterns
        // that were fine.
        format!(
            "{head}: none of its {} `@[simp]` clause(s) fired here. A clause fires only \
             where its left-hand pattern matches STRUCTURALLY (a COMPUTED argument never \
             matches a pattern that writes a literal); the typer additionally declines \
             one carrying a typed pattern bound (`?x: T`) and one its type-directed \
             guard rejects. There is no operation to dispatch to",
            census.simp_tagged,
        )
    }
}

/// WI-843 (058 §4.1 tier 3) — the tie a use site must resolve: which spec's
/// providers tied, which they were, and whether a bracket at this call can reach
/// them at all.
///
/// Carried by SYMBOL and stamped WHERE THE TIE WAS OBSERVED. Both halves are
/// load-bearing, and the first cut got both wrong:
///
///   * `spec` was filled in by [`resolve_at_goal`] from the DISPATCHED goal, two
///     frames later. But `resolve_inner` propagates a SUB-goal's tie verbatim, so a
///     conditional witness whose `:-` subgoal tied was reported against the OUTER
///     spec — naming providers of a different spec and advising a bracket the very
///     next compile refuses (MEASURED: `[Pretty = ShowA]` → *"ShowA does not provide
///     Pretty"*). A level's description belongs to that level; `goal_text` was
///     already per-level, which is what made the mismatch visible.
///   * `candidates` was a pre-rendered `Vec<String>` beside a concreteness verdict
///     computed IN THE RESOLVER, which meant a whole-KB `SortInfo` scan on paths that
///     then discard it (MEASURED: 5 of 19 calls, via `req_insertion`'s
///     `require_complete = false` dep loop, which has no memo). Symbols are free to
///     carry; the scan belongs at the one place a message is emitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceTie {
    /// The spec whose providers tied — the goal the tie was observed AT.
    pub spec: Symbol,
    /// The providers that tied, in candidate order.
    pub candidates: SmallVec<[Symbol; 2]>,
    /// True when the tie is at the CALL'S OWN goal — `resolve_inner`'s
    /// `stack.is_empty()`, the same test WI-841's step 0 uses to decide that a
    /// selection reaches this goal and no sub-goal (§4.5). When false, NO bracket at
    /// this call can steer the tie whatever the candidates are, because a key
    /// deliberately does not reach sub-resolutions.
    pub at_call_goal: bool,
    /// WI-456 — which NAMED slot of which provider this sub-goal was filling, when it
    /// was filling one. `None` at a call's own goal, and at a sub-goal that fills a
    /// provision CONDITION (§4's `:- goals` tail admits no binder) or an ANONYMOUS
    /// `requires`.
    ///
    /// It does NOT re-attribute the tie — `spec` and `candidates` stay the sub-goal's
    /// own, which is the mis-attribution 058 §8 fixed. It adds the one fact the repair
    /// needs and only the level that owns the slot knows: `TieRepair::SubGoal` can say
    /// *bind `OA` of `LexFst`* instead of telling an author to add a named slot to a
    /// provider that already has two.
    pub slot: Option<TieSlot>,
}

/// WI-456 — a named requirement slot, as a tie names it. See [`InstanceTie::slot`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TieSlot {
    /// The provider whose slot it is (`LexFst`).
    pub owner: Symbol,
    /// The slot's binder (`OA`).
    pub binder: Symbol,
}

/// WI-843 — what the author can actually DO about a tie. A typed answer rather than
/// an emergent one: every way of reaching this diagnostic must say which of the three
/// it is, so a new one cannot quietly inherit "offer the bracket".
///
/// Each arm was DRIVEN to its refusal before being given a message; advertising a
/// repair that the next compile rejects is the failure mode this enum exists to make
/// impossible to reintroduce.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TieRepair {
    /// Write this bracket in the call's list — rendered ready to print
    /// (`[Monoid = ns.AddM]`). The key is the spec's SHORT name: a key is a bare
    /// label and a QUALIFIED one is refused rather than resolved (§4.2), so echoing
    /// the qualified spec would print advice that does not load.
    Bracket(String),
    /// Every candidate is a CONCRETE provider, where §4.4 check 3 refuses an explicit
    /// witness because the VALUE decides — and a call that reached here has no value
    /// that does. MEASURED on `wi822_op_scoped_supply_test`'s receiver-less
    /// `Zeroable.zero()`: `[Zeroable = Pebble]` there is
    /// *"an explicit `[Zeroable = Pebble]` cannot change it"*.
    ValueDirected,
    /// The tie is at a SUB-GOAL of the resolution, where §4.5 step 0 deliberately
    /// keeps a bracket key out (a key's candidate set is the CALLEE's slots, and
    /// extending it into the resolution tree would make key resolution depend on
    /// which witness was pinned). MEASURED: naming the outer spec is
    /// *"W does not provide Outer"* and naming the inner one is
    /// *"unknown type-param"* — so neither spelling exists, and §4.2's answer is for
    /// the witness to declare a NAMED slot the caller binds in the key's value
    /// position (`fold[Monoid = ListM[O = MyEq]]`).
    ///
    /// WI-456 — the payload is that slot, WHEN THE PROVIDER ALREADY HAS ONE. Without it
    /// this arm told an author to "give the conditional provider a NAMED requirement
    /// slot" in front of a `LexFst` that declares two, leaving them to guess the name
    /// and the spelling; with it the message names both. `None` is the honest answer for
    /// the shape that has no binder to name — an ANONYMOUS `requires`, conditional or
    /// not, and a provision CONDITION, whose `:- goals` tail admits no name at all (§4)
    /// — where declaring a named slot really is the first step. Its own driver
    /// (`a_tie_below_a_named_slot_is_not_attributed_to_that_slot`) fires it for an
    /// UNCONDITIONAL `requires Marked[T = Tok]`, which is why the wording may not say
    /// "the conditional provider".
    SubGoal(Option<SubGoalSlot>),
    /// WI-1032 — every candidate is the SAME provider, reached through two provisions
    /// that are not identical. A bracket names a PROVIDER, so no spelling separates them;
    /// and the repair is not "keep one" either, because the provisions may agree (one
    /// binding `A`, another `B`, merged by `provider_spec_view_bindings` into one view).
    /// What the author has to do is make them ONE provision.
    ///
    /// DRIVEN by `wi1032_provision_dedup_test::one_carrier_two_disagreeing_provisions_
    /// names_it_once`. Before it existed this rendered as [`Self::ValueDirected`] and
    /// printed the carrier TWICE — advising a pin on a carrier that is already pinned.
    OneProviderTwoProvisions,
}

/// WI-456 — [`TieRepair::SubGoal`]'s payload, rendered: the provider whose named slot
/// the tied sub-goal fills, and the slot's binder. Strings rather than `Symbol`s because
/// [`TieRepair`] is what crosses into `LoadError` and `TypeError`, which render without
/// a `KnowledgeBase` in hand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubGoalSlot {
    /// The provider, qualified (`my.ns.LexFst`).
    pub owner: String,
    /// The binder, as written (`OA`).
    pub binder: String,
}

/// WI-1032 — a tie's candidates as names, BY CANONICAL PROVIDER rather than one entry
/// per candidate. Two provisions of one carrier are two candidates whenever they are not
/// byte-identical (the collector's dedup is structural), and rendering them per candidate
/// printed the carrier TWICE. Deduping cannot hide a rival: two distinct providers have
/// distinct canonical symbols and both survive.
///
/// WI-456 gave it a second caller — [`describe_resolution_failure`], which was rendering
/// `tie.candidates` raw and so printed the `(Leaf, Leaf)` this fixed on the other face.
pub(super) fn tie_candidate_names(kb: &KnowledgeBase, tie: &InstanceTie) -> Vec<String> {
    let mut candidates: Vec<String> = Vec::with_capacity(tie.candidates.len());
    let mut seen: SmallVec<[Symbol; 2]> = SmallVec::new();
    for s in &tie.candidates {
        let canon = kb.canonical_sort_sym(*s);
        if !seen.contains(&canon) {
            seen.push(canon);
            candidates.push(kb.qualified_name_of(*s).to_string());
        }
    }
    candidates
}

/// WI-843 — §4.4 check 3's criterion, with ONE owner: is `sort` a provider whose
/// dispatch the VALUE already decides?
///
/// [`validate_instance_selection`] refuses a selection on one; [`tie_repair`] must
/// therefore not advertise one. Sharing the `concrete` SET is not enough to keep those
/// two agreeing — the drift channel is the TEST, and the raw-plus-canonical probe is
/// the test. (`check_provider_operations`' exemption spells `contains(raw)` only; that
/// is pre-existing, and widening it would newly exempt groups, so it is left as found
/// rather than folded in here.)
pub(super) fn is_value_directed_provider(
    kb: &KnowledgeBase,
    concrete: &std::collections::HashSet<Symbol>,
    sort: Symbol,
) -> bool {
    concrete.contains(&sort) || concrete.contains(&kb.canonical_sort_sym(sort))
}

/// WI-843 — render a tie for a diagnostic: its candidates, and the one repair that
/// actually applies. The `sorts_with_constructors` scan lives HERE, at the render
/// boundary, so the resolver pays nothing for ties whose result is discarded.
///
/// WI-1032 — IT DOES NOT DEDUP THE NAMES, and that is a decision with a measurement
/// behind it rather than an omission. This did once print one carrier twice
/// (`2 instances provide Desc (Leaf, Leaf)`), because two provisions saying the same
/// thing reached `pick_most_specific` as two candidates. That was fixed at the COLLECTOR
/// — equal candidates are one candidate — not here, since the duplicate name was the
/// symptom and a program with a single implementation being refused was the defect.
/// The one remaining way two candidates could share an `impl_sort` is differing in a
/// TYPE-param binding, and that does not tie: the ground binding raises
/// `head_specificity` and tier 2 picks it (MEASURED, in
/// `wi1032_provision_dedup_test::a_specificity_ordered_pair_still_takes_the_more_specific`).
/// With no driver left, a dedup here would be untested code.
pub(super) fn render_instance_tie(
    kb: &KnowledgeBase,
    tie: &InstanceTie,
) -> (Vec<String>, TieRepair) {
    let candidates = tie_candidate_names(kb, tie);
    if !tie.at_call_goal {
        // WI-456 — the slot rides from the frame that owns it ([`InstanceTie::slot`]).
        return (
            candidates,
            TieRepair::SubGoal(tie.slot.map(|s| SubGoalSlot {
                owner: kb.qualified_name_of(s.owner).to_string(),
                binder: kb.local_name_of(s.binder).to_string(),
            })),
        );
    }
    // ONE provider reached twice: no bracket separates a provider from itself, and
    // `ValueDirected`'s "pin the carrier" is advice for a carrier that is already pinned.
    if candidates.len() == 1 {
        return (candidates, TieRepair::OneProviderTwoProvisions);
    }
    let concrete = crate::kb::load::sorts_with_constructors(kb);
    let repair = match tie
        .candidates
        .iter()
        .position(|s| !is_value_directed_provider(kb, &concrete, *s))
    {
        Some(i) => TieRepair::Bracket(format!(
            "[{} = {}]",
            short_name_of(kb.qualified_name_of(tie.spec)),
            candidates[i],
        )),
        None => TieRepair::ValueDirected,
    };
    (candidates, repair)
}

/// WI-843 — the one message body for a dispatch that several instances answer and
/// the call selects none (058 §4.1 tier 3), shared by [`TypeError::format`] and
/// [`crate::kb::load::LoadError`]'s two renderings so the wording cannot drift (the
/// [`bare_member_call_message`] discipline).
///
/// It names each candidate AND the repair, because this refusal REPLACED one that
/// pointed at the declarations: telling an author that two instances exist is no
/// longer news — the news is that this call has to choose, and how. When no bracket
/// applies, [`TieRepair`] says which reason, and the message says that instead of
/// suggesting a spelling that would be refused.
pub(crate) fn unselected_instance_message(
    op: &str,
    spec: &str,
    candidates: &[String],
    repair: &TieRepair,
) -> String {
    // WI-1032: `candidates` is per PROVIDER (deduped at `render_instance_tie`), so the
    // count says how many distinct providers — never one provider named twice.
    let head = format!(
        "ambiguous dispatch of `{op}`: {} instances provide `{spec}` ({}) and the call \
         selects none",
        candidates.len(),
        candidates.join(", "),
    );
    format!("{head}{}", tie_repair_advice(spec, repair))
}

/// WI-456 — the REPAIR half of a tie's message, with one owner.
///
/// Split out of [`unselected_instance_message`] because a tie reaches an author by two
/// routes and only one of them was saying what to do. The other is
/// [`describe_resolution_failure`]'s `Ambiguous` arm — a requirement that could not be
/// supplied for a call, which rendered the candidates and dropped [`TieRepair`] on the
/// floor, so the sentence the author then read was the generic *"select a witness that
/// provides this requirement at these bindings, or drop the selection"*. MEASURED on
/// `SortedSet[T = Duo[…], O = LexFst]`: the witness DOES provide at those bindings and
/// dropping the selection loses the ordering, while the repair that works — binding
/// `LexFst`'s own `OA` in the type — went unmentioned. That is the two-checks-disagree
/// defect WI-456's 2026-08-15 note caught between §4.5 and the explicit-witness check,
/// one level down, and the [`TieRepair`] discipline ("every way of reaching this
/// diagnostic must say which of the arms it is") is only enforceable if every way of
/// reaching it goes through this function.
///
/// "EVERY WAY" MEANS EVERY LOAD-TIME WAY, and the exception is named rather than
/// implied: [`BridgeRequirements::Ambiguous`] → `EvalError::AmbiguousRequirement` is a
/// THIRD face of the same tie, and it does not read this sentence. That is not an
/// oversight left to tidy — it is the RUNTIME, value-directed route, where §4.2 leaves
/// rule bodies out of selection and there is genuinely no bracket to write, so its
/// repair ("route the call through an operation that can write one") is a different
/// one. Giving it the slot's NAME would still help, and that is an increment of its
/// own: the slot would have to ride through `BridgeRequirements` and the wording would
/// be a third arm, on the face WI-456(a) deliberately kept as WI-855's raise.
///
/// The leading separator belongs to the arm — the four read as one sentence with the
/// head and they do not punctuate alike.
pub(super) fn tie_repair_advice(spec: &str, repair: &TieRepair) -> String {
    match repair {
        TieRepair::Bracket(bracket) => format!(
            " — they may coexist, so say which: write `{bracket}` (or another of \
             them) in the call's bracket list"
        ),
        TieRepair::ValueDirected => ", and none can be named here: each is a CONCRETE \
             provider, where an explicit witness is refused because the VALUE decides the \
             dispatch — and this call has no value that does. Pin the carrier through the \
             call's receiver or its expected result type"
            .to_owned(),
        // WI-456 — the two arms differ in whether a binder EXISTS to name, and that is
        // the whole difference: the channel is the same one either way.
        TieRepair::SubGoal(Some(slot)) => format!(
            ". The tie is in a SUB-GOAL of this call's resolution, which no \
             call-site bracket KEY reaches (§4.5) — it fills named slot `{binder}` of \
             `{owner}`, so bind that slot in the VALUE position, as \
             `{owner}[{binder} = …]`: in the call's bracket where the call names the \
             witness itself, or, where it is reached as the value of an enclosing slot, \
             in the type that names it there. Or keep a single provider of `{spec}`",
            binder = slot.binder,
            owner = slot.owner,
        ),
        // The requirement it fills has NO BINDER, so there is no name to print and
        // nothing to bind. That is an anonymous `requires` (conditional or not) or a
        // provision CONDITION, whose `:- goals` tail admits no name at all — saying
        // "the conditional provider" would send an author who wrote a plain
        // `requires Marked[T = Tok]` looking for a condition they never wrote.
        TieRepair::SubGoal(None) => format!(
            ". The tie is in a SUB-GOAL of this call's resolution, which no \
             call-site bracket reaches (§4.5), and the requirement it fills is \
             ANONYMOUS, so there is no slot to bind — give that requirement a NAMED \
             slot on its provider (`requires O: …`) and bind it in the value position \
             (`f[Spec = W[O = Chosen]]`), or keep a single provider of `{spec}`"
        ),
        TieRepair::OneProviderTwoProvisions => format!(
            " — it is ONE provider reached through several provisions of `{spec}` \
             that are not identical. No bracket separates a provider from itself — write \
             the provisions as ONE (a single `provides`/`fact` binding every parameter), \
             since two that merely AGREE still tie here"
        ),
    }
}

/// WI-1012 — whether a supplier tie has a candidate the author could NAME, the typed
/// discriminator [`ambiguous_spec_op_dispatch_message`] branches on. The
/// [`TieRepair`] discipline, one refusal over: "every way of reaching this diagnostic
/// must say which it is, so a new one cannot quietly inherit" the wrong repair — and
/// here the danger runs the other way, inheriting "no bracket helps" for a tie where
/// one does.
///
/// Both arms are DRIVEN: [`Self::KeepOne`] by WI-1012's load and abstract-carrier
/// tests, [`Self::NameableWitness`] by WI-842's `a_two_provider_value_directed_
/// dispatch_names_both_candidates`, which is the only tie shape the corpus drives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SupplierTieRepair {
    /// Nothing here can be named at any site, so deleting a text is the whole repair.
    /// Either the op carries a DEFAULT body — then it has no `Dispatch` requirement
    /// slot ([`callee_requirement_slots`] pushes one only for a body-less spec op), so
    /// no bracket binds anything at any call — or every rival is the carrier's OWN
    /// member or an INSTANCE FACT, and neither has a name (058 §4.3).
    KeepOne,
    /// A body-less spec op with a WITNESS SORT among the rivals. That witness is a
    /// nameable provider distinct from the carrier, and `op[Spec = W](…)` selects it
    /// through the `Dispatch` slot — just not HERE, since a value-directed read is
    /// bracket-less by construction. So routing the call through a site that can write
    /// the bracket is a real second repair, and dropping it (as one shared sentence
    /// did) is the mistake [`crate::kb::load::LoadError::CallTypeArgsNotSupportedHere`]
    /// carries a `position` field to avoid, mirror-imaged.
    NameableWitness,
}

/// WI-1012 — classify a tie for [`ambiguous_spec_op_dispatch_message`]. Asked of the
/// candidates rather than of the call site, so the three construction sites cannot
/// each reason it out and drift: the typer's WI-444 arm is body-less-gated shut and so
/// always answers [`SupplierTieRepair::KeepOne`], but it asks anyway.
pub(crate) fn supplier_tie_repair(
    kb: &KnowledgeBase,
    spec_op: Symbol,
    candidates: &[SpecOpSupplier],
) -> SupplierTieRepair {
    let bracket_dispatchable = lookup_spec_op_dispatch(kb, spec_op).is_some();
    let has_witness = candidates
        .iter()
        .any(|c| matches!(c.route, SupplyRoute::Witness(_)));
    if bracket_dispatchable && has_witness {
        SupplierTieRepair::NameableWitness
    } else {
        SupplierTieRepair::KeepOne
    }
}

/// WI-20260917-NR6FJ DEFECT B — THE CALL IS SILENT ABOUT ITS CARRIER: it has no
/// self-receiver, it classified no carrier param, and the spec op DECLARES no
/// carrier-typed parameter at all. `true` iff NOTHING at this call site — no argument
/// now, no runtime value later — can say which provider it means, so the only thing that
/// can direct it is the enclosing scope's `requires` slot.
///
/// SILENT, NOT MERELY UNPINNED — and the difference between those two readings is a
/// WRONG ANSWER. [`statically_pinned_carrier`] returns `None` for BOTH "this call names
/// no carrier at all" (a nullary op) and "this call HAS a carrier argument whose type is
/// abstract here", and only the first belongs to a slot-directed route. The second is
/// deliberately left to eval's value-directed dispatch (see the WI-444 block's own note:
/// *"Eval's value-directed override (eval.rs step 3) is the dynamic dual for an
/// ABSTRACT-receiver call this cannot pin"*), which reads the carrier off the RUNTIME
/// VALUE — the only correct source when the argument decides it.
///
/// MEASURED, on the first cut of [`carrier_from_declared_slot`], which lacked this gate:
///
/// ```text
/// operation viaop[U](x: U) -> Int64 requires Desc[T = Rich] = Desc.describe(x)
/// rule answer(?r) :- viaop(plain(), ?r)
/// ```
///
/// answered 7 — `Rich`'s `describe` run on a `plain()` value — where it had answered 3,
/// `Plain`'s own. Silently pre-empting a dynamic dispatch with a static guess is the same
/// class of defect the slot routes exist to remove, so they are gated on the call SHAPE
/// and `wi_nr6fj_defect_b_slot_over_default_test::
/// an_abstract_argument_still_dispatches_on_the_runtime_value` drives it.
///
/// ASKED OF THE DECLARATION, NOT OF THE CALL, and that is the whole correction. The first
/// cut gated on `carrier_param` — the call-site CLASSIFICATION — which is `None` both for
/// an op with no carrier parameter AND for one whose argument was too abstract to
/// classify. The hazard above is the second, so the gate let it straight through.
/// [`declared_type_param_vid`] reads the spec op's OWN declared parameter type
/// (`describe(x: T)`), which no argument can make abstract.
///
/// `classified_carrier_param` is still taken: it is the cheap positive answer, and a call
/// that classified a carrier param is one every caller must decline anyway. It is named
/// apart from the spec's own carrier param BECAUSE the two were once one word at the only
/// call site, and reading the first as the second is what produced the wrong answer.
///
/// WI-20260919-H20YY — EXTRACTED because a SECOND route asks it. The defaulted block's
/// slot DEFERRAL (the `requires Spec[T = P]` half, over a type PARAMETER, which pins no
/// static carrier for [`carrier_from_declared_slot`] to find) must answer the same
/// question in the same words: it too would otherwise pre-empt value-directed dispatch on
/// an abstract argument. Two copies of a gate whose failure mode is a silent wrong answer
/// is exactly the drift this tree keeps paying for.
pub(super) fn call_names_no_carrier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    self_receiver: &ReceiverCarrier,
    // The carrier param the CALL SITE classified, not the spec's own — see above, where
    // confusing the two was a shipped wrong answer.
    classified_carrier_param: Option<Symbol>,
    op_params: &[(Symbol, Value)],
) -> bool {
    if classified_carrier_param.is_some()
        || !matches!(self_receiver, ReceiverCarrier::NotApplicable)
    {
        return false;
    }
    let canon_spec = kb.canonical_sort_sym(spec_sort);
    // The DECLARATION half of [`carrier_param_receiver_for_values`] — a parameter whose
    // declared type is one of the spec's own type parameters. Spelled from the same two
    // primitives so the two cannot drift about what "carrier-typed" means.
    let spec_params = sort_type_params_as_pairs(kb, canon_spec);
    let declares_a_carrier_param = op_params.iter().any(|(_, pty)| {
        declared_type_param_vid(kb, pty).is_some_and(|pvid| {
            spec_params
                .iter()
                .any(|(_, t)| matches!(kb.get_term(*t), Term::Var(Var::Global(v)) if *v == pvid))
        })
    });
    !declares_a_carrier_param
}

/// WI-20260917-NR6FJ DEFECT B — THE DECLARED SLOT AS A CARRIER SOURCE, third beside the
/// self-receiver and the carrier param, and read only when neither of those pinned one.
///
/// A `requires` is an IMPLICIT PARAMETER — `SupplySource`'s own reading, "the A
/// dictionary is PASSED IN, an inbound slot the caller fills". So in
///
/// ```text
/// operation viaop() -> Int64 requires Desc[T = Rich] = Desc.tag()
/// ```
///
/// the author has already said WHICH `Desc` dictionary is in scope, and `Desc.tag()`
/// must read it. [`statically_pinned_carrier`] answers `None` here — `tag` is nullary,
/// so there is no receiver and no carrier-param argument to pin from — and before this
/// the defaulted block therefore declined and the SPEC'S OWN `= 1` ran in place of
/// `Rich`'s `= 7`.
///
/// MEASURED, and the measurement is what makes this a defect rather than a policy: the
/// only difference between answering 7 and answering 1 was whether the spec op happened
/// to carry a default body. Body-less, the identical program dispatches through the slot
/// and answers 7 ([`lookup_spec_op_dispatch`] admits it); defaulted, it folded. One
/// declaration, two meanings, decided by something the caller cannot see.
///
/// A FALLBACK AND NOT A PRIORITY, and [`call_names_no_carrier`] is what enforces it. When
/// the call has ANY carrier source of its own — a self-receiver or a carrier-param
/// argument — this declines outright, whether or not that source pinned a carrier
/// statically. For `describe(x: T)` called at a `Plain` inside an operation whose slot
/// names `Rich`, the value being described is the carrier, and when its type is abstract
/// the carrier is eval's to read at run time. So this widens the block strictly into
/// ground where NO call-site carrier exists at all; no call that pins today, and no call
/// that eval pins tomorrow, changes its answer.
///
/// TWO SLOTS THAT DISAGREE PIN NOTHING. `requires Desc[T = Rich], Desc[T = Other]`
/// leaves the block where it was (running the default) rather than taking the first
/// written: picking by chain order would be exactly the silent route-order choice the
/// surrounding refusals exist to prevent (WI-1010). It is `None` and not a refusal
/// because this function's contract is "which carrier, if any" — the arbitration a tie
/// deserves belongs to [`arbitrate_defaulted_supplier_tie`] below, which sees the
/// suppliers. No corpus program writes two such slots.
///
/// THE BINDING FILTER IS [`provision_binding_at_param`]'s and is load-bearing: it admits
/// only a SORT-like base, so `requires Desc[T = U]` over a type PARAMETER pins nothing
/// here — there IS no static carrier to name, since which provider `U` stands for is
/// settled per call.
///
/// WI-20260919-H20YY — AND THAT HALF IS NOT THIS FUNCTION'S TO ANSWER, where this
/// paragraph used to claim it "already works … through the SLD bridge". MEASURED FALSE:
/// `tagOfP[P](x: P) requires TypeTerm[T = P] = TypeTerm.valueOf()` over a `Box` that
/// OVERRIDES the defaulted `valueOf` ran the SPEC'S DEFAULT and answered `Box(V: Boom)`
/// where the override says `Option(T: Boom)` — silently, because a carrier this declines
/// to pin left the defaulted block with no route at all and the call became a plain apply
/// of the default. Nothing consulted the dictionary. The parametric half is served beside
/// this one, by the slot DEFERRAL in the WI-444 block ([`defer_defaulted_call_to_slot`]):
/// over a type parameter the answer is not a carrier but the frame's slot at run time,
/// which is the dictionary-passing reading 058 gives a spec op.
pub(super) fn carrier_from_declared_slot(
    kb: &KnowledgeBase,
    env: &TypingEnv,
    spec_sort: Symbol,
    self_receiver: &ReceiverCarrier,
    // The carrier param the CALL SITE classified, not the spec's own — see
    // [`call_names_no_carrier`], where confusing the two was a shipped wrong answer.
    classified_carrier_param: Option<Symbol>,
    op_params: &[(Symbol, Value)],
) -> Option<GoalCarrier> {
    if !call_names_no_carrier(
        kb,
        spec_sort,
        self_receiver,
        classified_carrier_param,
        op_params,
    ) {
        return None;
    }
    let canon_spec = kb.canonical_sort_sym(spec_sort);
    // The enclosing OPERATION's chain — the sort's slots then its own (WI-822 LEG 1) —
    // because an operation body DOES inherit its sort's `requires`. (A rule body does
    // not; that is `check_rule_body_requirements`' documented rule and 060 §8.9 row I1,
    // deliberately untouched here.)
    //
    // CHEAPEST GATE FIRST, which is the typer's habit and here it is load-bearing for
    // cost: this runs on every defaulted-spec-op call whose arguments pinned nothing, and
    // the enclosing chain is EMPTY for almost all of them. A symbol compare over an empty
    // slice leaves immediately; `spec_carrier_param_or_sole` below walks the spec's
    // operations and must not be paid by a call with no slot at all. The surrounding
    // block already reaches `type_params_of_sort` four times per call (see the WI-1042
    // note at its head) — this must not be a fifth for the common case.
    let entries = env.enclosing_frame_chain().entries();
    if !entries
        .iter()
        .any(|e| kb.canonical_sort_sym(e.required_sort) == canon_spec)
    {
        return None;
    }
    // WI-1102's two-rung ladder, not `spec_carrier_param` alone: a NULLARY spec op is
    // precisely the shape with no self-receiver to read the carrier off, and it is also
    // the shape this function exists for. WI-20260916-8WRJC took the same rung for the
    // same reason one lookup over.
    let spec_carrier_param = spec_carrier_param_or_sole(kb, canon_spec)?;
    let mut found: Option<Symbol> = None;
    for entry in entries {
        if kb.canonical_sort_sym(entry.required_sort) != canon_spec {
            continue;
        }
        let Some((_, base)) = provision_binding_at_param(kb, spec_carrier_param, &entry.spec)
        else {
            continue;
        };
        // WI-20260919-H20YY — A TYPE PARAMETER IS NOT A CARRIER, and the shared filter
        // above does not say so. [`provision_binding_at_param`] admits any base of
        // `SymbolKind::Sort`, and a type parameter IS one: it is DECLARED `sort T = ?`,
        // so `requires TypeTerm[T = P]` pinned `P` itself as the carrier sort. Nothing
        // downstream then matched — `carrier_override_suppliers` finds no supplier at a
        // parameter — so the block ran the spec's DEFAULT body and a provider's override
        // was never reached. MEASURED: `tagOfP(box(…))` answered `Box(V: Boom)` where
        // `Box`'s override says `Option(T: Boom)`.
        //
        // This restores what this function's own doc always claimed ("`requires Desc[T =
        // U]` over a type PARAMETER pins nothing here"); the claim was true of the
        // intent and false of the code. [`genuine_concrete_sort`] is the predicate that
        // means it — "not a sort-type-param, and a name that really plays the sort role"
        // — and it is the same question its two existing readers ask: *may I treat this
        // as a carrier now*.
        //
        // `return None` AND NOT `continue`, so a parametric slot cannot be passed over in
        // favour of a concrete sibling: `requires Desc[T = Rich], Desc[T = U]` must pin
        // nothing, exactly as the disagreement clause above requires, rather than
        // silently taking the one that happens to be written concretely. Over a
        // parameter there is no static carrier to find, and the honest answer for the
        // whole question is "not statically pinned" — which is what hands the call to the
        // slot deferral ([`defer_defaulted_call_to_slot`]), where it belongs.
        let Some(base) = genuine_concrete_sort(kb, base) else {
            return None;
        };
        let base = kb.canonical_sort_sym(base);
        match found {
            Some(prev) if prev != base => return None,
            _ => found = Some(base),
        }
    }
    found.map(GoalCarrier::bare)
}

/// WI-1027 — the carrier a spec-op call pins STATICALLY, whichever of the two receiver
/// shapes classified it: the SELF-RECEIVER form (`collect(s: Stream)`, whose carrier is
/// the receiver argument's concrete sort) or the CARRIER-PARAM form (`describe(x: T)`,
/// whose carrier is what filled the spec's own param). `None` when nothing static pins
/// one — which is the signal to leave the call to eval's value-directed dispatch.
///
/// Extracted at WI-1027 because a SECOND site had to ask the same question, and the two
/// answering it separately is the shape this tree keeps paying for: the WI-444 arm's copy
/// carries the WI-608 rule below, and a body-less guard that re-derived the carrier from
/// [`ReceiverCarrier`] alone answered `None` for every carrier-param call — MEASURED, it
/// made the whole refusal silently inert while its tests read as ordinary "loads clean".
///
/// WI-608: an ABSTRACT-SPEC carrier param (a `FiniteCollection`-typed receiver) is NOT a
/// static pin — its runtime value is some concrete provider, so a qualified
/// `Iterable.map(src)` on it would otherwise mis-pin to `FiniteCollection`'s OWN `map`, a
/// different operation. A concrete carrier — direct OR transitive — does pin.
///
/// That leg is what the body-less block's WI-496/WI-598 deferral now ASKS rather than
/// spells: its arm reads this function's answer instead of calling
/// `carrier_is_abstract_spec` itself, so the predicate has one owner AND one evaluation
/// per call site. That matters for cost, not only for tidiness — it reaches
/// `KnowledgeBase::sort_has_constructors`, which builds a `format!` prefix and scans every
/// qualified name in the symbol table, so a second ask is far dearer than the provision
/// walk the guard it feeds performs.
///
/// The two inputs are never both informative: `carrier_param_receiver` is consulted only
/// when there is no self-receiver (the shapes are mutually exclusive at the classifier),
/// so the fallback runs exactly when the first arm is `NotApplicable`.
///
/// `spec_sort` is the spec whose operation is being called, and it is what the REFLEXIVE
/// clause below reads — see there. Every caller has it; `None` is for a caller that
/// passes no carrier param at all, where the clause cannot apply.
pub(super) fn statically_pinned_carrier(
    kb: &KnowledgeBase,
    self_receiver: &ReceiverCarrier,
    carrier_param: Option<Symbol>,
    spec_sort: Option<Symbol>,
) -> Option<GoalCarrier> {
    match self_receiver {
        // WI-20260828-EKWDC: the self-receiver form's arguments come with it — see
        // [`GoalCarrier`].
        ReceiverCarrier::Concrete(c) => Some(c.clone()),
        ReceiverCarrier::Abstract | ReceiverCarrier::NotApplicable => carrier_param
            // WI-20260831-PYNS2 — THE REFLEXIVE CARRIER, asked directly instead of through
            // the provider census. `carrier_is_abstract_spec` was standing in for "is this
            // an abstract spec value?", and its PROVIDER leg is what made it answer `true`
            // for a spec. Once WI-609's reflexive arm stopped needing a provider, a spec
            // NOTHING provides reached this filter, answered `false`, and was reported as a
            // statically pinned CONCRETE carrier — the exact mis-pin the WI-608 leg above
            // exists to prevent, stated in its own words ("its runtime value is some
            // concrete provider"). Benign as measured (a spec with no providers has no
            // competing supplier to mis-pin TO, and both readers agreed either way), but
            // the invariant was false, so it is asked rather than argued. `None` for the
            // callers that pass no carrier param — the clause cannot matter there.
            .filter(|&c| {
                Some(kb.canonical_sort_sym(c)) != spec_sort.map(|s| kb.canonical_sort_sym(s))
            })
            .filter(|&c| !carrier_is_abstract_spec(kb, c))
            // NO ARGUMENTS, and none are missing: the carrier-PARAM shape's carrier IS
            // a spec binding, so whatever the receiver wrote at it is already
            // `goal.bindings`' value for that param. Reading it a second time here
            // would put it in the goal twice.
            .map(GoalCarrier::bare),
    }
}

/// WI-1027 — refuse a BODY-LESS spec op whose statically pinned carrier has two suppliers
/// that nothing arbitrated between. The load face of
/// [`crate::eval::EvalError::AmbiguousSpecOpDispatch`] for the half WI-1012 did not cover.
///
/// **"TWO SUPPLIERS" IS NOT THE CONDITION**, which is the ticket's own premise and is
/// FALSE at the typer — measured: a bare `cands.len() >= 2` guard refused SIX delivered
/// programs (wi817 ×1, wi843 ×2, wi857 ×2, wi858 ×1). The count is sound for eval's
/// [`crate::eval::Interpreter::resolve_spec_op_target_by_value`] because that read is
/// BRACKET-LESS BY CONSTRUCTION — no call site, so nothing could ever have selected. Here
/// a call site exists and 058 §4.1 gives it two ways to arbitrate that a count cannot see:
///
///   * TIER 1, an explicit `f[Spec = W](…)` — `wi857`'s `Ord.compare[Ord =
///     Descending](7, 3)` has two suppliers for `Int64` and is a correct program. Applied
///     by the CALLER, which holds the selections.
///   * TIER 2, SPECIFICITY — `pick_most_specific` takes the ground provision over the
///     parametric one and the call runs with no diagnostic. WI-843 pinned that
///     deliberately and recorded that making it loud "amounts to a new coherence rule", so
///     refusing it here would overturn a delivered decision as a side effect.
///
/// **SO THE CONDITION IS WHAT THE ARBITRATION COULD NOT WEIGH.** `resolve_inner` weighs
/// PROVISIONS and projects each to an operation through `sort_ops_lookup(impl_sort,
/// op_short)`. A WITNESS provision survives that projection intact — its supplier IS the
/// lookup's answer — so a tie among witnesses is broken by tier 1 or tier 2, or raised as
/// `Ambiguous`, all before this runs. The other two routes do not:
///
///   * [`SupplyRoute::Own`] contributes NO provision, so it is never a distinguishable
///     candidate — the arbitration can never compare it against a rival. Note this does
///     NOT mean it cannot win: when the chosen provision is carrier-keyed its `impl_sort`
///     IS the carrier, so `sort_ops_lookup` returns the carrier's own member and route 1
///     wins by riding on someone else's provision, never having been weighed. That is
///     fixture 2 below answering 7.
///   * [`SupplyRoute::Fact`] IS weighed as a provision, but its op-valued BINDING is not
///     what `sort_ops_lookup` returns, so the projection is lossy exactly where it matters
///     — a provision the arbitration DID select still loses its binding to a same-named
///     member of the carrier.
///
/// **COUPLING, stated because nothing else enforces it.** The `Fact` leg is a property of
/// two lines elsewhere, not of the route: `collect_provides_candidates` drops op-valued
/// bindings, and `resolve_at_goal` projects through `sort_ops_lookup`. Make the `Unique`
/// resolution consult the resolved provision's own op binding — the natural deeper fix for
/// fixture 2, and a plausible future ticket — and `Fact` becomes arbitrated, at which
/// point [`SupplyRoute::weighed_by_provision_arbitration`] must say so or this refusal
/// starts firing on a legitimate selection. That is why the classification is a method on
/// the route with its mechanism in its doc, and not a `matches!` here.
///
/// MEASURED, the three fixtures, before any of this existed
/// (`wi1027_bodyless_supplier_tie_test`): an own member DECLARED-but-unrunnable beside a
/// fact binding loaded clean and refused at the CALL (WI-1012's cost 1); the same member
/// given a body answered 7, the loader-certified `describe = otherDescribe` meaning
/// nothing (WI-1010's defect one half over); and with a witness rival instead it answered
/// 9, the carrier's own member silently losing. BLAST RADIUS: across `stdlib` +
/// `anthill-stl` there is no (body-less spec op, carrier) pair with two suppliers at all —
/// a whole-KB scan reported 0 — so the corpus reaches this only through fixtures.
///
/// COST: this is a THIRD caller of [`spec_op_suppliers_for_carrier`], and the first on the
/// BODY-LESS population, which is far larger than the two defaulted-op sites WI-1011
/// bounded ("per apply-site-per-load, negligible"). The walk is per call site with a
/// pinned carrier and is not short-circuitable — skipping it on an own-member hit is the
/// first-match blindness the design removes. Unmeasured here; **WI-1011** owns the memo.
///
/// WI-1035 added a FOURTH reaching path — [`dot_member_dispatch_decision`] — whose
/// population this paragraph's reasoning does not cover: not a call site with a pinned
/// carrier, but every DOT that resolves the receiver's own member. It is 0 across the
/// corpus (measured at that site) and so unexercised, not cheap; the memo is the same one.
///
/// Reads [`spec_op_suppliers_for_carrier`] and NOT [`carrier_override_suppliers`]: the
/// interpretability filter is the defaulted half's own (WI-1010 — there a default is the
/// fallback, so a member eval cannot call is not a supplier). A body-less op has no
/// fallback, and this question is a coherence one — "did the author supply two
/// implementations?" — which must not change answer with the host backend (WI-886).
/// Driven by the unrunnable-member fixture, which has two suppliers here and one there.
///
/// WI-861 (058 §3.2 RUNG 2a) — and the guard now DECLINES when the default names exactly
/// one of the tied suppliers. It selects nothing itself, so the licence is that the
/// dispatch it lets through lands on the same provider the rung named, in both shapes:
///
///   * the default is the CARRIER (its own provision, inferred). The carrier self-provides,
///     so it contributes a provision; a rival provision makes `resolve_inner` tie and
///     [`default_among_candidates`] takes the carrier, whose `sort_ops_lookup` answer is
///     the `Own` member — this very supplier. With no rival provision the outcome is
///     `Unique(carrier)` already, and the surviving tie is `Own`-vs-`Fact`, one provider
///     twice, which the rung declines (see [`SpecOpSupplier::provider`]).
///   * the default is a WITNESS. Then `resolve_inner` resolves to that witness — by
///     uniqueness or by the same rung — and the projection lands on its own member.
///
/// Driven by `wi861_rung2a_default_dispatch_test::a_bodyless_own_member_beside_a_marked_
/// witness_takes_the_default`, whose value assertion is what makes the agreement measured
/// rather than argued.
///
/// IT RETURNS THE SUPPLIER IT DECLINED FOR, and that is not decoration: a caller that
/// SELECTS (the dot — [`dot_takes_or_reroutes`]) must know WHICH candidate the rung named,
/// because declining to refuse and then calling the other one is the same wrong answer
/// with no diagnostic. `check_apply_iter`'s caller ignores the answer, and may: the
/// dispatch there is `dispatch_spec_op_cached`'s, which reads the same rung one layer down
/// at `resolve_inner` and lands on the same provider (both shapes argued at the guard's
/// head, and driven by the test named above).
///
/// `Ok(None)` means "nothing arbitrated here" — 0 or 1 supplier, or a tie every candidate
/// of which the provision arbitration CAN weigh, which `resolve_inner` owns.
pub(super) fn arbitrate_unarbitrated_supplier_tie(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier: Symbol,
    spec_op: Symbol,
    op_short_sym: Symbol,
    span: Option<Span>,
) -> Result<Option<Symbol>, TypeError> {
    let cands = spec_op_suppliers_for_carrier(kb, spec_sort, carrier, spec_op, op_short_sym);
    // Count first: the route scan is skipped for the 0- and 1-supplier case, which the
    // blast-radius scan measured as every call in the tree.
    if cands.len() < 2
        || cands
            .iter()
            .all(|c| c.route.weighed_by_provision_arbitration())
    {
        return Ok(None);
    }
    match default_among_suppliers(kb, spec_sort, carrier, &cands) {
        Some(i) => Ok(Some(cands[i].target)),
        None => Err(supplier_tie_error(kb, spec_op, carrier, &cands, span)),
    }
}

/// WI-861 — 058 §3.2 RUNG 2a at a SUPPLIER tie: the index of the tied supplier whose
/// PROVIDER the default names, or `None` for "say which".
///
/// The sibling of [`default_among_candidates`], over the other candidate population, and
/// both reduce to [`crate::kb::defaults::default_among`] so the rung has ONE implementation.
/// What differs is only the carrier key: a supplier tie is asked at a carrier SORT — the
/// value's own, or the call's statically pinned one — with no carrier TERM in hand, so
/// the lookup is base-only and declines wherever that is not decisive
/// ([`crate::kb::defaults::CarrierKey`] carries why that direction is the safe one).
pub(crate) fn default_among_suppliers(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier: Symbol,
    cands: &[SpecOpSupplier],
) -> Option<usize> {
    crate::kb::defaults::default_among(
        kb,
        spec_sort,
        crate::kb::defaults::CarrierKey::Base(carrier),
        cands.iter().map(|c| c.provider(carrier)),
    )
}

/// WI-1042 — the DEFAULTED half's tie condition, in ONE place. The sibling of
/// [`arbitrate_unarbitrated_supplier_tie`], and deliberately a DIFFERENT condition: this one
/// is a bare count.
///
/// Takes the candidate slice the caller ALREADY computed, which is what makes sharing
/// possible at all. WI-1035 recorded the opposite — "extracting it would make that arm's
/// `[only]` pin walk the suppliers twice or leave it matching an arm it can no longer
/// reach" — and that is true only of a helper that re-derives [`carrier_override_suppliers`]
/// itself. Passing the slice is the shape [`supplier_tie_error`] and
/// `arbitrate_unarbitrated_supplier_tie` already use, and it serves BOTH sites in one walk:
/// `check_apply_iter`'s WI-1012 arm asks this, then matches the same slice for its single
/// pin. What the coupling cost while it was two copies: the WI-1012 arm carries a
/// documented REACH narrowing (only the carrier-param shape can tie), and the moment that
/// became a CLAUSE the dot spelling would have silently diverged from the qualified
/// spelling on the same program — the spelling-keyed silence WI-1035 was opened to close.
///
/// WHY IT IS A BARE COUNT while the body-less sibling carries two narrowing clauses —
/// stated here, once, because the symmetry is tempting and copying them over would be
/// WRONG. NOTHING ARBITRATES ON THIS PATH. Neither caller runs `dispatch_spec_op_cached`,
/// so there is no `resolve_at_goal` and no tier-2 specificity to defer to; and
/// `callee_requirement_slots` pushes no dispatch slot for a defaulted op, so no tier-1
/// bracket can bind one either (at the dot site tier 1 is out for a second reason:
/// `Expr::DotApply` carries no `type_args` field, so a dot is bracket-less by
/// construction — the WI-842 argument). Two suppliers therefore genuinely ARE a tie. The
/// clauses over there exist because something does.
///
/// WI-861 — IT ALSO SELECTS NOW, and the two jobs are one function because they are one
/// decision. 058 §3.2's rung 2a says an unselected dispatch takes the DEFAULT among the
/// tied candidates; a helper that only declined to refuse would leave both callers
/// falling through to the spec's own default body, which is precisely the silence the
/// rung exists to fill. So the answer is *which supplier*, and `Err` is the tier-3
/// refusal that stands when nothing says.
///
/// `Ok(None)` is the ZERO-supplier gap — a default is what fills it, and the caller runs
/// the spec's default body.
pub(super) fn arbitrate_defaulted_supplier_tie<'a>(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    spec_op: Symbol,
    carrier: Symbol,
    cands: &'a [SpecOpSupplier],
    span: Option<Span>,
) -> Result<Option<&'a SpecOpSupplier>, TypeError> {
    match cands {
        [] => Ok(None),
        [only] => Ok(Some(only)),
        many => match default_among_suppliers(kb, spec_sort, carrier, many) {
            Some(i) => Ok(Some(&many[i])),
            None => Err(supplier_tie_error(kb, spec_op, carrier, cands, span)),
        },
    }
}

/// WI-1035/WI-1038 — what a dot does with the member it resolved on the receiver's sort.
/// A `Result<Option<Symbol>, _>` said the same thing and needed a comment at the call site
/// to say which `Option` arm meant what, which is why the typer already carries ~20 named
/// verdicts ([`MemberMiss`], [`ReceiverCarrier`], [`SigmaVerdict`], …) rather than bare
/// options. Refusals ride the `Err`; this is only the two ways to proceed.
pub(super) enum DotMember {
    /// Call the member, which is what a dot has always done.
    Take,
    /// Call the SPEC OP instead, so the value picks the implementation — the receiver
    /// pinned no carrier, so the member is not "the carrier's" anything.
    ///
    /// THE SYMBOL IS THE LADDER'S NEXT RUNG, not a second route to it: it is exactly what
    /// `.or_else(find_spec_op_for_provided_sort)` would have produced had the own-member
    /// rung missed, and this arm means precisely "on an abstract-spec receiver that rung is
    /// not authoritative — fall through". It is carried rather than recomputed only because
    /// the decision already paid for the lookup.
    DispatchByValue(Symbol),
}

/// WI-1035/WI-1038 — the DOT spelling's decision: `leaf().describe(…)` resolves `describe` on the
/// receiver's sort BY NAME, so the member was taken before anything asked which spec it
/// backs, and the two guards above were never reached at all.
///
/// MEASURED on WI-1010's two-supplier fixture, all four combinations silent, and the
/// two rows the qualified spelling REFUSES are the ones that make it a defect and not a
/// spelling preference:
///
/// | spec op | rival | `leaf().describe()` | `Desc.describe(leaf())` |
/// |---|---|---|---|
/// | defaulted (`= 1`) | instance fact | **7** | REFUSED (WI-1012) |
/// | body-less | instance fact | **7** | REFUSED (WI-1027) |
/// | body-less | witness sort | **7** | REFUSED (WI-1027) |
///
/// and both faces of the first row — an operation body and a rule body — answer 7
/// alike, which is what proved the silence keyed on the SPELLING rather than on
/// WI-1026's rule-body path.
///
/// THE OWN MEMBER IS ROUTE 1, NOT A LADDER RUNG. The name ladder (§8.6, WI-907/908/914)
/// is about which NAME a member resolves to and ends at an ambiguity; this is a
/// different question one layer down — given the name, which of the texts that supply
/// an implementation FOR THIS CARRIER wins — and 058 §3.7 answers it the same way for
/// every reader: a read that SELECTS one goes loud on the second candidate, never
/// first-match. The dot was the last reader still selecting silently.
///
/// TWO ANSWERS, and which one depends on whether the receiver pins a CARRIER.
///
/// WHAT THE BACKING CHECK BUYS, stated exactly because it is easy to overclaim: it closes
/// the WRONG-MEMBER hazard (the spec op's implementation for this carrier is the member the
/// dot found, not some other same-named one). It does NOT verify that the spec op's
/// SIGNATURE fits — nothing here does. That is caught by the synthesized `Apply` being
/// re-typed, so a mismatch is a type error rather than a silently different call.
///
/// On an ABSTRACT-SPEC receiver it REROUTES (WI-1038): there is no static carrier — the
/// runtime value is some concrete provider — so the member is not "the carrier's"
/// implementation, and 058 §3.1 says dispatch answers by the value. Handing the call to the
/// spec op is what the SAME program's qualified spelling does, so this is the two spellings
/// agreeing rather than a new rule. MEASURED before: the dot answered 7 while the qualified
/// spelling was refused at the call.
///
/// On a CONCRETE carrier it does not: the member is taken, and only what happens at a
/// SECOND supplier changes. **This is a scope limit, not a soundness one, and TWO earlier
/// readings of it were wrong** — both recorded, because each is what a reader will reach
/// for next:
///
///   * "rerouting re-types every `xs.map(f)` in the tree" is FALSE by this ticket's own
///     number — `xs.map(f)` never reaches this function, it resolves at the NEXT rung,
///     which already synthesizes the spec op and rides `req_insertion` (WI-281), and
///     own-member dots measure ZERO across the corpus.
///   * "[`find_spec_op_for_provided_sort`] matches by SHORT NAME, so rerouting could call a
///     different operation" was true of a reroute with no backing check and is no longer
///     the discriminator: the `carrier_own_op` agreement in the abstract arm below closes
///     exactly that hazard, and nothing stops the concrete arm from asking it too.
///
/// What actually separates them is WHEN the answer is available. A concrete carrier makes
/// the tie decidable at LOAD, which is the whole of WI-1012's argument — the span, the
/// carrier and the candidate list are in hand — and rerouting would trade that refusal for
/// eval's later one. So the concrete arm keeps the load refusal and the member; the
/// abstract arm has no load answer to keep.
///
/// THE TWO HALVES ASK DIFFERENT QUESTIONS, and each is now DELEGATED to the owner of its
/// condition: the BODY-LESS one to [`arbitrate_unarbitrated_supplier_tie`], whose narrowing
/// clauses exist because `dispatch_spec_op_cached` can weigh provisions, and the DEFAULTED
/// one to [`arbitrate_defaulted_supplier_tie`], shared with WI-1012's arm in
/// [`check_apply_iter`]. **WI-1042 — WHAT THE COPY COST, recorded because the reason it
/// was a copy was WRONG:** WI-1035 kept the three-line condition inline here on the ground
/// that extracting it would make that arm's `[only]` pin walk the suppliers twice. It does
/// not — the helper takes the ALREADY-COMPUTED slice, the shape `supplier_tie_error`
/// already used. What the copy did buy was a live coupling: that arm carries a documented
/// REACH narrowing (only the carrier-param shape can tie) which is prose today, and the
/// moment it became a clause the dot spelling would have diverged from the qualified one
/// on the same program — the spelling-keyed silence this ticket was opened to close.
///
/// TIER 1 CANNOT APPLY HERE: `Expr::DotApply` carries no `type_args` field, so a dot is
/// BRACKET-LESS BY CONSTRUCTION and the `!pinned_spec` clause the body-less guard's
/// caller applies has nothing to read. That is the same argument eval's bracket-less
/// readers make for taking the bare count (WI-842).
///
/// TIER 2 IS WHY THE BODY-LESS HALF DELEGATES RATHER THAN COUNTING: no dispatch runs on
/// this path, so there is no `DispatchOutcome` to defer to, and a bare count would refuse
/// the specificity-ordered pair WI-843 pinned as deliberate. STATED SO IT IS NOT READ AS
/// A DRIVEN CLAUSE: at THIS site the shared guard's route clause is not known to be
/// reachable — this function runs only on an own-member hit, and an `Own` candidate is
/// never `weighed_by_provision_arbitration`, so the clause is satisfied whenever the count
/// is. It is not PROVABLY inert ([`carrier_own_op`] reads `sort_ops_lookup` while the dot
/// reads `find_operation_in_scope`, and WI-616's doc records a shape where those differ),
/// and delegating keeps ONE owner for the condition either way — but no test here drives
/// it, and this paragraph is instead of a control that would only look like one.
///
/// AN AUTHOR-WRITTEN `@[simp]` DOT RULE IS NOT PRE-EMPTED, because it fires EARLIER in this
/// frame and never reaches here. That ordering is unchanged and is not a silent
/// first-match: a sort-specific rewrite declared in the receiver's sort is a text the
/// author wrote for this receiver, which is a selection, not a route order.
///
/// ONE DIVERGENCE LEFT, STATED BECAUSE IT IS A DECISION AND NOT AN OVERSIGHT: where the
/// carrier ALSO self-provides the spec beside a witness rival, the qualified spelling
/// reports the PROVIDER tie (`DispatchOutcome::Ambiguous`, which raises on its own
/// account and is excluded there) while the dot reports the SUPPLIER tie — the dot ran
/// no dispatch, so it has no outcome to yield to. Both refuse the same program at load
/// and name the same two texts; only the sentence differs. Pinned by
/// `a_dot_on_a_provision_tie_refuses_as_a_supplier_tie`.
pub(super) fn dot_member_dispatch_decision(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    own_member: Symbol,
    short: &str,
    span: Option<Span>,
) -> Result<DotMember, TypeError> {
    // The spec op the member backs, found the same way the ladder's NEXT rung finds one
    // when the carrier declares no member of its own — so "backed" here means exactly
    // what "resolved through a provided spec" means one line below, including the WI-450
    // witness match and the WI-495 transitive hop.
    let Some(spec_op) = find_spec_op_for_provided_sort(kb, carrier, short) else {
        return Ok(DotMember::Take);
    };
    // WI-1042 — WHAT A MISS MEANS HERE, stated because every other early-out in this
    // function states its own and this one did not. `find_spec_op_for_provided_sort`
    // answered `Some`, so the member backs something the carrier `provides` — but a
    // PROVIDED SORT NEED NOT BE A SPEC. 058's spec sort is one declaring `sort X = ?`;
    // `sort Leaf provides Plain` where `Plain` declares none loads clean, and
    // `Plain.describe` then has no parametric parent.
    //
    // So `Take` is the ANSWER, not a fallback: with no type parameter there is no carrier
    // to key a supplier set on and no spec-op dispatch to decide, and the tie guard below
    // is INAPPLICABLE rather than skipped. Filed as a loud error by this ticket's
    // description and REFUTED by driving — a `panic!` here fired on exactly that program
    // and on nothing else in the workspace, so raising would refuse a legal one.
    // `wi1042_defaulted_gate_test::a_non_parametric_provided_sort_takes_the_member` is
    // that program, kept as the driver.
    let Some(spec_sort) = spec_op_parent_sort(kb, spec_op) else {
        return Ok(DotMember::Take);
    };
    let op_short_sym = kb.intern(short);
    // WI-608: an ABSTRACT-SPEC receiver is not a static pin — its runtime value is some
    // concrete provider — so the suppliers of the SPEC sort are not the suppliers of the
    // value. It is not vacuous here: a spec declaring its own defaulted members
    // (`Stream.collect`) resolves an own member for a `Stream`-typed receiver exactly as a
    // concrete carrier does; dropped, a two-supplier program behind such a receiver is
    // refused at LOAD, which is the half WI-1012 deliberately left to the call.
    //
    // NOT ROUTED THROUGH [`statically_pinned_carrier`], which applies the same filter: that
    // function's job is SELECTING between two receiver shapes, and this frame made neither
    // classification — its carrier is the receiver's `min_sort`. Passing `NotApplicable` +
    // `Some(carrier)` would answer correctly by coincidence of the filter while claiming a
    // classification that was never made. The RULE has one owner and both sites call it:
    // [`carrier_is_abstract_spec`].
    //
    // WI-1038 — and this arm is why the early return is a REROUTE rather than a bare
    // `Ok(None)`. Taking the member here would not merely skip the tie check: it would also
    // keep the call away from eval's value-directed reader, so the dot ANSWERED where the
    // qualified spelling of the same program is refused AT THE CALL (measured, 7 vs. a
    // refusal). Sending the spec op instead puts both spellings on the one reader.
    //
    // A SOLE supplier still reaches the member, via that same reader — which is the control
    // this could most easily have broken, since `check_apply_iter`'s WI-444 block declines
    // to pin an abstract carrier and would otherwise leave the spec's DEFAULT running.
    // Driven by `an_abstract_spec_receiver_with_one_supplier_still_reaches_it`.
    if carrier_is_abstract_spec(kb, carrier) {
        // Is `own_member` the LANGUAGE's backing for `spec_op` on this carrier, and not
        // merely a same-named member? [`carrier_own_op`] is that relation (`sort_ops_lookup`
        // narrowed to a member the carrier itself declares) and the one
        // [`resolve_op_target`] dispatches through, so agreeing with it is what makes the
        // reroute mean "the same implementation, chosen by the value". Where they DISAGREE
        // the dot found something the supplier set does not contain, and nothing may act as
        // if it had. Asked HERE and not above: the concrete path never reads it, and this
        // function's own budget note two paragraphs up is about not paying a second lookup
        // on that path.
        //
        // AND WHAT `false` LEAVES, so this reads as a bound and not as completeness: the
        // dot then keeps the member and answers where the qualified spelling would refuse
        // — the pre-WI-1038 behaviour, for the one shape where the two lookups disagree
        // (WI-616 records `sort_ops_lookup` returning one arbitrarily when a carrier
        // provides two specs with the same short name). Answering wrongly on a name
        // coincidence would be worse than answering as before, so the fallback is `Take`.
        // WI-616 is DELIVERED and owns only that RECORD; the residual gap — the two
        // spellings still disagreeing on such a carrier — is **owned by WI-1042** until
        // the disagreeing shape has a decided answer.
        let backs = carrier_own_op(kb, carrier, spec_op, op_short_sym)
            .is_some_and(|o| kb.canonical_sym(o) == kb.canonical_sym(own_member));
        return Ok(if backs {
            DotMember::DispatchByValue(spec_op)
        } else {
            DotMember::Take
        });
    }
    // WI-1042 — WHICH HALF, asked through the gate the other two sites ask
    // ([`defaulted_spec_op_parent`]) rather than through a local `operation_has_no_body`.
    // The two spellings agree today, which is exactly why the local one was a hazard: a
    // clause added to the gate would have moved `check_apply_iter`'s population and left
    // this one behind, silently, on a path no corpus program reaches.
    //
    // THEY ARE EXACT COMPLEMENTS HERE, which is not true of them in general and is worth
    // one sentence: `operation_has_no_body` requires an `OperationInfo` and the gate's
    // `op_has_runnable_body` requires one too, so they differ only where none exists — and
    // `find_spec_op_for_provided_sort` found `spec_op` BY WALKING the `OperationInfo`
    // facts, so at this line one exists by construction. `spec_sort` above supplies the
    // gate's other two legs.
    //
    // AND IT PAYS `type_params_of_sort` A SECOND TIME, knowingly. The note that stood here
    // ("ONE `spec_op_parent_sort`, deliberately") was a micro-optimization of a path this
    // function's own contract measures at ZERO own-member dots across the corpus; the
    // 51 µs it was avoiding on a branch that never runs bought nothing (and WI-954 has
    // since made that call an owner-scope read), and it bought a second reading of
    // "defaulted".
    // The hot reader is `call_dispatch_shape` (~745 calls/load), which pays it once; the
    // `check_apply_iter` frame went from five reaches to four, enumerated at that site.
    if defaulted_spec_op_parent(kb, spec_op).is_none() {
        // BODY-LESS — a different question with a different condition; see
        // [`arbitrate_unarbitrated_supplier_tie`].
        let broke_a_tie = arbitrate_unarbitrated_supplier_tie(
            kb,
            spec_sort,
            carrier,
            spec_op,
            op_short_sym,
            span,
        )?;
        return Ok(dot_takes_or_reroutes(kb, own_member, spec_op, broke_a_tie));
    }
    // DEFAULTED.
    let cands = carrier_override_suppliers(kb, spec_sort, carrier, spec_op, op_short_sym);
    let chosen = arbitrate_defaulted_supplier_tie(kb, spec_sort, spec_op, carrier, &cands, span)?;
    // ONLY A TIE, and the `len() >= 2` is the whole of that claim: `chosen` is also `Some`
    // for a SOLE supplier, and rerouting there would change what an ordinary one-supplier
    // dot calls whenever `carrier_override_suppliers`' interpretability filter has dropped
    // the member itself — reachable, and exactly the WI-616 name-coincidence shape the
    // abstract arm above declines to act on.
    let broke_a_tie = (cands.len() >= 2)
        .then(|| chosen.map(|c| c.target))
        .flatten();
    Ok(dot_takes_or_reroutes(kb, own_member, spec_op, broke_a_tie))
}

/// WI-861 — WHAT A DOT DOES WITH ITS MEMBER once 058 §3.2's rung 2a has spoken, for BOTH
/// halves, because the two diverging is the typer's own subject one rung down.
///
/// `Take` says exactly one thing — "call the member this dot resolved" — so a default
/// naming a WITNESS has no expression there, and taking the member anyway answers where
/// the qualified spelling pins the witness. MEASURED before this was shared: the body-less
/// half consulted the rung (through the guard's new decline) and then returned `Take`
/// regardless, so one program answered `7` qualified and `1` dotted — the spelling-keyed
/// silence WI-1035 was opened to close, re-created by its own successor.
///
/// The call is handed to [`DotMember::DispatchByValue`] instead, whose synthesized
/// `Desc.describe(x)` is re-typed through the arm that CAN express "the provider silence
/// takes", so both spellings read one arbitration rather than two.
///
/// `chosen` is `Some` ONLY for a TIE the rung broke — never for a sole supplier, which is
/// not the rung's business and keeps the member, so every dot in the corpus (0 own-member
/// dots, measured at this function's caller) is bit-for-bit unchanged.
fn dot_takes_or_reroutes(
    kb: &KnowledgeBase,
    own_member: Symbol,
    spec_op: Symbol,
    chosen: Option<Symbol>,
) -> DotMember {
    match chosen {
        Some(t) if kb.canonical_sym(t) != kb.canonical_sym(own_member) => {
            DotMember::DispatchByValue(spec_op)
        }
        _ => DotMember::Take,
    }
}

/// WI-1027 — build the load-time supplier-tie refusal from a candidate list the caller
/// already has. The typer sites that decline to select — WI-1012's defaulted-op arm,
/// WI-1027's body-less guard, and WI-1035's dot-member guard, which reaches both by
/// spelling — construct one error out of `(span, op, carrier)` plus
/// the two derived fields, and both derivations are easy to get subtly wrong: the
/// candidate list must be route-rendered against the op's SHORT name (so the fact leg can
/// echo `describe = otherDescribe`), and the repair must be ASKED rather than assumed
/// (WI-1012's own first cut hard-coded `KeepOne`, which is false for a witness rival on a
/// body-less op — see [`SupplierTieRepair`]). Sharing the construction is what keeps the
/// two halves of one mechanism from drifting the way WI-1010's four route enumerations
/// did; the message body below is already shared with eval for the same reason.
///
/// Takes the candidates rather than re-deriving them: the WI-1012 arm computes
/// [`carrier_override_suppliers`] to find its single pin and must not walk the provisions
/// twice, and the WI-1027 guard reads the wider [`spec_op_suppliers_for_carrier`] — the
/// interpretability filter is the defaulted half's own (WI-1010), so the two lists are
/// deliberately not the same query.
pub(crate) fn supplier_tie_error(
    kb: &KnowledgeBase,
    spec_op: Symbol,
    carrier: Symbol,
    cands: &[SpecOpSupplier],
    span: Option<Span>,
) -> TypeError {
    let op_qn = kb.qualified_name_of(spec_op).to_string();
    TypeError::AmbiguousSpecOpDispatch {
        span,
        op: spec_op,
        carrier,
        candidates: render_suppliers(kb, cands, short_name_of(&op_qn)),
        repair: supplier_tie_repair(kb, spec_op, cands),
    }
}

/// WI-1012 — the one message body for "several texts supply one spec op's
/// implementation FOR one carrier, and nothing selects among them" (058 §4.9),
/// shared by [`TypeError::AmbiguousSpecOpDispatch`],
/// [`crate::kb::load::LoadError::AmbiguousSpecOpDispatch`]'s two renderings, and
/// [`crate::eval::EvalError::AmbiguousSpecOpDispatch`] — the same refusal raised at
/// LOAD when the carrier is statically concrete and at the CALL when it is not, so
/// the two faces must not drift apart (the [`unselected_instance_message`] /
/// `macro_rejection_message` discipline).
///
/// `candidates` are pre-rendered by [`render_suppliers`], which names each by its
/// SUPPLY ROUTE because the three are written in three different syntaxes and the
/// author has to know which text to delete.
///
/// THE REPAIR VARIES AND IS THEREFORE PASSED, not inferred from the strings: the
/// first cut of this function asserted "no bracket at this site can choose between
/// them" unconditionally, which is true of a DEFAULTED op (no `Dispatch` slot to bind)
/// and FALSE of a body-less one whose rival is a witness sort — the one tie shape the
/// corpus actually drives (WI-842). See [`SupplierTieRepair`].
pub(crate) fn ambiguous_spec_op_dispatch_message(
    op: &str,
    carrier: &str,
    candidates: &[String],
    repair: SupplierTieRepair,
) -> String {
    let head = format!(
        "ambiguous dispatch of `{op}` on carrier `{carrier}`: {} implementations are \
         supplied for that carrier ({}) and nothing here selects one",
        candidates.len(),
        candidates.join(", "),
    );
    match repair {
        SupplierTieRepair::KeepOne => format!(
            "{head} — keep exactly one and delete the rest. No bracket names any of \
             them: a `[Spec = Witness]` bracket binds a body-less spec op's dispatch \
             slot to a PROVIDER, and here there is no such slot or no rival with a \
             name (a carrier's own member and an instance fact have none)"
        ),
        SupplierTieRepair::NameableWitness => format!(
            "{head} — keep exactly one and delete the rest, or route the call through \
             an operation that can write `[Spec = Witness]`: a witness sort among the \
             rivals IS nameable there, and this read is bracket-less, which is why it \
             has to refuse rather than pick"
        ),
    }
}

/// WI-1012 — render every candidate of a supplier tie by its SUPPLY ROUTE. The THIRD
/// construction of `AmbiguousSpecOpDispatch` (the typer's) made this a copy, which is
/// exactly what [`crate::eval::Interpreter::sole_supplier_by_value`]'s doc says the
/// shared body exists to prevent, so the rendering moved here rather than the doc's
/// claim being narrowed. `op_short` is the spec op's short name, so the fact leg can
/// echo the binding the author wrote (`describe = leafDescribe`).
pub(crate) fn render_suppliers(
    kb: &KnowledgeBase,
    candidates: &[SpecOpSupplier],
    op_short: &str,
) -> Vec<String> {
    candidates.iter().map(|c| c.render(kb, op_short)).collect()
}

/// WI-672 — sort identity by CANONICAL symbol: `a` and `b` name the same sort iff their
/// `canonical_sort_sym` agree. Differently-interned copies of one sort share a qualified
/// name, hence a canonical symbol, so this bridges them — but UNLIKE the deleted
/// `same_symbol` it does NOT bridge a bare/dotless name to the last segment of a
/// qualified one. Identity is by resolved symbol, never by last segment (spec §8.6), so
/// it de-conflates a top-level `sort Ring` from `anthill.prelude.algebra.Ring`. Short-
/// circuits on the exact `a == b` hit (the common case) before the two `qualified_name_of`
/// + map lookups. A sort's qualified name is always registered in `by_qualified_name`, so
/// for sorts `canonical_sort_sym` agreement is equivalent to `qualified_name_of` agreement
/// ([`same_qname`]) — the canonical form additionally normalizes to the index's canonical
/// copy, which is why sort sites use this rather than `same_qname`.
pub(crate) fn same_sort_canonical(kb: &KnowledgeBase, a: Symbol, b: Symbol) -> bool {
    a == b || kb.canonical_sort_sym(a) == kb.canonical_sort_sym(b)
}

/// Entity IDENTITY by QUALIFIED NAME (bridge #1): `a` and `b` name the same entity iff
/// they are the same symbol OR share a qualified name. This is exactly the deleted
/// `same_symbol` MINUS its bare-vs-last-segment bridge #2 — it bridges differently-
/// interned copies of one entity (same QN) but does NOT match a bare name to a qualified
/// one's last segment (spec §8.6: identity is by resolved symbol, never last segment).
/// Used for UNGATED non-sort entity identity — projection members in [`expr_carried_zeta`],
/// where two members are compared with no enclosing same-container scope to make a
/// short-name match sound, so identity is the right question. A member's qualified name
/// may NOT be registered in `by_qualified_name`; raw QN equality bridges interned copies
/// there unconditionally, whereas [`same_sort_canonical`]'s `canonical_sym` would fall
/// through to identity for an unregistered QN and miss a copy. (For a registered QN the
/// two agree.) Binding-key matching does NOT use this — it is scoped by a same-spec gate,
/// so it is a short-name lookup ([`same_label`]), consistent with `goal_binding_value`.
pub(super) fn same_qname(kb: &KnowledgeBase, a: Symbol, b: Symbol) -> bool {
    a == b || kb.qualified_name_of(a) == kb.qualified_name_of(b)
}

/// Resolve a WRITTEN or SCOPED name against a candidate set by SHORT NAME — the
/// legitimate short-name LOOKUP (spec §8.6, the same principle as constructor-pattern
/// resolution). Two families of caller:
///   1. a bare source-written identifier — a named-argument label, a record/tuple field
///      selector, or a scope variable — matched against a parameter, field, or binder
///      whose registered name may be qualified;
///   2. a type-param binding key matched WITHIN an already-established same-spec context
///      (`entries_cover` / `goals_equal`, each gated on the spec
///      sort first). The key may be bare `T` from one producer and qualified `Spec.T` from
///      another (the cross-producer divergence `goal_binding_value` documents), so it must
///      match by short name — and the same-spec gate makes short names unique, so this
///      cannot collide two specs' `T`.
/// Matching a bare name to the last segment of a qualified one is exactly name resolution
/// — NOT the unsound short-name comparison of two SORT identities (that is
/// [`same_sort_canonical`] / [`same_qname`], neither of which matches on last segment).
/// WI-672 split this out of `same_symbol` so short-name matching survives ONLY for name
/// resolution. The `debug_assert` catches the one misuse — two DISTINCT fully-qualified
/// names sharing a last segment (`A.x` vs `B.x`) — that would reintroduce that unsoundness.
pub(in crate::kb) fn same_label(kb: &KnowledgeBase, a: Symbol, b: Symbol) -> bool {
    if a == b {
        return true;
    }
    let aq = kb.qualified_name_of(a);
    let bq = kb.qualified_name_of(b);
    debug_assert!(
        !(aq != bq && aq.contains('.') && bq.contains('.') && short_name_of(aq) == short_name_of(bq)),
        "same_label matched two distinct qualified names by short name: {aq} vs {bq} — use same_qname/same_sort_canonical for identity"
    );
    short_name_of(aq) == short_name_of(bq)
}
