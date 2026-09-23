//! WI-224 — SLD-based instance synthesis: `SortGoal`, `resolve`, the resolution result,
//! and describing why a resolution failed.

use super::*;

// ── WI-224 — SLD-based instance synthesis ──────────────────────
//
// Replacement for the original single-shot `find_unique_impl_op`. Per
// `docs/design/operation-call-model.md` §"Resolution": instance
// synthesis is an SLD query over `SortProvidesInfo`. Each candidate's
// head may be a non-conditional fact (a "leaf" impl with no further
// requirements) or a conditional impl whose sort declares its own
// `requires` chain (the subgoals).
//
// `find_unique_impl_op` (kept as a thin compatibility wrapper) now
// delegates to `resolve`.

/// A goal in instance resolution: "find an impl that provides `spec_sort`
/// at the given bindings." Bindings keyed by the spec's short
/// parameter names (`T`, `State`, …) per the `SortView` convention.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SortGoal {
    pub spec_sort: Symbol,
    pub bindings: SmallVec<[(Symbol, TermId); 2]>,
    /// WI-350 — the receiver's concrete carrier, when the spec op has a
    /// *self-receiver* parameter (one declared with the spec sort itself, e.g.
    /// `head(s: Stream)`). For such specs the carrier is NOT a type parameter
    /// (Stream's only param `T` is the element), so the per-call `bindings` never
    /// pin which impl provides the op — every impl's universally-quantified `fact
    /// Stream[T]` matches, and a ≥2-impl spec would resolve `Ambiguous` for even a
    /// fully concrete call. The carrier (the receiver argument's base sort —
    /// `List`, `LogicalStream`) discriminates: `collect_provides_candidates`
    /// keeps only candidates whose `impl_sort` equals it. `None` for
    /// the common type-parameter-carrier specs (`Eq`/`Numeric`/`Iterable`,
    /// where the carrier IS a binding and dispatch is already pinned) and
    /// for transitive sub-goals — those resolve by binding alone.
    pub carrier: Option<GoalCarrier>,
}

/// WI-20260828-EKWDC — a dispatch goal's receiver carrier: its SORT, and the type
/// ARGUMENTS the receiver's own type wrote at that sort.
///
/// THE SORT ALONE WAS NOT ENOUGH, and the gap is silent. A carrier's `requires`
/// clause is written in the carrier's DECLARATION scope (`MappedStream requires
/// Iterable[C = Source, Element = Src, E = ES]`), and
/// [`candidate_provider_sub_goals`] instantiates it through the substitution the
/// PROVISION HEAD matched. A head that does not mention a parameter therefore leaves
/// it standing as a bare reference to the declaration's own param: `MappedStream
/// provides Stream[T = T, E = {ES, EF}]` names neither `Source` nor `Src`, so
/// `Stream.splitFirst(mapped(xs, inc))` asked for `Iterable[C = MappedStream.Source,
/// …]` — a goal about a parameter rather than about the receiver — and no provider
/// answers it. The receiver's type was FULLY GROUND at that point
/// (`MappedStream[Source = List[T = Int64], Src = Int64, …]`, which WI-20260828-BH1JZ
/// delivered); the dispatch simply could not see it, because a `Symbol` cannot carry
/// it.
///
/// The arguments ride IN THE GOAL, not beside it, for the reason WI-350 put the sort
/// there: the goal is the `resolve_cache` key. Two receivers of one carrier at
/// different arguments (`MappedStream` over a `List` and over an infinite `ZNats`)
/// now resolve their sub-goals differently, so sharing a memo entry would answer one
/// with the other's dictionary.
///
/// `args` is EMPTY when the receiver's type is a bare sort reference, and for the
/// carrier-PARAM shape (`describe(x: T)`), whose arguments are already the goal's own
/// binding for that param — [`statically_pinned_carrier`] says so at the arm that
/// builds one.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GoalCarrier {
    /// The carrier sort, canonical (`canonical_sort_sym`) — the candidate filter in
    /// [`collect_provides_candidates`] compares it against a canonicalized
    /// `impl_sort`.
    pub sort: Symbol,
    /// The receiver type's own arguments at `sort`, keyed by the parameter symbol the
    /// TYPE wrote. Joined to the impl's parameters by LOCAL NAME at the one consumer
    /// ([`carrier_arg_impl_subst`]) — within a single sort that join is exact, and it
    /// is the same join [`impl_param_symbols`] already makes.
    pub args: SmallVec<[(Symbol, TermId); 2]>,
}

impl GoalCarrier {
    /// A carrier whose arguments this route cannot see — see the type's own doc for
    /// the two callers that are in that position and why each is right. Public because
    /// a suite that drives [`dispatch_spec_op_cached`] directly is in exactly that
    /// position: it hands the dispatch a carrier symbol and no receiver value.
    pub fn bare(sort: Symbol) -> Self {
        GoalCarrier {
            sort,
            args: SmallVec::new(),
        }
    }
}

/// WI-350 — classification of a spec op's receiver at a call site,
/// driving carrier-aware dispatch. Computed by [`receiver_carrier`] from
/// the spec op's *self-receiver* parameter (the one declared with the
/// spec sort itself, e.g. `head(s: Stream)`) and that argument's actual
/// inferred type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReceiverCarrier {
    /// No self-receiver parameter — the op's carrier arguments are typed
    /// with the spec's own type-parameter (`PartialEq.eq(a: T, b: T)`,
    /// `Iterable.iterator(c: C)`). The carrier is a binding, so the
    /// per-call substitution already pins it; dispatch proceeds by
    /// binding (the pre-WI-350 behaviour, including legitimate `Ambiguous`
    /// for two impls at the same binding).
    NotApplicable,
    /// A self-receiver parameter exists and its argument's base sort IS
    /// the spec sort (`s : Stream[T = …]`) — an abstract spec value — or
    /// its type is still unresolved. No concrete impl is pinnable here;
    /// the call types through the spec op's interface signature and the
    /// impl is resolved at runtime from the value's own witness (or, if
    /// earlier `find_requires_location` matched, from a `requires` slot).
    Abstract,
    /// A self-receiver parameter exists and its argument has a concrete
    /// carrier sort (`s : List[Int]` → `List`). Dispatch keeps only the
    /// candidate whose `impl_sort` equals this carrier.
    ///
    /// WI-20260828-EKWDC — carries the receiver's own type ARGUMENTS as well as its
    /// sort. This is the one place they are read off the receiver argument, so it is
    /// the one place that can record them; see [`GoalCarrier`] for what goes wrong
    /// when only the sort travels.
    Concrete(GoalCarrier),
}

/// Context for `resolve` — the `requires` entries already in scope
/// (matched at scope_index `i` so the requirement-insertion pass can
/// emit `requirement_at_current(i)`).
///
/// WI-821: `sigma` is the call-site σ context when the resolution serves a
/// CALL-SITE dict build (`build_dep_projection` Strategy 3). The scope lookup
/// is wildcard-tolerant exactly like `entries_cover`, so without a gate an
/// abstract caller entry (`Desc[AT]`) covers a CONCRETE goal (`Desc[Pebble]`)
/// and short-circuits construction with the same wrong forward Strategy 1
/// was just gated out of. With `sigma` present a scope entry covers only on
/// σ-class agreement ([`requires_entry_covers_goal`]'s σ mode); `None` (every
/// other `resolve` consumer: bridges, dispatch leniency, diagnostics, tests)
/// keeps the coarse cover.
#[derive(Clone)]
pub struct ResolutionScope<'a> {
    pub available_requires: &'a [RequiresEntry],
    pub sigma: Option<&'a SigmaCtx<'a>>,
    /// WI-841 (058 §4.5) — the providers the CALL SITE explicitly selected, `f[Spec =
    /// W](…)`. Read by [`resolve`]'s **step 0** and by nothing else: at the TOP goal a
    /// matching selection restricts the candidate set to `W` and suppresses the scope
    /// (`FromScope`) lookup, because explicit outranks both searched and forwarded
    /// (§4.1 tier 1). Empty on every path with no bracket in hand — the compat
    /// dispatch wrappers, the req-insertion diagnostic build, the eval bridge.
    ///
    /// A selection deliberately does NOT reach sub-resolutions: rule (2)'s candidate
    /// set is the CALLEE's slots, and extending it into the tree would make key
    /// resolution depend on which witness was pinned (pinning changes which subgoals
    /// exist). Steering a sub-resolution is written instead as a type application of
    /// the witness — `fold[Monoid = ListM[O = MyEq]]` — where the selection happens at
    /// the witness's own boundary, as a callee slot again.
    pub selected: &'a [InstanceSelection],
    /// WI-20260918-CKD4J — the enclosing OPERATION's own `requires` (the op half of its
    /// frame chain, [`DictChain::op_entries`]), consulted for SUB-goals only: a
    /// conditional provision's `:- goals` below the goal the call made. A match is
    /// `FromScope` at `available_requires.len() + j`, i.e. an index into the FRAME
    /// chain, so it is set only where the tree is named against that chain.
    ///
    /// NOT for the call's own goal, and that is WI-822 LEG 1's decision, not an
    /// omission: an op-scoped requirement serves the call's own spec by value-directed
    /// dispatch, and widening the top-level lookup flipped 30 working dispatches to an
    /// unbound slot. A sub-goal has no value to direct it — `eq(a, b)` over
    /// `Pair[A = X, B = X]` reaches `PartialEq[X]` only as `Pair`'s condition — so
    /// without this `requires PartialEq[X]` on the operation was invisible to it and
    /// the call was refused while the sort-level spelling of the same program loaded.
    pub sub_goal_requires: &'a [RequiresEntry],
}

/// The synthesized resolution chain. Returned to the requirement-
/// insertion pass which emits the IR (the `Dictionary` node /
/// `requirement_at_current` / projections) per node.
#[derive(Clone, Debug)]
pub enum ResolvedRequiresNode {
    /// Non-conditional impl. `impl_sort` is the carrier sort symbol
    /// (e.g., `IntEq`), `bindings` is the head's per-binding values
    /// after impl-param substitution.
    Leaf {
        impl_sort: Symbol,
        spec_sort: Symbol,
        bindings: SmallVec<[(Symbol, TermId); 2]>,
    },
    /// Conditional impl: head matched + sub_resolutions resolved.
    Conditional {
        impl_sort: Symbol,
        spec_sort: Symbol,
        bindings: SmallVec<[(Symbol, TermId); 2]>,
        sub_resolutions: Vec<ResolvedRequiresNode>,
    },
    /// Matched an entry in `scope.available_requires`. No new
    /// construction needed — the caller's `frame.requirements[slot]`
    /// already holds the right requirement value.
    FromScope {
        scope_index: usize,
        spec_sort: Symbol,
        /// WI-20260918-CKD4J — the path INTO the slot's dictionary, empty when the slot
        /// itself answers. `[k]` when the slot's spec reaches the goal's through its OWN
        /// chain — `requires Eq[X]` answering `PartialEq[X]` through `Eq provides
        /// PartialEq[T = T]` (WI-1110's conversion): the evidence is sub-slot `k` of the
        /// `Eq` dictionary, the same projection `build_dep_projection`'s Strategy 2 emits.
        projection: SmallVec<[usize; 2]>,
    },
    /// WI-857 — a SPEC-HALF slot ([`DictLayout`]) whose goal did not resolve:
    /// no provider at these bindings, a tie, or a cycle. Recorded rather than
    /// propagated, because the slot must exist for the halves to stay
    /// positionally exact, and because the spec's own `requires` is often
    /// satisfied only LOOSELY — `check_provider_requires` falls back to a
    /// base-level existence check when σ leaves a binding abstract, and the
    /// stdlib relies on that: `FiniteCollection requires Iterable[C = C]` holds
    /// for a `List` carrier only through `List provides Stream provides
    /// Iterable`, which no `Iterable[C = List[…]]` provision matches. Refusing
    /// to build the dictionary there would reject every program that dispatches
    /// such a spec op without ever reading the evidence (MEASURED: 33 tests).
    ///
    /// So the absence is CARRIED, and every attempt to USE it is loud — eval
    /// refuses to dispatch through the marker functor
    /// ([`absence_marker_sym`]). A slot nobody reads costs nothing; a slot
    /// somebody reads names the requirement that has no provider.
    ///
    /// WI-865 — and it names WHY. Placement is still uniform across every failure
    /// kind (that is what the paragraphs above are about); `why` rides ALONGSIDE so
    /// the refusal at the read can distinguish what the placement rule deliberately
    /// does not. Without it a two-provider tie inside a spec half reported as "no
    /// provider" — the attribution regression against WI-843 that WI-865 closes.
    Unavailable {
        spec_sort: Symbol,
        why: UnavailableWhy,
        /// [`ResolutionResult::is_forwarded`] — whether what failed is a goal BENEATH
        /// this slot. Not derivable from `spec_sort` and `why`'s goal; see
        /// [`AbsenceRecord::Slot`].
        below: bool,
    },
}

impl ResolvedRequiresNode {
    /// The spec sort this tree resolves (for diagnostics / WI-226).
    pub fn spec_sort(&self) -> Symbol {
        match self {
            ResolvedRequiresNode::Leaf { spec_sort, .. }
            | ResolvedRequiresNode::Conditional { spec_sort, .. }
            | ResolvedRequiresNode::FromScope { spec_sort, .. }
            | ResolvedRequiresNode::Unavailable { spec_sort, .. } => *spec_sort,
        }
    }

    /// The impl carrier sort. `None` for `FromScope` — no specific
    /// impl is pinned; the runtime reads the slot's bundled handle.
    pub fn impl_sort(&self) -> Option<Symbol> {
        match self {
            ResolvedRequiresNode::Leaf { impl_sort, .. }
            | ResolvedRequiresNode::Conditional { impl_sort, .. } => Some(*impl_sort),
            // Neither pins an impl: `FromScope` reads the caller's slot, and
            // `Unavailable` has none to pin (WI-857).
            ResolvedRequiresNode::FromScope { .. } | ResolvedRequiresNode::Unavailable { .. } => {
                None
            }
        }
    }
}

/// Outcome of `resolve`. The error variants carry enough context to
/// produce a user diagnostic (NoMatch / Ambiguous / Cyclic).
#[derive(Clone, Debug)]
pub enum ResolutionResult {
    Resolved(ResolvedRequiresNode),
    /// No candidate's head unifies with the goal.
    ///
    /// WI-865: `spec` is `goal.spec_sort` at the level that failed — the SYMBOL
    /// beside the rendered `goal_text`, for a reader that must relate the failure to
    /// another goal rather than print it. `resolve_inner` returns a provider-half
    /// sub-goal's failure VERBATIM, so a caller several levels up receives a failure
    /// about a goal that is not its own, and only this field says which. The
    /// `Ambiguous` arm has carried the same coordinate since WI-843
    /// ([`InstanceTie::spec`], for exactly that reason); this makes the three arms
    /// uniform. NOT redundant with `goal_text`, which is a rendering (bindings
    /// included) and cannot be compared to a spec.
    NoMatch {
        goal_text: String,
        hint: String,
        spec: Symbol,
        forwarded: bool,
    },
    /// Multiple candidates match and specificity coherence couldn't
    /// pick a unique winner. WI-843: the colliding carriers ride as an
    /// [`InstanceTie`] — by SYMBOL, and stamped with the spec of THIS level's
    /// goal, because a sub-goal's tie is propagated verbatim to the caller.
    Ambiguous {
        goal_text: String,
        tie: InstanceTie,
        forwarded: bool,
    },
    /// Detected a cycle in conditional-instance resolution. `path` is
    /// the goal stack at the point the cycle was detected.
    ///
    /// WI-865: `spec` is the repeated goal's own — `path`'s last entry as a SYMBOL —
    /// for the same reason [`Self::NoMatch`]'s is.
    Cyclic {
        path: Vec<String>,
        spec: Symbol,
        forwarded: bool,
    },
}

impl ResolutionResult {
    /// WI-865 — mark a FAILURE as being about a goal BELOW the one its receiver asked
    /// for, and answer that question back.
    ///
    /// `resolve_inner` returns a provider-half sub-goal's failure VERBATIM (WI-869:
    /// "the goal it names is the unmet CONDITION, which is the only thing that
    /// explains the refusal"), so a caller receiving a failure is not necessarily
    /// being told about the goal it asked for. Nothing else answers this:
    ///
    ///  * the SPEC cannot — `provides Base[T = Wrap[E]]` beside `requires Base[T =
    ///    Bool]` fails one level down on the SAME spec, and gating on spec identity
    ///    reports "nothing provides `Base` at the bindings this dictionary was built
    ///    for" about a carrier that provides exactly that (MEASURED —
    ///    `wi865_absence_reason_test::a_failure_below_the_slot_on_the_same_spec…`);
    ///  * the BINDINGS could, but they live only in the rendered `goal_text`, and
    ///    [`UnavailableWhy`] says why a rendering must not enter the record.
    ///
    /// A single bit set at a single site, so there is no per-arm rule to get wrong,
    /// and it composes: a twice-forwarded failure stays marked.
    ///
    /// `Resolved` is not a failure and has nothing to forward — it is returned by the
    /// arm above the one that calls this, never through it.
    pub(super) fn forwarded(self) -> Self {
        match self {
            ResolutionResult::NoMatch {
                goal_text,
                hint,
                spec,
                ..
            } => ResolutionResult::NoMatch {
                goal_text,
                hint,
                spec,
                forwarded: true,
            },
            ResolutionResult::Ambiguous { goal_text, tie, .. } => ResolutionResult::Ambiguous {
                goal_text,
                tie,
                forwarded: true,
            },
            ResolutionResult::Cyclic { path, spec, .. } => ResolutionResult::Cyclic {
                path,
                spec,
                forwarded: true,
            },
            resolved @ ResolutionResult::Resolved(_) => resolved,
        }
    }

    /// WI-456 — [`Self::forwarded`], plus the NAMED SLOT this sub-goal was filling.
    ///
    /// One method rather than two calls because the two facts are recorded at the same
    /// place for the same reason: the frame below is the only one that knows either.
    /// `slot` is stamped ONLY into an as-yet-unstamped [`InstanceTie`] and touches
    /// nothing else, so every non-tie failure passes through exactly as `forwarded` left
    /// it. The caller has already decided it OWNS the tie (`!is_forwarded()`), which
    /// makes the `or` unreachable rather than load-bearing — kept because "a stamp never
    /// overwrites a stamp" is the property, and a second caller would have to earn it.
    fn stamped_slot(self, slot: Option<TieSlot>) -> Self {
        match (self.forwarded(), slot) {
            (
                ResolutionResult::Ambiguous {
                    goal_text,
                    mut tie,
                    forwarded,
                },
                Some(s),
            ) => {
                // ONE gate, at the caller (`!is_forwarded()`). This is not a second
                // one: it fails a future caller that skips that test rather than
                // quietly preferring the first stamp, which is how the mis-attribution
                // `a_tie_below_a_named_slot_is_not_attributed_to_that_slot` catches
                // would come back.
                debug_assert!(
                    tie.slot.is_none(),
                    "a tie is stamped by the frame that OWNS it, and only once",
                );
                tie.slot = Some(s);
                ResolutionResult::Ambiguous {
                    goal_text,
                    tie,
                    forwarded,
                }
            }
            (other, _) => other,
        }
    }

    /// Whether this failure came back from a SUB-goal — see [`Self::forwarded`].
    /// `false` for `Resolved`, which is about the goal it resolved.
    pub(super) fn is_forwarded(&self) -> bool {
        match self {
            ResolutionResult::NoMatch { forwarded, .. }
            | ResolutionResult::Ambiguous { forwarded, .. }
            | ResolutionResult::Cyclic { forwarded, .. } => *forwarded,
            ResolutionResult::Resolved(_) => false,
        }
    }
}

/// WI-861 — may 058 §3.2's RUNG 2a answer this goal's tie?
///
/// **THE DISTINCTION IS §3.4's, AND IT IS MEASURED.** A default fills SILENCE: nowhere
/// in the program did anyone say which provider, so the language may. A NAMED
/// requirement slot is not silence — it is a TYPE PARAMETER, and its value is part of
/// the type's identity. A signature that omits it (`size(s: SortedSet[T = String])`)
/// means ANY, so the value flowing in ALREADY CHOSE and carries its choice; picking a
/// default there does not fill a gap, it overrides a decision that was made elsewhere.
///
/// MEASURED, on `SortedSet[T = Int64, O = Descending]` built at one site and inserted
/// into through a signature that erases `O` (scratch probe, this ticket): the erased
/// route inserts with `Int64`'s OWN ascending order and reads back `3` where the
/// slot-keeping route reads `7`. Rung 2a would have made exactly that program load.
///
/// **AND WHY WITHHOLDING IS NOT A CONTRADICTION OF §3.4's OTHER HALF** ("omitting it at
/// a call leaves it to inference"): inference there must BIND the slot — the result of
/// `SortedSet.empty[T = String]()` would have to be typed `SortedSet[T = String, O =
/// <chosen>]`. Rung 2a fills a DICTIONARY and writes nothing into the type, so it cannot
/// express that inference; a value whose type says "any O" and whose dictionary says
/// `String` is the mismatch the measurement above produced. Named-slot inference is a
/// separate increment — **WI-1094**.
///
/// The one-provider case is UNCHANGED and still silently constructs (measured: the same
/// erasing program over a carrier with a single `Ord` provider loads clean today). That
/// is the pre-existing half of the same hazard, it is not this ticket's to widen or to
/// close, and **WI-1094** owns it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DefaultRung {
    /// The goal is an UNSELECTED dispatch, or an ANONYMOUS `requires` slot — which
    /// "fixes nothing about the type" (§3.4), so no value carries a competing choice.
    Consult,
    /// The goal fills a NAMED requirement slot whose binding is not in hand.
    Withhold,
}

/// WI-861 — [`DefaultRung`] for one dependency of `owner`'s requirement chain.
///
/// BY SPEC, not by chain index. The index would be exact — `NamedRequirementSlot::slot`
/// IS the dictionary-chain index ([`dict_chain_index_of_named_slot`] states that
/// identity) — but every caller here iterates a chain it built for its own purpose, and
/// WI-857's dual lesson is that a positional channel with four producers grows four
/// plausible indexings. Matching on the SPEC needs no shared convention and errs toward
/// `Withhold`, which is the direction that refuses rather than answers: it over-fires
/// only for an owner declaring a named AND an anonymous slot of ONE spec.
///
/// **RE-EXAMINED AT WI-1094 AND KEPT, with a narrower job.** That ticket gave the named
/// slot its own mechanism — [`infer_named_slot_bindings`] answers a still-FLEX binder at
/// the CALL SITE by writing the ladder's answer into the TYPE, and refuses an ERASED one
/// outright — so the two cases this gate was carrying at WI-861 no longer reach it. What
/// still does is the SUB-GOAL recursion below: `resolve_inner` re-derives the rung for the
/// CHOSEN PROVIDER's own named slots (`LexFst requires OA: Ord[A]`), one level inside a
/// resolution tree, where no call site exists to infer at. MEASURED: backing this out cost
/// 4 tests at WI-861 and costs **2** now, both `wi870`, both that recursion. (WI-456: a
/// slot the provider's CARRIER binds to a witness is pinned before this gate matters —
/// [`carried_slot`]; the gate governs the slots nothing wrote.)
///
/// COST: one `HashMap<Symbol, _>` probe per dep, and `named_requirement_slots` answers
/// `&[]` for every owner that declares none — which is nearly all of them, so the
/// `same_sort_canonical` walk (a qualified-name compare) is not on the common path. It is
/// asked per sub-goal inside `resolve_inner`'s recursion and deliberately not hoisted:
/// the loop takes `&mut kb`, so keeping the slice across it would need a clone of a list
/// that is empty in the case worth optimizing for.
pub(super) fn rung_for_dep(kb: &KnowledgeBase, owner: Symbol, dep_spec: Symbol) -> DefaultRung {
    let named = kb.named_requirement_slots(owner).iter().any(|s| {
        s.spec_base
            .is_some_and(|b| same_sort_canonical(kb, b, dep_spec))
    });
    if named {
        DefaultRung::Withhold
    } else {
        DefaultRung::Consult
    }
}

/// Public entry point — instance synthesis for `goal` in `scope`.
/// Takes a mutable KB because conditional resolution allocates
/// freshly-substituted subgoal terms (impl-param `Ref(EqList.A)`
/// replaced by the matched per-call value) for the recursive
/// resolution step.
///
/// WI-861: 058 §3.2's rung 2a APPLIES — this entry point is the DISPATCH's, where a tie
/// is exactly the silence a default fills. A caller building a requirement dictionary
/// for a named slot asks [`resolve_with_rung`] instead.
pub fn resolve(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    scope: &ResolutionScope,
) -> ResolutionResult {
    resolve_with_rung(kb, goal, scope, DefaultRung::Consult)
}

/// [`resolve`] with 058 §3.2's rung 2a explicitly enabled or withheld — see
/// [`DefaultRung`] for which goals may take a default and why the named-slot half may
/// not.
pub fn resolve_with_rung(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    scope: &ResolutionScope,
    rung: DefaultRung,
) -> ResolutionResult {
    let mut stack: Vec<SortGoal> = Vec::new();
    resolve_inner(kb, goal, scope, &mut stack, None, None, rung)
}

pub(super) fn resolve_inner<'a>(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    scope: &ResolutionScope<'a>,
    stack: &mut Vec<SortGoal>,
    // WI-857 — the provider whose dictionary this goal is a sub-requirement OF, when
    // it is one (`None` at the goal the call made). The LOCALITY rule: a sub-goal
    // that provider itself provides resolves to its OWN provision before any global
    // search. The IMMEDIATELY enclosing provider only — one level down, the sub-goal's
    // own chosen provider takes over, which is what makes locality compose.
    local_provider: Option<Symbol>,
    // WI-870 (058 §3.3) — the binding a bracket VALUE wrote for THIS sub-goal's slot,
    // when this goal is a named slot of the provider one level up and the call named
    // it: `[Ord = ListOrd[OE = LexFst]]`. `None` at the call's own goal (where
    // `scope.selected` answers instead) and at every slot the value left unwritten.
    //
    // The whole `SlotSelection` rather than its witness, because the REFUSAL has to
    // name the slot: "provides no instance at these bindings" is unactionable when the
    // author's text was `OE = LexFst` and the goal rendered is `Ord[T = Int64]`.
    //
    // WI-456 — or the binding the provider's CARRIER wrote for the slot, read out of the
    // provision match by [`carried_slot`]; the source words the refusal.
    slot_pin: Option<(&SlotSelection, SlotPinSource)>,
    // WI-861 (058 §3.2 rung 2a) — may a DEFAULT answer this goal's tie? Carried per goal
    // rather than on the scope because it is a property of the SLOT this goal fills, and
    // the recursion re-derives it per sub-goal from the CHOSEN PROVIDER's own declaration
    // ([`rung_for_dep`]) — a witness's named element slots are named slots too, and a
    // bracket-less call into one is the same erased binding one level down.
    rung: DefaultRung,
) -> ResolutionResult {
    // WI-20260921-28TAT — A REFINEMENT GOAL IS ALREADY DISCHARGED, and asking the
    // provider search about it can only fail. `sort Narrow requires Boom` names a DATA
    // sort — no type parameter, so nothing can `provides` it and no member could be
    // reached through a slot held for it — and the clause declares `Narrow <: Boom`
    // rather than demanding a dictionary ([`clause_is_dispatchable`]). Reaching the
    // search, it produced "no impl provides test.reify.Boom; declare `provides
    // test.reify.Boom[…]`", advice no author can act on, and it made EVERY derived
    // instance of a refinement sort unresolvable: `TypeValue[T = Narrow]` failed on it,
    // and `Narrow provides Eq` would have failed identically.
    //
    // A LEAF ROOTED AT THE SORT ITSELF, not a skip: this walk is positional (it produces
    // the dictionary's spec half), so the slot must stay exactly where the chain indexes
    // it. Same shape and same reason as the `EffectsRuntime` kind-anchor's leaf — "there
    // is nothing to resolve, and the slot the `DictLayout` halves count is present and
    // positionally exact". Nothing dispatches through it, so nothing reads it.
    //
    // ONE SITE, NOT THREE, AND THAT IS MEASURED. The anchor beside it is exempted at two
    // OTHER sites as well (`build_dep_projection` and the resolved-tree builder), and
    // mirroring it there looked like the consistent thing to do. It is not needed:
    // backed out of both, the whole `wi_tests` suite is 4826/0 — every refinement clause
    // reaches the resolver, so this is where it belongs and the other two would have
    // been dead code carrying a confident comment. The anchor needs its own two because
    // it is SYNTHESIZED into chains those sites build directly (WI-857); a refinement
    // clause is written by an author and only ever arrives here, as a goal.
    if !clause_is_dispatchable(kb, goal.spec_sort) {
        return ResolutionResult::Resolved(ResolvedRequiresNode::Leaf {
            impl_sort: goal.spec_sort,
            spec_sort: goal.spec_sort,
            bindings: SmallVec::new(),
        });
    }
    // WI-841 (058 §4.5) — STEP 0. `stack.is_empty()` is exactly "this is the goal the
    // CALL made", so a selection reaches the call's own goal and no sub-goal: a
    // conditional witness still resolves its `:-` subgoals by SEARCH (tier 2), which
    // is what keeps a bracket key from depending on which witness was pinned.
    // WI-843 reuses this exact test for the tie diagnostic (see `InstanceTie`): "the
    // goal the CALL made" is also the only level a call-site bracket can steer.
    //
    // WI-870 — and a sub-goal is steered ONLY by a slot binding written on the
    // provider that owns it, which is the same rule seen from the other side: a
    // spec-keyed bracket entry still reaches exactly one level, and the composition
    // is written as a type application of the witness, resolved at the witness's own
    // boundary. So the two sources are exclusive by construction, not by precedence.
    let at_call_goal = stack.is_empty();
    let pin: Option<&InstanceSelection> = if at_call_goal {
        pinned_selection_for(kb, scope.selected, goal.spec_sort)
    } else {
        slot_pin.map(|(s, _)| &s.selection)
    };
    let pinned = pin.map(|s| s.witness);

    // Steps 1–4 are untouched — except that a PINNED goal skips the scope lookup:
    // explicit beats forwarded as well as searched (§4.1 tier 1), and returning
    // `FromScope` here would hand back the caller's dictionary and lose the pin.
    // WI-841: a pinned goal consults NO scope entry, so the invariant is expressed by
    // what is iterated rather than by a test inside the loop.
    let scope_entries: &[RequiresEntry] = if pinned.is_some() {
        &[]
    } else {
        scope.available_requires
    };
    for (i, ar) in scope_entries.iter().enumerate() {
        if ar.required_sort != goal.spec_sort {
            continue;
        }
        // WI-821: with a call-site σ in hand, a scope entry covers only on
        // σ-class agreement — the coarse wildcard cover alone would hand a
        // concrete or re-instantiated goal back to the caller's dictionary,
        // re-creating the forward the Strategy-1 gate just refused. The
        // agreeing case (a sub-goal over the SAME param, e.g. the conditional
        // WrapDesc's `Desc[E := GT]`) still resolves FromScope.
        if requires_entry_covers_goal(kb, ar, goal, scope.sigma) {
            return ResolutionResult::Resolved(ResolvedRequiresNode::FromScope {
                scope_index: i,
                spec_sort: goal.spec_sort,
                projection: SmallVec::new(),
            });
        }
    }
    // WI-20260918-CKD4J — a SUB-goal may also be answered by the enclosing operation's
    // own `requires`, at its frame-chain index. See [`ResolutionScope::sub_goal_requires`]
    // for why the call's own goal may not. Behind the sort half, so a sort-level entry
    // that covers keeps its slot.
    if !at_call_goal && pinned.is_none() {
        let base = scope.available_requires.len();
        for (j, ar) in scope.sub_goal_requires.iter().enumerate() {
            if ar.required_sort == goal.spec_sort
                && requires_entry_covers_goal(kb, ar, goal, scope.sigma)
            {
                return ResolutionResult::Resolved(ResolvedRequiresNode::FromScope {
                    scope_index: base + j,
                    spec_sort: goal.spec_sort,
                    projection: SmallVec::new(),
                });
            }
        }
        // WI-20260918-CKD4J — THROUGH a scope entry's own chain, one level: `requires
        // Eq[X]` answers a `PartialEq[X]` sub-goal, because `Eq provides PartialEq[T =
        // T]` puts `PartialEq` in `Eq`'s chain and so in every `Eq` dictionary. The
        // call's OWN goal already reached this through `find_requires_location`; a
        // conditional provision's SUB-goal (`Pair`'s `PartialEq[A]` under `eq(a, b)`)
        // had only the direct cover above, so `requires Eq[X]` was refused where
        // `requires PartialEq[X]` loaded. Tried AFTER every direct cover, so a slot of
        // the goal's own spec still wins. Each sub-entry is compared COMPOSED into the
        // caller's scope through the slot's bindings (`Eq[T = X]`'s chain entry
        // `PartialEq[T = Eq.T]` becomes `PartialEq[T = X]`) — Strategy 2's composition.
        let all: Vec<RequiresEntry> = scope
            .available_requires
            .iter()
            .chain(scope.sub_goal_requires.iter())
            .cloned()
            .collect();
        for (i, ar) in all.iter().enumerate() {
            let chain = direct_requires_chain_rc(kb, ar.required_sort);
            if !chain.iter().any(|e| e.required_sort == goal.spec_sort) {
                continue;
            }
            let map = build_child_subst_map(kb, ar);
            for (k, sub) in chain.iter().enumerate() {
                if sub.required_sort != goal.spec_sort {
                    continue;
                }
                let composed = RequiresEntry {
                    required_sort: sub.required_sort,
                    spec: substitute_in_spec(kb, &sub.spec, &map),
                    supply: sub.supply,
                };
                if requires_entry_covers_goal(kb, &composed, goal, scope.sigma) {
                    return ResolutionResult::Resolved(ResolvedRequiresNode::FromScope {
                        scope_index: i,
                        spec_sort: goal.spec_sort,
                        projection: SmallVec::from_elem(k, 1),
                    });
                }
            }
        }
    }

    if stack.iter().any(|g| goals_equal(kb, g, goal)) {
        let mut path: Vec<String> = stack.iter().map(|g| format_goal(kb, g)).collect();
        path.push(format_goal(kb, goal));
        return ResolutionResult::Cyclic {
            path,
            spec: goal.spec_sort,
            forwarded: false,
        };
    }
    stack.push(goal.clone());

    // WI-827: the same call-site σ that gates the scope `FromScope` lookup
    // above rides into candidate matching, so a per-call element's rigid /
    // wildcard / concrete role is classified once, spelling-neutrally, rather
    // than by the head-only `Var::Rigid` test. `None` (the `resolve_at_goal`
    // dispatch/diagnostic path) keeps today's behaviour.
    let mut candidates = collect_provides_candidates(kb, goal, scope.sigma);

    // WI-841 STEP 0, second half: restrict the goal's OWN candidate set to the pinned
    // witness. Filtering rather than short-circuiting is what makes a CONDITIONAL
    // witness work unchanged — its `:-` subgoals are still walked below, and still
    // searched. It is also the binding-precise half of §4.4 check 1: the site check
    // asked only "does W provide this spec"; here the candidate's head has been
    // matched against THIS goal's bindings, so a witness that provides the spec at
    // other bindings empties the set and the goal fails loudly.
    if let Some(witness) = pinned {
        candidates.retain(|c| same_sort_canonical(kb, c.impl_sort, witness));
        if candidates.is_empty() {
            stack.pop();
            // WI-870: the SAME refusal at two levels, worded from the text the author
            // wrote. The outer pin names a spec key; a slot pin names a slot of a
            // witness, and reporting it as "the call selected W" would send the author
            // looking at the bracket's key instead of at its value.
            let hint = match slot_pin {
                Some((s, source)) => format!(
                    "{} slot `{}` of `{}` to `{}`, which provides no {} instance at these \
                     bindings",
                    match source {
                        SlotPinSource::Bracket => "the call bound",
                        SlotPinSource::Carrier => "the carrier's type binds",
                    },
                    kb.local_name_of(s.binder),
                    kb.qualified_name_of(s.owner),
                    kb.qualified_name_of(witness),
                    kb.qualified_name_of(goal.spec_sort),
                ),
                None => format!(
                    "the call selected `{}` for {}, which provides no instance at these \
                     bindings",
                    kb.qualified_name_of(witness),
                    kb.qualified_name_of(goal.spec_sort),
                ),
            };
            return ResolutionResult::NoMatch {
                goal_text: format_goal(kb, goal),
                hint,
                spec: goal.spec_sort,
                forwarded: false,
            };
        }
    }

    // WI-857 LOCALITY (058 §3.8): inside provider `W`'s dictionary, a sub-goal `W`
    // itself provides IS `W`'s — its own provision beats every rival. A filter, like
    // step 0's pin, so the head has already been matched against THIS sub-goal's
    // bindings: a `W` that provides the spec only at OTHER bindings contributes no
    // candidate here and the search proceeds globally, rather than being narrowed to
    // an instance that does not fit.
    if let Some(w) = local_provider {
        // Canonicalize `w` ONCE, not once per candidate per pass.
        let w_canon = kb.canonical_sort_sym(w);
        let is_w =
            |c: &Candidate| c.impl_sort == w || kb.canonical_sort_sym(c.impl_sort) == w_canon;
        if candidates.iter().any(&is_w) {
            candidates.retain(&is_w);
        }
    }

    if candidates.is_empty() {
        stack.pop();
        return ResolutionResult::NoMatch {
            goal_text: format_goal(kb, goal),
            // `provides`, not `fact`: WI-20260917-S8JYF retired `fact Spec[…]` as a
            // provision, so advising it sent the author back to this same `NoMatch`.
            hint: format!(
                "no impl provides {0}; declare `provides {0}[…]` on the carrier or on a \
                 witness sort, or add `requires {0}[…]` in scope",
                kb.qualified_name_of(goal.spec_sort)
            ),
            spec: goal.spec_sort,
            forwarded: false,
        };
    }

    // WI-861 (058 §3.2 RUNG 2a): specificity FIRST, the default only at its tie. The
    // order is the rule — "a strictly-more-specific candidate wins silently; a default is
    // a fallback, not a competitor" — and writing it as a fallback of this `match` is what
    // makes it unstateable the other way round. `rung` is [`DefaultRung::Withhold`] where
    // the goal fills a NAMED slot, which is not silence at all.
    let chosen = match pick_most_specific(kb, &candidates).or_else(|| {
        (rung == DefaultRung::Consult)
            .then(|| default_among_candidates(kb, goal, &candidates))
            .flatten()
    }) {
        Some(idx) => &candidates[idx],
        None => {
            stack.pop();
            // WI-843: `at_call_goal` is the SAME test step 0 used above, captured
            // before the push — a tie under a conditional witness's `:-` subgoal is
            // propagated verbatim to the caller, and no bracket there can reach it.
            let candidates = candidates.iter().map(|c| c.impl_sort).collect();
            return ResolutionResult::Ambiguous {
                goal_text: format_goal(kb, goal),
                tie: InstanceTie {
                    spec: goal.spec_sort,
                    candidates,
                    at_call_goal,
                    // WI-456 — stamped by the level that OWNS the slot, on the way out
                    // (the `err` arm of the sub-goal loop below); this level is the
                    // tie's own and knows only that it tied.
                    slot: None,
                },
                forwarded: false,
            };
        }
    };

    // Save chosen's data before recursing: `resolve_inner` takes &mut kb
    // (it allocates substituted subgoal terms) and `chosen` borrows
    // `candidates` immutably; cloning out releases that borrow.
    let chosen_impl_sort = chosen.impl_sort;
    let chosen_bindings = chosen.resolved_head_bindings.clone();
    let chosen_impl_subst = chosen.impl_subst.clone();
    drop(candidates);

    // WI-857/WI-866 — the producer/consumer contract is asserted INSIDE
    // `dict_sub_goals` now, against the layout it actually built, so this list cannot
    // reach the loop below disagreeing with what `dict_layout` counts. It CAUGHT the
    // last violation while it lived here: the `EffectsRuntime` anchor was dropped from
    // the provider half while the layout counted it (144 dictionaries across the
    // suite), which the green suite hid because none of those dictionaries reached a
    // frame push.
    let DictSubGoals {
        goals: sub_goals,
        provider_half_start,
    } = dict_sub_goals(
        kb,
        goal,
        chosen_impl_sort,
        &chosen_impl_subst,
        &chosen_bindings,
    );
    // The pin's own slot selections, and who wrote them: at the call's goal a bracket; one
    // level in, whoever wrote the pin that got us here — a carrier's nested selection is
    // still the carrier's.
    let written_slots: &[SlotSelection] = pin.map_or(&[], |p| &p.slots);
    let written_source = match slot_pin {
        Some((_, source)) if !at_call_goal => source,
        _ => SlotPinSource::Bracket,
    };
    let mut sub_resolutions: Vec<ResolvedRequiresNode> = Vec::with_capacity(sub_goals.len());
    let anchor = effects_runtime_sym(kb);
    for (i, sg) in sub_goals.iter().enumerate() {
        // WI-857: the `EffectsRuntime` kind-anchor occupies its slot as a STRUCTURAL
        // LEAF, never resolved — see [`effects_runtime_sym`]. Byte-identical to what
        // `build_dep_projection` emits for the same anchor, so the two dictionary
        // producers agree.
        //
        // A `Leaf` over the anchor sort, NOT the `Unavailable` marker, and the
        // difference is the point: the anchor IS satisfied — structurally, by the
        // effect-row machinery — and names a real sort a body can read
        // (`var_ref(__req_effectsruntime)` in a cross-sort delegating body), whereas
        // `Unavailable` records that nothing satisfies the slot at all and is refused
        // at any use. Two encodings because there are two facts.
        if anchor.is_some_and(|er| same_sort_canonical(kb, sg.spec_sort, er)) {
            sub_resolutions.push(ResolvedRequiresNode::Leaf {
                impl_sort: sg.spec_sort,
                spec_sort: sg.spec_sort,
                bindings: SmallVec::new(),
            });
            continue;
        }
        // WI-857, the LOCALITY rule (058 §3.8): the sub-goals of `chosen_impl_sort`'s
        // dictionary see that provider FIRST. Once the spec half is bundled (see
        // `dict_sub_goals`), a bundled witness — the only lawful form of an
        // alternative ordering, since `Ord`'s inherited `gt`/`lt` are derived
        // from `compare` and a lone witness's dictionary would contradict itself —
        // provides both `Ord[C]` and `PartialOrd[C]`, so `PartialOrd[C]` has one
        // candidate inside EACH of two coexisting witnesses' chains and a global
        // search ties. The only right answer is witness-local. It depends on the
        // SELECTED provider and never on caller scope, so it introduces no
        // import-coupling.
        //
        // WI-456 — and what the CARRIER's type says about the slot, when it is one of the
        // chosen provider's named slots ([`carried_slot`]).
        let written = slot_pin_at(written_slots, i, provider_half_start);
        let named = i
            .checked_sub(provider_half_start)
            .and_then(|j| named_slot_at(kb, chosen_impl_sort, j));
        let frame = FrameEntries {
            head: scope.available_requires,
            tail: scope.sub_goal_requires,
        };
        let carried = named.map(|slot| {
            carried_slot(
                kb,
                chosen_impl_sort,
                slot,
                &chosen_impl_subst,
                scope.sigma,
                frame,
            )
        });
        let refuse = |kb: &mut KnowledgeBase, stack: &mut Vec<SortGoal>, hint: String| {
            stack.pop();
            ResolutionResult::NoMatch {
                goal_text: format_goal(kb, goal),
                hint,
                spec: goal.spec_sort,
                forwarded: false,
            }
        };
        let binder_name = |kb: &KnowledgeBase| {
            named.map_or(String::new(), |s| kb.local_name_of(s.binder).to_string())
        };
        // WI-20260923-WN9P8 — A FORWARD IS ANSWERED FROM ITS PARAMETER'S OWN SLOT, and is
        // never searched: the scope's spec-keyed lookup below would take any entry that
        // covers the goal. A slot binding a bracket VALUE wrote (`written`) still
        // outranks it, as it outranks every carried reading.
        if written.is_none() {
            match &carried {
                Some(CarriedSlot::Forwarded(Some(held))) => {
                    let answered = held.answer(kb, sg.spec_sort, |kb, e| {
                        requires_entry_covers_goal(kb, e, sg, scope.sigma)
                    });
                    match answered {
                        // Answered HERE, without the recursion below: the slot is the
                        // caller's own dictionary, so there is no provider to choose and no
                        // sub-goal of its own, as for the `EffectsRuntime` anchor above.
                        Some((scope_index, projection)) => {
                            sub_resolutions.push(ResolvedRequiresNode::FromScope {
                                scope_index,
                                spec_sort: sg.spec_sort,
                                projection,
                            });
                            continue;
                        }
                        None => {
                            let hint = format!(
                                "the carrier's type binds named slot `{}` of `{}` to a \
                                 parameter whose dictionary in the enclosing scope \
                                 (`requires {}`) does not answer it",
                                binder_name(kb),
                                kb.qualified_name_of(chosen_impl_sort),
                                render_requires_entry(kb, &held.slots[0].entry),
                            );
                            return refuse(kb, stack, hint);
                        }
                    }
                }
                Some(CarriedSlot::Untied(u)) => {
                    let hint = format!("the carrier's type binds {}", u.render(kb));
                    return refuse(kb, stack, hint);
                }
                _ => {}
            }
        }
        let sub_pin = match (&carried, written) {
            // Two producers of a slot pin, and like [`push_selection`]'s two they are not
            // ranked: they name the SAME instance — witness and nested selections alike —
            // or the goal is refused.
            (Some(CarriedSlot::Pinned(c)), Some(w)) => {
                if !same_selection(kb, &w.selection, &c.selection) {
                    let hint = format!(
                        "slot `{}` of `{}` is bound to `{}` by {} and to `{}` by the \
                         carrier's type",
                        kb.local_name_of(w.binder),
                        kb.qualified_name_of(w.owner),
                        kb.qualified_name_of(w.selection.witness),
                        match written_source {
                            SlotPinSource::Bracket => "the call",
                            SlotPinSource::Carrier => "an enclosing type",
                        },
                        kb.qualified_name_of(c.selection.witness),
                    );
                    return refuse(kb, stack, hint);
                }
                Some((w, written_source))
            }
            (Some(CarriedSlot::Pinned(c)), None) => Some((c, SlotPinSource::Carrier)),
            (_, Some(w)) => Some((w, written_source)),
            (Some(CarriedSlot::Erased), None) => {
                let hint = format!(
                    "the carrier's type leaves named slot `{b}` of `{}` universally \
                     quantified: the value's `{b}` was chosen at its construction and no \
                     dictionary travels with a value, so a provider supplied here would \
                     answer for this signature and not for the value (WI-1094). Write `{b}` \
                     in the type, or declare a named slot for it on the enclosing \
                     declaration and write that name there",
                    kb.qualified_name_of(chosen_impl_sort),
                    b = binder_name(kb),
                );
                return refuse(kb, stack, hint);
            }
            (Some(CarriedSlot::NotInHead), None)
                if is_value_directed_provider(
                    kb,
                    &crate::kb::load::sorts_with_constructors(kb),
                    chosen_impl_sort,
                ) =>
            {
                let hint = format!(
                    "the provision of `{0}` this dispatch took does not bind its named slot \
                     `{b}` in its head, so the carrier's `{b}` cannot reach the slot — write \
                     `{b} = {b}` in the provision's `{0}[…]`",
                    kb.qualified_name_of(chosen_impl_sort),
                    b = binder_name(kb),
                );
                return refuse(kb, stack, hint);
            }
            // `Forwarded(None)`: no σ, so the scope and the search answer, as they always
            // did there. `Unspoken`: the search is the ladder, as at a construction site.
            // `NoWitness`: the requirement's own route reports it. A witness sort's
            // `NotInHead`: a bracket value or an enclosing selection writes it, and nothing
            // did. (`Forwarded(Some)` and `Untied` were answered above.)
            _ => None,
        };
        // WI-861 — a sub-goal filling one of the CHOSEN PROVIDER's own NAMED slots is the
        // same erased binding one level down (`LexFst requires OA: Ord[A]` reached with no
        // `[OA = …]`), so the default is withheld there for the reason [`DefaultRung`]
        // gives. Derived from `chosen_impl_sort`, which is why the rung rides per goal
        // rather than on the scope.
        let sub_rung = rung_for_dep(kb, chosen_impl_sort, sg.spec_sort);
        match resolve_inner(
            kb,
            sg,
            scope,
            stack,
            Some(chosen_impl_sort),
            sub_pin,
            sub_rung,
        ) {
            ResolutionResult::Resolved(t) => sub_resolutions.push(t),
            // WI-857: a SPEC-half slot that does not resolve is CARRIED as
            // `Unavailable`, uniformly across NoMatch / Ambiguous / Cyclic — the
            // honest record either way is "no dictionary was pinned here", and one
            // rule has no cases to get wrong. See the variant's own note for why
            // refusing instead would reject working programs. The PROVIDER half
            // stays strict: those are the provision's OWN conditions, which the
            // provider's body will read, and failing them has always been the
            // dispatch failure the caller reports.
            //
            // Written as a branch on the FAILURE rather than a guarded `_` arm beside
            // `Resolved`: a guarded wildcard would silently shadow any arm added after
            // it (for half the loop, with no reachability lint), and the tolerance is a
            // property of the slot, not of the outcome's shape.
            err => {
                if i < provider_half_start {
                    // WI-865: the failure KIND rides into the slot. Read off `err`
                    // before it is dropped, and off THIS level's failure — the tie
                    // that reaches here is the sub-goal's own, forwarded exactly as
                    // WI-843 forwards one at a call's goal rather than restamping it.
                    sub_resolutions.push(ResolvedRequiresNode::Unavailable {
                        spec_sort: sg.spec_sort,
                        why: unavailable_why_of(&err),
                        below: err.is_forwarded(),
                    });
                } else {
                    stack.pop();
                    // WI-865: THE ONE PLACE A FAILURE STOPS BEING ABOUT THE GOAL THE
                    // CALLER ASKED FOR. Everything else returns a failure this frame
                    // generated for its own `goal`.
                    //
                    // WI-456 — and THE one place that knows whose named slot the failed
                    // sub-goal was filling, which is what lets `TieRepair::SubGoal` name
                    // a repair instead of describing a shape. Nothing else about the tie
                    // is touched — `spec` and `candidates` stay the sub-goal's, which is
                    // the re-attribution 058 §8 measured and fixed.
                    //
                    // `!is_forwarded()` IS THE WHOLE CORRECTNESS CONDITION, and reading it
                    // as "innermost wins" is not the same test. A tie passes through every
                    // enclosing provider on its way out; `forwarded` is false only in the
                    // frame whose OWN sub-goal `sg` is the goal that tied. Without it, a
                    // tie raised under a provider with ANONYMOUS requires (which stamps
                    // nothing) would keep travelling until some outer provider with a
                    // named slot stamped it — and the message would then assert that the
                    // tie fills THAT slot and advise binding it, which re-selects the same
                    // provider and the same tie. An unstamped tie renders the schema
                    // wording instead, which is true of every shape.
                    let owns_the_tie = !err.is_forwarded();
                    return err.stamped_slot(named.filter(|_| owns_the_tie).map(|s| TieSlot {
                        owner: chosen_impl_sort,
                        binder: s.binder,
                    }));
                }
            }
        }
    }
    // Proposal 066 §7 — TWO OR MORE CLAUSES OF THIS SPEC ARE ALTERNATIVES: the
    // provision holds iff ONE clause's conditions resolve. They fill no slot (no body
    // reads them), so the trees are dropped; the first failure is what is reported when
    // none holds, forwarded as a failure of a sub-goal of this one.
    if let Some(groups) =
        alternative_condition_goals(kb, chosen_impl_sort, &chosen_impl_subst, goal.spec_sort)
    {
        let mut first_failure: Option<ResolutionResult> = None;
        let holds = groups.iter().any(|group| {
            group.iter().all(|sg| {
                match resolve_inner(
                    kb,
                    sg,
                    scope,
                    stack,
                    Some(chosen_impl_sort),
                    None,
                    DefaultRung::Consult,
                ) {
                    ResolutionResult::Resolved(_) => true,
                    err => {
                        first_failure.get_or_insert(err);
                        false
                    }
                }
            })
        });
        if !holds {
            stack.pop();
            return first_failure
                .expect("an alternative that does not hold has a failed condition")
                .forwarded();
        }
    }
    stack.pop();

    let tree = if sub_resolutions.is_empty() {
        ResolvedRequiresNode::Leaf {
            impl_sort: chosen_impl_sort,
            spec_sort: goal.spec_sort,
            bindings: chosen_bindings,
        }
    } else {
        ResolvedRequiresNode::Conditional {
            impl_sort: chosen_impl_sort,
            spec_sort: goal.spec_sort,
            bindings: chosen_bindings,
            sub_resolutions,
        }
    };
    ResolutionResult::Resolved(tree)
}

/// A SortProvidesInfo candidate matched against a goal. Carries the
/// impl sort + the impl-side substitution (impl param → resolved
/// value) used to instantiate the impl's `requires_chain` subgoals.
#[derive(PartialEq, Eq)]
pub(super) struct Candidate {
    /// The carrier sort symbol (e.g., `IntEq`, `EqList`).
    pub(super) impl_sort: Symbol,
    /// Head bindings after impl-param substitution — used for the
    /// resolved tree node's `bindings` slot.
    pub(super) resolved_head_bindings: SmallVec<[(Symbol, TermId); 2]>,
    /// Impl-side substitution: maps the impl sort's type-param symbols
    /// to the values they got from matching the goal. Used to
    /// instantiate the impl's `requires_chain` subgoals.
    pub(super) impl_subst: SmallVec<[(Symbol, TermId); 2]>,
    /// True iff the candidate's head is fully-ground (no impl-params
    /// referenced) — i.e., a strictly more-specific instance than a
    /// candidate whose head still carries impl-params. Used by
    /// `pick_most_specific`.
    pub(super) head_specificity: u32,
}

/// Walk `SortProvidesInfo` facts, return those whose head pattern
/// unifies with `goal.bindings`. A candidate whose binding values do
/// not match the goal's is dropped silently and does NOT count as
/// "spec is in use" — `Eq[T = Type]` (meta-equality on Type values)
/// and `Eq[T = Int]` (equality on Int values) are independent specs
/// that happen to share the same spec sort; the presence of one in
/// the KB must not gate dispatch of the other.
/// WI-325 — true iff abstract-binding `NoCandidates` on this spec
/// should fire the `MissingRequiresForSpecOp` diagnostic. Two cases
/// warrant it:
///
/// 1. Spec has at least one declared provider (Eq, Numeric, Ord,
///    …): the user clearly intends per-carrier dispatch and forgot
///    either the `requires` clause or to specialize the call.
/// 2. Spec is user-defined (outside the stdlib `anthill.*` namespace
///    prefix) and has zero providers: the WI-324 'forgot to register
///    an impl' case. Without this leg, a user who defines `sort MySpec
///    { … }` and calls a MySpec op on abstract T silently slips through
///    just because no `fact MySpec[T = …]` has been written yet — the
///    exact phantom WI-325 set out to eliminate.
///
/// Stdlib specs with no providers (Map, List, Stream, Collection,
/// Iteration, IndexedSeq, Field, Lattice, BoundedLattice, Algebra, …)
/// are host-builtin: the runtime resolves their operations directly,
/// no `fact Spec[…]` ever appears, and abstract calls against them
/// (e.g. `Map.empty()` at unbound K, V) are legitimate pass-through.
pub(super) fn spec_warrants_abstract_check(kb: &KnowledgeBase, spec_sort: Symbol) -> bool {
    if spec_has_any_providers(kb, spec_sort) {
        return true;
    }
    // User-defined spec without providers: still warrants the check.
    !kb.qualified_name_of(spec_sort).starts_with("anthill.")
}

/// User precondition clauses of an operation — its `requires` field minus the
/// loader's auto-inferred `EffectsRuntime[Effects=E]` entries (WI-320), which
/// track the effect row, not a caller-facing precondition. WI-347. WI-366 B2:
/// carrier-agnostic `Value` clauses (read through `TermView`).
pub(super) fn user_precondition_clauses(kb: &KnowledgeBase, clauses: &[Value]) -> Vec<Value> {
    clauses
        .iter()
        .filter(|c| !is_effects_runtime_clause(kb, c))
        .cloned()
        .collect()
}

/// Is `clause` an auto-inferred `EffectsRuntime[Effects=…]` requires clause?
/// Such clauses are `Fn{ functor: EffectsRuntime, … }` (see
/// `infer_effects_row_requires`); they ride in the `requires` list but are not
/// user preconditions, so the override contract check skips them. WI-366 B2: the
/// functor is read through [`TermView`] so the check is carrier-agnostic (a
/// denoted-bearing user precondition rides as a `Value::Node`).
pub(super) fn is_effects_runtime_clause(kb: &KnowledgeBase, clause: &Value) -> bool {
    matches!(clause.head(kb),
        ViewHead::Functor { functor: Some(f), .. }
            if kb.qualified_name_of(f) == "anthill.prelude.EffectsRuntime")
}

/// Apply a spec↔impl param-alignment `subst` to a carrier-agnostic
/// precondition/postcondition clause for the override-refinement comparison
/// (WI-366 B2). A ground `Value::Term` clause is rewritten via
/// [`substitute_impl_params_alloc`]; a denoted-bearing `Value::Node` clause is
/// returned verbatim — substituting into the occurrence is deferred parametric
/// handling, so the structural comparison treats it as un-rewritten
/// (conservative: a denoted precondition that needed alignment would not be
/// recognized as covered, never falsely accepted).
pub(super) fn substitute_clause(
    kb: &mut KnowledgeBase,
    clause: &Value,
    subst: &[(Symbol, TermId)],
) -> Value {
    match clause {
        // Empty-subst guard like [`sigma_subst_type`]'s: same-named params
        // need no rewrite, and the deep walk re-allocs every node.
        Value::Term { id: t, .. } if !subst.is_empty() => {
            Value::term(substitute_impl_params_alloc(kb, *t, subst))
        }
        other => other.clone(),
    }
}

/// WI-20260822-1TKN0 — align ONE effect label into the spec operation's parameter
/// vocabulary, on EITHER carrier.
///
/// The alignment is what lets an honest override restate the spec's own row: the
/// two operations' parameters are distinct symbols even when they are spelled the
/// same (`Stream.splitFirst.s` vs `FiniteStream.splitFirst.s`), so without it every
/// place-denoting effect label would read as naming a different place.
///
/// A hash-consed label goes through [`substitute_clause`] exactly as before. A
/// `Value::Node` label — the carrier a denoted `Modify[c]` rides — goes through
/// [`substitute_ref_syms_value`], which is the occurrence-level `Ref` rewrite that
/// EXISTS FOR THIS REWRITE: its own doc describes it as re-keying "a callee's
/// `Modify[c]` to the caller's `Modify[s]`". `substitute_clause`'s `other =>
/// other.clone()` arm silently no-opped on that carrier, so a `Modify[c]` override
/// compared against the spec's `Modify[c]` under two different symbols.
///
/// DELIBERATELY NOT FOLDED INTO [`substitute_clause`]. That function is shared with
/// the contract legs and with [`result_binder_discharges`], whose verdict GATES the
/// WI-20260822-59CDQ return-type refusal; teaching it a second carrier there is a
/// different question with its own measurement, and this ticket measured the
/// effects leg.
pub(super) fn align_effect_label(
    kb: &mut KnowledgeBase,
    e: &Value,
    align: &[(Symbol, TermId)],
    align_syms: &HashMap<Symbol, Symbol>,
) -> Value {
    match e {
        Value::Node(_) if !align_syms.is_empty() => substitute_ref_syms_value(kb, e, align_syms),
        other => substitute_clause(kb, other, align),
    }
}

/// WI-20260822-59CDQ — does aligning the RESULT binder actually DISCHARGE anything?
///
/// True iff some impl clause matches some spec clause under `with_result` (the param
/// alignment plus the `<impl op>.result ↦ <spec op>.result` entry) and does NOT match
/// under `params_only`. That is the exact condition the return-type guard in
/// [`check_override_refinement`] needs: the binder alignment, and nothing else, is what
/// made the two clauses compare equal, so the two `result`s must denote values of the
/// same type for the discharge to mean anything.
///
/// Asked by RUNNING THE COMPARISON THE LEGS RUN — [`substitute_clause`] then
/// [`views_structurally_equal`], twice — rather than by a hand-written "does this clause
/// mention the binder" walk. A separate reader listing the carriers
/// [`substitute_impl_params_alloc`] rewrites would drift from it the first time a
/// carrier is added, and it would answer the WRONG QUESTION besides: a clause can
/// mention `result` and still be refused for weakening the postcondition, and naming the
/// return types there sends the author to a line whose repair would not load.
pub(super) fn result_binder_discharges(
    kb: &mut KnowledgeBase,
    impl_clauses: &[Value],
    spec_clauses: &[Value],
    with_result: &[(Symbol, TermId)],
    params_only: &[(Symbol, TermId)],
) -> bool {
    for ic in impl_clauses {
        let with = substitute_clause(kb, ic, with_result);
        for sc in spec_clauses {
            if !views_structurally_equal(kb, &with, sc) {
                continue;
            }
            let without = substitute_clause(kb, ic, params_only);
            if !views_structurally_equal(kb, &without, sc) {
                return true;
            }
        }
    }
    false
}

/// Apply a provision's σ (spec param symbol → binding) to a spec operation's DECLARED
/// TYPE — a parameter type, the return type or an effect label — on whatever carrier
/// it rides.
///
/// WI-20260923-Z1Q8B — THE ONE VALUE-LEVEL σ, and it reads the type through
/// [`TermView`]. Until this ticket it was `sigma_subst_effect`, which rewrote a
/// `Value::Term` and handed a `Value::Node` back UNSUBSTITUTED as "deferred
/// parametric-effect handling". A type rides the occurrence carrier whenever it
/// carries a denoted — the literal `3` in `Foo[T = T, N = 3]` — which says nothing about
/// whether it is parametric, so a spec parameter beneath one was never grounded and
/// every reader failed open on it: [`check_override_refinement`]'s return leg, its
/// effects leg, and [`instance_binding_type_ok`], which kept a `TermId`-only copy of
/// this σ beside it and read `Value::Node` as "not confident" outright.
///
/// A hash-consed subtree stays in the term world: [`substitute_impl_params_alloc`],
/// hash-consed result, the path a `Value::Term` always took. Anything else is read
/// through the view, where a bare name σ binds is a LEAF — replaced, never descended —
/// by the same [`view_ref_symbol`] reading the term walk uses, and ONLY THE SPINE ABOVE
/// A REPLACED LEAF IS REBUILT: as a `Value::Entity`, or a `Value::Tuple` for a
/// functor-less aggregate, which reads through `TermView` exactly as the occurrence it
/// replaces did (WI-361 — the two carriers are indistinguishable through the view).
/// A subtree σ does not touch comes back as the value it was, carrier and all, so a type
/// with nothing to substitute — `Modify[c]` — is returned unchanged. A head the view
/// cannot present (`Opaque` — a `Parameterized` whose base is itself an occurrence) is
/// returned unchanged too, and fails open downstream rather than being compared
/// unsubstituted: [`view_contains_type_param`] reads `Opaque` as abstract.
///
/// [`substitute_ref_terms`]' SHAPE, AND DELIBERATELY NOT THAT FUNCTION. It σ-applies a
/// GOAL, so it replaces a `var_ref` binder whole and rebuilds every application it passes
/// through; a spec type must keep an untouched subtree on its own carrier, and must read
/// the nullary-`Fn` spelling of a parameter as the name it is — which that function's
/// term arm does not (a `Term::Fn` there only maps its children).
pub(super) fn sigma_subst_type(
    kb: &mut KnowledgeBase,
    ty: &Value,
    sigma: &[(Symbol, TermId)],
) -> Value {
    if sigma.is_empty() {
        return ty.clone();
    }
    sigma_subst_view(kb, ty, sigma).unwrap_or_else(|| ty.clone())
}

/// [`sigma_subst_type`]'s walk. `None` when σ changes nothing at or beneath `v`, which
/// is what lets an untouched subtree keep its own carrier.
fn sigma_subst_view(
    kb: &mut KnowledgeBase,
    v: &Value,
    sigma: &[(Symbol, TermId)],
) -> Option<Value> {
    if let Value::Term { id, .. } = v {
        let t = substitute_impl_params_alloc(kb, *id, sigma);
        return (t != *id).then(|| Value::term(t));
    }
    if let Some(s) = view_ref_symbol(kb, v) {
        return sigma
            .iter()
            .find(|(k, _)| *k == s)
            .map(|(_, t)| Value::term(*t));
    }
    // A variable, a literal, `⊥` or an opaque head names nothing σ binds.
    let ViewHead::Functor {
        functor, pos_arity, ..
    } = v.head(kb)
    else {
        return None;
    };
    // `.to_value()` owns each child, ending the view's borrow of `kb` before the
    // `&mut kb` recursion — the borrow shape `subst_view_pos` uses.
    let mut changed = false;
    let mut pos = Vec::with_capacity(pos_arity);
    for i in 0..pos_arity {
        let child = v.pos_arg(kb, i).expect("pos_arg within arity").to_value();
        let new = sigma_subst_view(kb, &child, sigma);
        changed |= new.is_some();
        pos.push(new.unwrap_or(child));
    }
    let keys = v.named_keys(kb);
    let mut named = Vec::with_capacity(keys.len());
    for k in keys {
        let child = v.named_arg(kb, k).expect("named key present").to_value();
        let new = sigma_subst_view(kb, &child, sigma);
        changed |= new.is_some();
        named.push((k, new.unwrap_or(child)));
    }
    if !changed {
        return None;
    }
    Some(match functor {
        Some(f) => {
            kb.canonicalize_record_named_args(f, &mut named);
            Value::Entity {
                functor: f,
                pos: Rc::from(pos),
                named: Rc::from(named),
            }
        }
        None => Value::Tuple {
            pos: Rc::from(pos),
            named: Rc::from(named),
        },
    })
}

/// Replace every `Ref(p)` / `Ident(p)` / nullary `Fn(p, [], [])` in
/// `term` where `p` is in `impl_subst` with its bound value. The
/// nullary-Fn shape is what `convert_term` produces for a bare name
/// like `A` inside a `requires Eq[T = A]` clause — it's structurally
/// the same as `Ref(A)` for resolution purposes. Allocates new Fn
/// terms when children need substitution; returns the original TermId
/// otherwise.
pub(super) fn substitute_impl_params_alloc(
    kb: &mut KnowledgeBase,
    term: TermId,
    impl_subst: &[(Symbol, TermId)],
) -> TermId {
    // A bare name is a LEAF — replaced when σ binds it, kept otherwise, never descended.
    if let Some(s) = view_ref_symbol(kb, &TermIdView(term)) {
        return impl_subst
            .iter()
            .find(|(k, _)| *k == s)
            .map_or(term, |(_, v)| *v);
    }
    kb.map_fn_children(term, |kb, t| {
        substitute_impl_params_alloc(kb, t, impl_subst)
    })
}

/// True iff `entry`'s bindings cover `goal`. Used at the
/// `available_requires` lookup step (step 1 of `resolve`).
/// Filters out op-bindings (auto-bound `eq`, `neq`, …) — only type-
/// param bindings constrain matching.
///
/// `sigma` selects the per-pair verdict via the shared
/// [`binding_pair_covers`], exactly as in the entry-vs-entry twin
/// [`entries_cover`] (this function's σ mode is NEW in WI-821 — it never had
/// a standalone σ twin): `None` keeps the coarse wildcard cover; `Some(ctx)`
/// is the σ-precise GATE a scope entry must pass when the resolution serves
/// a call-site dict build (`ResolutionScope.sigma`). σ-precise implies
/// coarse, so one walk decides either mode.
///
/// WI-826 — THE FIX, and it is leg 1 below: this walk used to visit only the
/// ENTRY's keys, so a key the GOAL named and the entry did NOT was never examined.
/// A bare bindingless `requires Desc` — no `SortView`, hence genuinely no
/// bindings, the one spelling that produces a missing key (a BRACKETED `requires
/// Pair[P = MT]` is filled by the loader with `Q = Pair.Q`, so it has no holes) —
/// therefore covered ANY goal of that spec, returning true before the σ mode was
/// ever consulted and handing a concrete downstream goal the caller's abstract
/// dictionary. Leg 1 is now the shared [`supply_covers_demanded_keys`], the
/// orientation [`entries_cover`] always had.
///
/// Leg 2 (every key the ENTRY names must be named by the goal; the PAIRS are
/// already decided by leg 1, so it only asks presence) has no counterpart in
/// [`entries_cover`], because the two walks answer DIFFERENT QUESTIONS — not
/// because their demands have different provenance (they can be the very same
/// written entry: Strategy 3 derives its goal via `goal_from_requires_entry(dep)`
/// from the `dep` Strategy 1 just handed to `entries_cover`):
///
/// * `entries_cover` asks "does this dictionary SATISFY that requirement slot?".
///   A slot naming no element accepts any dictionary of the spec — forwarding is
///   the only answer available, and the callee said nothing to contradict it.
/// * this asks "IS the scope's dictionary THE ONE for this goal?", and answering
///   yes SHORT-CIRCUITS construction. Under a goal that leaves an element unnamed
///   the honest answer is "cannot tell", so it must not short-circuit: let the
///   candidates decide, and let WI-828 refuse if the element is genuinely
///   unconstrained. Silently taking the scope's dictionary for an undetermined
///   element is the pre-WI-821 unsoundness in miniature.
///
/// Consequence, deliberate and currently unobservable: for the dual shape (entry
/// names a key, goal names none) the two walks give OPPOSITE verdicts. Strategy 1
/// runs first and returns, so `entries_cover`'s answer is the reachable one; a
/// future path that reads a bare slot's forwarded dictionary for a determinate
/// call would have to revisit this pair.
pub(super) fn requires_entry_covers_goal(
    kb: &mut KnowledgeBase,
    entry: &RequiresEntry,
    goal: &SortGoal,
    sigma: Option<&SigmaCtx>,
) -> bool {
    let Some((_, entry_bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
        return false;
    };
    let spec_qn = kb.qualified_name_of(goal.spec_sort).to_string();
    if !supply_covers_demanded_keys(
        kb,
        sigma,
        &spec_qn,
        Supply(&entry_bindings),
        Demand(&goal.bindings),
    ) {
        return false;
    }
    // Leg 2, through the same `binding_for_param` key rule leg 1 uses, so one
    // function cannot decide "entry names goal's key" and "goal names entry's
    // key" by two different rules.
    for (k, _) in &entry_bindings {
        if !is_type_param_binding(kb, *k, &spec_qn) {
            continue;
        }
        if binding_for_param(kb, &goal.bindings, *k, BindingKeyMatch::Label).is_none() {
            return false;
        }
    }
    true
}

/// Structural equality between two goals for cycle detection.
/// The `spec_sort` gate below confines binding-key matching to ONE spec (unique
/// type-param short names), so keys compare via `same_label` (short name) — the
/// keys reach here from different producers (`sort_goal_from_subst` may store a
/// bare `T`, a candidate sub-goal a qualified `Spec.T`), so short-name matching
/// bridges that divergence just as `goal_binding_value` does. Comparing by
/// qualified name would miss the bare-vs-qualified pair and drop a real cycle.
fn goals_equal(kb: &KnowledgeBase, a: &SortGoal, b: &SortGoal) -> bool {
    if a.spec_sort != b.spec_sort {
        return false;
    }
    if a.bindings.len() != b.bindings.len() {
        return false;
    }
    a.bindings.iter().all(|(k, av)| {
        b.bindings
            .iter()
            .find(|(kk, _)| same_label(kb, *kk, *k))
            .map_or(false, |(_, bv)| values_structurally_equal(kb, *av, *bv))
    })
}

/// Render WHY a [`ResolutionResult`] is not a `Resolved` — one owner, so every
/// reader of a failed instance synthesis words it identically.
///
/// WI-822 factored this out of the WI-821 σ-refusal diagnostic (its sole reader
/// then) when [`resolve_bridge_requirements`] gained the same need: a value-directed
/// dispatch that cannot construct its impl's dictionary must say what the resolver
/// actually decided, not just "unresolvable". A `Resolved` maps to the empty string
/// — callers reach here only on the failure edge, and an empty tail reads as "no
/// further detail" rather than asserting something false.
pub(super) fn describe_resolution_failure(kb: &KnowledgeBase, result: &ResolutionResult) -> String {
    match result {
        // WI-843: `kb` is threaded in so the tie can ride as SYMBOLS all the way to a
        // renderer. It was rendered eagerly in the resolver before, which meant every
        // consumer paid for strings — and, worse, for the concreteness scan beside
        // them — including the two that drop the result on the floor.
        // WI-456 — AND THE REPAIR, which this arm used to drop. It rendered the
        // candidates and stopped, so the only advice the author got was the generic tail
        // its caller appends ("select a witness that provides this requirement at these
        // bindings, or drop the selection") — false on both halves for the shape that
        // reaches here most often, a pinned witness whose OWN named slot tied. See
        // [`tie_repair_advice`], which is now the one owner of the sentence.
        ResolutionResult::Ambiguous { goal_text, tie, .. } => {
            // AND ONLY FOR A SUB-GOAL TIE, which is a COST decision and is measured.
            // [`render_instance_tie`]'s concreteness scan walks every `SortInfo` fact,
            // and this arm runs EAGERLY to fill `RequirementRefusal::construction` —
            // including for the WI-945 refusals that are parked and then truncated, on
            // loads that go on to succeed. Attaching the advice unconditionally cost
            // **+9% on a clean stdlib load** (0.72 s → 0.79 s, release, quiet machine,
            // 5 runs each); the `!at_call_goal` branch returns BEFORE the scan, so this
            // spelling measures 0.73 s, back inside the noise. The arms left out lose nothing they had:
            // an at-call-goal tie reaching a requirement projection is already answered
            // by `RequirementRefusal`'s own `pinned` / element advice, whereas the
            // sub-goal tie is the one that had NO repair anywhere, which is this
            // ticket's whole subject.
            let advice = tie_repair_is_attachable(tie)
                .then(|| {
                    tie_repair_advice(
                        kb.qualified_name_of(tie.spec),
                        &render_instance_tie(kb, tie).1,
                    )
                })
                .unwrap_or_default();
            format!(
                // WI-1032's dedup holds on THIS face too. Re-rendering `tie.candidates`
                // raw printed one carrier twice for a provider reached through two
                // non-identical provisions — the very `(Leaf, Leaf)` symptom WI-1032
                // records as fixed — while the other face printed it once.
                "constructing `{goal_text}` is ambiguous among providers: {}{advice}",
                tie_candidate_names(kb, tie).join(", "),
            )
        }
        // The reader of NoMatch's purpose-built hint (eagerly formatted since
        // WI-821, previously consumed by nothing).
        ResolutionResult::NoMatch { hint, .. } => hint.clone(),
        ResolutionResult::Cyclic { path, .. } => {
            format!("construction is cyclic: {}", path.join(" -> "))
        }
        ResolutionResult::Resolved(_) => String::new(),
    }
}

/// WI-456 — may a tie's repair be attached where [`describe_resolution_failure`]
/// renders it?
///
/// THE ONE OWNER OF THE `at_call_goal` GATE, and it has to be one: the first cut asked
/// this question in two places — here, to decide [`PinnedWitness::TiedInside`], and at
/// the render, to decide whether to pay [`render_instance_tie`]'s scan — with two
/// different predicates. `/code-review` found the gap that opens between them: an
/// at-call-goal tie under a pinned witness was classified `TiedInside` (so the generic
/// tail was suppressed) and then given no advice (so nothing replaced it), leaving a
/// refusal with NO repair at all where HEAD had one. Two gates for one invariant is the
/// two-checks-disagree defect this ticket exists to close, so there is now one.
fn tie_repair_is_attachable(tie: &InstanceTie) -> bool {
    !tie.at_call_goal
}

/// WI-456 — does this failure's rendering already name a repair? See
/// [`tie_repair_is_attachable`] for why the `at_call_goal` half is part of the question
/// and not a separate one. `None` is "construction was never attempted", which advises
/// nothing either; the non-`Ambiguous` arms render an ACCOUNT — a hint, a cycle path —
/// with no advice in it.
pub(super) fn failure_carries_repair(result: Option<&ResolutionResult>) -> bool {
    matches!(result, Some(ResolutionResult::Ambiguous { tie, .. }) if tie_repair_is_attachable(tie))
}

/// WI-456 — a witness this call-site bracket PINNED, and why the projection failed
/// with it, because the two answers need opposite advice.
///
/// Written as one value rather than a `Symbol` beside a `bool` on the
/// "make illegal state unrepresentable" rule: a flag would let a refusal carry
/// [`Self::Unusable`]'s advice with a tie's account, or the reverse, and both render as a
/// confident sentence. Here the witness cannot be recorded without saying which it is.
#[derive(Clone, Copy, Debug)]
pub(super) enum PinnedWitness {
    /// Nothing the pinned witness provides fits, so naming a different one is the repair.
    Unusable(Symbol),
    /// The pinned witness is FINE and construction tied INSIDE it — the tie's own repair
    /// is already in [`RequirementRefusal::construction`] (WI-456's `tie_repair_advice`),
    /// and the generic *"select a witness … or drop the selection"* would contradict it.
    /// MEASURED on `SortedSet[T = Boxed[E = String], O = ByInner]`: `ByInner` does
    /// provide at these bindings and dropping it loses the ordering the program is for.
    TiedInside(Symbol),
}

impl PinnedWitness {
    pub(super) fn witness(self) -> Symbol {
        match self {
            PinnedWitness::Unusable(w) | PinnedWitness::TiedInside(w) => w,
        }
    }
}

/// WI-9PGCM — an unsatisfied `requires` clause as diagnostic text.
///
/// NOT [`type_display_name_value`], which every `UnsatisfiedPrecondition` rendering
/// used to call: that is a TYPE renderer and a precondition is a GOAL, so it printed
/// the head alone — `flows_to`, where the clause is `flows_to(Untrusted, Public)` and
/// the whole content of the report is WHICH label failed. [`TermPrinter`] is the
/// general term printer, and its own doc names a diagnostic as one of the three
/// readers of its canonical surface. (Same call, same reason, as the WI-849
/// malformed-`type_params` report a few thousand lines below.)
///
/// A non-`Term` carrier — a denoted `Value::Node` precondition — has no `TermId` to
/// print and keeps the type renderer, which reads it through the View layer.
pub(super) fn format_precondition_clause(kb: &KnowledgeBase, clause: &Value) -> String {
    match clause {
        Value::Term { id, .. } => crate::persistence::print::TermPrinter::over(kb).print_term(*id),
        other => type_display_name_value(kb, other),
    }
}

/// Human-readable goal text for diagnostics ("Eq[T = Int]").
pub(super) fn format_goal(kb: &KnowledgeBase, goal: &SortGoal) -> String {
    let mut out = kb.qualified_name_of(goal.spec_sort).to_string();
    if !goal.bindings.is_empty() {
        out.push('[');
        let mut first = true;
        for (k, v) in &goal.bindings {
            if !first {
                out.push_str(", ");
            }
            first = false;
            out.push_str(kb.local_name_of(*k));
            out.push_str(" = ");
            out.push_str(&format_term_for_goal(kb, *v));
        }
        out.push(']');
    }
    out
}

/// Render a binding value compactly. Sort symbols → short name;
/// parametric forms → `Base[K = V]`.
pub(super) fn format_term_for_goal(kb: &KnowledgeBase, t: TermId) -> String {
    if let Some(sym) = extract_sort_ref_sym(kb, &TermIdView(t)) {
        return kb.qualified_name_of(sym).to_string();
    }
    match kb.get_term(t) {
        // bare `Ref` is named above via `extract_sort_ref_sym` (WI-361); a still-
        // unresolved `Ident` falls here.
        Term::Ident(s) => kb.qualified_name_of(*s).to_string(),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            let base = kb.qualified_name_of(*functor).to_string();
            if pos_args.is_empty() && named_args.is_empty() {
                base
            } else {
                let mut s = base;
                s.push('[');
                let mut first = true;
                for (k, v) in named_args.iter() {
                    if !first {
                        s.push_str(", ");
                    }
                    first = false;
                    s.push_str(kb.local_name_of(*k));
                    s.push_str(" = ");
                    s.push_str(&format_term_for_goal(kb, *v));
                }
                s.push(']');
                s
            }
        }
        Term::Const(Literal::Int(i)) => i.to_string(),
        // WI-20260921-3G1YT — AN UNBOUND VAR IN TYPE POSITION IS "THIS ELEMENT IS
        // UNDETERMINED", and `?` is how the language already spells that (`sort T = ?`).
        // It fell to the `<term#NNN>` arm below, which is loud about nothing: the reader
        // is shown an interning id and cannot tell that the element IS the defect.
        //
        // MEASURED as the message this repairs. `Holder[U = List].tyb()` — a bare
        // parametric bracket whose element nothing writes — refused naming
        // `TypeValue[T = anthill.prelude.List[T = <term#23484>]]`; it now reads
        // `List[T = ?]`, which shows the unwritten element and therefore the repair
        // (write it — `Holder[U = List[T = Int64]]` is that fixture's own control).
        Term::Var(_) => "?".to_owned(),
        _ => format!("<term#{}>", t.raw()),
    }
}
