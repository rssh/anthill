//! Which operation a call reaches (`resolve_op_target`, spec-op parents, carrier
//! overrides), the `CallClass` handed to requirement insertion, and requires-slot location.

use super::*;

/// The parent sort of `op_sym` when it is a SPEC operation — declared in a
/// parametric sort (one with at least one `sort <Param> = ?` declaration),
/// REGARDLESS of whether it has a default body. Returns the spec sort symbol,
/// or `None` when `op_sym` is not a member of a parametric sort.
///
/// WI-444: this is the body-agnostic core. [`lookup_spec_op_dispatch`] layers
/// the body-less gate on top (a body-less spec op is the call-site dispatch
/// target via `SortProvidesInfo`); a DEFAULTED spec op (with its own body) is
/// not a body-less dispatch target but is still a spec op whose carrier may
/// OVERRIDE it (typeclass default-method semantics — defaults fill gaps, they
/// do not shadow), so the override paths gate on this instead.
///
/// WI-958 — and THE one reader of "the parametric sort that declares this op":
/// [`self_receiver_spec_sort`] is this plus a self-receiver gate, so the two cannot
/// disagree about which sorts are spec sorts. The owner AND its kind gate come from
/// [`impl_parent_sort_of_op`] (WI-956, which took that gate's `has_kind` — stated
/// there — and gave it to this reader's four siblings); only the PARAMETRIC gate is
/// stated here.
///
/// The kind gate is NOT subsumed by the parametric one, though on today's surface
/// it never fires: `add_type_param`'s two surface sites are gated on
/// `is_sort_scope`, so a NAMESPACE never accumulates params (MEASURED: 0 of the 30
/// namespaces in stdlib + anthill-stl report any), and 0 of 373 operations have a
/// non-`Sort` parent with a non-empty param list. But an OPERATION scope does take
/// params — `operation outer[U](…)` gives `type_params_of_sort(outer) == ["U"]` —
/// so the parametric gate alone states "some scope with brackets", which is not the
/// question either caller asks.
pub fn spec_op_parent_sort(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    let parent_sym = impl_parent_sort_of_op(kb, op_sym)?;
    sort_is_parametric(kb, parent_sym).then_some(parent_sym)
}

/// WI-1042 — "declares at least one `sort <Param> = ?`", the PARAMETRIC leg of
/// [`spec_op_parent_sort`], named so [`defaulted_spec_op_parent`] can order it after
/// its own cheaper legs without re-spelling it. One line, and the name is the point:
/// the two gates must not each carry their own reading of what makes a sort a spec.
///
/// IT WAS THE EXPENSIVE LEG, AND WI-954 MADE IT O(1). `type_params_of_sort` used to
/// `format!` a prefix, scan ALL of `by_qualified_name` without short-circuiting and
/// deep-clone a `Vec<String>` — 51 µs/call, O(|symbols|). It now reads the owner's own
/// scope. Callers that place this last for cost may stop bothering; nothing here needs
/// them to move.
///
/// WI-1042 CALLED THAT REWRITE "NOT A DROP-IN", on the measurement that the scope-based
/// spelling `load.rs`'s `enclosing_is_spec` uses disagreed with `type_params_of_sort` on
/// 24 of 2755 symbols. RE-MEASURED under WI-954, the 24 are real and all of one shape:
/// CALLBACK-PARAMETER symbols (`anthill.prelude.List.foldLeft.f`), which the child scan
/// gave their OPERATION's parameters because `register_callback_places` defines
/// `…foldLeft.f.a` in the op scope and the scan took an arbitrary direct child's
/// `declaring_scope`. `["Acc", "EffP"]` for a callback parameter was the wrong answer;
/// `[]` is the right one, and no caller passes such a symbol. Shielding it was the right
/// call on what WI-1042 could measure, and the shield is no longer what makes it safe.
fn sort_is_parametric(kb: &KnowledgeBase, sort_sym: Symbol) -> bool {
    !kb.type_param_syms_of(sort_sym).is_empty()
}

/// WI-1042 — THE defaulted-spec-op gate: `op_sym` is a member of a PARAMETRIC sort and
/// HAS a runnable body, i.e. the typeclass DEFAULT a carrier may override. Returns the
/// parent spec sort.
///
/// ONE OWNER, because three sites asked this and two of them spelled it differently:
///
///   * [`check_apply_iter`]'s WI-444 carrier-override block, which pins the call to the
///     carrier's supplied implementation or refuses a tie;
///   * [`dot_member_dispatch_decision`]'s DEFAULTED leg, the same decision reached by
///     the dot spelling (WI-1035);
///   * [`call_dispatch_shape`], the WI-1026 rule-body walk trigger — this gate and
///     nothing else since WI-1036 deleted its `!is_builtin` clause. WI-1043 turned that
///     site's ADMISSION into [`spec_op_call_parent`] (both halves) and left this gate
///     naming WHICH half, which is what its error tail is keyed on;
///   * [`defaulted_spec_op_witness_grounds_soundly`], WI-1040's last witness scan — a
///     FOURTH reader, found by this ticket's own review, which asked the question by name
///     while reading only the body-AGNOSTIC parent and leaning on caller scan order for
///     the rest.
///
/// The drift this closes is not hypothetical: the equivalence of the two spellings was
/// held by a doc comment 30k lines away, so a clause added to the WI-444 block would
/// have silently diverged the rule-body FIRE population from the op-body PIN/REFUSAL
/// population with no test moving — the corpus population of the third spelling is
/// ZERO, so nothing could observe it. `wi1042_defaulted_gate_test` drives the
/// agreement over a real corpus load instead of asserting it in prose.
///
/// THE TWO SPELLINGS IT UNIFIES ARE NOT EQUIVALENT, AND THIS IS THE NARROWING. The
/// WI-444 block read `lookup_spec_op_dispatch(..).is_none() && spec_op_parent_sort(..)
/// .is_some()`, whose body test is `!operation_has_no_body` — TRUE for a symbol with no
/// `OperationInfo` at all. This reads [`op_has_runnable_body`], which requires one. So
/// they differ on exactly one population: a symbol parented by a parametric sort that is
/// not an operation — `anthill.prelude.Option.some`, an entity constructor declared
/// inside `Option`, is one, and the old spelling calls it a defaulted spec op.
///
/// WHAT MAKES THE NARROWING SAFE IS A PRECONDITION AT EACH SITE, not a coincidence, and
/// NOT the corpus agreement test — that test walks `all_operation_params`, one entry per
/// `OperationInfo` FACT, which is precisely the population where the two cannot differ.
/// It measures the rest of the gate; it cannot see this case. The preconditions:
///
///   * `check_apply_iter`'s WI-444 block sits inside `if let Some(mut op) =
///     lookup_operation_info_full(kb, fn_sym)`, which IS the `OperationInfo` probe;
///   * [`dot_member_dispatch_decision`] reaches its leg only through
///     `find_spec_op_for_provided_sort` → `find_operation_in_scope`, which finds symbols
///     BY WALKING the `OperationInfo` facts;
///   * [`call_dispatch_shape`] is asked per `Expr::Apply` functor, where a symbol
///     with no `OperationInfo` must answer `false` — the strict read IS the requirement
///     there, not a precondition (see the measurement below). Since WI-1043 the
///     admission is [`spec_op_call_parent`], which carries that same probe as its own
///     clause for exactly this reason; this gate is asked BEHIND it.
///
/// THE STRICT READ IS NOT MERELY THE STRONGER ONE — IT IS REQUIRED, and that was MEASURED
/// after this ticket's review called the first justification here vacuous. Give this gate
/// the old body test and **15 tests across 5 suites fail** (`wi936`, `wi618`,
/// `parameterized_provides_block`, `sql_store_example`, and this ticket's own). FOURTEEN
/// of them come from [`call_dispatch_shape`]: the rule-body walk then fires
/// `type_check_node` on an entity constructor declared inside a parametric sort — which
/// is what `operation_has_no_body`'s doc means by "so non-operation symbols are not
/// misclassified" — and re-conjoining [`op_has_runnable_body`] at that site alone restores
/// all fourteen (driven, both halves). RE-MEASURED after WI-1036 deleted that site's
/// `!is_builtin` clause: the same 15 tests, unchanged. The fifteenth is
/// `wi1042_defaulted_gate_test::a_non_operation_functor_is_not_a_defaulted_spec_op`, the
/// one test that pins THIS function's answer rather than one site's use of it.
///
/// At the dot site the swap is not conjunctive either: a misclassified symbol would not
/// merely be admitted, it would take the DEFAULTED refusal predicate (a bare count over
/// the interpretability-filtered supplier list) where the old spelling took the BODY-LESS
/// one (arbitration-narrowed, unfiltered). Those reject different programs in both
/// directions. No corpus program reaches it — the precondition above — but the failure
/// would be a silently different refusal, not a louder one.
///
/// CLAUSE ORDER IS LOAD-BEARING AND IS NOT THE ORDER OF THE CONJUNCTION IT REPLACES.
/// [`impl_parent_sort_of_op`] runs FIRST — a name split plus an O(1) kind probe — and it
/// is the cheap NON-OPERATION early-out this gate previously lacked: a relational atom
/// head (dot-less, or parented by a NAMESPACE) leaves HERE, before
/// [`op_has_runnable_body`] can fall through `lookup_operation_info`'s record miss into
/// its O(N_ops) fact scan, and before [`sort_is_parametric`]'s parametric leg — which
/// WI-954 made an O(1) owner-scope read, so that last consideration no longer applies;
/// the early-out is still what keeps the FACT SCAN off a relational atom head.
///
/// MEASURED over a stdlib + host-bindings load (counters on each leg, 2026-08-07): the
/// gate is asked 523 times; the name split answers for 244 of them, 279 reach the body
/// probe and 55 the parametric leg. Applying the OLD conjunct order (`!is_builtin`, then
/// `op_has_runnable_body`, then the parent+parametric probe bundled inside
/// `spec_op_parent_sort`) to the same 523 calls: 466 reach the body probe and 80 the
/// parametric leg. Read it as an ordering comparison and not as history — the three call
/// sites did not previously share one gate, so nothing ever ran the old order over this
/// exact call set. [`call_dispatch_shape`]'s own doc carries the per-site count for
/// the walk trigger (~745 per load on examples/github-todo); WI-1036 deleted the
/// `!is_builtin` clause that used to shield it, so every one of those calls now reaches
/// this gate's own legs.
pub fn defaulted_spec_op_parent(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    let parent_sym = impl_parent_sort_of_op(kb, op_sym)?;
    if !op_has_runnable_body(kb, op_sym) {
        return None;
    }
    sort_is_parametric(kb, parent_sym).then_some(parent_sym)
}

/// WI-1043 — THE WALK TRIGGER'S gate: `op_sym` is an OPERATION declared by a
/// PARAMETRIC sort, i.e. a spec op of EITHER half — [`defaulted_spec_op_parent`]'s
/// (a runnable default a carrier may override) or [`lookup_spec_op_dispatch`]'s
/// (body-less, resolved by call-site dispatch). Returns the parent spec sort.
///
/// ONE reader — [`call_dispatch_shape`] — and it is the union because
/// [`check_apply_iter`] decides both halves in the same frame: the WI-444 block pins
/// or refuses a defaulted call, the WI-210 block dispatches a body-less one and
/// [`arbitrate_unarbitrated_supplier_tie`] refuses ITS tie. WI-1026 admitted only the
/// defaulted half, so a rule body naming a BODY-LESS spec op reached no dispatch
/// decision at all: MEASURED, `rule answer(?r) :- Desc.describe(leaf(), ?r)` on a
/// body-less `describe` loaded CLEAN and answered `[]` for every supply shape — one
/// supplier, two suppliers, own member or instance fact alike — while the identical
/// call in an operation body pins the supplied impl and refuses the tie at load
/// (WI-1027). Same program, two verdicts, decided by where the call is written.
///
/// THE OPERATION-HOOD LEG IS NOT DECORATION and is the one clause a reader will try to
/// drop, since [`spec_op_parent_sort`] already spells "member of a parametric sort".
/// That predicate is operation-AGNOSTIC: `anthill.prelude.Option.some`, an entity
/// constructor declared inside a parametric sort, passes it. WI-1042 measured what
/// admitting that population at THIS site costs — 14 tests across 4 suites, the walk
/// firing `type_check_node` on entity-constructor calls. Both halves' own gates carry
/// the same leg (`op_has_runnable_body` / `operation_has_no_body` each require an
/// `OperationInfo`), so asking for one directly is what makes this their union and not
/// a wider third reading. `wi1043_bodyless_rule_body_test::the_walk_gate_is_exactly_-
/// the_two_halves` drives that equality over the corpus.
///
/// CLAUSE ORDER as [`defaulted_spec_op_parent`] measured it: the name split first (the
/// cheap non-operation early-out — every relational atom head leaves here), then the
/// `OperationInfo` probe, then [`sort_is_parametric`] last. Since WI-954 that last leg
/// is an O(1) owner-scope read; the order is kept because the `OperationInfo` probe's
/// fact-scan fallback is still the expensive one to shield.
pub fn spec_op_call_parent(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    let parent_sym = impl_parent_sort_of_op(kb, op_sym)?;
    crate::kb::op_info::lookup_operation_info(kb, op_sym)?;
    sort_is_parametric(kb, parent_sym).then_some(parent_sym)
}

/// WI-210 — `op_sym` is a "spec operation" if it is declared in a sort
/// that has at least one `sort <Param> = ?` declaration AND the
/// operation has no body. Spec operations are subject to call-site
/// dispatch via `SortProvidesInfo` lookup.
///
/// Returns the *parent sort* symbol (the spec sort) when `op_sym`
/// qualifies; `None` otherwise.
pub fn lookup_spec_op_dispatch(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    // The op must be body-less (declaration only): a DEFAULTED spec op is a
    // normal-bodied op the runtime can run directly, not a call-site dispatch
    // placeholder. (Its carrier-override path is the body-agnostic
    // [`spec_op_parent_sort`] — WI-444.)
    let parent_sym = spec_op_parent_sort(kb, op_sym)?;
    if !operation_has_no_body(kb, op_sym) {
        return None;
    }
    Some(parent_sym)
}

/// WI-857 — [`resolve_op_target`] with the `NoProvider` refusal, for every reader
/// that DISPATCHES through a dictionary. `Err` carries the rendered reason.
///
/// The guard lives here, beside the resolution, rather than at eval's
/// `dispatch_via_sort_ops_table`: `resolve_op_target`'s own doc promises that the
/// interpreter and the reflect `Dictionary.resolveOp` / `ops` faces share it "so the
/// three cannot drift", and a guard placed only in the interpreter would have made
/// them drift in exactly the direction that doc names — a body could reach a marker
/// slot through `Dictionary.sub` and `resolveOp` it into an `OpRef` on the spec op,
/// which is the silent fall-through to the host default the marker exists to refuse.
///
/// `Dictionary.impl` deliberately does NOT go through this: it is an INSPECTION face
/// ("which impl did this resolve to"), and the marker is a truthful answer to it —
/// self-describing by name, and the only way to observe a recorded absence at all.
/// The line is dispatch-vs-inspect, not read-vs-write.
pub(crate) fn resolve_op_target_checked(
    kb: &KnowledgeBase,
    impl_sym: Symbol,
    spec_op: Symbol,
) -> Result<Symbol, String> {
    if let Err(msg) = marker_refusal(kb, impl_sym) {
        return Err(format!(
            "cannot dispatch `{}`: {msg}",
            kb.qualified_name_of(spec_op),
        ));
    }
    Ok(resolve_op_target(kb, impl_sym, spec_op))
}

/// WI-857 — `Err(sentence)` iff `functor` is a [`absence_marker_sym`] marker. The ONE
/// place the refusal is worded, for every reader that treats a dictionary as usable:
/// dispatch ([`resolve_op_target_checked`]), the bulk reflect face (`Dictionary.ops`,
/// whose per-element check can never fire because a marker has no ops), and eval's
/// projection descent.
///
/// WI-865 — AND IT NO LONGER HEDGES. The sentence used to name all three of "nothing
/// provides it" / "more than one does" / "entered from a host entry point" at every
/// read, because the marker carried no payload and the reader could not be sent to
/// the wrong fix. Each is now its own arm, off the [`AbsenceRecord`] the mint filed —
/// which is what makes a TIE report as a tie, naming the candidates that tied and the
/// bracket that picks one, exactly as WI-843's `describe_resolution_failure` does for
/// the same tie at a call's own goal. The two are deliberately not shared: this one
/// has no goal text, no span and no candidate ORDER to offer, and inventing them here
/// is the mis-attribution WI-843 exists to have closed.
///
/// The shared head — "pins no provider" — is load-bearing wording, not a leftover:
/// it is what every reader of this refusal keys on, and the arms differ after it.
pub(crate) fn marker_refusal(kb: &KnowledgeBase, functor: Symbol) -> Result<(), String> {
    if !is_absence_marker(kb, functor) {
        return Ok(());
    }
    let head = "the requirement it reads pins no provider";
    // A marker with no filed record: reachable only when something minted the symbol
    // without going through `absence_marker_sym`. Still refused (that is
    // `is_absence_marker`'s job) and still says so, but it cannot say more — and it
    // says THAT rather than reciting the old hedge, so a missing record reads as a
    // missing record and not as a program defect.
    let Some(rec) = kb.absence_record(functor) else {
        return Err(format!(
            "{head}, and no reason was recorded for the marker. Declare a provider, \
             select one at the call site, or enter through `call_with_requirements`."
        ));
    };
    let detail = match rec {
        AbsenceRecord::HostEntry => {
            "this frame was entered from a host entry point that supplied no \
             dictionary. Enter through `call_with_requirements` to supply one."
                .to_string()
        }
        AbsenceRecord::Slot { spec, why, below } => {
            let slot_qn = kb.qualified_name_of(*spec);
            // WHERE the absence sits — the slot — as CONTEXT for a failure that may
            // be several levels below it. Emitted exactly when the failure IS below,
            // so the ordinary case reads as one fact and not as a redundant pair.
            //
            // ON `below`, NOT ON SPEC IDENTITY: the two specs can be equal with the
            // failure still a level down (`provides Base[T = Wrap[E]]` beside
            // `requires Base[T = Bool]`), and suppressing the clause there says "the
            // failure is at this level" about a carrier that provides exactly this
            // level — the same falsehood one coordinate over. Driven:
            // `wi865_absence_reason_test::a_failure_below_the_slot_on_the_same_spec…`.
            //
            // AND `below` DECIDES WHOSE BINDINGS THE SENTENCE ASSERTS, not just
            // whether to name the slot. "at the bindings this dictionary was built
            // for" is true only at the slot's own level; one level down they are a
            // DIFFERENT goal's, and the same fixture reads as a falsehood without this
            // half — `SelfDeep` provides `Base` at exactly those bindings, and it is
            // `Base[T = Bool]` that has none.
            match why {
                UnavailableWhy::NoProvider { goal } if *below => format!(
                    "nothing provides `{}` where it was reached, while filling this \
                     dictionary's `{slot_qn}` slot. Declare a provider for it.",
                    kb.qualified_name_of(*goal),
                ),
                UnavailableWhy::NoProvider { goal } => format!(
                    "nothing provides `{}` at the bindings this dictionary was built \
                     for. Declare a provider for it.",
                    kb.qualified_name_of(*goal),
                ),
                UnavailableWhy::Ambiguous { goal, candidates } => {
                    let named = candidates
                        .iter()
                        .map(|c| format!("`{}`", kb.qualified_name_of(*c)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    // Spelled here rather than hoisted above the `match`: this is the
                    // only arm that appends the clause (the `NoProvider` below-arm
                    // builds the phrase into its own sentence, and `Cyclic` emits
                    // none), and a shared binding with one consumer reads as though
                    // the wording were common when it is not.
                    let at_slot = if *below {
                        format!(", reached while filling this dictionary's `{slot_qn}` slot")
                    } else {
                        String::new()
                    };
                    // NO BRACKET IS OFFERED, and that is WI-843's verdict, not a
                    // shortfall: an `Unavailable` is only ever a SUB-goal of a
                    // resolved tree (see the variant), where §4.5 step 0 deliberately
                    // keeps a call-site key out — `TieRepair::SubGoal` records both
                    // spellings being driven to a refusal. Advertising one here would
                    // print advice that does not load.
                    format!(
                        "MORE THAN ONE provider matched `{}` here{at_slot} — {named} — \
                         and none is more specific, so the slot was left unpinned. \
                         Retract one of those provisions or make one more specific; a \
                         call-site bracket does not reach a dictionary sub-slot.",
                        kb.qualified_name_of(*goal),
                    )
                }
                // NO SLOT CLAUSE HERE, WHATEVER `below` SAYS. The clause's job is "the
                // thing that failed is elsewhere, look there"; for a cycle the thing
                // that failed is this goal RE-ENTERED, which is what "cyclic" already
                // says, so the clause points back at the level it just came from.
                // Driven by /code-review on `SELF_CONDITIONAL`, where it rendered as
                // "resolving `Base` here is cyclic … (reached while filling this
                // dictionary's `Base` slot)".
                //
                // The reason is that, NOT "a cycle is always `below`" — which is how
                // this was first written and is not established: a cycle detected at a
                // spec-half sub-goal's OWN level (mutually-requiring specs) would be
                // recorded `below: false`, and whether such specs load is UNMEASURED.
                // Nothing here depends on it, since the arm emits no clause either
                // way — but `below` is still part of the record and must stay in the
                // marker name, or two cyclic absences differing only in it would
                // collide on one symbol.
                UnavailableWhy::Cyclic { goal } => format!(
                    "resolving `{}` here is cyclic — a conditional provision depends on \
                     the instance being built.",
                    kb.qualified_name_of(*goal),
                ),
                // WI-20260830-NX4FD. NO SLOT CLAUSE and no `below` split: this absence
                // is only ever recorded AT its own slot (the bridge pins per slot, and
                // there is no sub-goal walk to inherit a deeper failure from), so the
                // "look one level down" clause would point at nothing.
                UnavailableWhy::UnderDetermined => format!(
                    "the argument types did not pin every type-parameter of \
                     `{slot_qn}`, and its providers left no single completion for the \
                     rest, so no provider was searched for this slot. Give the \
                     operation a parameter that determines the element, or a provision \
                     that decides it at this carrier."
                ),
                // WI-456 — likewise recorded only at its own slot.
                // Recorded only by value-directed dispatch (`NamedSlotTies::RecordAbsent`),
                // so the route in the sentence is the one that took it.
                UnavailableWhy::NamedSlotNotCarried => format!(
                    "`{slot_qn}` fills a NAMED requirement slot of the carrier, and this \
                     operation was reached by dispatching on a VALUE, which carries its \
                     sort but none of its type parameters — so the provider the value's \
                     construction chose for the slot cannot be recovered here, and more \
                     than one could have been. Reach the operation through a typed call \
                     whose carrier type writes the slot, where the typer pins it."
                ),
            }
        }
    };
    Err(format!("{head} — {detail}"))
}

/// Resolve `spec_op` against a dispatching impl sort to its concrete target op —
/// the load-time `sort_ops_table[impl_sym][op_short]` (WI-240): the impl's own
/// `S.<op>` override when it has one (filtering the body-less spec-op
/// placeholder), else the RETROACTIVE-INSTANCE-FACT binding
/// (`fact HasZero[T = Tag, zero = tagZero]`, WI-431), else `spec_op` itself (a
/// genuine spec rewrite-rule / builtin default, or a Pin-now / already-concrete
/// op the dict carries no row for).
///
/// The single source for dict-threaded op resolution: the interpreter's
/// `Interpreter::dispatch_via_sort_ops_table` and the reflect
/// `Dictionary.resolveOp` / `Dictionary.ops` faces all call this so the three
/// cannot drift. `spec_op` is expected to be a RESOLVED (canonical) symbol —
/// the interpreter's `fn_sym` is, and the reflect callers pass symbols minted by
/// `impl`/`op`/`lookup_symbol`, all resolved.
pub fn resolve_op_target(kb: &KnowledgeBase, impl_sym: Symbol, spec_op: Symbol) -> Symbol {
    let fn_qn = kb.qualified_name_of(spec_op);
    let Some((_, op_short)) = fn_qn.rsplit_once('.') else {
        return spec_op;
    };
    let Some(op_short_sym) = kb.lookup_symbol(op_short) else {
        return spec_op;
    };
    // The carrier's own table entry: a real override (`S.<op>` with a body), or
    // the spec op itself — which is EITHER a genuine spec rewrite-rule / builtin
    // default (runnable) OR, for a RETROACTIVE INSTANCE FACT, the inherited
    // body-less placeholder with no impl. Filter that placeholder so it doesn't
    // mask the instance-fact binding below; a genuine default still rides the
    // `spec_op` fall-through (its rewrite rule / builtin runs).
    let own = kb
        .sort_ops_lookup(impl_sym, op_short_sym)
        .filter(|&op| op != spec_op);
    own.or_else(|| {
        let spec = lookup_spec_op_dispatch(kb, spec_op)?;
        instance_fact_op_binding(kb, impl_sym, spec, op_short)
    })
    .unwrap_or(spec_op)
}

/// WI-616 — the carrier sort's OWN member for a spec op's short name,
/// REGARDLESS of how it is backed (a runnable body, or SLD rules only — the
/// `Set.eq`/`Map.eq` membership instances are bodyless rule-backed ops). The
/// body-agnostic core [`carrier_override_op`] layers its runnable-body gate on.
/// The two non-`carrier` cases the parent check rejects are NOT overrides:
///   * the spec op itself — a carrier that only INHERITS the default;
///   * a DIFFERENT spec's same-short-name default the carrier also inherits
///     (`Stream.find` when resolving `Iterable.find` on a `List` that provides
///     both `Stream` and `Iterable`) — `sort_ops_lookup` returns one arbitrarily,
///     and it is not the carrier's own member.
pub(crate) fn carrier_own_op(
    kb: &KnowledgeBase,
    carrier: Symbol,
    spec_op: Symbol,
    op_short_sym: Symbol,
) -> Option<Symbol> {
    let carrier_canon = kb.canonical_sort_sym(carrier);
    kb.sort_ops_lookup(carrier, op_short_sym)
        .filter(|&o| o != spec_op)
        .filter(|&o| {
            impl_parent_of_op(kb, o).map(|p| kb.canonical_sort_sym(p)) == Some(carrier_canon)
        })
}

/// WI-444 — the carrier sort's OWN member backing a (possibly defaulted) spec
/// op, when it genuinely OVERRIDES the spec rather than merely inheriting it —
/// [`carrier_own_op`] narrowed to a RUNNABLE impl (the eval-side gate: a
/// bodyless rule-backed member is not invocable by the interpreter).
/// Returns the override op symbol, or `None` (run the spec's default body).
///
/// WI-1010 — THE TWO WI-444 SITES NO LONGER READ THIS: they read
/// [`carrier_override_suppliers`], which is this predicate's rule applied to all three
/// supply routes instead of route 1 alone. The one remaining caller is WI-606's
/// [`concrete_self_receiver_override`], whose doc records why it stays route-1. Kept
/// as its own function because that caller narrows the result further, and because
/// `carrier_own_op` + this filter is the definition `carrier_override_suppliers`
/// preserves bit-for-bit for route 1.
///
/// WI-876 widened "runnable" from a BODY to executability — a body-less
/// member whose implementation is the HOST's is runnable too, and rejecting it here
/// meant the spec's default body ran INSTEAD of the carrier's own host code.
/// MEASURED once `Float` declared its own IEEE `gt`: `gt(nan, 1.0)` fell through to
/// `PartialOrd`'s `compare`-based default and died `OperationBodyMissing
/// {Ord.compare}` — `Float` provides no `Ord` — and a `String` comparison
/// inside a witness ordering fell through the same way into an
/// `AmbiguousSpecOpDispatch` between `String`'s own `compare` and the program's two
/// witnesses. Both are the carrier's own implementation not being seen.
///
/// The gate still excludes what it was built to exclude: a member that is merely
/// DECLARED, or backed only by rules, which the interpreter cannot invoke (and which
/// a same-short-name collision — `sub` ↔ `Numeric.sub` — would otherwise capture).
/// The predicate is [`op_is_interpretable`], not the `op_is_executable` this paragraph
/// named before WI-886 split the two: a cpp `operation_map` entry is a real
/// implementation that THIS interpreter cannot call, so counting it would select a
/// member eval then fails to find.
pub(crate) fn carrier_override_op(
    kb: &KnowledgeBase,
    carrier: Symbol,
    spec_op: Symbol,
    op_short_sym: Symbol,
) -> Option<Symbol> {
    carrier_own_op(kb, carrier, spec_op, op_short_sym).filter(|&o| op_is_interpretable(kb, o))
}

/// WI-1010 — every RUNNABLE implementation of a DEFAULTED spec op that reaches
/// `carrier`, from ALL THREE supply routes.
///
/// [`carrier_override_op`] answers the same question for route 1 alone, and that
/// was the defect: a spec op with a default body consumed on a carrier whose impl
/// arrives through a WI-431 instance fact resolved to `None` here, so the DEFAULT
/// ran and the written binding meant nothing — a silent wrong answer, since the
/// loader had already validated the binding's signature
/// ([`check_instance_fact_op_signatures`]) and counted it as backing. WI-444's rule
/// is that defaults fill GAPS and do not SHADOW; a written binding is not a gap,
/// whichever syntax writes it.
///
/// This is [`spec_op_suppliers_for_carrier`] — the SAME owner the body-less path
/// reads (WI-842 / proposal 058 §4.9) — narrowed to what the interpreter can run.
/// Sharing it is the point: the alternative, `carrier_override_op(…).or_else(fact)`,
/// would have been a FOURTH enumeration of the three routes and a first-match chain
/// of exactly the shape WI-842 deleted, blind to the second candidate again.
///
/// THE INTERPRETABILITY FILTER IS THIS READER'S OWN, and MUST NOT be pushed down into
/// [`spec_op_suppliers_for_carrier`], for two independent reasons.
///
/// WHY IT IS NEEDED HERE: this question has a fallback and the body-less one does not.
/// WI-876 measured that running the spec's default beats selecting a member the
/// interpreter cannot call — the latter turns a working call into
/// `OperationBodyMissing`. So an unrunnable candidate is not a supplier at all for
/// this question, and is dropped BEFORE the count: a rules-only member beside a fact
/// binding leaves ONE supplier, not an ambiguity between a live impl and one nothing
/// can call. DRIVEN by `an_unrunnable_own_member_is_not_a_supplier`.
///
/// WHY IT MUST NOT MOVE DOWN — the load-bearing one, and the reason the shared owner
/// is left alone rather than "improved": [`op_is_interpretable`] is BACKEND-RELATIVE.
/// WI-886 made its mapping leg `is_interpreter_mapped_op` (rust only), so a
/// cpp-`operation_map`ped member answers `false` here. The other consumer of the
/// shared owner is eval's body-less `resolve_spec_op_target_by_value`, whose ≥2 arm is
/// a COHERENCE refusal — "did the author supply two implementations?" — and that
/// question must not change answer with the host backend, which is exactly what
/// filtering inside the owner would do. Note this is NOT what the test above pins:
/// moving the filter down keeps the whole suite green, because the tree has no
/// cpp-mapped rival to make the two counts diverge. The argument is the guard.
///
/// Route 1's answer is preserved bit-for-bit — `carrier_own_op` + `op_is_interpretable`
/// is [`carrier_override_op`] spelled out — so a carrier with no provision-supplied
/// impl resolves exactly what it resolved before.
pub(crate) fn carrier_override_suppliers(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier: Symbol,
    spec_op: Symbol,
    op_short_sym: Symbol,
) -> SmallVec<[SpecOpSupplier; 2]> {
    let mut cands = spec_op_suppliers_for_carrier(kb, spec_sort, carrier, spec_op, op_short_sym);
    cands.retain(|c| op_is_interpretable(kb, c.target));
    cands
}

/// WI-876 — can the INTERPRETER run `op`? A runnable body, or a HOST
/// implementation: a resolver builtin, or an `operation_map` binding
/// ([`KnowledgeBase::is_host_mapped_op`]).
///
/// The third leg is what a binding block's `operation_map` buys. Before it existed a
/// host implementation had nowhere to be keyed per carrier, so it was registered on
/// the SPEC op — where `is_builtin` answered `true` for EVERY carrier, including ones
/// the implementation could not handle. Keyed per carrier, this predicate answers for
/// the carrier that actually has an implementation, and for no other.
///
/// TWO PREDICATES, because there are two questions and they have different answers.
/// This one is the LOAD CHECK's — "does an implementation exist anywhere?" — and its
/// `kb.is_builtin` leg reads the RESOLVER's `BuiltinTag` registry, which is a real
/// implementation for the SLD world even when the interpreter has none. Eval must not
/// ask it: see [`op_is_interpretable`].
///
/// The two HOST legs are asked FIRST: both are `HashMap`/`HashSet` hits, whereas
/// `op_has_runnable_body` goes through `lookup_operation_info`, which builds a whole
/// `OpInfoRecord` (cloning params, return type, effects, type params, requires,
/// ensures) to read one `is_some()`. The order is pure short-circuiting — all three
/// legs are side-effect-free predicates — and every carrier this ticket introduces
/// (`Int64.gt`, `Float.lte`, …) answers from a host leg.
pub(crate) fn op_is_executable(kb: &KnowledgeBase, op: Symbol) -> bool {
    kb.is_builtin(op) || kb.is_host_mapped_op(op) || op_has_runnable_body(kb, op)
}

/// WI-876 — can the INTERPRETER run `op`? [`op_is_executable`] MINUS the resolver
/// builtin leg: a runnable body, or an `operation_map` host implementation THIS
/// runtime registers.
///
/// The two registries are DIFFERENT MAPS and this ticket made them maximally
/// divergent — `anthill.prelude.PartialOrd.gt` is in the resolver's (`kb.builtins`,
/// `BuiltinTag::Gt`) and NOT in the interpreter's, its eval registration having moved
/// per carrier. So `kb.is_builtin` answers "yes, an implementation exists" for four
/// operations the interpreter cannot call, and an eval-side gate that trusted it would
/// SELECT such a member as a carrier's override and skip the spec default that would
/// have worked. Nothing routes through that today — every carrier-keyed resolver tag
/// is also `operation_map`ped — but the gate must not depend on that coincidence, and
/// WI-880's migration of the remaining families is exactly where it would stop holding.
///
/// WI-886 — the LANGUAGE is part of "can this runtime run it", and the mapping leg
/// therefore reads [`KnowledgeBase::is_interpreter_mapped_op`] (rust only) rather than
/// the program-wide `is_host_mapped_op` that [`op_is_executable`] wants. The same
/// argument, one axis over: a cpp `operation_map` entry is a real implementation of
/// the operation and NOT one this interpreter has registered, so counting it here
/// would select a carrier override eval cannot find. Live as of WI-886, which gives
/// cpp-gen the first non-rust `operation_map` blocks in the tree.
pub(crate) fn op_is_interpretable(kb: &KnowledgeBase, op: Symbol) -> bool {
    kb.is_interpreter_mapped_op(op) || op_has_runnable_body(kb, op)
}

/// WI-231 — per-call-site classification produced by the typer for
/// consumption by the requirement-insertion pass (`kb/req_insertion.rs`).
/// Each tagged apply site carries its `CallClass` on the apply
/// occurrence's `OccurrenceEntry`; `req_insertion::run` walks the
/// classified occurrences and emits the corresponding rewrite into
/// `kb.dispatch_rewrites`.
///
/// External codegen targets (Rust monomorphization, reflection
/// tooling, alternative elaborations) can read these classifications
/// directly (via `kb.occurrence_store().classifications_iter()`) and
/// choose to emit their own elaboration rather than invoking the
/// standard pass.
///
/// Reference: docs/design/operation-call-model.md §"Pass structure:
/// typer first, requirement-insertion separate".
#[derive(Clone, Debug)]
pub enum CallClass {
    /// Pin-now rewrite from a spec op to a concrete impl op (WI-218).
    /// The impl's parent sort has no `requires`, so the call becomes
    /// a plain `apply(fn = Ref(impl_op_sym), args)` — no apply_within
    /// wrap, no requirements channel.
    PinNow {
        spec_op_sym: Symbol,
        impl_op_sym: Symbol,
    },
    /// Pin-now to an impl whose parent sort has `requires`, OR a
    /// Direct call to a non-spec op whose parent has `requires`
    /// (WI-222 Phase E (i)). Emits `apply_within(fn = Ref(fn_target),
    /// args, requirements = …)`. `resolved_tree` is `Some` for the
    /// Pin-now path (WI-228 tree-threaded projection); `None` for
    /// Direct (falls back to per-dep search against `caller_requires`
    /// derived from `enclosing_sort`).
    ///
    ConcreteApplyWithin {
        fn_target_sym: Symbol,
        callee_spec_sort: Symbol,
        spec_op_sym: Symbol,
        enclosing_sort: Option<Symbol>,
        resolved_tree: Option<ResolvedRequiresNode>,
        /// WI-415: the parent-bundle dispatching dict
        /// (`Dictionary(<resolved sub-reqs>, impl: callee_parent)`),
        /// built at COMPILE stage by the typer when the call-site
        /// substitution pinned the callee parent sort's type params
        /// concretely — a cross-sort / no-enclosing-sort direct call such
        /// as `member(2, [1,2,3])` from a plain namespace, where the
        /// same-sort requirement-inheritance path cannot supply the
        /// callee's `requires`. Eval installs it into the callee's frame
        /// via the same path an explicit `apply_within` dict takes, with
        /// no requirement re-resolution at runtime. `None` when no param
        /// binds concretely (an in-sort call inherits the enclosing frame's
        /// requirement at eval; a cross-sort abstract call has no covering
        /// requirement — a pre-existing gap) and for the Pin-now path.
        dispatch_dict: Option<TermId>,
        /// WI-822 LEG 1 — one entry per OP-SCOPED `requires` slot of
        /// `fn_target_sym` (WI-448/WI-562), in op-chain order, each the
        /// dictionary expression that fills it: a constructed
        /// `Dictionary(…, impl: P)` for a call-site-pinned element, or a caller-frame
        /// `var_ref(__req_*)` forward for one the caller's own chain covers. `None`
        /// at a slot that could not be projected here — the callee is entered
        /// WITHOUT it and a body that reads it raises (see
        /// [`build_op_scoped_dicts`]). EMPTY for an operation that declares no
        /// `requires` of its own, which is nearly all of them.
        ///
        /// SEPARATE from `dispatch_dict`, not folded into it: that one is a spec
        /// INSTANCE and these are this CALL's evidence for this OPERATION. Eval
        /// appends them to the frame AFTER the sort half, matching the slot order
        /// [`op_dict_entries`] lays out.
        ///
        /// WI-20260921-28TAT MOVED IT OUT, onto `NodeOccurrence`'s own `op_dicts`
        /// stamp; this paragraph stays because it is still what the stamp holds. What
        /// changed is only WHERE: a dispatch class records where a call GOES, and the
        /// callee's op-scoped input is owed whether or not the call goes anywhere.
        /// WI-822 LEG 1 — the CALLER's operation, whose chain the `var_ref` forwards
        /// above read at eval. Recorded beside `enclosing_sort` because a forward may
        /// now name an OP slot, which no sort alone can name.
        enclosing_op: Option<Symbol>,
    },
    /// Defer-to-requirement (WI-222 Phase C+D): dispatch deferred to
    /// runtime via `apply_within(fn = requirement_at_current(slot,
    /// op = some(op_short)), args, requirements = …)`. The impl is
    /// determined at dispatch time by reading `frame.requirements[slot]`.
    ///
    /// WI-232: `resolved_spec` is the matched requires entry from the
    /// caller's chain — `enclosing_requires[slot]` at classification
    /// time. Embedding it eliminates the slot→entry re-indexing in
    /// `req_insertion::run`; `resolved_spec.required_sort` replaces the
    /// previous parallel `spec_sort` field.
    ///
    /// WI-239: `slot` is always a DIRECT requirement slot. `proj_path`
    /// descends into that direct requirement's tree-shaped value: empty
    /// when the spec *is* the direct requirement (read the frame slot
    /// directly — the original WI-222 case), non-empty when the spec is
    /// reached transitively, by applying one `requirement_at_sort`
    /// projection per index. The pre-WI-239 flat `requires` chain made
    /// every transitive spec a top-level slot, so `proj_path` was always
    /// empty; the direct-chain ABI moves transitive specs inside their
    /// direct parent's bundled value.
    ///
    /// WI-822 LEG 1: `slot` indexes the ENCLOSING OPERATION's chain — its sort's
    /// slots then its own op-scoped ones ([`op_dict_entries`]) — so a slot at or past
    /// the sort half is an op-scoped requirement, which only `enclosing_op` can name.
    /// The sort half's indices are unchanged, which is what keeps every pre-existing
    /// classification pointing at the slot it always did.
    DeferToRequirement {
        spec_op_sym: Symbol,
        op_short_sym: Symbol,
        resolved_spec: RequiresEntry,
        slot: usize,
        proj_path: SmallVec<[usize; 2]>,
        enclosing_sort: Option<Symbol>,
        /// WI-822 LEG 1 — the operation whose frame `slot` indexes. `None` outside an
        /// operation body (the rule-body dot-dispatch sweep), where only a sort slot
        /// can be named.
        enclosing_op: Option<Symbol>,
    },
    /// WI-325: dispatch returned `NoCandidates` AND the call's per-call
    /// substitution leaves at least one of the spec's type parameters
    /// abstract (`is_type_param_value`). The typer detects the abstract
    /// case here (where the subst is still in scope) and tags the
    /// occurrence; `req_insertion::run` translates the tag into a
    /// `MissingRequiresForSpecOp` error. Concrete-binding `NoCandidates`
    /// is **not** classified — it remains a legitimate pass-through
    /// (host builtin / spec-derived rule may resolve at runtime).
    ///
    /// `abstract_params` lists the spec's short type-param names
    /// (e.g. `T`) that the call left abstract. `enclosing_sort` is
    /// `Some(spec_sort_sym)` only for self-recursive calls inside the
    /// spec's own body — `req_insertion::run` filters those out.
    UnresolvedSpecOp {
        spec_op_sym: Symbol,
        spec_sort_sym: Symbol,
        abstract_params: SmallVec<[Symbol; 2]>,
        span: Option<Span>,
        enclosing_sort: Option<Symbol>,
    },
    /// WI-420: a bare operation reference eta-lifted to a `Value::OpRef` whose
    /// op needs a requirement dictionary. `dict` is the dispatching-dict
    /// expression, built at the eta site: a caller-frame `var_ref(__req_self)`
    /// for a SAME-SORT eta (the op's own sort dict), or — for a cross-sort eta —
    /// `Dictionary(…, impl: callee_parent)` for a concrete dep / a
    /// caller-frame `var_ref` projection for an abstract one (via
    /// `build_concrete_dispatch_dict` from the expected arrow's pinning). Eval
    /// evaluates it IN THE ETA-SITE FRAME at mint and stores the resulting
    /// requirement on the `OpRef`, then installs it into the callee frame at
    /// apply. A requires-carrying eta (INCLUDING a same-sort eta, which cannot
    /// inherit because an eta'd `OpRef` escapes to a foreign apply frame) carries
    /// `dict = Some(...)`; a requires-free or namespace-level op carries
    /// `dict = None` and forwards the caller's requirements. WI-700: the marker is
    /// now set at EVERY eta site (not only requires-carrying ones), because a
    /// NULLARY eta needs it to disambiguate "mint the `OpRef`" from "zero-arg
    /// call" at eval — an arity-≥1 bare ref is unambiguously a function value, but
    /// a bare `poke` is not, so `None` here is the load-bearing "this occurrence
    /// is an eta, not a call" signal.
    EtaOpRef {
        dict: Option<TermId>,
        /// WI-1087: `A`'s component labels, in declared order, when the slot this
        /// reference is lifted into reads `A` as the callback's PARAMETER LIST — see
        /// [`Value::OpRef`](crate::eval::Value)'s field of the same name for what the
        /// runtime does with them and why the value cannot re-derive them.
        spread_labels: Option<std::rc::Rc<[Symbol]>>,
        // WI-1091's op half — the OPERATION'S OWN `requires` slots, built at the eta
        // site by the very `build_op_scoped_dicts` a written call site uses — LIVED
        // HERE until WI-20260921-28TAT moved it to `NodeOccurrence`'s `op_dicts` stamp.
        // It is still the whole supply for the shape that needed it (`List.member`
        // carries `requires Eq[T]` on the OPERATION while `List` requires nothing, so
        // `dict` above is `None`); what changed is that the evidence no longer depends
        // on this variant being the one that got written.
    },
}

/// WI-210 — dispatch result for a spec-op call.
///
/// WI-843: no longer `Copy`. `Ambiguous` carries the candidates that tied, because
/// under 058 tier 3 it is the ONLY refusal the author gets — the load-time
/// two-witness one that used to name them is gone. Dropping `Copy` is deliberate:
/// the alternative was to re-derive the candidate list at the diagnostic site from
/// the goal, which is a second walk that can disagree with the one that actually
/// tied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DispatchOutcome {
    /// No `SortProvidesInfo` records exist for this spec at all.
    /// Dispatch is opt-in per spec: with zero candidates, the call
    /// type-checks against the spec's signature (legacy semantics)
    /// — no impl is required. Stdlib specs like `Numeric` and `Map`
    /// rely on this to be called without explicit impl declarations.
    NoCandidates,
    /// Exactly one candidate's bindings match the per-call subst.
    /// Carries the impl operation symbol for the runtime to call.
    Unique(Symbol),
    /// Candidates exist but none match the inferred bindings.
    /// User likely forgot to declare an impl at the right binding.
    ///
    /// WI-869 — `unmet` is the failure the SEARCH observed, verbatim from it (the
    /// reason WI-828 gives one level over: a second walk can disagree with the one that
    /// failed). For a conditional provision the goal it names is a CONDITION and not the
    /// call's own goal, which is the whole diagnostic.
    ///
    /// A STRUCT and not a bare `String`, because the first cut was a bare one and it
    /// silently dropped `ResolutionResult::NoMatch.hint` — the actionable half ("add
    /// `fact X[…]` or `requires X[…]` in scope") at the one site whose purpose is
    /// actionability. `InstanceTie`'s doc records the same lesson from the other side:
    /// pre-rendering what the emitter should render is how a message loses what it was
    /// added to carry.
    NoMatch { unmet: Option<Box<DispatchFailure>> },
    /// Two or more candidates match and the call selected none — 058 §4.1 tier 3.
    /// The payload is the tie itself, forwarded from the level that observed it.
    Ambiguous(InstanceTie),
    /// WI-221 (defer-to-requirement, open-bound trigger): spec sort
    /// reached via the enclosing sort's `requires` chain. Impl varies
    /// per requirement value at runtime, so Pin-now rewrite is skipped.
    /// See `docs/design/operation-call-model.md` §"Defer-to-requirement
    /// detection".
    Deferred,
}

/// WI-221/WI-222 — defer-to-requirement detection (open-bound trigger).
/// Returns the **slot index** (position in `chain`) of the matching requires
/// entry, or `None` if the spec sort isn't reached via this chain. WI-222 needs
/// the slot to populate `requirement_at_current(slot = N)` in the rewritten
/// `apply_within`. The chain is cached on `TypingEnv` (see `set_enclosing_sort`)
/// to avoid re-walking `SortRequiresInfo` per apply check.
///
/// WI-613: when MORE THAN ONE entry wildcard-covers the call — a sort with two
/// `requires` of the SAME spec over distinct element params (`requires Eq[A],
/// Eq[B]`) — a blind first-match attributes the call to the wrong slot and reads
/// the wrong `__req_*` dictionary at runtime. `disambig` (the σ context) breaks
/// the tie by element identity: the unique covering entry whose element shares a
/// σ-class with the per-call value. A `None` `disambig` keeps first-match — the
/// `.is_some()` defer-trigger caller (`dispatch_spec_op_cached`) only needs
/// whether ANY entry covers, not which.
pub fn find_requires_slot(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    chain: &[RequiresEntry],
    disambig: Option<&SigmaCtx>,
) -> Option<usize> {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    // Each coarse-covering chain entry paired with its σ verdict (`Vacuous` with
    // no σ context). WI-829: a `Refutes` cover (a shallow-vs-deep compound the
    // head fallback coarse-accepted) is dropped — NO cover — the flat-chain twin
    // of [`find_requires_location`] and of the forwarding dual (`entries_cover`,
    // which gates a σ-disagreeing cover at every arity). Among the survivors the
    // WI-613 soft tie-break picks the first σ-precise, else the first: slot
    // attribution names the frame's OWN dictionary for a body call and does not
    // forward across a call boundary, so a genuinely-ambiguous (non-refuting)
    // cover set keeps the softer policy. No σ context ⇒ all `Vacuous` ⇒ nothing
    // refutes and none is precise ⇒ the first covering index (pre-WI-613).
    let survivors: SmallVec<[(usize, SigmaVerdict); 2]> = chain
        .iter()
        .enumerate()
        .filter_map(|(i, entry)| {
            if !entry_matches_subst(kb, subst, spec_sort, &spec_qn, entry) {
                return None;
            }
            let v = disambig.map_or(SigmaVerdict::Vacuous, |ctx| {
                entry_sigma_verdict(kb, ctx, spec_sort, &spec_qn, entry)
            });
            (v != SigmaVerdict::Refutes).then_some((i, v))
        })
        .collect();
    let idxs: SmallVec<[usize; 2]> = (0..survivors.len()).collect();
    pick_precise(&idxs, |k| survivors[k].1 == SigmaVerdict::Precise).map(|k| survivors[k].0)
}

/// WI-613 — resolve `entry`'s type-param bindings against the per-call `subst`,
/// yielding one `(per_call_value, entry_value)` pair per CONSTRAINING binding
/// (a spec param that resolved through `subst` to a concrete `Value::Term`).
/// Non-constraining bindings are dropped, exactly as the pre-WI-613
/// `entry_matches_subst` per-binding `continue` did:
///   * an unbound spec param — the OPEN-T defer trigger (impl picked at runtime
///     from the caller's requirement value);
///   * a denoted-`Node` carrier (WI-348 Phase C; flagged loudly in debug);
///   * a non-type-param binding (an auto-bound op like `eq`/`neq`), or an
///     unresolvable alias.
///
/// `None` iff `entry` is not a `requires` for `spec_sort`, or its spec term is
/// malformed (the structural reject — a coarse non-match). `Some(empty)` is a
/// VACUOUS match: a plain bindingless `requires` (e.g. `requires Paintable`), or
/// a spec whose every binding is non-constraining.
///
/// The post-`resolve_requires_bindings` SortView carries bindings for both
/// type-params (`T`) and auto-bound operations (`eq`, `neq`); only the type-param
/// bindings constrain the substitution, detected via SortAlias resolution (only a
/// spec param produces a `Term::Var` alias target). Shared by
/// [`entry_matches_subst`] (wildcard cover) and [`entry_sigma_verdict`]
/// (σ-class verdict) so the two agree on which bindings constrain the call.
fn entry_type_param_bindings(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    spec_qn: &str,
    entry: &RequiresEntry,
) -> Option<SmallVec<[(TermId, TermId); 2]>> {
    if entry.required_sort != spec_sort {
        return None;
    }
    let bindings: SmallVec<[(Symbol, TermId); 2]> = match &entry.spec {
        // WI-662: ground fast path — byte-identical to the pre-WI-662 term read.
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Fn {
                functor,
                named_args,
                pos_args,
            } => {
                if is_sort_view_functor(kb, *functor) {
                    named_args.clone()
                } else if pos_args.is_empty() && named_args.is_empty() {
                    // Plain sort term, e.g. `requires Paintable`.
                    SmallVec::new()
                } else {
                    return None;
                }
            }
            Term::Ref(_) | Term::Ident(_) => SmallVec::new(),
            _ => return None,
        },
        // A denoted spec — its SortView bindings via the shared view unwrap (a
        // denoted binding value drops out; the per-call resolution below consumes
        // only the type-param bindings, all of which are ground terms).
        other => match unwrap_spec_view_value(kb, other) {
            Some((_, bindings)) => bindings,
            None => return None,
        },
    };
    let mut out: SmallVec<[(TermId, TermId); 2]> = SmallVec::new();
    for (binding_short_sym, entry_value) in &bindings {
        let binding_short = kb.local_name_of(*binding_short_sym);
        let param_qn = format!("{spec_qn}.{binding_short}");
        let Some(param_qn_sym) = kb.try_resolve_symbol(&param_qn) else {
            continue;
        };
        let Some(alias_target) = resolve_sort_alias(kb, param_qn_sym) else {
            continue;
        };
        let vid = match kb.get_term(alias_target) {
            Term::Var(Var::Global(v)) => *v,
            _ => continue,
        };
        let per_call_value = match subst.resolve_as_value(vid) {
            // Unbound spec param — the OPEN-T defer trigger; no constraint.
            None => continue,
            Some(Value::Term { id: v, .. }) => *v,
            // A denoted `Value::Node` param: carrier-agnostic entry match is
            // WI-348 Phase C. Conservatively drop (sound — resolved at runtime),
            // but flag loudly in debug so the gap surfaces.
            Some(other) => {
                debug_assert!(
                    false,
                    "WI-348: denoted {} spec param in defer-match — carrier-agnostic entry match is Phase C",
                    other.type_name(),
                );
                continue;
            }
        };
        out.push((per_call_value, *entry_value));
    }
    Some(out)
}

/// WI-221/WI-222 — true iff `entry` is a `requires` for `spec_sort` whose
/// bindings are consistent with the per-call substitution `subst` (the
/// wildcard-tolerant defer-to-requirement cover). Drives both the flat-chain slot
/// search (`find_requires_slot`) and the tree walk in `find_requires_location`.
/// `spec_qn` is `qualified_name_of(spec_sort)`, hoisted by callers that test many
/// entries.
///
/// Wildcard-tolerant by design: either side may be a type-param (the entry uses
/// the enclosing open `T`, or the call is on an abstract param). WI-613 layers a
/// σ-class verdict ([`entry_sigma_verdict`]) ON TOP for when two entries
/// both cover — this predicate stays the coarse candidate filter.
fn entry_matches_subst(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    spec_qn: &str,
    entry: &RequiresEntry,
) -> bool {
    let Some(pairs) = entry_type_param_bindings(kb, subst, spec_sort, spec_qn, entry) else {
        return false;
    };
    for (per_call_value, entry_value) in &pairs {
        // WI-414: a CONCRETE per-call value (e.g. `Eq.T := Int` from `eq(i: Int,
        // 0)`) must NOT defer to an OPEN-T requirement entry (`requires Eq[T]`,
        // the enclosing sort's abstract element) — such a call dispatches
        // concretely to the available `fact Eq[Int]`. Without this the wildcard
        // match below treated `Int` vs the open `T` as a match, deferring a
        // concretely-dispatchable call to a `__req` slot an external caller never
        // binds. An ABSTRACT per-call value (the enclosing T) still defers — its
        // impl IS the requirement; a concrete call to a CONCRETE requirement
        // (`requires Eq[T=Int]`) still defers via the dispatch match (not a
        // wildcard).
        if !is_type_param_value(kb, *per_call_value) && is_type_param_value(kb, *entry_value) {
            return false;
        }
        // Either side may be a wildcard — symmetric match, try both directions.
        if !dispatch_values_match(kb, *per_call_value, *entry_value)
            && !dispatch_values_match(kb, *entry_value, *per_call_value)
        {
            return false;
        }
    }
    true
}

/// WI-613 / WI-829 — the σ verdict for a coarse-covering `entry` against the
/// per-call substitution, computed in ONE pass over its constraining bindings
/// (each pair judged by [`sigma_pair_precise`], which owns the mixed / concrete /
/// both-compound rules). The three states drive the two same-spec DIRECT
/// attribution decisions:
///   * `Precise` — ≥1 constraining pair, ALL σ-precise: the entry pins the SAME
///     element the call has, so among several covers it is the WI-613 tie-break
///     winner (the [`find_requires_slot`] / [`find_requires_location`] survivor
///     pick, via [`pick_precise`]).
///   * `Refutes` — ≥1 constraining pair NOT σ-precise: a σ-DISAGREEING cover (the
///     shallow-vs-deep compound `entry_matches_subst`'s head fallback coarse-
///     accepted). WI-829 treats it as NO cover, so the caller constructs the
///     deeper dictionary instead of forwarding the frame's wrong-depth one.
///   * `Vacuous` — no constraining binding (a bindingless `requires Paintable`,
///     or all-non-constraining): neither a precise disambiguator NOR a refusal,
///     so a vacuous sole cover still defers. A structural non-match (`None`
///     pairs) can't reach a covering entry, but maps here too.
/// `(Precise, Refutes)` cannot co-occur — precise is "all agree", refutes is
/// "some disagrees". Mirrors [`entries_cover`]'s σ mode (the entry-vs-entry
/// forwarding analog) but reads the per-call element from the substitution.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SigmaVerdict {
    /// No constraining binding — neither disambiguates nor refuses.
    Vacuous,
    /// ≥1 constraining pair, all σ-precise — the tie-break winner.
    Precise,
    /// ≥1 constraining pair σ-disagrees — no cover (WI-829).
    Refutes,
}

pub(super) fn entry_sigma_verdict(
    kb: &mut KnowledgeBase,
    ctx: &SigmaCtx,
    spec_sort: Symbol,
    spec_qn: &str,
    entry: &RequiresEntry,
) -> SigmaVerdict {
    let Some(pairs) = entry_type_param_bindings(kb, ctx.subst, spec_sort, spec_qn, entry) else {
        return SigmaVerdict::Vacuous;
    };
    if pairs.is_empty() {
        return SigmaVerdict::Vacuous;
    }
    if pairs
        .iter()
        .all(|(pc, ev)| sigma_pair_precise(kb, ctx, *pc, *ev))
    {
        SigmaVerdict::Precise
    } else {
        SigmaVerdict::Refutes
    }
}

/// WI-239 — locate the spec a deferred call needs within `sort_sym`'s
/// `requires` **tree** (substitution-composed). Pre-order DFS; returns
/// the path of child indices to the first node whose entry matches
/// `subst` at `spec_sort`, or `None` if unreachable. The path is always
/// non-empty on `Some`: its head is the DIRECT (frame-slot) index, and
/// any tail indices are the `requirement_at_sort` projection path into
/// that direct requirement's bundled value (empty tail = the spec *is*
/// the direct requirement).
///
/// Reproduces — on the DIRECT chain plus its tree — the reachability the
/// pre-WI-239 flat `requires_chain` gave `find_requires_slot` for free
/// (the flat chain spliced transitive entries inline as top-level slots).
/// Under the tree-native ABI a transitive entry is no longer a frame
/// slot, so the typer's classification consults this to recover the
/// `(slot, proj_path)` encoding for `CallClass::DeferToRequirement`.
///
/// WI-613: when MORE THAN ONE node covers the call — a sort with two `requires`
/// of the SAME spec over distinct element params — first-match (pre-order) reads
/// the wrong requirement. `disambig` (the σ context) prefers a σ-precise covering
/// node — one whose element shares a σ-class with the per-call value — via the
/// shared [`pick_precise`] policy (first σ-precise, else first pre-order match). A
/// `None` `disambig`, or no σ-precise node, keeps the first pre-order match.
pub fn find_requires_location(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    sort_sym: Symbol,
    disambig: Option<&SigmaCtx>,
) -> Option<SmallVec<[usize; 2]>> {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let tree = requires_tree(kb, sort_sym);
    let mut path: SmallVec<[usize; 2]> = SmallVec::new();
    // Each coarse cover paired with its σ verdict (`Vacuous` with no σ context).
    let mut matches: Vec<(SmallVec<[usize; 2]>, SigmaVerdict)> = Vec::new();
    collect_requires_matches(
        kb,
        subst,
        disambig,
        spec_sort,
        &spec_qn,
        &tree,
        &mut path,
        &mut matches,
    );
    // WI-829: drop `Refutes` covers (a shallow-vs-deep compound the head fallback
    // coarse-accepted is NO cover), then pick among the survivors — the same
    // "σ-disagreement is not a cover" rule the forwarding dual (`entries_cover`)
    // applies at every arity, and the flat-chain [`find_requires_slot`] mirrors.
    // A sole survivor is returned; zero survivors refuse (→ construct the deeper
    // dict); ≥2 keep the WI-613 soft `pick_precise` tie-break (first σ-precise,
    // else first). A vacuous / σ-agreeing cover survives; no σ context ⇒ all
    // `Vacuous` ⇒ nothing refutes, none is precise ⇒ the first pre-order match.
    let survivors: SmallVec<[usize; 2]> = (0..matches.len())
        .filter(|&i| matches[i].1 != SigmaVerdict::Refutes)
        .collect();
    pick_precise(&survivors, |i| matches[i].1 == SigmaVerdict::Precise)
        .map(|i| matches[i].0.clone())
}

/// WI-1091 — classify a body call onto the enclosing OPERATION's own `requires` slot,
/// when its chain has one. `true` iff it did.
///
/// THE ONE PLACE the op-scoped deferral is decided, shared by the three dispatch
/// outcomes that can reach it: `Ambiguous` (nothing else can answer — WI-822's
/// original and only caller) and the two arms where [`op_requires_covers`] LICENSES
/// the call (`NoCandidates`, `NoMatch`). WI-822 wired only the first, on the measured
/// grounds that value-direction already served the rest; WI-1091 widened it because
/// being served by value-direction is exactly what makes a call-site SELECTION
/// unreachable — value-directed dispatch never sees `selections`, so WI-841 had to
/// REFUSE `probe[Monoid = AddM](2, 3)` rather than let it compute `AnyM`'s 99. The
/// slot's supply DOES honour the bracket ([`build_op_scoped_dicts`] threads `selected`
/// into [`build_dep_projection`]), so reading it is what makes the pin land.
///
/// A PIN AT THIS CALL still outranks the forward (058 §4.1 tier 1, the same gate the
/// three sort-level defer sites keep): deferring says "the enclosing frame answers
/// this", and an explicit witness on THIS call says otherwise.
pub(super) fn defer_to_op_scoped_slot(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    subst: &Substitution,
    spec_sort: Symbol,
    fn_sym: Symbol,
    op_short_sym: Symbol,
    enclosing_sort: Option<Symbol>,
    pinned_spec: bool,
) -> bool {
    if pinned_spec {
        return false;
    }
    let sigma_ctx = SigmaCtx {
        subst,
        param_rigids: env.param_rigids(),
    };
    let chain = env.enclosing_frame_chain().clone();
    let Some((slot, proj_path)) =
        op_scoped_defer_location(kb, subst, spec_sort, &chain, Some(&sigma_ctx))
    else {
        return false;
    };
    let resolved_spec = chain.entries()[slot].clone();
    classify(
        kb,
        occ,
        CallClass::DeferToRequirement {
            spec_op_sym: fn_sym,
            op_short_sym,
            resolved_spec,
            slot,
            proj_path,
            enclosing_sort,
            enclosing_op: env.enclosing_op(),
        },
    );
    true
}

/// WI-20260919-H20YY — ROUTE A DEFAULTED SPEC MEMBER THROUGH THE SAME SLOT A BODY-LESS
/// ONE TAKES, when the call names no carrier of its own. `true` iff it did.
///
/// THE DEFECT, measured on the R541X delivery commit (c3fe68ab):
///
/// ```text
/// sort TypeTerm { sort T = ?  operation valueOf() -> Type = T }        -- a DEFAULT body
/// sort Box { sort V = ?  entity box(v: V)  provides TypeTerm[T = Box[V = V]]
///            operation valueOf() -> Type = Option[T = V] }             -- Box's OVERRIDE
/// operation tagOfP[P](x: P) -> Type requires TypeTerm[T = P] = TypeTerm.valueOf()
/// tagOfP(box(boom("x")))   -- answered `Box(V: Boom)`, the DEFAULT's `T`
/// ```
///
/// It LOADED CLEAN and answered the spec's default, never the provider's override, with
/// no diagnostic. CONTROL, measured at the same time: the identical member made BODY-LESS
/// DOES dispatch to the provider through the slot (R541X's (C) fixtures,
/// `TypeTermB.valueOfB`). One declaration, two meanings, decided by whether the spec op
/// happens to carry a default body — which is WI-20260917-NR6FJ DEFECT B's sentence
/// verbatim, one binding-shape over. That ticket closed the half where the slot names a
/// CONCRETE carrier (`requires Desc[T = Rich]`, served by
/// [`carrier_from_declared_slot`]); this is the half where it names a type PARAMETER,
/// which pins no static carrier at all and which that function's doc wrongly recorded as
/// "already works".
///
/// WHY A DEFERRAL AND NOT A CARRIER. Over `requires TypeTerm[T = P]` there is no carrier
/// to name at load: which provider `P` stands for is settled per call, and the evidence
/// that settles it is the dictionary the caller already passes. So the repair is the
/// dictionary-passing reading 058 gives a spec op — classify
/// [`CallClass::DeferToRequirement`] and let eval walk the slot — and NOT a static pin.
/// Eval's `dispatch_via_sort_ops_table` then asks [`resolve_op_target`] for the
/// dictionary's own member: the provider's override when it has one, and `fn_sym` ITSELF
/// when it does not, which runs the spec's default body exactly as before. That
/// fall-through is what keeps a provider WITHOUT an override on the default — defaults
/// fill GAPS, they do not SHADOW (WI-444's rule, read from the other end).
///
/// THE TWO ROUTES ARE THE BODY-LESS BLOCK'S, IN ITS ORDER, and calling them here is the
/// whole change: the sort-level [`find_requires_location`] pre-check (WI-239) first, then
/// the operation's own [`defer_to_op_scoped_slot`] (WI-822/1091) as its fallback. Both are
/// needed and neither subsumes the other — MEASURED: `tagOfP` is a FREE operation, so
/// `enclosing_sort` is `None` and only the op-scoped route can serve it, while
/// `SHold.f()`'s sort-level `requires TypeTerm[T = E]` is reached only by the first.
///
/// A PIN AT THIS CALL STILL OUTRANKS THE FORWARD — 058 §4.1 tier 1, the same
/// `pinned_witness_for` gate all three sort-level defer sites keep. Deferring says "the
/// enclosing frame answers this"; an explicit witness on THIS call says otherwise.
///
/// GATED ON [`call_names_no_carrier`], which is the one clause a reader will try to drop
/// since the enclosing block already failed to pin a carrier. Failing to pin is NOT the
/// same question: [`statically_pinned_carrier`] answers `None` both for a call that names
/// no carrier at all and for one whose carrier ARGUMENT is merely abstract here, and the
/// second belongs to eval's value-directed dispatch, which reads the carrier off the
/// runtime value. Deferring those to the slot is precisely the wrong answer NR6FJ
/// measured — `viaop[U](x: U) requires Desc[T = Rich] = Desc.describe(x)` computing
/// `Rich`'s 7 for a `plain()` — so the gate is shared with that route rather than
/// re-derived here.
pub(super) fn defer_defaulted_call_to_slot(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    subst: &Substitution,
    spec_sort: Symbol,
    fn_sym: Symbol,
    op_short_sym: Symbol,
    selections: &[InstanceSelection],
) -> bool {
    // WI-841 tier 1 — A PIN AT THIS CALL OUTRANKS THE FORWARD, the same gate all three
    // sort-level defer sites keep. Not an early return: it is the gate on the SORT half
    // below and is handed to the op half, which asks it in its own words, so the two
    // halves refuse a pinned call for one reason rather than two.
    let pinned_spec = pinned_witness_for(kb, selections, spec_sort).is_some();
    // EXACTLY ONE CLAUSE OVER THE SPEC, OR NOTHING IS DIRECTED — the same refusal
    // [`bind_sort_params_from_sole_enclosing_requirement`] applies to the same shape, and
    // asked through the same owner so the two cannot drift.
    //
    // WITHOUT IT THIS ROUTE PICKS, which is exactly what it must not do, and two shipped
    // rows measured it: `requires Desc[T = Rich], Desc[T = Other]` answered `Rich`'s 7
    // where the default (1) is the only honest answer
    // (`wi_nr6fj_defect_b_slot_over_default_test::two_slots_that_disagree_pin_nothing`),
    // and R541X's `twoReq[P, Q] requires TypeTerm[T = P], TypeTerm[T = Q]` LOADED — the
    // deferral silently supplied the evidence whose absence is what N31XX refuses the
    // program for (`wi_r541x_body_read_of_type_param_test::
    // two_clauses_over_one_spec_are_refused_at_load`). Both are the ORDER-DEPENDENT
    // answer, reached through the soft first-match tie-break the locating walks fall back
    // to when no clause is σ-precise; the walks are right to be soft for a call that
    // pins something, and this route is for calls that pin nothing at all.
    if sole_chain_entry_over_spec(kb, env.enclosing_frame_chain(), spec_sort).is_none() {
        return false;
    }
    let enclosing_sort = env.enclosing_sort();
    let enclosing_requires = env.enclosing_requires().to_vec();
    if !pinned_spec && !enclosing_requires.is_empty() {
        let sigma_ctx = SigmaCtx {
            subst,
            param_rigids: env.param_rigids(),
        };
        if let Some(path) = enclosing_sort
            .and_then(|encl| find_requires_location(kb, subst, spec_sort, encl, Some(&sigma_ctx)))
        {
            // `path` is non-empty on `Some`. Head = direct frame slot; tail = projection
            // path into its bundled value — the same encoding the body-less pre-check
            // hands `CallClass::DeferToRequirement`.
            let slot = path[0];
            let proj_path: SmallVec<[usize; 2]> = path[1..].iter().copied().collect();
            let resolved_spec = enclosing_requires[slot].clone();
            classify(
                kb,
                occ,
                CallClass::DeferToRequirement {
                    spec_op_sym: fn_sym,
                    op_short_sym,
                    resolved_spec,
                    slot,
                    proj_path,
                    enclosing_sort,
                    enclosing_op: env.enclosing_op(),
                },
            );
            return true;
        }
    }
    defer_to_op_scoped_slot(
        kb,
        env,
        occ,
        subst,
        spec_sort,
        fn_sym,
        op_short_sym,
        enclosing_sort,
        pinned_spec,
    )
}

/// WI-822 LEG 1 — the frame slot of the enclosing OPERATION's OWN `requires` chain
/// that answers `spec_sort` at this call's bindings, as `(slot, proj_path)` in the
/// COMPOSED chain's numbering (`chain.sort_len()` is added, so the answer indexes the
/// same list [`CallClass::DeferToRequirement::slot`] does).
///
/// THE ONE READER OF THE OP HALF, reached through [`defer_to_op_scoped_slot`].
///
/// WI-822 called it from the `Ambiguous` arm ALONE — the route where nothing else can
/// answer: a spec op with NO receiver argument (`zero() -> T`), whose providers tie
/// with nothing to break the tie, since §4.4 check 3 refuses an explicit
/// `[Zeroable = Pebble]` over concrete providers. That was a LOAD REFUSAL while the
/// sort-level twin of the same program loaded and was right.
///
/// WI-1091 WIDENED IT to the two licensing arms as well, and the widening is what
/// makes a call-site SELECTION reach an op-scoped slot at all. It cost four routes a
/// supply they had never needed — see [`defer_to_op_scoped_slot`] and the ticket.
///
/// Reuses [`collect_requires_matches`] over a tree built from the op's own entries,
/// so a TRANSITIVE op-scoped requirement (`requires Ord[T]` answering an `Eq` call)
/// is located with its `requirement_at_sort` projection path exactly as the sort
/// half's is — one walk, one σ policy, one tie-break.
pub(super) fn op_scoped_defer_location(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    chain: &DictChain,
    disambig: Option<&SigmaCtx>,
) -> Option<(usize, SmallVec<[usize; 2]>)> {
    let op_entries = chain.op_entries();
    if op_entries.is_empty() {
        return None;
    }
    // The op half AS A TREE: each entry, then the required spec's own chain beneath
    // it — the same `build_requires_tree` descent `requires_tree` does for a sort's
    // direct entries, seeded from the entry's own bindings.
    let mut nodes: Vec<RequiresNode> = Vec::with_capacity(op_entries.len());
    for entry in op_entries.to_vec() {
        let child_subst = build_child_subst_map(kb, &entry);
        let mut visited: Vec<Symbol> = Vec::new();
        let sub_requires = build_requires_tree(kb, entry.required_sort, &child_subst, &mut visited);
        nodes.push(RequiresNode {
            entry,
            sub_requires,
        });
    }
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let mut path: SmallVec<[usize; 2]> = SmallVec::new();
    let mut matches: Vec<(SmallVec<[usize; 2]>, SigmaVerdict)> = Vec::new();
    collect_requires_matches(
        kb,
        subst,
        disambig,
        spec_sort,
        &spec_qn,
        &nodes,
        &mut path,
        &mut matches,
    );
    let survivors: SmallVec<[usize; 2]> = (0..matches.len())
        .filter(|&i| matches[i].1 != SigmaVerdict::Refutes)
        .collect();
    let winner = pick_precise(&survivors, |i| matches[i].1 == SigmaVerdict::Precise)?;
    let found = &matches[winner].0;
    Some((
        chain.sort_len() + found[0],
        found[1..].iter().copied().collect(),
    ))
}

/// WI-239 / WI-613 / WI-829 — pre-order DFS collector for
/// [`find_requires_location`]. Pushes each node's index onto `path`, and for
/// every node whose entry `entry_matches_subst` (the coarse cover) records
/// `(path, σ_verdict)`. Preserves the original DFS short-circuit: a matching
/// entry does NOT descend into its own `sub_requires` (the entry IS the target;
/// its sub-requires are the required spec's OWN transitive requires — a different
/// spec). The [`SigmaVerdict`] is computed only when a σ context is present (else
/// `Vacuous`), so with none nothing refutes and the caller falls back to the
/// first pre-order match. `nodes` comes from the substitution-composed
/// `requires_tree`, so it does not alias `kb`.
fn collect_requires_matches(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    disambig: Option<&SigmaCtx>,
    spec_sort: Symbol,
    spec_qn: &str,
    nodes: &[RequiresNode],
    path: &mut SmallVec<[usize; 2]>,
    out: &mut Vec<(SmallVec<[usize; 2]>, SigmaVerdict)>,
) {
    for (i, node) in nodes.iter().enumerate() {
        path.push(i);
        if entry_matches_subst(kb, subst, spec_sort, spec_qn, &node.entry) {
            let verdict = disambig.map_or(SigmaVerdict::Vacuous, |ctx| {
                entry_sigma_verdict(kb, ctx, spec_sort, spec_qn, &node.entry)
            });
            out.push((path.clone(), verdict));
        } else {
            collect_requires_matches(
                kb,
                subst,
                disambig,
                spec_sort,
                spec_qn,
                &node.sub_requires,
                path,
                out,
            );
        }
        path.pop();
    }
}
