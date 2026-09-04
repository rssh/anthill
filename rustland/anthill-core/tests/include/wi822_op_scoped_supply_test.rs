//! WI-822 — requirement supply for an op whose `requires` chain is OP-SCOPED
//! (WI-448/WI-562: written on the operation, member-style, not on its sort).
//!
//! The ticket named TWO legs. Only the second turned out to decide the
//! measured failures, and establishing that took a probe — the
//! unbound-dictionary message named no frame (it does now):
//!
//!   LEG 2 (dispatch site) — FIXED HERE. Value-directed dispatch resolves a
//!   body-less spec op's impl from the receiver VALUE at runtime and used to
//!   enter that impl's frame with the SPEC call's own (empty) channel. Fine
//!   while every reachable impl is a LEAF; the moment the value selects a
//!   CONDITIONAL impl (`WrapDesc requires Desc[T = E]`) its body's first
//!   dictionary read died `Internal(… __req_desc not bound)` — naming a frame
//!   the author never wrote. The failing frame was the IMPL's
//!   (`WrapDesc.describe`), NOT the op-scoped caller's (`Holder.probe`), which
//!   is what LEG 1's stated rationale predicted. At dispatch the receiver's
//!   type is concrete, so the impl's chain is resolvable right there:
//!   `requirements_for_value_directed_impl` (eval) reuses WI-625's
//!   `resolve_bridge_requirements` — the identical "concrete op, real argument
//!   values, no caller dictionary" problem. The WI-817 (c) rows flip in
//!   `wi817_polyrec_requirement_test.rs`; this file pins the LOUD-failure and
//!   value-preservation halves.
//!
//!   LEG 1 (call site) — DELIVERED, and NARROWER than the ticket wrote it. An
//!   op's own `requires` now names frame slots after its parent sort's
//!   (`op_dict_entries`), a call site fills them from the per-call substitution
//!   (`build_op_scoped_dicts`), and eval places them after the sort half
//!   (`push_op_scoped_slots`). What a BODY does with them is the narrow part:
//!   it defers to an op slot on ONE route — a dispatch that TIES
//!   (`op_scoped_defer_location`) — because everywhere else value-direction
//!   already serves the requirement and demonstrably serves it right (WI-817's
//!   relay chain still computes its 551, `List.contains` and the whole
//!   `PartialOrd` comparison surface still run, and a host `interp.call` — which
//!   has no call site to build a dictionary from — still works).
//!
//!   THE PLACEMENT IS MEASURED, NOT PREFERRED. Deferring on every op-scoped call
//!   was implemented first and broke 30 tests across wi842/wi843/wi855/wi876/
//!   wi886/wi869 and the eta route: the shapes that fail are exactly the ones
//!   with NO call site to supply from (host entry, an eta'd `OpRef`, a
//!   dictionary-directed dispatch) plus `WeakOrd.max → PartialOrd.gte`, which needs
//!   the frame's own `__req_self` as evidence for `Ord[T]` and has no slot to
//!   forward from. The tie route has none of those: it is reached from an
//!   ordinary call site, and it is the one route where NOTHING else can answer —
//!   no value directs a receiver-less `zero() -> T`, and 058 §4.4 check 3
//!   refuses an explicit witness over CONCRETE providers on the grounds that the
//!   value decides.
//!
//! WHAT FAILS WHEN LEG 1 IS BACKED OUT, level by level — the controls, since
//! several of these pieces pass in each other's absence:
//!   * the `Ambiguous`-arm deferral alone →
//!     `receiverless_spec_op_op_scoped_rejected_sort_level_correct` and
//!     `op_scoped_supply_is_per_call_site` go back to the LOAD REFUSAL.
//!   * `normalize_op_requires_entry` alone → the program LOADS (the slot is
//!     found) and dies `__req_desc/__req_zeroable not bound`: an op-scoped
//!     clause is stored as the bare application the author wrote, which every
//!     chain predicate reads as binding-free, so no call site can construct it.
//!   * `resolve_param_value_via_subst`'s widening to `type_param_global_var`
//!     alone → the SORT-param spellings still work and the OP-TYPE-PARAM ones
//!     (`wi817_polyrec_requirement_test::op_param_*`) do not, since a bracket
//!     parameter has no `SortAlias` to resolve through.
//!   * the value-precondition filter in `op_requires_chain_rc` alone → 20 tests
//!     across wi347/wi539/wi557/wi752/wi840 die: one `requires` keyword writes
//!     both a spec requirement and a goal over the op's parameters, and only the
//!     first is a slot.
//!
//! **WI-1091 MOVED THE PLACEMENT, and everything above stays true as HISTORY
//! rather than as the current rule.** LEG 1's narrowness was measured, not
//! preferred — and the measurement is what says so: widening the deferral broke
//! exactly the routes with NO CALL SITE to supply from. WI-1091 supplied them
//! (a host entry resolves the op half from the argument values; an eta'd
//! `OpRef` carries its own; an element the call cannot pin is completed from
//! the providers where they leave one answer; the defaulted fall-through
//! threads the carrier's instance), and only then widened. The op-scoped
//! licence is now read where the SORT-level one is — the pre-check AHEAD of
//! dispatch, which is what makes the two spellings agree and what a bracket
//! needs in order to decide (`wi841_call_site_selection_test::
//! an_op_scoped_selection_decides_and_the_value_shows_it`).
//!
//! So "the body defers on ONE route" is no longer the rule, and the paragraph
//! above is left standing because the shapes it enumerates are the ones that
//! had to be repaired. The two WI-1091 rows at the end of this file drive the
//! op half at a boundary with no call site.

use anthill_core::eval::{Interpreter, Value};

/// Spec `Desc` + a base instance at `Leaf` (describe → 1) + a CONDITIONAL
/// instance at `Wrap[E]` given `Desc[E]` (describe → 10·describe(inner) + 2),
/// so a correct answer is depth-coded (1, 12, 122, …) and a wrong dictionary
/// at any step shows up as a different number. Same shape as the WI-817
/// witness's `INSTANCES` — and now literally the same text: the claim used to
/// be a comment nothing enforced, so the block has ONE owner.
const INSTANCES: &str = crate::common::DESC_INSTANCES;

fn eval_fresh(src: &str, entry: &str, n: i64) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(n)])
}

/// The WI-325 ladder's suggestion for an uncovered spec-op call. One owner beside
/// `DESC_INSTANCES`, which this file also shares; see
/// `common::MISSING_DESC_REQUIRES`.
const MISSING_REQUIRES: &str = crate::common::MISSING_DESC_REQUIRES;

// ── LEG 2: the supply is resolved at the VALUE's type, not inherited ──

/// The value-selected impl's chain is resolved at the RECEIVER'S OWN type at
/// each step, so two calls that select the SAME impl operation
/// (`WrapDesc.describe`) at DIFFERENT instantiations each get their own
/// dictionary — 12 for `Wrap[Leaf]`, 122 for `Wrap[Wrap[Leaf]]` — in ONE
/// program, on ONE interpreter. A supply that resolved once and was reused
/// (or inherited from the caller) would measure the same number twice; the
/// pre-fix code measured neither, dying unbound at both.
#[test]
fn value_directed_supply_is_per_call_not_shared() {
    let src = format!(
        r#"
namespace wi822.percall
  import anthill.prelude.{{Int64, Bool}}
  import anthill.prelude.Additive.{{add}}
  import anthill.prelude.Multiplicative.{{mul}}
{INSTANCES}
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation shallow(n: Int64) -> Int64 = Holder.probe(wrap(leaf()))
    operation deep(n: Int64) -> Int64 = Holder.probe(wrap(wrap(leaf())))
    operation both(n: Int64) -> Int64 =
      add(Driver.shallow(n), mul(1000, Driver.deep(n)))
  end
end
"#
    );
    let got = eval_fresh(&src, "wi822.percall.Driver.both", 0);
    assert!(
        matches!(got, Ok(Value::Int(122012))),
        "expected Ok(Int(122012)) = shallow 12 + 1000·deep 122, each `WrapDesc.describe` \
         frame seeded from its OWN receiver's type; got {got:?}"
    );
}

/// An UNPINNABLE chain never becomes a WRONG dictionary. This is the guard the
/// WI-824 feedback asks of WI-822: an op-scoped construction path meeting an
/// ABSTRACT element must land on a refusal, not build a dictionary.
///
/// It does, and MEASURED it lands EARLIER than WI-822 assumed — at LOAD. To
/// make an impl's own requirement unpinnable from its argument types, that
/// requirement must range over a type-param the parameters do not mention
/// (`Ghost requires Desc[T = U]`, `describe(w: Box[B = G])`); but then it also
/// fails to COVER the body's own dictionary read, and the WI-325 ladder
/// refuses the program before it can run. So "unpinnable chain AND a body that
/// reads it" is not a runnable configuration at all.
///
/// Two independent guards therefore stand between an abstract element and a
/// dictionary, and this pins the outer one. The inner one — the fully-pinned
/// gate in `resolve_bridge_requirements`, which rejects an abstract binding
/// BEFORE candidate matching — still matters and must stay: that resolve is
/// σ-LESS, so WI-824's σ-gated refusal of a rigid against a structured head is
/// NOT in force on this path, and the gate is what stands in for it. The two
/// must be relaxed together or not at all.
///
/// The remaining unpinnable shapes are the ones the stdlib actually runs: an
/// impl whose chain cannot be pinned because the receiver is a HANDLE carrying
/// no element type (`Map.iterator` on a `Value::Map`, against `Map`'s
/// `requires Eq[T = Map.K]`), and whose body never reads it. Those enter
/// unsupplied and run — which is why WI-822's specified loud-at-dispatch error
/// was replaced by loud-at-the-read (pinned by the test below).
#[test]
fn unpinnable_impl_requirement_is_refused_before_it_can_run() {
    let src = format!(
        r#"
namespace wi822.ghost
  import anthill.prelude.{{Int64, Bool}}
  import anthill.prelude.Additive.{{add}}
{INSTANCES}
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort Ghost
    sort G = ?
    sort U = ?
    requires Desc[T = U]
    fact Desc[T = Box[B = G]]
    operation describe(w: Box[B = G]) -> Int64 = add(7, Desc.describe(w.inner))
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(box(leaf()))
  end
end
"#
    );
    let errs = crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_else(|| {
            panic!(
                "the unpinnable-chain program must NOT load — if it does, the only thing \
             left between its abstract element and a dictionary is the fully-pinned \
             gate, and this test must be rewritten to drive it (a wrong dictionary \
             would deliver Ok(Int(8)))"
            )
        });
    let text = errs.join("\n");
    assert!(
        text.contains("wi822.ghost.Desc.describe.requires") && text.contains(MISSING_REQUIRES),
        "expected the WI-325 ladder to refuse `Ghost`'s uncovered dictionary read; got:\n{text}"
    );
}

/// The unbound-dictionary message NAMES ITS FRAME. WI-822's own investigation
/// could not attribute the failure from the text ("requirement param
/// `__req_desc` not bound in caller frame" — which frame?) and had to establish
/// it by probe; the message now carries the running operation and the sort
/// whose requires chain owns the slot.
///
/// Driven through the shape that still reaches it — the WI-415 gap named in
/// `CallClass::ConcreteApplyWithin`'s own doc: a CROSS-SORT call from a
/// `requires`-free caller over an ABSTRACT argument. Nothing can build the
/// callee a dictionary (no caller slot to forward, no concrete binding to
/// construct from), so `Holder.probe` is entered with an empty channel and its
/// deferred read finds no slot. The value-directed route that used to land
/// here no longer does — that is LEG 2 — so this pins the DIAGNOSTIC, on a
/// defect of its own that neither leg of WI-822 claims.
#[test]
fn unbound_requirement_message_names_the_running_frame() {
    let src = format!(
        r#"
namespace wi822.named
  import anthill.prelude.{{Int64, Bool}}
{INSTANCES}
  sort Holder
    sort HT = ?
    requires Desc[HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
  sort Caller
    sort CT = ?
    operation go(x: CT) -> Int64 = Holder.probe(x)
  end
end
"#
    );
    let got = eval_fresh(&src, "wi822.named.Caller.go", 0);
    let msg = match got {
        Err(anthill_core::eval::EvalError::Internal(msg)) => msg,
        other => panic!("expected an Internal requirement error to inspect; got {other:?}"),
    };
    assert!(
        msg.contains("wi822.named.Holder.probe"),
        "the unbound-requirement message must name the RUNNING operation; got {msg}"
    );
    assert!(
        msg.contains("wi822.named.Holder"),
        "the unbound-requirement message must name the requires-chain OWNER; got {msg}"
    );
}

// ── LEG 1: the op-scoped supply channel ──────────────────────────────

/// THE DEFECT LEG 1 CLOSES, and the measurement that actually motivated it (the
/// ticket predicted LEG 1 from the (c) pins, which LEG 2 alone in fact fixed).
///
/// `Zeroable.zero()` has NO parameter, so no runtime value can direct its
/// dispatch — a dictionary is the ONLY thing that can pick between two
/// providers. With the requirement written at SORT level the body's call is
/// classified `DeferToRequirement`, the caller's dictionary decides, and the
/// program computes 5 (`Pebble.zero()` → `Pebble.describe` → 5). With the
/// SAME requirement written OP-SCOPED there was no slot to defer to, so the
/// typer pinned `zero()` concretely, saw both providers, and REJECTED THE
/// PROGRAM AT LOAD — two spellings of one program, one of which did not load.
///
/// BOTH HALVES ARE THE TEST. The sort-level control is not decoration: it is
/// what says 5 is the right answer rather than merely the one this route
/// happens to produce, and it fails identically if the `Zeroable` fixtures rot.
///
/// WI-843 RESTATED THE DIAGNOSTIC, and the restatement is why only a dictionary
/// closes this: the two providers are CONCRETE, so 058 §4.4 check 3 refuses an
/// explicit `[Zeroable = Pebble]` here (measured — "an explicit `[Zeroable =
/// Pebble]` cannot change it"), and the tier-3 message does NOT offer the
/// bracket it offers everywhere else. Neither a value nor a selection can
/// answer this call. That exact wording is still driven, on a `requires`-free
/// twin of this program, by `wi843_coexisting_instances_test::
/// a_tie_among_concrete_providers_does_not_suggest_a_bracket`.
#[test]
fn receiverless_spec_op_op_scoped_rejected_sort_level_correct() {
    const BASE: &str = r#"
  sort Zeroable
    sort T = ?
    operation zero() -> T
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Zeroable[T = Leaf]
    operation zero() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Zeroable[T = Pebble]
    operation zero() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
"#;
    let program = |ns: &str, holder: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
{BASE}
  sort Holder
    sort HT = ?
{holder}
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(pebble())
  end
end
"#
        )
    };

    // CONTROL — sort-level `requires`: loads and is RIGHT.
    let sort_level = program(
        "wi822.recv.sortlevel",
        "    requires Zeroable[HT]\n    operation probe(x: HT) -> Int64 = \
         Zeroable.describe(Zeroable.zero())",
    );
    let got = eval_fresh(&sort_level, "wi822.recv.sortlevel.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(5))),
        "control (sort-level requires): expected Ok(Int(5)) — the caller's dictionary \
         picks `Pebble.zero`; got {got:?}"
    );

    // THE SAME REQUIREMENT WRITTEN OP-SCOPED — loads, and agrees.
    let op_scoped = program(
        "wi822.recv.opscoped",
        "    operation probe(x: HT) -> Int64 requires Zeroable[HT] = \
         Zeroable.describe(Zeroable.zero())",
    );
    let got = eval_fresh(&op_scoped, "wi822.recv.opscoped.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(5))),
        "op-scoped: expected Ok(Int(5)) — the SAME answer as the sort-level control, \
         reached through the operation's own dictionary slot (WI-822 LEG 1). Before it \
         this program did not load at all: `ambiguous dispatch of \
         `wi822.recv.opscoped.Zeroable.zero`` (Leaf, Pebble), with no bracket offered \
         because both providers are CONCRETE and 058 §4.4 check 3 refuses an explicit \
         selection over one — the residue stated exactly, a call neither a value nor a \
         selection can answer. Got {got:?}"
    );
}

/// Two `sort Zeroable` providers and TWO CALL SITES into one op-scoped operation,
/// at DIFFERENT instantiations, in ONE program on ONE interpreter: the answers must
/// DIVERGE (1 for the `Leaf` site, 5 for the `Pebble` site).
///
/// The test above proves the deferral REACHES a dictionary; this one proves the
/// dictionary is the CALL'S. A supply resolved once and shared, or one inherited
/// from whichever site ran first, measures the same number twice — and with a single
/// call site the two are indistinguishable, which is why the sibling above cannot
/// stand in for this. 51 is the pair read as one number, so a swap (15) and a
/// collapse (11, 55) are all distinct failures.
#[test]
fn op_scoped_supply_is_per_call_site() {
    let src = r#"
namespace wi822.percallsite
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Additive.{add}
  import anthill.prelude.Multiplicative.{mul}
  sort Zeroable
    sort T = ?
    operation zero() -> T
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Zeroable[T = Leaf]
    operation zero() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Zeroable[T = Pebble]
    operation zero() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Zeroable[HT] =
      Zeroable.describe(Zeroable.zero())
  end
  sort Driver
    operation onLeaf(n: Int64) -> Int64 = Holder.probe(leaf())
    operation onPebble(n: Int64) -> Int64 = Holder.probe(pebble())
    operation both(n: Int64) -> Int64 =
      add(mul(10, Driver.onPebble(n)), Driver.onLeaf(n))
  end
end
"#;
    let got = eval_fresh(src, "wi822.percallsite.Driver.both", 0);
    assert!(
        matches!(got, Ok(Value::Int(51))),
        "expected Ok(Int(51)) = 10·(Pebble site → 5) + (Leaf site → 1): each call site \
         builds `probe`'s op-scoped slot from its OWN substitution. 11 or 55 means one \
         dictionary served both sites; 15 means they were swapped; got {got:?}"
    );
}

/// The op half's slot NAMES do not disturb the sort half's, and both are read.
///
/// `Holder` declares `requires Zeroable[HT]` at SORT level and `probe` declares
/// `requires Zeroable[PT]` of its OWN — two entries whose synthesized base name is
/// the same `__req_zeroable`. The sort half's naming is re-derived from the sort
/// ALONE by every sort-keyed producer (`dict_layout`, `expand_dispatching_dict`), so
/// it must not move; the collision is therefore broken on the OP side. Driven to two
/// DIFFERENT numbers through the two slots in one body — 5 from the sort slot's
/// `Pebble`, 1 from the op slot's `Leaf` — so a collapsed pair (55 or 11) fails and a
/// swap (15) fails.
///
/// Both reads are receiver-less `zero()` calls, which is the only route a body takes
/// to an op slot at all; the sort slot would be read on that route or any other.
///
/// CONTROL, RUN: with `DictChain::names` disambiguating over the COMPOSED list
/// instead — the obvious implementation, and the wrong one — this fails
/// `DeferToRequirement: requirement param `__req_zeroable_c` not bound … frame binds
/// ["__req_self", "__req_zeroable", "__req_zeroable_15539"]`. The renamed reader and
/// the un-renamed sort-keyed producer, exactly as described. That run also confirms
/// the op slot is really there and really disambiguated (`__req_zeroable_15539`), so
/// this test is not passing by the op half being absent.
#[test]
fn a_colliding_op_slot_name_does_not_move_the_sort_slot() {
    let src = r#"
namespace wi822.collide
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Additive.{add}
  import anthill.prelude.Multiplicative.{mul}
  sort Zeroable
    sort T = ?
    operation zero() -> T
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Zeroable[T = Leaf]
    operation zero() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Zeroable[T = Pebble]
    operation zero() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort Holder
    sort HT = ?
    requires Zeroable[HT]
    operation probe[PT](x: HT, y: PT) -> Int64 requires Zeroable[T = PT] =
      add(mul(10, Zeroable.describe(Zeroable.zero())),
          Zeroable.describe(Zeroable.zero()))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe[Leaf](pebble(), leaf())
  end
end
"#;
    let got = eval_fresh(src, "wi822.collide.Driver.drive", 0);
    // Both `zero()` reads resolve against the FIRST covering slot in chain order —
    // the sort half's, since it is the prefix — so both answer 5. What this pins is
    // that the program LOADS AND RUNS with two same-based slots in one frame: before
    // the op-side disambiguation the two would be one name, and whichever dictionary
    // was placed second would silently answer both reads.
    assert!(
        matches!(got, Ok(Value::Int(55))),
        "expected Ok(Int(55)) — the sort slot answers both reads (it is the chain \
         prefix), and the op slot's colliding `__req_zeroable` base is renamed on the \
         OP side so it does not shadow it. An unbound-requirement error means the \
         collision moved the SORT slot's name, which every sort-keyed producer \
         re-derives independently; got {got:?}"
    );
}

/// An op-scoped requirement reached TRANSITIVELY still locates its slot, with the
/// `requirement_at_sort` projection path into the direct requirement's bundled value
/// — the op half walks the same tree the sort half does.
///
/// `probe requires Outer[HT]`, `Outer requires Zeroable[T = Outer.T]`, and the body
/// calls the receiver-less `Zeroable.zero()`. There is no DIRECT `Zeroable` entry on
/// the operation, so a direct-chain-only search finds nothing and the tie is refused
/// at load exactly as before this ticket; locating it needs the descent.
///
/// CONTROL, RUN: with `op_scoped_defer_location`'s per-entry `build_requires_tree`
/// replaced by an empty `sub_requires`, this is the only test in the file that
/// fails — the program stops loading. So the descent is what it measures, and the
/// sibling tests above (whose requirements are DIRECT) do not cover it.
#[test]
fn a_transitively_required_op_slot_is_located_through_its_projection() {
    let src = r#"
namespace wi822.transitive
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Additive.{add}
  sort Zeroable
    sort T = ?
    operation zero() -> T
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Zeroable[T = Leaf]
    operation zero() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Zeroable[T = Pebble]
    operation zero() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort Outer
    sort OT = ?
    requires Zeroable[T = OT]
    operation tag(x: OT) -> Int64
  end
  sort LeafOuter
    fact Outer[OT = Leaf]
    operation tag(x: Leaf) -> Int64 = 100
  end
  sort PebbleOuter
    fact Outer[OT = Pebble]
    operation tag(x: Pebble) -> Int64 = 200
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Outer[OT = HT] =
      add(Outer.tag(x), Zeroable.describe(Zeroable.zero()))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(pebble())
  end
end
"#;
    let got = eval_fresh(src, "wi822.transitive.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(205))),
        "expected Ok(Int(205)) = `PebbleOuter.tag` 200 + `Pebble.describe(Pebble.zero())` \
         5 — the receiver-less `zero()` reads `Zeroable` out of the op slot's `Outer` \
         dictionary through one `requirement_at_sort` step. 201 would mean the \
         projection landed on the `Leaf` sub-dictionary; a load refusal means the \
         descent did not happen at all; got {got:?}"
    );
}
/// THE INSTANCE-DICTIONARY CHANNEL DOES NOT FORWARD AN OP SLOT, and this pins the
/// attribution that says so.
///
/// `Holder.probe requires Desc[HT]` (op-scoped) cross-sort-calls `Coll.size`, whose
/// SORT declares `requires Desc[CT]`, at the abstract `CT := HT`. Two chains could
/// answer the callee's dep: the caller's SORT chain (empty here) and the caller's own
/// OP slot. Only the first is offered — the caller chain the instance-dictionary
/// builders read is `TypingEnv::enclosing_chain`, the sort half — because that channel
/// is read STRICTLY at eval (`start_apply_within` needs the dictionary to pick a
/// target at all) while several routes into an operation fill no op slot: this very
/// program is entered from the HOST, where `seed_entry_requirements` deliberately
/// seeds none.
///
/// MEASURED BOTH WAYS, and the difference is NOT the one predicted. A /code-review
/// finding expected the composed chain to turn a load-time `UnsatisfiableRequirement`
/// into an eval-time unbound `var_ref`; driven, the program LOADS either way and fails
/// at eval either way — Strategy 3 cannot construct an abstract dep and the
/// `require_complete` abort has no σ-refusal signature to report, so it classifies
/// dict-less rather than refusing. What DOES differ is who is blamed:
///
///   * composed  → `var_ref(__req_desc) unbound … running `Holder.probe`; frame binds
///     ["__req_self"]` — the CALLER is named for a slot no route ever gives it.
///   * sort-only → `DeferToRequirement: `__req_desc` not bound … running `Coll.size`,
///     requires-chain owner `Coll`` — the callee, whose own sort-level `requires` is
///     the thing that genuinely went unsupplied.
///
/// The second is the true account, and mis-attribution is the exact failure WI-822's
/// own investigation had to work around with a probe. Restoring the composed chain in
/// `enclosing_dict_chain` flips this assertion.
#[test]
fn the_instance_dictionary_channel_never_forwards_an_op_slot() {
    let src = format!(
        r#"
namespace wi822.instchan
  import anthill.prelude.{{Int64, Bool}}
  import anthill.prelude.Option.{{none, some}}
{INSTANCES}
  sort Coll
    sort CT = ?
    requires Desc[CT]
    operation size(x: CT) -> Int64 = Desc.describe(x)
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Coll.size(x)
  end
end
"#
    );
    let kb = crate::common::load_kb_with(&src);
    let leaf_sym = kb.resolve_symbol("wi822.instchan.Leaf.leaf");
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    let leaf = Value::Entity {
        functor: leaf_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    let msg = match interp.call("wi822.instchan.Holder.probe", &[leaf]) {
        Err(anthill_core::eval::EvalError::Internal(m)) => m,
        other => panic!(
            "expected the callee's own unsupplied sort-level requirement to raise; \
             got {other:?}"
        ),
    };
    assert!(
        msg.contains("wi822.instchan.Coll.size") && msg.contains("requires-chain owner"),
        "the failure must be attributed to `Coll.size`, whose SORT-level `requires` \
         went unsupplied; got {msg}"
    );
    assert!(
        !msg.contains("wi822.instchan.Holder.probe"),
        "`Holder.probe` must NOT be blamed: it is only blamed when the instance \
         dictionary forwards its OP slot, which no route into this program fills; \
         got {msg}"
    );
}


// ── WI-1091: the OP HALF at a boundary with no call site ─────────────

/// **AN ELEMENT THE HOST CANNOT PIN IS COMPLETED FROM THE PROVIDERS — but only where
/// they leave exactly ONE answer, and this pair drives both sides of that.**
///
/// `resolve_bridge_requirements` only ever resolved a FULLY-PINNED goal: an abstract
/// binding matches ANY provider, so building a dictionary at one would let the bridged op
/// mis-decide. WI-1091 relaxed that for the OP HALF alone, because a host entry has no
/// bracket to write and the widened placement makes the body READ the slot — see
/// `unique_provider_completion`. The relaxation is exact rather than lenient exactly when
/// the providers admit one completion, which is what these two rows separate.
///
/// The fixture is the smallest shape with the defect: `probe[E, F]` requires `Pair[E, F]`
/// and takes only an `E`, so `F` appears in no parameter type and NOTHING at a host entry
/// can pin it. `Pair` is a two-parameter spec so that the un-pinnable element is a genuine
/// dispatch element and not an effect row (which is non-discriminating by design).
///
/// FAILS IF THE RELAXATION IS BACKED OUT: the sole-provider row raises
/// `__req_pair not bound`. FAILS IF IT IS WIDENED TO FIRST-MATCH: the two-provider row
/// answers 1 or 2 instead of raising.
#[test]
fn wi1091_an_unpinnable_op_element_is_completed_only_when_the_providers_agree() {
    let program = |ns: &str, second: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.prelude.Additive.{{add}}
  import anthill.prelude.Multiplicative.{{mul}}
  sort Tag
    entity tag
  end
  sort Pair
    sort E = ?
    sort F = ?
    operation combine(x: E) -> Int64
  end
  sort First
    fact Pair[E = Tag, F = Int64]
    operation combine(x: Tag) -> Int64 = 1
  end
{second}
  sort Holder
    operation probe[E, F](x: E) -> Int64 requires Pair[E, F] = Pair.combine(x)
  end
end
"#
        )
    };
    const RIVAL: &str = r#"  sort Second
    fact Pair[E = Tag, F = Tag]
    operation combine(x: Tag) -> Int64 = 2
  end
"#;
    let enter = |ns: &str, src: &str| {
        let kb = crate::common::load_kb_with(src);
        let tag = kb.resolve_symbol(&format!("{ns}.Tag.tag"));
        let mut interp = anthill_core::eval::Interpreter::new(kb);
        anthill_core::eval::builtins::register_standard_builtins(&mut interp)
            .expect("register standard eval builtins");
        interp.call(
            &format!("{ns}.Holder.probe"),
            &[Value::Entity {
                functor: tag,
                pos: Vec::new().into(),
                named: Vec::new().into(),
            }],
        )
    };

    // ONE completion — `F` has exactly one value any provider gives it at `E = Tag`, so
    // the goal has exactly one answer and taking it is exact.
    let sole = program("wi1091.complete.sole", "");
    let got = enter("wi1091.complete.sole", &sole);
    assert!(
        matches!(got, Ok(Value::Int(1))),
        "with one provider the open `F` has ONE answer, so the host entry must complete \
         the goal and the body must read the slot; got {got:?}"
    );

    // TWO completions — `F = Int64` and `F = Tag` both answer at `E = Tag`. Neither may
    // be picked for the author: the slot stays absent and the body's read reports it.
    let tied = program("wi1091.complete.tied", RIVAL);
    let got = enter("wi1091.complete.tied", &tied);
    let err = got.expect_err(
        "CONTROL: with two completions the arguments genuinely do not decide, and \
         picking either would be the WRONG-dictionary case the `all_pinned` gate exists \
         to prevent",
    );
    let msg = err.to_string();
    assert!(
        msg.contains("__req_pair") && msg.contains("not bound"),
        "…and the body's read must name the slot it did not get; got {msg}"
    );

    // AN OPEN-ENDED RIVAL IS THE SAME VERDICT, and it is the row the first cut of this
    // test could not see (found by /code-review). `Anything` binds `F` to its OWN
    // parameter, so it answers at EVERY completion rather than proposing one — and a
    // provider that proposes nothing used to be indistinguishable from a provider that
    // is not there. MEASURED before the fix: `Ok(Int(1))`, the ground provider's answer,
    // silently chosen where `F := Tag` was equally available (2). This is the reason the
    // enumeration RETURNS on an unproposable provider rather than skipping it.
    const OPEN_ENDED: &str = r#"  sort Anything
    sort A = ?
    fact Pair[E = A, F = A]
    operation combine(x: A) -> Int64 = 2
  end
"#;
    let open_ended = program("wi1091.complete.open", OPEN_ENDED);
    let got = enter("wi1091.complete.open", &open_ended);
    let err = got.expect_err(
        "CONTROL: a provider that leaves `F` abstract answers at more than one \
         completion, so the arguments do not decide and no completion may be taken",
    );
    assert!(
        err.to_string().contains("__req_pair"),
        "…and the body's read must name the slot it did not get; got {err}"
    );
}

/// **THE ACCESSOR RUNS** — WI-1088's rule applied to WI-1091's field. `opref_shape`'s
/// keys are DECLARED accessors, so carrying the op-scoped channel as a fifth key means
/// declaring `OpRef.opRequirements` on the reflect `OpRef` sort, "and a declared accessor
/// a caller cannot call is a surface that only looks complete"
/// (`wi1088_spread_labels_identity_test::the_spread_labels_accessor_answers_for_both_
/// mints`, whose shape this follows).
///
/// Driven to the VALUE, and to BOTH answers, because a reader that returned `some([])`
/// for an op with no `requires` of its own would pass a positive-only test. The FILLED
/// row keeps an unprojected slot as `none()` IN PLACE: position is which requirement each
/// slot answers (the apply site zips this list against `op_dict_entries`' tail), so a
/// reader that dropped absences would mis-name every slot after the gap.
#[test]
fn wi1091_the_op_requirements_accessor_answers_for_both_mints() {
    use anthill_core::eval::value::Dictionary;
    let mut interp = crate::common::interp_for("namespace test.wi1091.acc\nend\n");
    let op = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option")
        .expect("a symbol to name as the op");
    let some_s = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option.some")
        .expect("Option.some");
    let none_s = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Option.none")
        .expect("Option.none");
    let cons_s = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons");
    // WI-867: the UNCHECKED constructor — this row drives the `opRequirements`
    // ACCESSOR, so the dictionary is a value to hand back, not evidence for a spec.
    let dict = interp
        .alloc_dictionary_unchecked(op, [])
        .expect("a one-slot dictionary");

    let functor = |v: &Value| match v {
        Value::Entity { functor, .. } => *functor,
        other => panic!("expected an entity, got {other:?}"),
    };
    let call = |i: &mut Interpreter, reqs: Option<Vec<Option<Dictionary>>>| {
        i.call(
            "anthill.realization.runtime.OpRef.opRequirements",
            &[Value::OpRef {
                op,
                dict: None,
                named: None,
                spread_labels: None,
                op_reqs: reqs.map(|r| std::rc::Rc::from(r.as_slice())),
            }],
        )
        .expect("OpRef.opRequirements")
    };

    // An op that writes no `requires` of its own — the universal case.
    assert_eq!(
        functor(&call(&mut interp, None)),
        none_s,
        "an op with no `requires` of its own must answer none(), not some([])"
    );

    // Two slots, the second unprojected: `some(cons(some(d), cons(none(), nil)))`.
    let answer = call(&mut interp, Some(vec![Some(dict), None]));
    assert_eq!(functor(&answer), some_s, "a chain-carrying op answers some(…)");
    let child = |v: &Value, name: &str, kb: &anthill_core::kb::KnowledgeBase| -> Value {
        match v {
            Value::Entity { named, .. } => named
                .iter()
                .find(|(s, _)| kb.local_name_of(*s) == name)
                .map(|(_, c)| c.clone())
                .unwrap_or_else(|| panic!("no `{name}` child on {v:?}")),
            other => panic!("expected an entity, got {other:?}"),
        }
    };
    let mut node = child(&answer, "value", interp.kb());
    let mut slots: Vec<bool> = Vec::new();
    while functor(&node) == cons_s {
        slots.push(functor(&child(&node, "head", interp.kb())) == some_s);
        node = child(&node, "tail", interp.kb());
    }
    assert_eq!(
        slots,
        vec![true, false],
        "the slots must come back IN ORDER with the unprojected one kept as none() in \
         place — dropping it would re-index every slot after the gap"
    );
}

