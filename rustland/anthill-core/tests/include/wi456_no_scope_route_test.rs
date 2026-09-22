//! WI-456 (found while measuring the ticket's remainder) — **a call whose enclosing
//! scope offers NO ROUTE to the callee's requirement is a LOAD error, not an `Internal`
//! at eval.**
//!
//! It has a second half — **Strategy 2b** — which makes one of those calls RUN instead:
//! a comparator sitting in the PROVIDER half of a dictionary the caller already holds is
//! now projected out of it rather than refused. See
//! `a_parent_instance_requirement_projects_the_comparator`.
//!
//! `build_dispatching_dict_from_chain`'s `require_complete` arm explains four reasons a
//! dep can fail to project — a witness the bracket PINNED that did not land (WI-841), a
//! σ-refused cover (WI-828), an UNCONSTRAINED element (WI-945), a carrier with no
//! provision row (WI-1102) — and took a silent `Ok(None)` for everything else. That
//! fall-back means *"no dictionary here; eval will inherit or value-direct"*, which is a
//! defensible answer for a same-sort call (`build_concrete_dispatch_dict` returns before
//! this point for one) and NO answer at all for a cross-sort call whose caller declares
//! nothing that could carry the dictionary.
//!
//! **THE SHAPE, and it is the one §7.1's abstract form invites.** `f[T, O](s: SortedSet[T
//! = T, O = O])` quantifies the ordering and declares no `requires` to carry it.
//! [`carried_slot`] reads the binder as `Forwarded` — the signature DECLARED it, which is
//! the `param_rigids` test — but declaring a type PARAMETER is not declaring a SLOT, so
//! the scope has nothing to forward. MEASURED at HEAD before this change: the program
//! LOADS CLEAN and dies with
//!
//! ```text
//! Internal: DeferToRequirement: requirement param `__req_weakord` not bound in caller
//! frame (running `anthill.prelude.SortedSet.insert`, …; frame binds [])
//! ```
//!
//! — which names neither the requirement nor a repair, and is the message
//! `eval/eval.rs`'s own WI-1102 note says one population should not be getting.
//!
//! **PARKED, NOT RAISED**, and since WI-20260921-3G1YT for one reason rather than two.
//! The refusal goes through [`UnsuppliableRequirement`] because an operation is routinely
//! called before its own body is classified, so the verdict waits for the pass that runs
//! once every body is typed. What it no longer waits FOR is a walk of the callee's body:
//! that walk is deleted, a declared `requires` is owed BECAUSE IT IS DECLARED, and the
//! `SortedSet.collect` / `SortedSet.insert` distinction this header used to draw is gone
//! with it — both are `SortedSet` members and both need the ordering forwarded. See
//! `a_callee_that_never_reads_the_slot_is_refused_too_and_the_slot_is_the_repair`.
//!
//! **CONTROLS, per CLAUDE.md.**
//!  * `a_declared_slot_still_carries_it` and `a_sort_level_slot_is_the_repair` PASS EITHER
//!    WAY BY DESIGN — they are the working spellings, and they are here because the
//!    refusal must not widen onto them. The second is also the repair the message names,
//!    driven to a VALUE rather than to a load verdict.
//!  * `a_callee_that_never_reads_the_slot_is_refused_too_and_the_slot_is_the_repair`
//!    drives the WI-20260921-3G1YT verdict and its repair; it INVERTED there, and says so
//!    at its site.
//!  * `positive_control_a_broken_program_is_refused` guards the oracle.
//!
//! **BACK-OUT MATRIX, measured on this tree rather than reasoned — THREE separable
//! changes, three disjoint failure sets.**
//!
//!  * the parked `no_scope_route` refusal → `an_undeclared_ordering_is_refused_at_load`
//!    and `the_refusal_names_the_repair_and_not_a_witness_choice` (2), each going back
//!    to loading clean and dying at eval. (It was 3 until WI-20260921-159S9 inverted the
//!    op-scoped arm, which no longer measures the refusal at all.)
//!  * the tail advice ALONE → `the_refusal_names_the_repair_and_not_a_witness_choice`
//!    alone (1). The other two assert the VERDICT and say nothing about the wording,
//!    which is why [`assert_no_route`] deliberately does not check the advice;
//!  * Strategy 2b (`provider_half_projection`) →
//!    `a_parent_instance_requirement_projects_the_comparator` alone (1);
//!  * its GATE — swapping [`carrier_is_its_own_sole_provider`] back for
//!    `carrier_has_provision_row` → `strategy_2b_declines_a_witness_provider` alone (1),
//!    which then LOADS AND ANSWERS 99 instead of refusing. That arm measures the gate
//!    rather than the program, which the first draft of it did not: written against a
//!    carrier with no `requires` of its own it passed under BOTH gates, because the wrong
//!    chain had no matching entry to mis-index.
//!
//! And the guard that makes the refusal YIELD to `ProvisionConditionOutOfScope` is
//! measured elsewhere, by `wi_1z3e7 a_helper_calling_a_member_directly_builds_its_-
//! dictionary`: without it the parked refusal displaces proposal 066 §7.4's message,
//! which names both operations and a repair this one cannot. That was the single
//! regression the refusal caused across the workspace, and it is why the least-specific
//! signature yields rather than wins.
//!
//! **ONE OF THE REFUSED SHAPES NAMED EVIDENCE THAT EXISTS, AND IT NOW RUNS.** Three
//! shapes reached the silent `Ok(None)`; they are not one gap, and conflating them would
//! send a follow-on at the wrong target:
//!
//!  * NOTHING DECLARED (`f[T, O](s: SortedSet[T = T, O = O])`) — a real language rule.
//!    An operation declares the evidence its body needs; the refusal states that at load
//!    instead of letting eval say it worse. Permanently correct;
//!  * THE PARENT INSTANCE (`requires PersistentCollection[C = SortedSet[T = E, O = OE]]`)
//!    — an unreached projection, and CLOSED here by Strategy 2b: the comparator is in the
//!    provider half of the very dictionary the caller holds, at
//!    `dict_layout(..).spec_len() + k`. `a_parent_instance_requirement_projects_the_-
//!    comparator` drives it to two values;
//!  * THE OP-SCOPED SLOT — **CLOSED by WI-20260921-159S9, and its arm here INVERTED
//!    rather than disappearing** (`an_op_scoped_slot_is_a_working_spelling`, now a value
//!    assertion over both orderings). It was refused BY DECISION rather than oversight:
//!    the instance-dictionary builders read `TypingEnv::enclosing_chain`, the SORT half,
//!    because that channel is read strictly at eval while several routes into an
//!    operation filled no op slot. The follow-on was NOT "compose the chain" but "make
//!    the op-half channel reliable at every entry" — and that is what landed. Three
//!    routes had closed already (a HOST entry seeds the op half from the argument values
//!    since WI-1091; an eta carries its slots captured; value-direction reads the
//!    composed chain); the DEFERRED route was the remaining hole and
//!    `Interpreter::fill_missing_op_scoped_slots` fills it at `enter_operation`. Only
//!    then did the builder widen to `enclosing_frame_chain()`.
//!
//! So `a_sort_level_slot_is_the_repair` is no longer THE repair, only A repair — the
//! message's tail still names it because it is the one that needs no type parameters,
//! but the operation-level spelling now works too. Both are driven to values here.

use anthill_core::eval::Value;

/// Two rival `WeakOrd[String]`, so no assertion below can be explained by there being
/// only one thing to pick — and so the refusals are visibly not tie refusals.
const ORDERINGS: &str = r#"
  sort ByLength
    import anthill.prelude.{String, Int64, WeakOrd}
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
  sort Alphabetical
    import anthill.prelude.{String, Int64, Ord}
    import anthill.prelude.PartialOrd.{lt, gt}
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 =
      if lt(a, b) then -1 else if gt(a, b) then 1 else 0
  end
  sort Head
    import anthill.prelude.{String, List}
    import anthill.prelude.List.{cons, nil}
    operation head(l: List[T = String]) -> String =
      match l
        case nil() -> "<empty>"
        case cons(h, t) -> h
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool, SortedSet, \
         PersistentCollection}}\n\
         {ORDERINGS}{body}\nend\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

fn loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got load errors: {errs:?}\n{src}");
    }
}

/// `entry()` on a FRESH interpreter — `interp_for` panics on a dirty load, so a value
/// assertion is also a clean-load assertion.
fn eval_str(src: &str, entry: &str, why: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[]) {
        Ok(Value::Str(s)) => s,
        other => panic!("{why}; got {other:?}\n{src}"),
    }
}

/// THE VERDICT ONLY — that the call is refused and the message names the requirement.
/// Deliberately NOT the advice: the two halves are separate changes (the parked refusal,
/// and the tail that replaces the generic "pin the element" line), so bundling them here
/// would make every back-out fail the same set and the matrix unattributable. The advice
/// has its own driver, `the_refusal_names_the_repair_and_not_a_witness_choice`.
///
/// Asserted on the QUALIFIED spelling the message actually prints, per WI-456(b)'s lesson
/// about grepping for advice that was never rendered.
fn assert_no_route(errs: &[String], why: &str) {
    assert!(
        errs.iter().any(|e| {
            e.contains("anthill.prelude.WeakOrd")
                && e.contains("cannot be supplied for call to")
        }),
        "{why}: expected the call to be refused, naming the requirement; got {errs:?}"
    );
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so every
/// `loads_clean` below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(&program(
        "wi456nr.control",
        "  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    ));
}

// ── The refusal ──────────────────────────────────────────────────────

/// THE HEADLINE. `O` is quantified by the operation and nothing declares a slot for it,
/// so no scope entry can carry the dictionary `SortedSet.insert` reads. Before the
/// `no_scope_route` arm this loaded clean and died `Internal(… __req_weakord not bound …
/// frame binds [])`.
#[test]
fn an_undeclared_ordering_is_refused_at_load() {
    let errs = load_errs(&program(
        "wi456nr.undeclared",
        "  sort PolyA\n    \
         operation insertA[T, O](s: SortedSet[T = T, O = O], x: T) \
         -> SortedSet[T = T, O = O] =\n      \
         SortedSet.insert(s, x)\n  end",
    ));
    assert_no_route(&errs, "an operation type parameter is not a requirement slot");
}

/// …AND IT IS NOT A TIE REFUSAL. Two `WeakOrd[String]` providers are in scope above, and
/// the message must be about the missing ROUTE rather than about which provider to pick —
/// otherwise the repair it names would be the wrong one.
#[test]
fn the_refusal_names_the_repair_and_not_a_witness_choice() {
    let errs = load_errs(&program(
        "wi456nr.notatie",
        "  sort PolyA\n    \
         operation insertA[T, O](s: SortedSet[T = T, O = O], x: T) \
         -> SortedSet[T = T, O = O] =\n      \
         SortedSet.insert(s, x)\n  end",
    ));
    assert!(
        errs.iter().any(|e| e.contains("declare a requirement slot")
            && e.contains("on the enclosing SORT")
            && !e.contains("select a witness")),
        "the no-route tail replaces the generic advice, which tells the author to pin an \
         element that is already pinned — to a parameter of their own signature: {errs:?}"
    );
}

/// An OP-SCOPED `requires OE: WeakOrd[E]` — the author DID declare a slot, and IT NOW
/// REACHES THE PROJECTOR. **THIS ARM INVERTED, as its earlier text said it would.**
///
/// It used to read `assert_no_route`: `caller_requires` was the SORT half, so the op
/// clause never reached the builder and the call was refused — the honest verdict then,
/// and strictly better than the eval `Internal` it replaced, but still one of two
/// spellings of one program of which only one worked.
///
/// WI-20260921-159S9 made the builder read the caller's WHOLE frame and gave the
/// deferred entry route a fill for its op half, so the clause is now carried. Written as
/// a VALUE assertion rather than a clean-load one, and over BOTH orderings: a load
/// verdict cannot tell "the slot travelled" from "the callee re-found a comparator", and
/// `zz` twice would mean the slot decided nothing.
///
/// The general form, its back-out matrix and the deferred-route control live in
/// `wi_159s9_op_scoped_entry_test`; this arm stays HERE because it is the refusal this
/// file's tail advice used to name, and the two must not drift.
#[test]
fn an_op_scoped_slot_is_a_working_spelling() {
    let src = program(
        "wi456nr.opscoped",
        "  sort PolyC\n    \
         operation insertC[E, OE](s: SortedSet[T = E, O = OE], x: E) \
         -> SortedSet[T = E, O = OE]\n        \
         requires OE: WeakOrd[E] =\n      \
         SortedSet.insert(s, x)\n  end\n  \
         sort Driver\n    \
         operation byLength() -> String =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         Head.head(SortedSet.toList(PolyC.insertC(PolyC.insertC(s, \"zz\"), \"aaa\")))\n    \
         operation alphabetical() -> String =\n      \
         let s = SortedSet.empty[T = String, O = Alphabetical]()\n      \
         Head.head(SortedSet.toList(PolyC.insertC(PolyC.insertC(s, \"zz\"), \"aaa\")))\n  end",
    );
    assert_eq!(
        eval_str(&src, "wi456nr.opscoped.Driver.byLength", "the length ordering travels"),
        "zz",
    );
    assert_eq!(
        eval_str(
            &src,
            "wi456nr.opscoped.Driver.alphabetical",
            "the alphabetic ordering travels"
        ),
        "aaa",
        "the SAME body as `a_sort_level_slot_is_the_repair` drives, with the clause \
         written on the OPERATION instead of the sort — two spellings of one program, \
         and they now agree",
    );
}

/// REQUIRING THE CARRIER INSTANCE RATHER THAN THE ORDERING — and it RUNS, which is
/// Strategy 2b ([`provider_half_projection`]).
///
/// `PolyD` names no comparator at all. It requires the collection instance, and the
/// dictionary that travels for it carries `SortedSet`'s own `WeakOrd` in its PROVIDER
/// half — past the spec half Strategy 2 searches, at `dict_layout(..).spec_len() + k`.
/// Before Strategy 2b this loaded clean and died `Internal(DeferToRequirement:
/// __req_weakord not bound … frame binds [])` with the comparator one
/// `requirement_at_sort` step inside the slot the frame did hold.
///
/// DRIVEN TO TWO VALUES, not to a clean load: one polymorphic body over the same two
/// strings, differing only in the ordering its caller's instance was built with. `zz`
/// twice would mean the projection landed somewhere that does not depend on `O` — which
/// is exactly what a WRONG index would look like, since a wrong slot still holds a real
/// dictionary and still resolves.
#[test]
fn a_parent_instance_requirement_projects_the_comparator() {
    let src = program(
        "wi456nr.parent",
        "  sort PolyD\n    \
         sort E = ?\n    \
         sort OE = ?\n    \
         requires PersistentCollection[C = SortedSet[T = E, O = OE], Element = E]\n    \
         operation insertD(s: SortedSet[T = E, O = OE], x: E) \
         -> SortedSet[T = E, O = OE] =\n      \
         SortedSet.insert(s, x)\n  end\n  \
         sort Driver\n    \
         operation byLength() -> String =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         Head.head(SortedSet.toList(PolyD.insertD(PolyD.insertD(s, \"zz\"), \"aaa\")))\n    \
         operation alphabetical() -> String =\n      \
         let s = SortedSet.empty[T = String, O = Alphabetical]()\n      \
         Head.head(SortedSet.toList(PolyD.insertD(PolyD.insertD(s, \"zz\"), \"aaa\")))\n  end",
    );
    assert_eq!(
        eval_str(&src, "wi456nr.parent.Driver.byLength", "the length ordering projects"),
        "zz",
    );
    assert_eq!(
        eval_str(
            &src,
            "wi456nr.parent.Driver.alphabetical",
            "the alphabetic ordering projects"
        ),
        "aaa",
        "the SAME body, differing only in the ordering the caller's INSTANCE carries — so \
         one answer twice would mean the provider-half projection read a slot that does \
         not depend on `O`",
    );
}

/// THE GATE ON STRATEGY 2B, and the arm that makes 2b admissible at all. Found by
/// /code-review, and DISCRIMINATING — the first cut of this test was not, which is the
/// whole reason it is written the way it is.
///
/// `ShowBox` is a WITNESS: a different sort from the carrier `Boxed`, providing
/// `Shown[T = Boxed[E = E]]` and carrying its OWN `requires Tagged[T = Boxed[E = E]]`. So a
/// caller's `Shown` slot holds a dictionary whose PROVIDER half is `ShowBox`'s chain. The
/// carrier `Boxed` ALSO declares `requires Tagged[T = E]` — same spec, different
/// instantiation — so reading the carrier's chain there finds a match at the same index
/// and indexes a REAL dictionary at the WRONG slot. `check_against_prediction` cannot see
/// it: that guards a dictionary's CONSTRUCTION and this is a READ.
///
/// MEASURED BOTH WAYS on the probe this fixture is:
///   * gate = `carrier_has_provision_row` (which answers `true` for a witness BY DESIGN) —
///     the program RUNS and answers **99**, `TagBoxed` via the witness's own requirement,
///     where 7 (`TagString`) is the caller's;
///   * gate = [`carrier_is_its_own_sole_provider`] — refused, which is the SAME verdict as
///     before Strategy 2b existed.
///
/// A silently wrong answer out of a correctly-refused program is the worst trade this file
/// can make, so the refusal below is the assertion and `99` is what must never appear.
/// Swapping the gate back flips it, which is what makes this arm measure the gate and not
/// merely the program.
#[test]
fn strategy_2b_declines_a_witness_provider() {
    let src = program(
        "wi456nr.witness",
        "  sort Tagged\n    \
         sort T = ?\n    \
         operation tag(x: T) -> Int64\n  end\n  \
         sort TagString\n    \
         provides Tagged[T = String]\n    \
         operation tag(x: String) -> Int64 = 7\n  end\n  \
         enum Boxed\n    \
         sort E = ?\n    \
         requires Tagged[T = E]\n    \
         entity boxed(v: E)\n  end\n  \
         sort Shown\n    \
         sort T = ?\n    \
         operation show(x: T) -> Int64\n  end\n  \
         sort TagBoxed\n    \
         sort E = ?\n    \
         provides Tagged[T = Boxed[E = E]]\n    \
         operation tag(x: Boxed[E = E]) -> Int64 = 99\n  end\n  \
         sort ShowBox\n    \
         sort E = ?\n    \
         requires Tagged[T = Boxed[E = E]]\n    \
         provides Shown[T = Boxed[E = E]]\n    \
         operation show(x: Boxed[E = E]) -> Int64 = 1\n  end\n  \
         sort NeedsTag\n    \
         sort T = ?\n    \
         requires Tagged[T = T]\n    \
         operation twice(x: T) -> Int64 = Tagged.tag(x)\n  end\n  \
         sort Uses\n    \
         sort E = ?\n    \
         requires Shown[T = Boxed[E = E]]\n    \
         operation viaSlot(x: E) -> Int64 = NeedsTag.twice(x)\n  end",
    );
    // Not [`assert_no_route`]: that one names `WeakOrd`, this fixture's spec is `Tagged`.
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("wi456nr.witness.Tagged")
                && e.contains("wi456nr.witness.NeedsTag")
                && e.contains("cannot be supplied for call to")
        }),
        "a WITNESS provider's dictionary must not be read as if it were the carrier's — \
         Strategy 2b declines and the CALLEE's dep stays unsupplied; got {errs:?}"
    );
}

// ── What must NOT be refused ─────────────────────────────────────────

/// **THIS ROW INVERTED AT WI-20260921-3G1YT.** It read
/// `a_callee_that_never_reads_the_slot_still_loads` and was the arm that kept the refusal
/// honest under the READ GATE: `toList`'s body reads no ordering, so the dictionary it
/// could not be given was called an IRRELEVANCE and the parked refusal was dropped by the
/// body pass.
///
/// That gate and the two body walks behind it are deleted. A declared `requires` is owed
/// by the caller BECAUSE IT IS DECLARED, and `SortedSet`'s `requires O: WeakOrd[T]` is
/// declared — `listOut` calls a `SortedSet` member while holding nothing for `O`, and
/// whether THAT member currently touches the ordering is not something `listOut`'s author
/// can see from the call.
///
/// AND THE REPAIR IS NOT "DELETE THE CLAUSE" HERE, which is what makes this row worth
/// keeping beside the ones that are: `SortedSet.insert` genuinely needs the ordering, so
/// the clause stays and the caller FORWARDS it — the same named-slot spelling
/// [`a_sort_level_slot_is_the_repair`] drives to a value. Deleting is the repair only
/// where no member of the declaring sort uses the evidence.
#[test]
fn a_callee_that_never_reads_the_slot_is_refused_too_and_the_slot_is_the_repair() {
    let unslotted = program(
        "wi456nr.unread",
        "  sort PolyE\n    \
         operation listOut[T, O](s: SortedSet[T = T, O = O]) -> List[T = T] =\n      \
         SortedSet.toList(s)\n  end",
    );
    assert_no_route(
        &load_errs(&unslotted),
        "a `SortedSet` member is called while the caller holds nothing for `O`",
    );

    // THE REPAIR: declare the slot, and the identical body loads.
    loads_clean(
        &program(
            "wi456nr.unread2",
            "  sort PolyE\n    \
             sort E = ?\n    \
             requires OE: WeakOrd[E]\n    \
             operation listOut(s: SortedSet[T = E, O = OE]) -> List[T = E] =\n      \
             SortedSet.toList(s)\n  end",
        ),
        "forwarding the ordering the callee's sort declares must discharge the call",
    );
}

/// THE REPAIR THE MESSAGE NAMES, driven to a VALUE. A sort-level named slot carries the
/// dictionary, and ONE polymorphic body answers differently for the two orderings — which
/// is what proves the dictionary travelled rather than being re-searched (`zz` twice would
/// mean the slot decided nothing).
///
/// PASSES EITHER WAY BY DESIGN: it is the working spelling, here so the refusal cannot
/// widen onto it.
#[test]
fn a_sort_level_slot_is_the_repair() {
    let src = program(
        "wi456nr.repair",
        "  sort PolyB\n    \
         sort E = ?\n    \
         requires OE: WeakOrd[E]\n    \
         operation insertB(s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] =\n      \
         SortedSet.insert(s, x)\n  end\n  \
         sort Driver\n    \
         operation byLength() -> String =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         Head.head(SortedSet.toList(PolyB.insertB(PolyB.insertB(s, \"zz\"), \"aaa\")))\n    \
         operation alphabetical() -> String =\n      \
         let s = SortedSet.empty[T = String, O = Alphabetical]()\n      \
         Head.head(SortedSet.toList(PolyB.insertB(PolyB.insertB(s, \"zz\"), \"aaa\")))\n  end",
    );
    assert_eq!(
        eval_str(&src, "wi456nr.repair.Driver.byLength", "the length ordering travels"),
        "zz",
    );
    assert_eq!(
        eval_str(
            &src,
            "wi456nr.repair.Driver.alphabetical",
            "the alphabetic ordering travels"
        ),
        "aaa",
        "the SAME polymorphic body over the SAME two strings, differing only in the \
         ordering the caller's slot carries — so one answer twice would mean the slot \
         decided nothing",
    );
}

/// The ordinary monomorphic call, which declares no slot and needs none because the
/// argument's TYPE names the ordering. PASSES EITHER WAY BY DESIGN — it is the shape the
/// whole `SortedSet` surface rests on, and the arm that would fail first if the refusal
/// reached calls whose σ already pins the slot.
#[test]
fn a_declared_slot_still_carries_it() {
    let src = program(
        "wi456nr.mono",
        "  sort Driver\n    \
         operation byLength() -> String =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         Head.head(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, \"zz\"), \"aaa\")))\n  end",
    );
    assert_eq!(
        eval_str(&src, "wi456nr.mono.Driver.byLength", "the pinned ordering runs"),
        "zz",
    );
}
