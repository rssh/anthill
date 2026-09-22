//! WI-20260921-EE0EP — **A PARAMETER'S UNWRITTEN NAMED SLOT RECEIVES THE ARGUMENT'S OWN
//! DICTIONARY**, so writing `O` and leaving it out mean the same thing at run time.
//!
//! THE DEFECT, IN ONE SENTENCE: the caller held the evidence and the signature had
//! nowhere to put it.
//!
//! ```anthill
//! operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)
//! ```
//!
//! over `enum MySet requires O: WeakOrd[T]` was a LOAD ERROR (WI-1094): the body's
//! `contains` reads `MySet`'s `O`, the signature declares no slot to carry one, and
//! constructing one here would answer for a value that already chose. §3.9 left two
//! repairs — forward the value's own dictionary, or refuse — and WI-1094 shipped the
//! refusal *because forwarding had no channel*. It does now.
//!
//! **WHY THE CALLER ALREADY HAS IT, which is what made this cheap.** WI-1059's
//! `rigidify_unwritten_sort_params` mints the slot for the BODY as the projection `s.O`
//! and leaves the call-side slot FLEX — so at every call the ARGUMENT's type binds it,
//! with no bracket written. [`a_declared_slot_needs_no_bracket`] measures exactly that,
//! and it is the control the whole ticket rests on: nothing had to be recovered from the
//! VALUE, and nothing added to the dictionary's shape.
//!
//! **THE CHANNEL IS THE ORDINARY ONE.** No new frame kind, no eval change: a synthesized
//! op-scoped entry ([`SupplySource::FromParam`]) per unwritten slot, appended after the
//! author's, filled at the call by READING the witness out of the argument's type, read
//! by the forward that was already there. The eval side is untouched because the frame's
//! requirement channel is keyed by NAME (`push_op_scoped_slots`).
//!
//! **ONE ANSWER TWICE IS A FAILURE.** Every row below is driven at BOTH rival orderings
//! through ONE body, and they must DISAGREE. A test that only asserted the program LOADS
//! would have passed on the first cut of this change, which loaded and answered `false`
//! at both — the map that carries the witness was gated off, so the slot was filled by a
//! *construction*, which is the very rival WI-1094 refused.
//!
//! **WHAT STAYS REFUSED, and each for its own reason** — decisions (c) and the collision
//! screen. An EXISTENTIAL RETURN names no provider to forward
//! ([`an_existential_return_is_still_refused`]); a slot some OTHER frame entry already
//! covers cannot be routed to this parameter
//! ([`a_slot_the_frame_already_covers_is_refused_not_guessed`],
//! [`two_parameters_of_one_carrier_are_refused`]).
//!
//! BACKING OUT: each test names, at its own site, which edit it measures.
//!
//! Reference: 058 §3.4, §3.9, §7.1; `docs/kernel-language.md` §"How the slot is named"
//! (WI-1059); `docs/design/path-dependent-types.md` §5.5; WI-1094 (the refusal this
//! replaces), WI-20260921-R10KC (the adjacent half), WI-20260919-N31XX (the `whole_frame`
//! precedent).

use anthill_core::eval::Value;

/// Two rival `WeakOrd[String]`. `ByLength` makes `"zz"` and `"aa"` one class; the
/// alphabetical one separates them. So `{"zz"}.contains("aa")` is `true` under the first
/// and `false` under the second — one query, two answers, and the comparator is the only
/// thing that differs.
const RIVALS: &str = r#"
  sort IntDesc
    import anthill.prelude.{Int64, Ord, WeakOrd}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  sort Alphabetical
    import anthill.prelude.PartialOrd.{lt, gt}
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 =
      if lt(a, b) then -1 else if gt(a, b) then 1 else 0
  end
"#;

/// The carrier with the named slot, and nothing else: no spec, no default body. The slot
/// `O` is read by `contains` through `WeakOrd.compare`, and it is recorded nowhere in the
/// set's DATA (`node(elem: "zz", rest: nothing())` names no ordering), which is what makes
/// the dictionary the only possible carrier of the answer.
const CARRIER: &str = r#"
  enum MySet
    import anthill.prelude.PartialOrd.{lt, gt}
    sort T = ?
    requires O: WeakOrd[T]

    entity nothing
    entity node(elem: T, rest: MySet[T = T, O = O])

    operation contains(s: MySet[T = T, O = O], x: T) -> Bool =
      match s
        case nothing() -> false
        case node(y, r) ->
          let c = WeakOrd.compare(x, y)
          if lt(c, 0) then false
          else if gt(c, 0) then contains(r, x)
          else true

    operation empty() -> MySet[T = T, O = O] = nothing()
    operation insert(s: MySet[T = T, O = O], x: T) -> MySet[T = T, O = O] = node(x, s)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool}}\n  \
         import anthill.prelude.List.{{nil, cons}}\n\
         {RIVALS}{CARRIER}{body}\nend\n"
    )
}

/// A `{"zz"}` built at `ordering`, as an argument expression.
fn set_at(ordering: &str) -> String {
    format!("MySet.insert(MySet.empty[T = String, O = {ordering}](), \"zz\")")
}

/// Run `entry(0)` on a FRESH interpreter — `interp_for` panics on a dirty load, so a
/// value assertion is also a clean-load assertion.
fn eval_bool(src: &str, entry: &str) -> bool {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("expected a Bool from {entry}; got {other:?}\n{src}"),
    }
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// Both orderings through one body, asserted to DISAGREE. The `why` is what a failure
/// prints, and "one answer twice" is called out because it is the shape a half-working
/// channel produces — the dictionary arrived, but not the argument's.
fn assert_discriminates(src: &str, by_length: &str, alphabetical: &str, why: &str) {
    let a = eval_bool(src, by_length);
    let b = eval_bool(src, alphabetical);
    assert!(
        a && !b,
        "{why}: expected ByLength=true, Alphabetical=false; got {a} and {b}. \
         One answer twice means the dictionary was re-derived here rather than taken \
         from the argument"
    );
}

// ── The subject ──────────────────────────────────────────────────────

/// **THE TICKET.** A parameter that omits the named slot, a body that dispatches through
/// it, no `requires` and no bracket anywhere — and the answer is the value's own.
///
/// BACKED OUT — MEASURED, one edit at a time, and this row fails on each of the three:
/// remove `param_derived_requires` and the chain has no slot, so WI-1094's refusal
/// returns; remove the `whole_frame` term and the body's forward cannot see the slot
/// (`an_unwritten_slot_takes_the_arguments_own_comparator`,
/// [`a_free_operation_carries_the_channel_too`] and
/// [`the_channel_relays_through_a_second_hop`] fail, the rest pass); remove the
/// `param_slot_witness` fill and the same three fail, refused at the ambiguous
/// construction. The FIRST CUT of this change is what says a load assertion would not
/// have been enough: with the fill present but `param_arg_types` gated off it LOADED and
/// read `false` at both orderings.
#[test]
fn an_unwritten_slot_takes_the_arguments_own_comparator() {
    let src = program(
        "ee0ep.subject",
        &format!(
            "  sort Bulk\n    \
             operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n  \
             end\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = Bulk.has({}, \"aa\")\n    \
             operation alphabetical(n: Int64) -> Bool = Bulk.has({}, \"aa\")\n  end",
            set_at("ByLength"),
            set_at("Alphabetical"),
        ),
    );
    assert_discriminates(
        &src,
        "ee0ep.subject.Driver.byLength",
        "ee0ep.subject.Driver.alphabetical",
        "the unwritten slot must forward the argument's own comparator",
    );
}

/// A FREE operation — no enclosing sort at all. Worth its own row because it is the shape
/// the obvious alternative could never serve: a sort-level `requires` needs a sort, and
/// this has none. It is also why the channel is op-scoped rather than sort-scoped.
///
/// BACKED OUT: same three edits as the subject.
#[test]
fn a_free_operation_carries_the_channel_too() {
    let src = program(
        "ee0ep.free",
        &format!(
            "  operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = has({}, \"aa\")\n    \
             operation alphabetical(n: Int64) -> Bool = has({}, \"aa\")\n  end",
            set_at("ByLength"),
            set_at("Alphabetical"),
        ),
    );
    assert_discriminates(
        &src,
        "ee0ep.free.Driver.byLength",
        "ee0ep.free.Driver.alphabetical",
        "a free operation has no sort-level chain, so this row measures the op-scoped \
         channel alone",
    );
}

/// TWO HOPS, both omitting. The second hop's argument is the first's PARAMETER, whose
/// type carries the WI-1059 projection and names no provider — so this row does not
/// measure the argument-reading fill at all. It measures the FORWARD: `outer`'s own
/// synthesized slot answers `inner`'s, one frame out.
///
/// BACKED OUT: without the `whole_frame` widening `inner`'s slot cannot be filled from
/// `outer`'s frame and the chain breaks at the second hop.
#[test]
fn the_channel_relays_through_a_second_hop() {
    let src = program(
        "ee0ep.chain",
        &format!(
            "  sort Bulk\n    \
             operation inner(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n    \
             operation outer(s: MySet[T = String], x: String) -> Bool = inner(s, x)\n  \
             end\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = Bulk.outer({}, \"aa\")\n    \
             operation alphabetical(n: Int64) -> Bool = Bulk.outer({}, \"aa\")\n  end",
            set_at("ByLength"),
            set_at("Alphabetical"),
        ),
    );
    assert_discriminates(
        &src,
        "ee0ep.chain.Driver.byLength",
        "ee0ep.chain.Driver.alphabetical",
        "a second hop that also omits the slot must relay the first's, not re-derive",
    );
}

// ── Decision (b): depth ──────────────────────────────────────────────

/// DECISION (b), MEASURED: the element of a `List`, reached by a `match` rather than by a
/// parameter. The ticket asked whether the LIST's channel reaches it; the answer is that
/// the question does not arise — a list has ONE element type
/// (`a_list_holds_one_witness_for_every_element`), the witness rides that type, and the
/// element's own carrier slot is written there. So this loads and discriminates with no
/// container-level machinery at all.
///
/// PASSES EITHER WAY with respect to this ticket's edits, and says so rather than being
/// presented as a driver: the element type here WRITES `O`, so no slot is unwritten and
/// nothing is synthesized. It is here because the ticket asked the question, and this is
/// the measurement that answers it.
#[test]
fn a_list_element_keeps_its_own_ordering() {
    let src = program(
        "ee0ep.nested",
        &format!(
            "  sort Bulk\n    \
             sort O = ?\n    \
             requires O: WeakOrd[String]\n    \
             operation headHas(ss: List[T = MySet[T = String, O = O]], x: String) -> Bool =\n      \
             match ss\n        \
             case nil() -> false\n        \
             case cons(h, t) -> MySet.contains(h, x)\n  \
             end\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = Bulk.headHas(cons({}, nil()), \"aa\")\n    \
             operation alphabetical(n: Int64) -> Bool = Bulk.headHas(cons({}, nil()), \"aa\")\n  end",
            set_at("ByLength"),
            set_at("Alphabetical"),
        ),
    );
    assert_discriminates(
        &src,
        "ee0ep.nested.Driver.byLength",
        "ee0ep.nested.Driver.alphabetical",
        "the element TYPE carries the witness, so a container needs no channel of its own",
    );
}

// ── Decision (c), and the collision screen ───────────────────────────

/// DECISION (c): an EXISTENTIAL RETURN stays refused, and for a reason that is not depth
/// and not caution — there is no argument. `mk()` PACKS a witness (WI-1063) and each use
/// opens a fresh skolem that names no provider, so there is nothing for a caller to
/// forward. The channel this ticket adds reads an ARGUMENT's type; a return has none.
///
/// PASSES EITHER WAY — it is the boundary, and it fails only if the synthesis ever starts
/// treating a return position as a parameter.
#[test]
fn an_existential_return_is_still_refused() {
    let errs = load_errs(&program(
        "ee0ep.exist",
        &format!(
            "  sort Maker\n    \
             operation mk() -> MySet[T = String] = {}\n  \
             end\n  \
             sort Bulk\n    \
             operation go(n: Int64) -> Bool = MySet.contains(Maker.mk(), \"aa\")\n  end",
            set_at("ByLength"),
        ),
    ));
    // AND THE MESSAGE SAYS WHY IT DIFFERS from the parameter case — decision (c)'s
    // second half. The old shared sentence advised "write `O` in the parameter's type",
    // which is advice for a parameter this call does not have: the argument is a call
    // result. MEASURED, and the reason the message now also rules out the bracket: both
    // `MySet[O = …].contains(mk(), x)` and `MySet.contains[O = …](mk(), x)` pin the
    // PARAMETER and leave the argument reading `?O`, so an author who tries the obvious
    // repair first gets a second, less clear refusal.
    assert!(
        errs.iter().any(|e| e.contains("NOTHING HERE CAN SUPPLY IT")
            && e.contains("where the value is PRODUCED")),
        "an opened skolem names no provider, so there is nothing to forward — and the \
         refusal must say that rather than naming a parameter repair: {errs:?}"
    );
}

/// THE COLLISION SCREEN, half one: the author's OWN anonymous `requires` of the same spec.
///
/// This is the row that caught a real defect in this ticket's first cut. Both entries
/// cover the goal `WeakOrd[T = String]`, the body reads a GOAL and not a parameter, so the
/// forward takes whichever comes first — and with the screen absent the program LOADED and
/// answered out of the author's slot, which records nothing about the argument. Refused
/// rather than ranked: ranking needs the READ to name its parameter, which is the `s.O`
/// spelling and a separate question.
///
/// BACKED OUT: remove the screen in `op_requires_chain_rc` and this loads and answers
/// `false` where the argument's `ByLength` says `true` — a WRONG ANSWER, not a missing one.
#[test]
fn a_slot_the_frame_already_covers_is_refused_not_guessed() {
    // The rival is declared at the SORT level, which is what makes this the COLLISION
    // case rather than the closed-channel one: `Bulk` writes no op-scoped `requires`, so
    // the slot IS synthesized and then screened against the frame's sort half. (An
    // op-scoped `requires` closes the channel before the screen runs at all — that is
    // [`a_mixed_chain_keeps_the_refusal`], a different cause and a different message. The
    // first cut used the op-scoped spelling here and so drove that one twice.)
    let errs = load_errs(&program(
        "ee0ep.collide",
        "  sort Bulk\n    \
         requires WeakOrd[T = String]\n    \
         operation has(s: MySet[T = String], x: String) -> Bool =\n      \
         MySet.contains(s, x)\n  end",
    ));
    // PINS THE CASE, not just the refusal: the message must be the AmbiguousWithFrame
    // one. A row that accepted any refusal here would keep passing if the collision were
    // ever mis-reported as "nothing can supply this", which names the wrong repair.
    assert!(
        errs.iter().any(|e| e.contains("already answers")
            && e.contains("named requirement slot `O")),
        "an anonymous `requires` of the same spec already covers the goal, so which \
         dictionary the body means is not decidable — refuse, and say THAT: {errs:?}"
    );
}

/// THE COLLISION SCREEN, half two: TWO parameters of one carrier. Their synthesized specs
/// are identical (`WeakOrd[T = String]` both), so the same ambiguity arises between two
/// SYNTHESIZED slots rather than against an author's.
///
/// REFUSING IS THE DECISION, confirmed by the user (2026-09-22) rather than chosen here:
/// the shape is refused, not answered. What would lift it is decision (d) — a `s.O`
/// spelling that lets the READ name its parameter, since in the body `b`'s type already
/// carries `O = b.O` and it is only the forward's spec-keyed matching that cannot see it.
///
/// BACKED OUT — MEASURED IN BOTH DIRECTIONS, because the first cut of this note PREDICTED
/// the wrong one. Remove the screen and the program LOADS, and a read of `a` answers out
/// of `b`'s dictionary — not, as predicted, `b` answering out of `a`'s. Driven at both
/// orderings so it cannot be read as coincidence:
///
///   body reads `a`, a=Alphabetical b=ByLength  ⟹  `true`, where `a`'s own order says false
///   body reads `a`, a=ByLength b=Alphabetical  ⟹  `false`, where `a`'s own order says true
///
/// ONE ROW WOULD HAVE MISSED IT: a body reading `b` answers `true` in the first shape and
/// looks correct, which is exactly what the first probe reported before the second
/// ordering was added.
#[test]
fn two_parameters_of_one_carrier_are_refused() {
    let errs = load_errs(&program(
        "ee0ep.two",
        "  sort Bulk\n    \
         operation both(a: MySet[T = String], b: MySet[T = String], x: String) -> Bool =\n      \
         if MySet.contains(a, x) then true else MySet.contains(b, x)\n  end",
    ));
    assert!(
        errs.iter().any(|e| e.contains("already answers")
            && e.contains("second parameter of the same carrier")),
        "two parameters of one carrier synthesize one spec twice; the read cannot say \
         which it means, so this is refused rather than answered from the first — and \
         the message names that shape: {errs:?}"
    );
}

// ── The control this ticket rests on ─────────────────────────────────

/// THE CONTROL, and the measurement the whole design was built on: with the slot
/// DECLARED, the call site already binds it from the ARGUMENT's type at **no bracket**.
/// That is what says the caller holds the evidence and only the channel was missing — so
/// the fix had to synthesize a slot, not recover anything from the value.
///
/// PASSES EITHER WAY BY DESIGN — this is WI-1094's own delivered behaviour (058 §7.1's
/// form), stated here because it is the premise every row above depends on. If it ever
/// fails, the premise is gone and this ticket's design is wrong, not merely broken.
#[test]
fn a_declared_slot_needs_no_bracket() {
    let src = program(
        "ee0ep.control",
        &format!(
            "  sort Bulk\n    \
             sort O = ?\n    \
             requires O: WeakOrd[String]\n    \
             operation has(s: MySet[T = String, O = O], x: String) -> Bool =\n      \
             MySet.contains(s, x)\n  \
             end\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = Bulk.has({}, \"aa\")\n    \
             operation alphabetical(n: Int64) -> Bool = Bulk.has({}, \"aa\")\n  end",
            set_at("ByLength"),
            set_at("Alphabetical"),
        ),
    );
    assert_discriminates(
        &src,
        "ee0ep.control.Driver.byLength",
        "ee0ep.control.Driver.alphabetical",
        "the DECLARED spelling binds its slot from the argument with no bracket — the \
         premise this ticket's channel is built on",
    );
}


// ── What review found, and what now holds it ─────────────────────────

/// **A RIVAL SELECTION FOR THE SAME SPEC BASE MUST NOT CAPTURE THIS DEP** (review
/// finding 2). An `InstanceSelection` is keyed by the SPEC, and `pinned_selection_for`
/// is a `.find` — so a selection the call ALREADY carries for `WeakOrd` wins over one
/// appended after it, whatever element each is about.
///
/// Here `Bulk` declares `requires O: WeakOrd[String]` and `a` writes it, so
/// `selections_from_slot_bindings` derives `WeakOrd -> Alphabetical`. `b` omits its slot
/// at a DIFFERENT element (`Int64`), so the collision screen keeps its synthesized entry —
/// and that entry must be answered by `b`'s own `IntDesc`, not by `a`'s `Alphabetical`.
///
/// BACKED OUT — MEASURED: push the pin onto the call's selection list instead of
/// replacing it for this dep, and this is refused, `"the call selected ... Alphabetical
/// for ... WeakOrd, which provides no instance at these bindings"`. Loud there only by
/// luck: `Alphabetical` provides nothing at `Int64`. A witness providing at BOTH elements
/// would have answered from the wrong parameter in silence, which is why the fix replaces
/// the list rather than ordering it.
#[test]
fn a_rival_selection_for_one_spec_does_not_capture_this_dep() {
    let src = program(
        "ee0ep.rival",
        "  sort Bulk\n    \
         sort O = ?\n    \
         requires O: WeakOrd[String]\n    \
         operation onlyB(a: MySet[T = String, O = O], b: MySet[T = Int64], x: Int64) -> Bool =\n      \
         MySet.contains(b, x)\n  end\n  \
         sort Driver\n    \
         operation hit(n: Int64) -> Bool =\n      \
         Bulk.onlyB(MySet.insert(MySet.empty[T = String, O = Alphabetical](), \"zz\"),\n                \
         MySet.insert(MySet.empty[T = Int64, O = IntDesc](), 7), 7)\n    \
         operation miss(n: Int64) -> Bool =\n      \
         Bulk.onlyB(MySet.insert(MySet.empty[T = String, O = Alphabetical](), \"zz\"),\n                \
         MySet.insert(MySet.empty[T = Int64, O = IntDesc](), 7), 9)\n  end",
    );
    assert!(
        eval_bool(&src, "ee0ep.rival.Driver.hit"),
        "`b`'s own `IntDesc` must answer `b`'s dep — a sibling parameter's written slot \
         selects for a DIFFERENT element and must not be found first"
    );
    assert!(
        !eval_bool(&src, "ee0ep.rival.Driver.miss"),
        "…and the same body must still say no for an element the set does not hold, so \
         the row is not passing on a constant"
    );
}

/// **AN OP THAT WRITES ITS OWN `requires` GETS NO CHANNEL** (review finding 3), and this
/// row exists so that bound is measured rather than assumed.
///
/// The `whole_frame` widening is chosen per CALL SITE, not per dep, so admitting it for
/// an operation whose op chain also holds AUTHOR-written slots would forward those too —
/// the exclusion `wi822_op_scoped_supply_test::the_instance_dictionary_channel_never_
/// forwards_an_op_slot` pins, and whose reason (a host entry fills no op slot) this
/// ticket does not touch. Filtering the chain is unavailable: [`DictChain::names`] is
/// memoized over the full op chain, so a subset would take the wrong names.
///
/// So the gate is `all`, not `any`, and the cost is this: a refusal where the channel
/// could in principle have served. A refusal, not a wrong answer, and the same one the
/// program got before this ticket.
#[test]
fn a_mixed_chain_keeps_the_refusal() {
    let errs = load_errs(&program(
        "ee0ep.mixed",
        "  sort Bulk\n    \
         operation has(s: MySet[T = String], x: String) -> Bool\n      \
         requires WeakOrd[T = Int64]\n      \
         = MySet.contains(s, x)\n  end",
    ));
    // WI-1094's OWN refusal, naming the slot — not the later dictionary-build one. The
    // difference is the point: synthesizing an entry the widening then refuses to expose
    // would leave a slot that exists and cannot be read, and the author would get
    // "ambiguous among providers" from a site that has nothing to do with their mistake.
    // PINS THE CAUSE, not merely a refusal. The first cut accepted either message with
    // an `||`, and review showed that let the WRONG one through: this frame contains a
    // `WeakOrd[T = Int64]` and the needed spec is `WeakOrd[T = String]`, so "something
    // else in this frame already answers it" is simply untrue here. The reason the
    // channel is closed is that `Bulk.has` writes a `requires` of its own.
    assert!(
        errs.iter().any(|e| e.contains("writes its OWN `requires`")
            && e.contains("named requirement slot `O")),
        "an author-written op slot closes the widening, and the message must say THAT \
         rather than blaming a collision that did not happen: {errs:?}"
    );
}

/// **THE HOST ENTRY DOES NOT GET THIS CHANNEL, AND ANSWERS FROM THE DATA INSTEAD** —
/// the boundary of the whole ticket, pinned rather than left to be discovered.
///
/// The channel reads the ARGUMENT'S TYPE. `interp.call` has no types: it is handed
/// `Value`s, and a `Value::Entity` is `{ functor, pos, named }` — it carries its sort and
/// NONE of its type arguments (058 §4.7). Two sets built at rival orderings are the same
/// datum, `node(elem: "zz", rest: nothing())`, so there is nothing to read and the body
/// falls to value-direction, which recovers `T` and cannot recover `O`.
///
/// MEASURED, same operation and same two values, one route each:
///
///   TYPED (an anthill call site)  byLength = true    alphabetical = false
///   HOST  (`interp.call`)         byLength = false   alphabetical = false
///
/// ONE ANSWER TWICE, which this file's own header calls a failure — so it is pinned here
/// as a KNOWN LIMIT rather than described as working.
///
/// **WHAT IS NEW IS THE EXPOSURE, NOT THE HOLE.** `interp.call` fabricates its frame's
/// requirements as self-rooted STAND-INS (WI-868, three measurements at
/// `Interpreter::stand_in_requirement`), and `wi_r10kc_spec_default_body_dictionary_test::
/// the_host_entry_route_answers_by_value_direction` already pins that a named slot reads
/// wrong there. Before this ticket the subject did not LOAD, so no route reached it; now
/// the typed route is right and this one is not.
///
/// **AND IT FALSIFIES A RECORDED PREDICTION, which is why this row exists.**
/// `Interpreter::call_with_requirements` — the entry that DOES take host-supplied
/// dictionaries — counts the PARENT SORT's chain only, and its doc says of the op half:
/// *"Nothing in tree declares an entry op with its own `requires`; if one ever does, its
/// slots stay unfilled here and the body's own read is what says so."* EE0EP is that "if
/// one ever does" — it synthesizes exactly such a slot — and the consolation is untrue:
/// the read does not say so, value-direction rescues it with a wrong answer. Closing that
/// is a change to WI-868's decision and to `call_with_requirements`' host-boundary
/// spelling, which is its own ticket; this row is the marker that it is owed.
#[test]
fn the_host_entry_does_not_receive_the_parameters_dictionary() {
    let src = program(
        "ee0ep.host",
        &format!(
            "  sort Bulk\n    \
             operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n  \
             end\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = Bulk.has({0}, \"aa\")\n    \
             operation mkByLength(n: Int64) -> MySet[T = String, O = ByLength] = {0}\n  end",
            set_at("ByLength"),
        ),
    );
    // The TYPED route is right — this is the control, and it is what says the row below
    // measures the BOUNDARY rather than a broken fixture.
    assert!(
        eval_bool(&src, "ee0ep.host.Driver.byLength"),
        "the typed call site forwards the argument's own comparator"
    );

    // The HOST route, handed the very same value, answers from the data.
    let mut interp = crate::common::interp_for(&src);
    let set = interp
        .call("ee0ep.host.Driver.mkByLength", &[Value::Int(0)])
        .expect("the ByLength set");
    let host = interp.call("ee0ep.host.Bulk.has", &[set, Value::Str("aa".into())]);
    assert!(
        matches!(host, Ok(Value::Bool(false))),
        "PINNED, NOT ENDORSED: `interp.call` supplies no argument type, so the slot is \
         unfilled and value-direction answers `false` where the value's own `ByLength` \
         says `true`. If this row starts failing with `true`, the host boundary has \
         gained the channel and this test should become a driver; if it fails some other \
         way, read the doc above before changing it. Got {host:?}"
    );
}
