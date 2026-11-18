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

use anthill_core::eval::{HostValue, Interpreter, Value};

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
    match interp.call(entry, &anthill_core::eval::HostValue::all(&[Value::Int(0)])).map(|h| h.value) {
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
/// finding 2). An `InstanceSelection` was keyed by the SPEC, and read back by a `.find`
/// — so a selection the call ALREADY carried for `WeakOrd` won over one appended after
/// it, whatever element each was about. (WI-20261013-0K8WD: a selection is kept by the
/// requirement it is for, and a dep the callee declares no slot for is handed its
/// argument's witness and nothing the call selected.)
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

/// **AN OP THAT WRITES ITS OWN `requires` TAKES THE CHANNEL TOO** — and this row is the
/// inverse of what it asserted when EE0EP landed, which is the point of keeping it.
///
/// It was a refusal, for a reason that has since dissolved. While `whole_frame` was
/// CONDITIONAL, admitting the widening for an operation whose chain also held
/// AUTHOR-written slots would have forwarded those into every callee dictionary the body
/// builds — the exclusion `wi822_op_scoped_supply_test` pinned — so the channel was
/// withheld from a mixed chain, and `op_requires_chain_rc` declined to synthesize into
/// one so the two halves agreed.
///
/// WI-20260921-3G1YT deleted the conditional: every call takes the whole frame chain by
/// the general rule now. MEASURED AFTER THAT MERGE, in two steps, because the two halves
/// had to be relaxed together — with only the synthesis re-enabled the program loads and
/// reads `false` at BOTH orderings (the `param_arg_types` gate was still `all`, so the
/// witness was never read and the slot was filled by construction); with the gate at
/// `any` as well it reads `true`/`false`. One answer twice is what says the first step
/// alone is not the fix.
///
/// BACKED OUT, and the TWO HALVES FAIL DIFFERENTLY — which is why the note names each.
/// Restoring the `op_requires_chain_rc` early return refuses (no slot is synthesized, so
/// WI-1094's refusal stands, as when the ticket shipped). Restoring only
/// `op_has_param_derived_slot`'s `all` form does NOT refuse: the slot exists and
/// `param_arg_types` is never populated for it, so the witness is not read and the
/// dictionary is CONSTRUCTED — `false` at both orderings, measured. The dangerous half is
/// the quiet one, and a note that called both "refuses" would have said the opposite.
#[test]
fn a_mixed_chain_takes_the_channel_too() {
    let src = program(
        "ee0ep.mixed",
        &format!(
            "  sort Bulk\n    \
             operation has(s: MySet[T = String], x: String) -> Bool\n      \
             requires WeakOrd[T = Int64]\n      \
             = MySet.contains(s, x)\n  end\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = Bulk.has({}, \"aa\")\n    \
             operation alphabetical(n: Int64) -> Bool = Bulk.has({}, \"aa\")\n  end",
            set_at("ByLength"),
            set_at("Alphabetical"),
        ),
    );
    assert_discriminates(
        &src,
        "ee0ep.mixed.Driver.byLength",
        "ee0ep.mixed.Driver.alphabetical",
        "an author-written op slot beside a param-derived one no longer closes the \
         channel — the unrelated `WeakOrd[T = Int64]` must not stop `s`'s own comparator \
         reaching the body",
    );
}

/// The subject program at both rival orderings, with a `mk*` entry per ordering so the
/// HOST can be handed the very values the typed rows build.
fn host_program(ns: &str) -> String {
    program(
        ns,
        &format!(
            "  sort Bulk\n    \
             operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n  \
             end\n  \
             sort Driver\n    \
             operation byLength(n: Int64) -> Bool = Bulk.has({0}, \"aa\")\n    \
             operation alphabetical(n: Int64) -> Bool = Bulk.has({1}, \"aa\")\n    \
             operation mkByLength(n: Int64) -> MySet[T = String, O = ByLength] = {0}\n    \
             operation mkAlphabetical(n: Int64) -> MySet[T = String, O = Alphabetical] = {1}\n    \
             operation mkEmpty(n: Int64) -> MySet[T = String, O = ByLength] =\n      \
             MySet.empty[T = String, O = ByLength]()\n  end",
            set_at("ByLength"),
            set_at("Alphabetical"),
        ),
    )
}

/// `op(n)` through the typed host entry: the value with the type `op` declares for it.
fn typed_at(interp: &mut Interpreter, op: &str, n: i64) -> HostValue {
    let arg = interp.host_value(Value::Int(n)).expect("a host value at its own type");
    interp
        .call(op, &[arg])
        .unwrap_or_else(|e| panic!("`{op}` must answer: {e:?}"))
}

/// The refusal of a call whose argument's type leaves `s.O` open: no provider is built for
/// a value that names none it was built with.
fn refused_open_slot(got: &Result<Value, String>) -> bool {
    matches!(got, Err(e) if e.contains("parameter `s`") && e.contains("`O` open"))
}

/// `has(set, x)` through the typed host entry, `x` at the type its value reads as.
fn has_typed(interp: &mut Interpreter, op: &str, set: &HostValue, x: Value) -> Result<Value, String> {
    let x = interp.host_value(x).expect("a host value at its own type");
    interp
        .call(op, &[set.clone(), x])
        .map(|h| h.value)
        .map_err(|e| e.to_string())
}

/// **THE HOST ENTRY READS THE WITNESS OFF THE TYPE THE ARGUMENT IS PASSED AT** — proposal
/// 074 §1.4 (WI-20261113-S4D63), replacing WI-20260922-ATFGH's named witness.
///
/// A host holding `s` holds `s.O`: `mkByLength`'s set comes back from `call_typed` with
/// its type `MySet[T = String, O = ByLength]`, and `has(s, "aa")` called with it reads
/// `s.O = ByLength` off that type, as the typed call site reads it off `s`'s.
///
/// WHAT THIS ROW ASSERTED BEFORE. EE0EP pinned a wrong answer here: the host entry's
/// op-half resolution broke the tie among `ByLength`, `Alphabetical` and `String`'s own
/// `WeakOrd` with 058 §3.2's default rung and built `String`'s ordering into the slot. ATFGH
/// refused it and gave the host `call_with_witnesses` to name the provider; 074 §1.4 types
/// the host call instead, and that entry is gone.
///
/// NOW: the host call agrees with the typed route at BOTH rival orderings; handed the bare
/// value, its type dropped, it is refused at the call, the type naming no `O` — as a body is
/// refused over a value whose type names none (`let s = mk()` over an existential return).
///
/// BACKED OUT, MEASURED: with the open-slot refusal of `build_op_scoped_dicts` removed, the
/// bare half answers `false` for the `ByLength` set — §8.7's order builds `String`'s own
/// ordering, the wrong answer this row was made for — and the bare halves of
/// `with_one_provider_the_set_answers_at_its_type_only`,
/// `a_value_built_with_the_default_is_refused_while_rivals_are_loaded`,
/// `specificity_does_not_choose_a_type_carried_slot` and
/// `the_slot_is_owed_whether_or_not_the_body_reads_it` answer too. The typed halves pass
/// either way.
#[test]
fn the_host_entry_reads_the_witness_off_the_type() {
    let src = host_program("ee0ep.host");
    // THE TYPED ROUTE, at both orderings — the answer the host route must agree with.
    assert_discriminates(
        &src,
        "ee0ep.host.Driver.byLength",
        "ee0ep.host.Driver.alphabetical",
        "the typed call site forwards the argument's own comparator",
    );

    let mut interp = crate::common::interp_for(&src);
    let by_length = typed_at(&mut interp, "ee0ep.host.Driver.mkByLength", 0);
    let alphabetical = typed_at(&mut interp, "ee0ep.host.Driver.mkAlphabetical", 0);
    let a = has_typed(&mut interp, "ee0ep.host.Bulk.has", &by_length, Value::Str("aa".into()));
    let b = has_typed(&mut interp, "ee0ep.host.Bulk.has", &alphabetical, Value::Str("aa".into()));
    assert!(
        matches!(a, Ok(Value::Bool(true))) && matches!(b, Ok(Value::Bool(false))),
        "the host route, handed each set at the type its construction gave it, must agree \
         with the typed route: ByLength=true, Alphabetical=false; got {a:?} and {b:?}"
    );

    let plain = interp
        .call("ee0ep.host.Bulk.has", &anthill_core::eval::HostValue::all(&[by_length.value, Value::Str("aa".into())]))
        .map(|h| h.value)
        .map_err(|e| e.to_string());
    assert!(
        refused_open_slot(&plain),
        "handed the set without its type, the call names no `O` and is refused: {plain:?}"
    );
}

/// **WITH ONE PROVIDER, THE SET AT ITS TYPE ANSWERS, AND WITHOUT IT IS REFUSED** — proposal
/// 074 §1.4 (WI-20261113-S4D63). The host holds the set at the type `mk` gives it, `O =
/// Int64`, and the call reads `s.O` off it. Handed bare, its type names no `O`, and no
/// provider is chosen for it — not even the one there is, as a body's call over a value
/// whose type names none is refused (`let s = mk()` over an existential return).
///
/// WHAT THIS ROW ASSERTED BEFORE (WI-20260922-ATFGH): the bare set answered, the one provider
/// taken as the one its construction chose.
///
/// At `T = Int64` with no rivals loaded, `WeakOrd[T = Int64]` has one provider, so the
/// set `{7}` answers `has(7)` and `has(9)` from plain `interp.call` — both, so the row is
/// not passing on a constant.
///
/// PASSES EITHER WAY with respect to the original defect (a default rung has nothing to
/// choose among one). It is the control for the DESIGN, raised by /code-review: the
/// first cut of this ticket refused EVERY type-carried slot on a value-only route, and
/// this row failed there, refused at the read — a regression on every route that used to
/// answer correctly when the provider is unique.
#[test]
fn with_one_provider_the_set_answers_at_its_type_only() {
    // NO `RIVALS`: their `IntDesc` is a second `WeakOrd[Int64]`. What is left is
    // `Int64`'s own ordering, the one provider — R10KC's single-provider control, and
    // `Int64` rather than `String` for the reason that control's doc measured.
    let src = format!(
        "\nnamespace ee0ep.hostone\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool}}\n\
         {CARRIER}  sort Bulk\n    \
         operation has(s: MySet[T = Int64], x: Int64) -> Bool = MySet.contains(s, x)\n  \
         end\n  \
         sort Driver\n    \
         operation mk(n: Int64) -> MySet[T = Int64, O = Int64] =\n      \
         MySet.insert(MySet.empty[T = Int64, O = Int64](), 7)\n  end\nend\n"
    );
    let mut interp = crate::common::interp_for(&src);
    let set = typed_at(&mut interp, "ee0ep.hostone.Driver.mk", 0);
    let hit = interp.call("ee0ep.hostone.Bulk.has", &[set.clone(), Value::Int(7).into()]).map(|h| h.value);
    let miss = interp.call("ee0ep.hostone.Bulk.has", &[set.clone(), Value::Int(9).into()]).map(|h| h.value);
    assert!(
        matches!(hit, Ok(Value::Bool(true))) && matches!(miss, Ok(Value::Bool(false))),
        "the set at its type: {{7}} holds 7 and not 9; got {hit:?} and {miss:?}"
    );
    let bare = interp
        .call("ee0ep.hostone.Bulk.has", &anthill_core::eval::HostValue::all(&[set.value, Value::Int(7)]))
        .map(|h| h.value)
        .map_err(|e| e.to_string());
    assert!(refused_open_slot(&bare), "the bare set names no `O`: {bare:?}");
}

/// **SPECIFICITY DOES NOT CHOOSE EITHER** — a value built with a GENERIC witness is not
/// handed a more specific rival's dictionary. Found by /code-review on the second cut,
/// which withheld only 058 §3.2's DEFAULT: `pick_most_specific` still ran first.
///
/// Three providers of `WeakOrd[T = Pair[A = String, B = String]]`: the stdlib's `Pair`
/// (lexicographic, generic head), `Flat` (a witness generic over any `Pair` of ordered
/// components, calling every pair equal) and `PairNe` (a witness at exactly
/// `Pair[String, String]`, calling no pair equal — the most specific head).
///
/// `Flat`'s `:- WeakOrd[A], WeakOrd[B]` is WI-20260925-4ZZKZ's: `WeakOrd` requires `Eq` and
/// `PartialOrd` at the pair, which hold only where the components have them, so the
/// unconditioned provision claimed an ordering at pairs with no equality. It loaded through
/// the load check's base-level fallback, which that ticket removed. The set `{pair("a", "z")}` is built at
/// `O = Flat`, so it holds `pair("a", "b")`; `PairNe` would say it does not.
///
/// BACKED OUT — MEASURED: resolve a type-carried slot with `DefaultRung::Withhold`
/// instead of `Unranked` and plain `interp.call` answers `Ok(false)` — `PairNe`'s answer
/// for a `Flat` set, in silence.
#[test]
fn specificity_does_not_choose_a_type_carried_slot() {
    let src = format!(
        "\nnamespace ee0ep.hostpair\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool, Pair}}\n  \
         import anthill.prelude.Pair.{{pair}}\n  \
         sort Flat\n    \
         sort A = ?\n    \
         sort B = ?\n    \
         provides WeakOrd[T = Pair[A = A, B = B]] :- WeakOrd[A], WeakOrd[B]\n    \
         operation compare(a: Pair[A = A, B = B], b: Pair[A = A, B = B]) -> Int64 = 0\n  \
         end\n  \
         sort PairNe\n    \
         provides WeakOrd[T = Pair[A = String, B = String]]\n    \
         operation compare(a: Pair[A = String, B = String], b: Pair[A = String, B = String]) \
         -> Int64 = 1\n  \
         end\n\
         {CARRIER}  sort Bulk\n    \
         operation has(s: MySet[T = Pair[A = String, B = String]], \
         x: Pair[A = String, B = String]) -> Bool = MySet.contains(s, x)\n  \
         end\n  \
         sort Driver\n    \
         operation typed(n: Int64) -> Bool =\n      \
         Bulk.has(MySet.insert(MySet.empty[T = Pair[A = String, B = String], O = Flat](), \
         pair(\"a\", \"z\")), pair(\"a\", \"b\"))\n    \
         operation mk(n: Int64) -> MySet[T = Pair[A = String, B = String], O = Flat] =\n      \
         MySet.insert(MySet.empty[T = Pair[A = String, B = String], O = Flat](), \
         pair(\"a\", \"z\"))\n    \
         operation probe(n: Int64) -> Pair[A = String, B = String] = pair(\"a\", \"b\")\n  \
         end\nend\n"
    );
    // PINNED TO ONE LOAD, BY NAME (WI-20261010-9BKZ4). `PairNe` provides the stdlib's
    // `WeakOrd` at the stdlib's `Pair[A = String, B = String]`, strictly more specific
    // than `Pair`'s own — so it changes who answers an unselected dispatch there, for
    // the stdlib's bodies as for these. Every element being the stdlib's, the stdlib's
    // load is the one this fixture has to be in; loaded after it sealed, it is a load
    // error (`ChangesSealedCode`). That most specific rival is the fixture's point.
    let one_load = || {
        let (kb, _) = crate::common::expect_loaded(crate::common::recipe_load(
            &[&src],
            None,
            anthill_core::kb::load::LoadOptions::default(),
            crate::common::LoadRecipe::OneShot,
            |_| {},
        ));
        let mut interp = Interpreter::new(kb);
        anthill_core::eval::builtins::register_standard_builtins(&mut interp);
        interp
    };
    // The typed route reads `Flat` out of the argument's type — the answer to agree with.
    assert!(
        matches!(
            one_load().call("ee0ep.hostpair.Driver.typed", &anthill_core::eval::HostValue::all(&[Value::Int(0)])).map(|h| h.value),
            Ok(Value::Bool(true))
        ),
        "Flat calls every pair equal"
    );
    let mut interp = one_load();
    let set = interp
        .call("ee0ep.hostpair.Driver.mk", &anthill_core::eval::HostValue::all(&[Value::Int(0)])).map(|h| h.value)
        .expect("the Flat set");
    let probe = interp
        .call("ee0ep.hostpair.Driver.probe", &anthill_core::eval::HostValue::all(&[Value::Int(0)])).map(|h| h.value)
        .expect("pair(a, b)");
    let args = [set, probe];
    let plain = interp
        .call("ee0ep.hostpair.Bulk.has", &anthill_core::eval::HostValue::all(&args))
        .map(|h| h.value)
        .map_err(|e| e.to_string());
    assert!(
        refused_open_slot(&plain),
        "`PairNe` is more specific than `Flat`, and that must not choose for a value built \
         with `Flat`: {plain:?}"
    );
    // Proposal 074 §1.4: the set at the type `mk` gives it, `O = Flat`, read off that type.
    let typed = typed_at(&mut interp, "ee0ep.hostpair.Driver.mk", 0);
    let probe = interp.host_value(args[1].clone()).expect("a host value at its own type");
    let named = interp
        .call("ee0ep.hostpair.Bulk.has", &[typed, probe])
        .map(|h| h.value);
    assert!(
        matches!(named, Ok(Value::Bool(true))),
        "the set at its type, `O = Flat`, answers as the typed route does: {named:?}"
    );
}

/// **A VALUE BUILT WITH THE DEFAULT IS REFUSED TOO, WHILE RIVALS ARE LOADED**. Raised by /code-review as a loss, and kept as the
/// decision: before this ticket the default rung filled the slot with `String`'s own
/// ordering, which is right for THIS value and wrong for a `ByLength` one, and the value
/// cannot say which it is. Refusing both is the only reading that is never wrong.
///
/// `MySet.empty[T = String]()` writes no `O`, so the call site's inference (WI-1094)
/// binds the default, `String`'s own `WeakOrd`: `{"zz"}.contains("aa")` is `false`.
///
/// PASSES ONLY WITH THIS TICKET: before it, plain `interp.call` answered `false` here —
/// the right answer, by the same default that answered wrong for `ByLength`.
#[test]
fn a_value_built_with_the_default_is_refused_while_rivals_are_loaded() {
    let src = program(
        "ee0ep.hostdefault",
        "  sort Bulk\n    \
         operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n  \
         end\n  \
         sort Driver\n    \
         operation mk(n: Int64) -> MySet[T = String] =\n      \
         MySet.insert(MySet.empty[T = String](), \"zz\")\n  end",
    );
    let mut interp = crate::common::interp_for(&src);
    let set = interp
        .call("ee0ep.hostdefault.Driver.mk", &anthill_core::eval::HostValue::all(&[Value::Int(0)])).map(|h| h.value)
        .expect("the default-ordered set");
    let args = [set, Value::Str("aa".into())];
    let plain = interp
        .call("ee0ep.hostdefault.Bulk.has", &anthill_core::eval::HostValue::all(&args))
        .map(|h| h.value)
        .map_err(|e| e.to_string());
    assert!(
        refused_open_slot(&plain),
        "with rivals loaded the value cannot say it was built with the default: {plain:?}"
    );
    // Proposal 074 §1.4: `mk` declares `MySet[T = String]`, its `O` unwritten — an
    // existential return — so the set comes back at a type that names no `O`, and the typed
    // host call is refused naming `s.O`, as the typed route refuses `has(mk(0), …)`
    // (`an_existential_return_is_still_refused`).
    let typed = typed_at(&mut interp, "ee0ep.hostdefault.Driver.mk", 0);
    let named = has_typed(&mut interp, "ee0ep.hostdefault.Bulk.has", &typed, Value::Str("aa".into()));
    assert!(refused_open_slot(&named), "a type that names no `O` reads none: {named:?}");
}

/// **THE SLOT IS OWED WHETHER OR NOT THE BODY READS IT** — proposal 074 §1.4
/// (WI-20261113-S4D63). `has` over an EMPTY set returns at `case nothing()` without
/// comparing; at its type (`O = ByLength`) it answers `false`, and handed bare it is refused
/// at the call, as a body's call over a value whose type names no `O` is: the requirement is
/// the caller's because it is declared.
///
/// WHAT THIS ROW ASSERTED BEFORE (WI-20260922-ATFGH): the bare set answered, the absence a
/// marker refused only at a read the body never made.
#[test]
fn the_slot_is_owed_whether_or_not_the_body_reads_it() {
    let src = host_program("ee0ep.hostempty");
    let mut interp = crate::common::interp_for(&src);
    let empty = typed_at(&mut interp, "ee0ep.hostempty.Driver.mkEmpty", 0);
    let got = has_typed(&mut interp, "ee0ep.hostempty.Bulk.has", &empty, Value::Str("aa".into()));
    assert!(matches!(got, Ok(Value::Bool(false))), "the empty set at its type: {got:?}");
    let bare = interp
        .call("ee0ep.hostempty.Bulk.has", &anthill_core::eval::HostValue::all(&[empty.value, Value::Str("aa".into())]))
        .map(|h| h.value)
        .map_err(|e| e.to_string());
    assert!(refused_open_slot(&bare), "the bare empty set names no `O`: {bare:?}");
}

/// **A VALUE HANDED OVER AT ANOTHER TYPE IS REFUSED AT THE ENTRY** — proposal 074 §1.4. A
/// host hands the `ByLength` set over at the type of a set of `Int64`s ordered by `IntDesc`,
/// and the call is typed as a body's is: `has` takes a `MySet[T = String]`, and is refused,
/// naming both types.
#[test]
fn a_type_whose_witness_does_not_answer_the_slot_is_refused() {
    let src = program(
        "ee0ep.hostbad",
        &format!(
            "  sort Bulk\n    \
             operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n  \
             end\n  \
             sort Driver\n    \
             operation mkByLength(n: Int64) -> MySet[T = String, O = ByLength] = {}\n    \
             operation mkInts(n: Int64) -> MySet[T = Int64, O = IntDesc] =\n      \
             MySet.insert(MySet.empty[T = Int64, O = IntDesc](), 7)\n  end",
            set_at("ByLength"),
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let strings = typed_at(&mut interp, "ee0ep.hostbad.Driver.mkByLength", 0);
    let ints = typed_at(&mut interp, "ee0ep.hostbad.Driver.mkInts", 0);
    let mislabelled = HostValue::typed(strings.value, ints.ty().expect("a result's type").clone());
    let got = has_typed(&mut interp, "ee0ep.hostbad.Bulk.has", &mislabelled, Value::Str("aa".into()));
    assert!(
        matches!(&got, Err(e) if e.contains("expected MySet[T = String]") && e.contains("IntDesc")),
        "the type the set is handed over at is no `MySet[T = String]`: {got:?}"
    );
}
