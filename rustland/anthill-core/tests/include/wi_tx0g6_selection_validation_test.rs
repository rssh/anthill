//! WI-20260911-TX0G6 — A WRITTEN SELECTION IS VALIDATED BY ONE OWNER IN BOTH BRACKET
//! SPELLINGS, AND A TYPE IS VALIDATED FOR CHECK 1 ONLY.
//!
//! Proposal 035 lists `SortedSet.empty[T = String, O = W]()` and
//! `SortedSet[T = String, O = W].empty()` as two spellings of one call. 058 §3.5 gives a
//! written selection three checks: the value names a sort, the sort provides the spec
//! (check 1), and it is not a CONCRETE provider (check 3). The callee spelling ran all
//! three at its own leg. The receiver spelling ran none there. WI-20260911-6B67S moved
//! the first two onto the σ-read producer, which both spellings reach. Check 3 was left
//! open, and two verdicts disagreed:
//!
//! | binding | callee `…empty[O = W]()` | receiver `…[O = W].empty()` |
//! |---|---|---|
//! | `O = ConcOrd` (a concrete witness) | refused | LOADED |
//! | `O = Pair` (a concrete self-provider) | refused | LOADED |
//! | `O = OE`, a forward inside `sort R { requires OE: … }` | REFUSED ("R.OE does not provide WeakOrd") | loaded, ran the caller's order |
//! | `O = P`, a PLAIN parameter of `sort R2 { sort P = ?; requires OE: … }` | refused ("R2.P does not provide WeakOrd") | LOADED, and ordered a `ByLength`-typed set by `OE`'s `RevLen` |
//!
//! MEASURED before any change. Both spellings now call `validate_written_selection`,
//! so they agree by construction: refused with the same bytes in the first, second and
//! fourth rows, and forwarded in the third.
//!
//! THE DECISION, ONE CHECK AT A TIME, because the ticket requires it:
//!  * CHECK 1 (provides the spec) runs on EVERY channel, at the σ-read producer, where
//!    6B67S put it. A type-carried selection that provides nothing is as wrong as a
//!    written one.
//!  * CHECK 3 (not a concrete provider) runs on the two WRITTEN channels only. It is a
//!    rule about a SPELLING, and a TYPE legitimately carries a concrete witness: WI-1094's
//!    inference WRITES one (`SortedSet.empty[T = Pair[…]]()` types as `O = Pair`), and
//!    every later call reads it back through the producer. Check 3 there would refuse
//!    the compiler's own inference. [`a_type_may_carry_a_concrete_witness_and_it_is_honoured`]
//!    drives that boundary, and the census below counts what it protects.
//!  * A VALUE NAMING ONE OF THE ENCLOSING DECLARATION'S OWN SLOTS forwards, in both
//!    spellings. The binding is also a type argument, so the producer reads the same
//!    variable back, and the frame holds a dictionary under exactly that name. A PLAIN
//!    parameter does not forward. The frame answers a forward by the slot's GOAL, which
//!    is keyed by spec, so `[O = P]` got `OE`'s dictionary: the fourth row. An
//!    ANONYMOUS-slot key binds no parameter at all, so it keeps check 1's refusal even
//!    for a slot-naming value. Forwarding there would drop the written text.
//!
//!    THE SLOT TEST IS CONSERVATIVE, and its cost is measured and pinned. A plain
//!    parameter that a REQUIREMENT of the declaration mentions is answered soundly out of
//!    that requirement, and this gate refuses it in brackets too. The receiver spelling
//!    ran that program before this ticket.
//!    [`a_plain_parameter_tied_to_a_requirement_is_refused_in_brackets_too`] records it,
//!    and WI-20260923-WN9P8 is the criterion that separates the two shapes, on the type
//!    channel as well as here.
//!
//! **BACK-OUT, MEASURED ONE MECHANISM AT A TIME** (rows are this file's):
//!
//! | backed out | fails |
//! |---|---|
//! | (R) the receiver leg's `validate_written_selection` call | [`every_refusal_reads_the_same_in_both_spellings`], [`the_concrete_refusal_names_no_bracket_the_author_did_not_write`], [`a_plain_parameter_is_refused_in_both_spellings`], [`a_plain_parameter_tied_to_a_requirement_is_refused_in_brackets_too`] |
//! | (F) the callee leg's forward (`binds_a_parameter = false` for every key) | [`an_abstract_slot_binding_forwards_in_both_spellings`] |
//! | (N) the forward widened from a slot to ANY abstract value (`view_is_abstract_type_param`) | [`a_plain_parameter_is_refused_in_both_spellings`], [`a_plain_parameter_tied_to_a_requirement_is_refused_in_brackets_too`] |
//! | (W) the channel-neutral wording of `ValueDirectedSelection` | [`the_concrete_refusal_names_no_bracket_the_author_did_not_write`] |
//! | (F) widened to every KEY (`binds_a_parameter = true`, rung-2 keys included) | [`an_abstract_value_at_a_spec_key_is_still_refused`] |
//! | (P3) check 3 MOVED onto the σ-read producer, over the whole `wi_tests` binary | [`a_type_may_carry_a_concrete_witness_and_it_is_honoured`], plus three pre-existing tests (the census) |
//!
//! **PASS EITHER WAY, BY DESIGN:**
//!  * the `NotOrd`, `(Int64, Int64)` and `ByLength` rows of
//!    [`every_refusal_reads_the_same_in_both_spellings`] agreed before this ticket, because
//!    6B67S's producer checks fire in both spellings. They stay in the table as its
//!    control, and they also pin the ORDER of checks at the receiver leg: `NotOrd` HAS a
//!    constructor, so running check 3 before check 1 there would call it "a CONCRETE
//!    provider" of a spec it does not provide.
//!  * [`an_abstract_value_at_a_spec_key_is_still_refused`] is unchanged by this ticket.
//!    It is the control on the forward's SCOPE, as the table's last row shows.
//!  * [`a_type_may_carry_a_concrete_witness_and_it_is_honoured`] is the boundary, not a
//!    change. It fails if check 3 is ever moved onto the σ-read producer. The census
//!    below measured exactly that.
//!
//! **CENSUS**, by counters at the three sites (removed) over `anthill load` of each
//! corpus and over the whole workspace suite. The full table is in the ticket's delivery
//! note. In short:
//!  * THE CORPORA: zero hits at every site. `stdlib/`, `examples/` and the loaded
//!    `anthill-todo` code write no form-(3) call and bind no named slot in any bracket.
//!    `SortedSet`'s `O` is their only named slot, bound only to `O` itself inside
//!    `sortedset.anthill`, which forwards. No corpus verdict flips in either direction.
//!  * BRACKET-CARRIED, pre-existing tests: 4 receiver slot bindings, all in 6B67S's
//!    file, and 254 callee named-slot bindings. None newly refused, none newly
//!    forwarded. The one pre-existing flip is 6B67S's pinned row, written to fail on
//!    closure.
//!  * ARGUMENT/TYPE-CARRIED: unchanged by construction. 864 producer reads of a decided
//!    witness, 24 of them CONCRETE, in 3 tests. Moving check 3 onto the producer fails
//!    exactly those 3 (wi858's and wi869's inferred `O = Pair`, wi_r10kc's `MySet`) and
//!    [`a_type_may_carry_a_concrete_witness_and_it_is_honoured`].
//!
//! REFERENCE: `validate_written_selection`, `seed_op_type_args`,
//! `seed_receiver_type_args`, `selections_from_slot_bindings`,
//! `validate_instance_selection` (typing.rs); `wi_6b67s_receiver_bound_requirement_test`
//! (check 1 at the producer), `wi_rs2g4_receiver_bracket_binds_sort_params_test` (the
//! receiver bracket), `wi870_bracket_value_slot_test` (check 3 is not a sub-slot's).

use anthill_core::eval::Value;

/// `NotOrd` provides nothing and HAS a constructor, which is what makes it the ORDER
/// control. `ByLength` provides `WeakOrd[T = String]` and has none. `ConcOrd` provides
/// the same with a constructor, which is check 3's shape, and orders by REVERSE length
/// so that a run shows WHICH witness answered. `RevLen` is `ConcOrd`'s order without the
/// constructor: a second NON-concrete witness, so a forward can be driven at two
/// orderings. `Show.join` renders a list so one string shows the whole order.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String, Bool, Ord, WeakOrd, List, SortedSet, Pair, Function}
  import anthill.prelude.String.{length}
  import anthill.prelude.Numeric.{sub}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Pair.{pair}

  sort NotOrd
    entity notOrd
  end

  sort ByLength
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  sort RevLen
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(b), length(a))
  end

  sort ConcOrd
    entity conc
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(b), length(a))
  end

  sort Show
    operation join(l: List[T = String]) -> String =
      match l
        case nil() -> ""
        case cons(h, t) -> String.concat(h, String.concat(",", join(t)))
  end
"#;

fn program(body: &str) -> String {
    format!("\nnamespace probe.tx0g6\n{DECLS}\n{body}\nend\n")
}

fn load_errors(body: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(&program(body)) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

/// The ONE error `body` must produce, with its `<line>:<col>: ` prefix stripped so two
/// spellings written at different columns compare by MESSAGE.
///
/// THE PREFIX IS CHECKED BY SHAPE and its absence PANICS, for the reason
/// `wi_6b67s_receiver_bound_requirement_test`'s twin gives: a spanless `TypeMismatch`
/// renders no prefix, and a bare `split_once(": ")` would then cut off the message HEAD
/// and still compare equal in both spellings.
fn sole_message(body: &str) -> String {
    let errs = load_errors(body);
    assert_eq!(
        errs.len(),
        1,
        "expected exactly one error for:\n{body}\ngot {errs:#?}"
    );
    let (prefix, msg) = errs[0]
        .split_once(": ")
        .unwrap_or_else(|| panic!("no `line:col: ` prefix to strip in: {}", errs[0]));
    let is_line_col = prefix.split_once(':').is_some_and(|(l, c)| {
        [l, c]
            .iter()
            .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit()))
    });
    assert!(
        is_line_col,
        "expected a `line:col` prefix, got {prefix:?} in: {}",
        errs[0]
    );
    msg.to_string()
}

/// `interp.call(entry)` must answer a string.
fn eval_str(src: &str, entry: &str, what: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Str(s)) => s.to_string(),
        other => panic!("{what}: expected a string from {entry}; got {other:?}"),
    }
}

/// Insert three strings whose three orders all differ, and render the set's order. By
/// alphabet `a,bbb,cc`; by length `a,cc,bbb`; by reverse length `bbb,cc,a`.
fn render_three(set: &str) -> String {
    render_three_via("SortedSet.insert", set)
}

/// [`render_three`] with the three inserts made through `insert` instead of
/// `SortedSet.insert`.
fn render_three_via(insert: &str, set: &str) -> String {
    format!(
        "Show.join(SortedSet.toList({insert}({insert}({insert}({set}, \"a\"), \"bbb\"), \
         \"cc\")))"
    )
}

/// THE TICKET'S HEADLINE, EVERY REFUSAL AT ONCE. For each slot value, the callee spelling
/// and the receiver spelling must refuse, and with the SAME BYTES — the comparison
/// RS2G4's `the_receiver_spelling_reads_as_the_callee_spelling` makes.
///
/// The `ConcOrd` and `Pair` rows are the ones this ticket changes: before it the receiver
/// spelling loaded, so `sole_message` panics on it (R). The other three agreed already
/// and are the control (see the header). They include both halves of the order control:
/// `NotOrd` must be told it provides nothing, not that it is a concrete provider.
#[test]
fn every_refusal_reads_the_same_in_both_spellings() {
    for (elem, o, fault) in [
        // Check 3, a concrete witness that is not its own carrier.
        (
            "String",
            "ConcOrd",
            "probe.tx0g6.ConcOrd is a CONCRETE provider of anthill.prelude.WeakOrd",
        ),
        // Check 3, a concrete SELF-provider: the prelude's canonical pair order.
        (
            "Pair[Int64, Int64]",
            "Pair",
            "anthill.prelude.Pair is a CONCRETE provider of anthill.prelude.WeakOrd",
        ),
        // Check 1: provides nothing. HAS a constructor, so this is the order control.
        (
            "Int64",
            "NotOrd",
            "probe.tx0g6.NotOrd does not provide anthill.prelude.WeakOrd",
        ),
        // No sort head at all.
        ("Int64", "(Int64, Int64)", "must name a WITNESS SORT"),
        // Provides the spec, at OTHER bindings: `check_selection_bindings`' wording.
        (
            "Int64",
            "ByLength",
            "provides anthill.prelude.WeakOrd, but not at the bindings",
        ),
    ] {
        let callee = sole_message(&format!(
            "  operation w() -> SortedSet[T = {elem}] = SortedSet.empty[T = {elem}, O = {o}]()"
        ));
        let recv = sole_message(&format!(
            "  operation w() -> SortedSet[T = {elem}] = SortedSet[T = {elem}, O = {o}].empty()"
        ));
        assert!(
            callee.contains(fault),
            "`O = {o}`: the callee spelling: {callee}"
        );
        assert_eq!(
            recv, callee,
            "`O = {o}`: 035's two spellings are one call, so one selection must produce \
             one message"
        );
    }
}

/// Check 3's message used to read "an explicit `[WeakOrd = ConcOrd]` cannot change it".
/// That names a bracket neither spelling of a NAMED slot writes: the callee writes
/// `[O = ConcOrd]` and the receiver writes `SortedSet[…, O = ConcOrd]`. The receiver
/// spelling reaches this refusal only since this ticket, which is what made the wording
/// false for a program with no call bracket at all. It is now the channel-neutral
/// "selection of `WeakOrd = ConcOrd`", the convention 6B67S set for check 1's refusal.
/// (W), and (R) reddens it too, since without (R) the receiver spelling is not refused.
///
/// It also states the RULE now, not "cannot change it". For this very program that claim
/// is false: `ConcOrd`'s values are not the arguments, and a type naming `O = ConcOrd` is
/// honoured (`a_type_may_carry_a_concrete_witness_and_it_is_honoured`). The rule is kept
/// as a property of the named sort (decided 2026-09-23), so the message gives its reason
/// conditionally.
/// Its last assertion pins the field name, `selection`, which the sibling refusals use.
#[test]
fn the_concrete_refusal_names_no_bracket_the_author_did_not_write() {
    let recv = sole_message(
        "  operation w() -> SortedSet[T = String] = SortedSet[T = String, O = ConcOrd].empty()",
    );
    assert!(
        !recv.contains("`[WeakOrd = ConcOrd]`"),
        "the author wrote no `[WeakOrd = …]` bracket; got: {recv}"
    );
    assert!(
        recv.contains(
            "an explicit selection of `WeakOrd = ConcOrd` is refused rather than preferred"
        ),
        "got: {recv}"
    );
    // …and it names the FIELD the other selection refusals name, not `type_arg`.
    assert!(
        recv.starts_with("type mismatch in anthill.prelude.SortedSet.empty.selection:"),
        "got: {recv}"
    );
}

/// AN ABSTRACT BINDING OF A NAMED SLOT FORWARDS, IN BOTH SPELLINGS, driven to a value
/// at TWO orderings. `R` declares its own ordering slot `OE`, and `mk` builds a set
/// ordered by it. That is §7.1's form: whatever order `R`'s caller chose.
///
/// Before this ticket the callee spelling was REFUSED — "probe.tx0g6.R.OE does not
/// provide anthill.prelude.WeakOrd". Check 1 read the binder `OE` as a witness, while the
/// receiver spelling, the argument's type and a nested bracket slot all forwarded it (F).
/// Two orderings per spelling, because one answer could come from a search that happened
/// to agree with the caller. `RevLen` is not concrete, so neither driver's own bracket
/// meets check 3.
#[test]
fn an_abstract_slot_binding_forwards_in_both_spellings() {
    for (spelling, construct) in [
        ("callee", "SortedSet.empty[T = E, O = OE]()"),
        ("receiver", "SortedSet[T = E, O = OE].empty()"),
    ] {
        let src = program(&format!(
            "  sort R\n    \
               sort E = ?\n    \
               requires OE: WeakOrd[E]\n    \
               operation mk() -> SortedSet[T = E, O = OE] = {construct}\n  \
             end\n  \
             operation byLength(n: Int64) -> String =\n    {}\n  \
             operation revLen(n: Int64) -> String =\n    {}",
            render_three("R.mk[E = String, OE = ByLength]()"),
            render_three("R.mk[E = String, OE = RevLen]()"),
        ));
        assert_eq!(
            eval_str(&src, "probe.tx0g6.byLength", spelling),
            "a,cc,bbb,",
            "the {spelling} spelling must forward the caller's `ByLength`"
        );
        assert_eq!(
            eval_str(&src, "probe.tx0g6.revLen", spelling),
            "bbb,cc,a,",
            "the {spelling} spelling must forward the caller's `RevLen`"
        );
    }
}

/// ONLY A SLOT FORWARDS, and a PLAIN parameter is refused in both spellings. A forward
/// hands the callee whatever dictionary the frame holds for the slot's GOAL, and that
/// goal is keyed by spec and bindings, not by the binder the type names. `R2` declares a
/// plain `P` beside its slot `OE`, so `[O = P]` could only ever be answered by `OE`'s
/// dictionary.
///
/// MEASURED before this ticket: the receiver spelling LOADED, and at
/// `R2.mk[E = String, P = ByLength, OE = RevLen]` a set whose TYPE said `O = ByLength`
/// ordered by `RevLen` (`bbb,cc,a`). That is a silent wrong answer. The callee spelling
/// refused, by check 1 on `P`. Both now refuse, with the same bytes (N).
///
/// NOT CLOSED ON THE TYPE CHANNEL. A parameter typed `SortedSet[T = E, O = P]` still
/// forwards through WI-1094's inference, and was measured doing the same thing. That is
/// WI-20260923-WN9P8, and the row below records what this gate costs meanwhile.
#[test]
fn a_plain_parameter_is_refused_in_both_spellings() {
    let r2 = |construct: &str| {
        format!(
            "  sort R2\n    \
               sort E = ?\n    \
               sort P = ?\n    \
               requires OE: WeakOrd[E]\n    \
               operation mk() -> SortedSet[T = E, O = P] = {construct}\n  \
             end"
        )
    };
    let callee = sole_message(&r2("SortedSet.empty[T = E, O = P]()"));
    let recv = sole_message(&r2("SortedSet[T = E, O = P].empty()"));
    assert!(
        callee.contains("probe.tx0g6.R2.P does not provide anthill.prelude.WeakOrd"),
        "a plain parameter names no dictionary, so it is not a forward; got: {callee}"
    );
    assert_eq!(recv, callee, "one rule, two spellings");
}

/// THE COST OF THE SLOT TEST, PINNED SO IT IS NOT REDISCOVERED AS A SURPRISE. A plain
/// parameter can be tied to a frame dictionary without being a slot: `PolyD` requires the
/// COLLECTION INSTANCE at `O = OE`, and a forward of `OE` is answered soundly out of that
/// instance (Strategy 2b, `wi456_no_scope_route_test`). The bare spelling runs, driven at
/// two orderings below. The two bracket spellings are refused, because the gate asks "is
/// `OE` a slot?" and cannot tell this shape from the wrong-answer one in the row above.
///
/// MEASURED: before this ticket the RECEIVER spelling ran this program correctly, and the
/// callee spelling refused it, by the same check 1 that refuses it now. So this ticket
/// traded one correct receiver program (none in the suite or the corpora) for closing a
/// silent wrong answer. Telling the two apart is WI-20260923-WN9P8.
///
/// THE ASSERTION IS THE CURRENT BEHAVIOUR: it fails the day WN9P8 lets the brackets
/// forward this shape, which makes that a recorded decision rather than a drift.
#[test]
fn a_plain_parameter_tied_to_a_requirement_is_refused_in_brackets_too() {
    let body = |call: &str| {
        format!(
            "  import anthill.prelude.PersistentCollection\n  \
             sort PolyD\n    \
               sort E = ?\n    \
               sort OE = ?\n    \
               requires PersistentCollection[C = SortedSet[T = E, O = OE], Element = E]\n    \
               operation insertD(s: SortedSet[T = E, O = OE], x: E) \
             -> SortedSet[T = E, O = OE] =\n      \
               {call}\n  \
             end\n  \
             operation byLength(n: Int64) -> String =\n    {}\n  \
             operation revLen(n: Int64) -> String =\n    {}",
            render_three_via(
                "PolyD.insertD",
                "SortedSet.empty[T = String, O = ByLength]()"
            ),
            render_three_via("PolyD.insertD", "SortedSet.empty[T = String, O = RevLen]()"),
        )
    };
    let bare = program(&body("SortedSet.insert(s, x)"));
    assert_eq!(eval_str(&bare, "probe.tx0g6.byLength", "bare"), "a,cc,bbb,");
    assert_eq!(eval_str(&bare, "probe.tx0g6.revLen", "bare"), "bbb,cc,a,");

    let callee = sole_message(&body("SortedSet.insert[T = E, O = OE](s, x)"));
    let recv = sole_message(&body("SortedSet[T = E, O = OE].insert(s, x)"));
    assert!(
        callee.contains("probe.tx0g6.PolyD.OE does not provide anthill.prelude.WeakOrd"),
        "got: {callee}"
    );
    assert_eq!(recv, callee, "one rule, two spellings");
}

/// THE FORWARD NEEDS A NAMED-SLOT KEY, and this is the row that keeps it scoped. A key
/// reached by a spec SHORT NAME (rung 2) selects for an ANONYMOUS slot and binds no
/// parameter. So even a value that names the enclosing sort's own slot, `[WeakOrd = OE]`,
/// has nothing to forward through. Treating it as a forward would drop the written `OE`
/// and let `Fwd`'s frame answer the goal with whatever `WeakOrd[E]` it holds, which is
/// `OE` here only because `Fwd` declares one. So it keeps check 1's refusal.
///
/// PASSES EITHER WAY: unchanged by this ticket. It is the control on the forward's KEY
/// scope, and it LOADS if `validate_written_selection` is handed
/// `binds_a_parameter = true` for every target instead of for a named one. The value is
/// a slot binder on purpose: a plain parameter would be refused by the value-side
/// narrowing too, and the row would then measure nothing about the key.
#[test]
fn an_abstract_value_at_a_spec_key_is_still_refused() {
    let msg = sole_message(
        "  sort Holder\n    \
           sort HT = ?\n    \
           requires WeakOrd[T = HT]\n    \
           operation probe(a: HT, b: HT) -> Int64 = WeakOrd.compare(a, b)\n  \
         end\n  \
         sort Fwd\n    \
           sort E = ?\n    \
           requires OE: WeakOrd[T = E]\n    \
           operation go(a: E, b: E) -> Int64 = Holder.probe[WeakOrd = OE](a, b)\n  \
         end",
    );
    assert!(
        msg.contains("probe.tx0g6.Fwd.OE does not provide anthill.prelude.WeakOrd"),
        "a SPEC key binds no parameter, so even a slot-naming value has nothing to \
         forward through; got: {msg}"
    );
}

/// THE BOUNDARY, DRIVEN: a TYPE may carry a concrete witness, and it is HONOURED. Check 3
/// is not run on the type channel (`selections_from_slot_bindings` runs check 1 only),
/// and every type-carried spelling below loads AND answers with the carried witness's
/// order. These are the result type, a parameter's type, an eta'd reference's expected
/// arrow, and the type WI-1094's inference writes for a bracket-less construction.
///
/// PASSES EITHER WAY: this ticket changes no type-channel verdict. It is the row that
/// fails if check 3 is ever moved onto the producer, and the census measured that move
/// over the whole suite. `ConcOrd` orders by REVERSE length, so `bbb,cc,a` can only be
/// `ConcOrd` answering: alphabet says `a,bbb,cc`, and `ByLength` says `a,cc,bbb`.
#[test]
fn a_type_may_carry_a_concrete_witness_and_it_is_honoured() {
    let src = program(&format!(
        "  import anthill.prelude.SortedSet.{{insert}}\n  \
         operation mk() -> SortedSet[T = String, O = ConcOrd] = SortedSet.empty()\n  \
         operation viaResult(n: Int64) -> String =\n    {}\n  \
         operation render(s: SortedSet[T = String, O = ConcOrd]) -> String =\n    \
           Show.join(SortedSet.toList(s))\n  \
         operation viaParam(n: Int64) -> String =\n    \
           render(SortedSet.insert(SortedSet.insert(SortedSet.insert(mk(), \"a\"), \"bbb\"), \"cc\"))\n  \
         operation grow(\n      \
           f: (SortedSet[T = String, O = ConcOrd], String) -> SortedSet[T = String, O = ConcOrd])\n      \
           -> String =\n    \
           render(f(f(f(mk(), \"a\"), \"bbb\"), \"cc\"))\n  \
         operation viaEta(n: Int64) -> String = grow(insert)\n  \
         operation viaInference(n: Int64) -> Int64 =\n    \
           let s = SortedSet.insert(SortedSet.insert(SortedSet.empty[T = Pair[Int64, Int64]](), \
         pair(fst: 2, snd: 1)), pair(fst: 1, snd: 9))\n    \
           SortedSet.size(s)",
        render_three("mk()"),
    ));
    for entry in ["viaResult", "viaParam", "viaEta"] {
        assert_eq!(
            eval_str(&src, &format!("probe.tx0g6.{entry}"), entry),
            "bbb,cc,a,",
            "{entry}: the type-carried `ConcOrd` must be SELECTED and honoured, not merely \
             accepted"
        );
    }
    // WI-1094 writes `O = Pair`, a concrete self-provider, into the type, and the next
    // call reads it back through the producer.
    let mut interp = crate::common::interp_for(&src);
    match interp.call("probe.tx0g6.viaInference", &[Value::Int(0)]) {
        Ok(Value::Int(n)) => assert_eq!(n, 2, "two distinct pairs were inserted"),
        other => panic!("the inferred `O = Pair` must run; got {other:?}"),
    }
}
