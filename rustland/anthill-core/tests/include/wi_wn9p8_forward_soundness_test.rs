//! WI-20260923-WN9P8 — A FORWARD IS ANSWERED BY ITS PARAMETER'S OWN DICTIONARY.
//!
//! A named requirement slot is a type parameter (058 §4.7). So a callee slot bound to a
//! parameter `X` the enclosing signature declared, as in `s: SortedSet[T = E, O = X]`, is a
//! FORWARD: the set was built with `X`'s provider, and the dictionary the call needs is
//! the one the enclosing declaration's caller supplied FOR `X`. It used to be answered by
//! the slot's GOAL, `WeakOrd[T = E]`, which is keyed by spec and does not mention `X` at
//! all. So any same-spec entry of the frame answered it.
//!
//! TWO SHAPES, and this file drives both on every channel a forward reaches:
//!  * TIED (sound). The frame holds `X`'s dictionary: `X` is itself a named slot
//!    (`requires OE: WeakOrd[E]`, or an operation's `requires OE: …`), or a requirement
//!    binds a carrier's slot to it (`requires FiniteCollection[C = SortedSet[T = El, O =
//!    OE], …]`, Strategy 2b's shape).
//!  * UNTIED (was a silent wrong answer). `X` is a plain parameter `P`, and what covers the
//!    goal is another parameter's slot, an anonymous `requires WeakOrd[E]`, a requirement
//!    about another parameter, or nothing.
//!
//! MEASURED AT THE PARENT COMMIT, scratch probe (deleted), a set typed `O = ByLength` driven
//! against a frame whose other ordering is `RevLen`, and the mirror image:
//!
//! | shape | direct | spec (`PersistentCollection.insert`) | callee `[]` | receiver `[]` | eta | callee's op slot |
//! |---|---|---|---|---|---|---|
//! | UNTIED, named `OE` beside plain `P` | WRONG order | WRONG order | refused (check 1) | refused (check 1) | WRONG order | WRONG order |
//! | UNTIED, anonymous `requires WeakOrd[E]` | WRONG | WRONG | refused | refused | | |
//! | UNTIED, op-level `P` beside an op slot | WRONG | WRONG | refused (not a sort) | refused (not a sort) | | |
//! | UNTIED, requirement binds `OE`, set typed `P` | WRONG | refused | refused | refused | | |
//! | UNTIED, no requirement at all, `T = String` | loaded, died at eval (`Internal`) | refused (tie) | refused | refused | | |
//! | TIED, named slot `OE` | ran | ran | ran | ran | ran | ran |
//! | TIED, requirement binds `OE` (2b) | ran | REFUSED (no route) | REFUSED (check 1) | REFUSED (check 1) | | |
//! | TIED, `X: Ord[E]` answering `WeakOrd` | ran | ran | ran | ran | | |
//! | TIED, operation's own slot | ran | ran | refused (not a sort) | refused (not a sort) | | |
//!
//! NOW every UNTIED cell is refused, with one message on the direct and both bracket
//! routes ([`an_untied_forward_reads_the_same_in_every_call_spelling`]), and every TIED cell
//! runs at two orderings except the last row's two brackets. Those are refused before any
//! forward is asked: an operation's own type parameter written as a bracket value reaches
//! the σ-read producer with no witness reading. That is a separate, loud limit of the
//! bracket, not of the forward. It is unchanged here, and recorded at
//! [`an_operations_own_slot_forwards`].
//!
//! THE MECHANISM, one owner asked from three sites (`typing.rs`): `binder_frame_slot`
//! finds the frame slot for `X`, and nothing else. The direct route's dictionary build
//! (`project_forwarded_slot`, for the sort half and a callee's op-scoped half) and the spec
//! route's sub-goal (`carried_slot` → `resolve_inner`) answer the forward from that slot, or
//! refuse it. The brackets (`validate_written_selection`) forward any value naming a
//! parameter and leave the verdict to those sites, which is why the brackets and the type
//! channel now agree.
//!
//! **BACK-OUT, MEASURED ONE MECHANISM AT A TIME** (rows are this file's):
//!
//! | backed out | fails |
//! |---|---|
//! | (D) the dictionary build's forward (`project_forwarded_slot` → `None`) | [`an_untied_forward_reads_the_same_in_every_call_spelling`], [`every_untied_variant_is_refused_on_the_direct_route`], [`an_eta_reference_refuses_an_untied_forward`], [`a_callees_own_slot_refuses_an_untied_forward`], and `wi_tx0g6 a_plain_parameter_is_refused_in_both_spellings` |
//! | (S) the spec route's forward (`carried_slot` → the old `Forwarded`, answered by the scope) | [`the_spec_route_refuses_an_untied_forward`], [`a_forward_through_a_requirement_runs_in_every_spelling`] |
//! | (B) the bracket gate back to "is the value a named slot" | [`a_forward_through_a_requirement_runs_in_every_spelling`], [`an_untied_forward_reads_the_same_in_every_call_spelling`], and `wi_tx0g6`'s `a_plain_parameter_is_refused_in_both_spellings` and `a_plain_parameter_tied_to_a_requirement_forwards_in_brackets_too` |
//! | (P) `binder_slot_path`'s projection into the parameter's own slot | [`a_forward_of_an_ord_slot_is_projected_out_of_it`] |
//! | (Q) `op_named_slot_chain_index` without the value-precondition skip | [`an_operations_own_slot_forwards`] |
//! | (I) the same-sort inherit taken without `inherit_answers_every_forward` | [`a_same_sort_sibling_refuses_an_untied_forward`] |
//!
//! (D) IS BACKED BY TWO OLDER REFUSALS for one shape, an operation's type parameter with no
//! slot at all (`insertA[T, O](s: SortedSet[T = T, O = O])`). wi456's three no-route rows
//! and `wi_3g1yt a_carriers_own_requires_is_not_held_by_a_value_of_it` are refused by (D)
//! first now, and still by the parked no-route refusal and route 4's obtainability gate
//! behind it. MEASURED: they redden with (D) and either of those backed out together, and
//! with neither alone.
//!
//! **PASS EITHER WAY, BY DESIGN** — the TIED controls that ran before this ticket, here so
//! the refusal cannot widen onto them: [`a_forward_of_a_named_slot_runs_in_every_spelling`],
//! [`a_forward_into_a_callees_own_slot_and_through_an_eta_runs`], and the direct and spec
//! columns of [`a_forward_of_an_ord_slot_is_projected_out_of_it`] and
//! [`an_operations_own_slot_forwards`] under (D) and (S).
//!
//! NOT DRIVABLE, and said so: two same-spec named slots (`requires A: WeakOrd[E]`, `requires
//! B: WeakOrd[E]`) are the other shape a spec-keyed answer gets wrong, but a caller cannot
//! give them two witnesses — "one spec, one witness per call" refuses it at the caller —
//! so no ordering can show which of the two answered.
//!
//! REFERENCE: `binder_frame_slot`, `project_forwarded_slot`, `carried_slot`,
//! `validate_written_selection` (typing.rs); `wi_tx0g6_selection_validation_test` (the
//! bracket rows this settles); `wi456_no_scope_route_test` (Strategy 2b).

use anthill_core::eval::Value;

/// `ByLength` and `RevLen` order strings by length and by reverse length, so an answer
/// shows WHICH witness ordered it. `LenOrd` and `RevOrd` are the same two orders as `Ord`
/// witnesses. `Show.join` renders a list as one string.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String, Bool, Ord, WeakOrd, List, SortedSet,
                          PersistentCollection, FiniteCollection}
  import anthill.prelude.SortedSet.{insert}
  import anthill.prelude.String.{length}
  import anthill.prelude.Numeric.{sub}
  import anthill.prelude.PartialEq.{neq}
  import anthill.prelude.List.{cons, nil}

  sort ByLength
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  sort RevLen
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(b), length(a))
  end

  sort LenOrd
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  sort RevOrd
    provides Ord[T = String]
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
    format!("\nnamespace probe.wn9p8\n{DECLS}\n{body}\nend\n")
}

/// Every channel a forward reaches from inside an operation body, spelled at binder `b`
/// over element `e`.
fn direct(_e: &str, _b: &str) -> String {
    "SortedSet.insert(s, x)".to_owned()
}
fn spec(_e: &str, _b: &str) -> String {
    "PersistentCollection.insert(s, x)".to_owned()
}
fn callee(e: &str, b: &str) -> String {
    format!("SortedSet.insert[T = {e}, O = {b}](s, x)")
}
fn receiver(e: &str, b: &str) -> String {
    format!("SortedSet[T = {e}, O = {b}].insert(s, x)")
}

const CHANNELS: [(&str, fn(&str, &str) -> String); 4] = [
    ("direct", direct),
    ("spec", spec),
    ("callee bracket", callee),
    ("receiver bracket", receiver),
];

/// Insert three strings whose three orders all differ, through `insert`, into `set`. By
/// length `a,cc,bbb`; by reverse length `bbb,cc,a`.
fn render_three(insert: &str, set: &str) -> String {
    format!(
        "Show.join(SortedSet.toList({insert}({insert}({insert}({set}, \"a\"), \"bbb\"), \
         \"cc\")))"
    )
}

/// `sort`, plus the two drivers: `byLength` inserts through `via_len` into a set built
/// with `len_witness`, `revLen` through `via_rev` into one built with `rev_witness`.
fn driven(sort: &str, via_len: &str, len_witness: &str, via_rev: &str, rev_witness: &str) -> String {
    program(&format!(
        "{sort}\n  \
         operation byLength(n: Int64) -> String =\n    {}\n  \
         operation revLen(n: Int64) -> String =\n    {}",
        render_three(via_len, &format!("SortedSet.empty[T = String, O = {len_witness}]()")),
        render_three(via_rev, &format!("SortedSet.empty[T = String, O = {rev_witness}]()")),
    ))
}

fn load_errors(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

/// The ONE error `src` must produce, with its `<line>:<col>: ` prefix stripped, so two
/// spellings written at different columns compare by MESSAGE. The prefix is checked by
/// shape, for the reason `wi_tx0g6_selection_validation_test`'s twin gives.
fn sole_message(src: &str, what: &str) -> String {
    let errs = load_errors(src);
    assert_eq!(errs.len(), 1, "{what}: expected exactly one error, got {errs:#?}");
    let (prefix, msg) = errs[0]
        .split_once(": ")
        .unwrap_or_else(|| panic!("{what}: no `line:col: ` prefix in: {}", errs[0]));
    let is_line_col = prefix.split_once(':').is_some_and(|(l, c)| {
        [l, c]
            .iter()
            .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit()))
    });
    assert!(is_line_col, "{what}: expected a `line:col` prefix in: {}", errs[0]);
    msg.to_string()
}

/// `entry` must answer a string, on a fresh interpreter (`interp_for` panics on a dirty
/// load, so a value is also a clean-load assertion).
fn eval_str(src: &str, entry: &str, what: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Str(s)) => s.to_string(),
        other => panic!("{what}: expected a string from {entry}; got {other:?}"),
    }
}

/// Both orderings, each the one its set was built with: `ByLength` says `a,cc,bbb`, and
/// `RevLen` says `bbb,cc,a`. One answer twice would mean the forward did not depend on
/// the value's ordering at all.
fn assert_runs_both_orders(src: &str, what: &str) {
    assert_eq!(
        eval_str(src, "probe.wn9p8.byLength", what),
        "a,cc,bbb,",
        "{what}: a set built by length must be inserted into by length"
    );
    assert_eq!(
        eval_str(src, "probe.wn9p8.revLen", what),
        "bbb,cc,a,",
        "{what}: a set built by reverse length must be inserted into by reverse length"
    );
}

/// THE REFUSAL NAMES THE PARAMETER, and says the frame holds nothing FOR it. `param` is
/// its qualified name.
fn assert_untied(msg: &str, param: &str, what: &str) {
    assert!(
        msg.contains(&format!("is bound to `{param}`")),
        "{what}: the refusal must name the parameter the slot is bound to; got: {msg}"
    );
    assert!(
        msg.contains("nothing in the enclosing scope holds a dictionary FOR"),
        "{what}: the refusal must say the frame holds no dictionary for it; got: {msg}"
    );
}

// ── UNTIED: refused on every channel ─────────────────────────────────

/// UNTIED, the ticket's own shape: `R3` declares a plain `P` beside its slot `OE`, and
/// `add` takes a set typed `O = P`. The driver builds the set by `ByLength` and gives
/// `OE` `RevLen`. At the parent commit the direct call inserted in `RevLen`'s order.
fn r3(call: &str) -> String {
    driven(
        &format!(
            "  sort R3\n    \
               sort E = ?\n    \
               sort P = ?\n    \
               requires OE: WeakOrd[E]\n    \
               operation add(s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] =\n      \
               {call}\n  \
             end"
        ),
        "R3.add[OE = RevLen]",
        "ByLength",
        "R3.add[OE = ByLength]",
        "RevLen",
    )
}

/// ONE RULE, ONE MESSAGE: the direct call and both bracket spellings refuse the untied
/// forward with the same bytes, because the brackets forward any parameter now and the
/// verdict is the dictionary build's.
///
/// MEASURED at the parent commit: the direct call LOADED and ordered by `RevLen`. The
/// brackets refused with check 1's "R3.P does not provide WeakOrd", which was true and
/// said nothing about why a parameter cannot be forwarded. (D) and (B) each redden this.
#[test]
fn an_untied_forward_reads_the_same_in_every_call_spelling() {
    let direct_msg = sole_message(&r3(&direct("E", "P")), "direct");
    assert_untied(&direct_msg, "probe.wn9p8.R3.P", "direct");
    for (name, spell) in [("callee bracket", callee as fn(&str, &str) -> String), ("receiver bracket", receiver)] {
        let msg = sole_message(&r3(&spell("E", "P")), name);
        assert_eq!(
            msg, direct_msg,
            "{name}: a bracket naming the parameter says what its type says, so it must be \
             refused in the same words"
        );
    }
}

/// THROUGH THE SPEC. `PersistentCollection.insert(s, x)` is answered by `SortedSet`'s
/// provision, whose `O` sub-goal the carrier's type binds to `P` (WI-456's
/// `carried_slot`). The scope answered it by spec with `OE`: measured at the parent commit,
/// inserted in `RevLen`'s order. (S) reddens it.
#[test]
fn the_spec_route_refuses_an_untied_forward() {
    let errs = load_errors(&r3(&spec("E", "P")));
    assert!(
        errs.iter().any(|e| e.contains("the carrier's type binds named slot `O`")
            && e.contains("is bound to `probe.wn9p8.R3.P`")
            && e.contains("nothing in the enclosing scope holds a dictionary FOR")),
        "the spec route must refuse the untied forward, naming the slot and the \
         parameter; got {errs:#?}"
    );
}

/// EVERY OTHER WAY A GOAL CAN BE COVERED WITHOUT BEING `P`'s, on the direct route. Each
/// LOADED at the parent commit, and all but the last inserted in the other ordering. The
/// last, which holds nothing at all over a concrete element, died at eval with
/// `Internal(DeferToRequirement: __req_weakord not bound …)`. (D) reddens it.
#[test]
fn every_untied_variant_is_refused_on_the_direct_route() {
    let cases: [(&str, String, &str); 4] = [
        (
            "an anonymous requirement of the spec",
            "  sort R4\n    \
               sort E = ?\n    \
               sort P = ?\n    \
               requires WeakOrd[E]\n    \
               operation add(s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] =\n      \
               SortedSet.insert(s, x)\n  \
             end\n  \
             operation drive(n: Int64) -> String =\n    \
               Show.join(SortedSet.toList(R4.add[WeakOrd = RevLen](SortedSet.empty[T = String, O = ByLength](), \"a\")))"
                .to_owned(),
            "probe.wn9p8.R4.P",
        ),
        (
            "an operation's own slot beside its plain parameter",
            "  sort R5\n    \
               operation add[E, P, OE](s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P]\n        \
               requires OE: WeakOrd[E] =\n      \
               SortedSet.insert(s, x)\n  \
             end\n  \
             operation drive(n: Int64) -> String =\n    \
               Show.join(SortedSet.toList(R5.add[OE = RevLen](SortedSet.empty[T = String, O = ByLength](), \"a\")))"
                .to_owned(),
            "probe.wn9p8.R5.add.P",
        ),
        (
            "a requirement that binds ANOTHER parameter into a carrier's slot (2b)",
            "  sort PolyU\n    \
               sort E = ?\n    \
               sort OE = ?\n    \
               sort P = ?\n    \
               requires PersistentCollection[C = SortedSet[T = E, O = OE], Element = E]\n    \
               operation add(s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] =\n      \
               SortedSet.insert(s, x)\n  \
             end\n  \
             operation drive(n: Int64) -> String =\n    \
               Show.join(SortedSet.toList(PolyU.add[OE = RevLen](SortedSet.empty[T = String, O = ByLength](), \"a\")))"
                .to_owned(),
            "probe.wn9p8.PolyU.P",
        ),
        (
            "nothing at all, over a concrete element",
            "  sort R10\n    \
               sort P = ?\n    \
               operation add(s: SortedSet[T = String, O = P], x: String) \
             -> SortedSet[T = String, O = P] =\n      \
               SortedSet.insert(s, x)\n  \
             end\n  \
             operation drive(n: Int64) -> String =\n    \
               Show.join(SortedSet.toList(R10.add(SortedSet.empty[T = String, O = ByLength](), \"a\")))"
                .to_owned(),
            "probe.wn9p8.R10.P",
        ),
    ];
    for (what, body, param) in cases {
        let msg = sole_message(&program(&body), what);
        assert_untied(&msg, param, what);
    }
}

/// ETA'D. `grow(insert, s, x)` types `insert` at the arrow `grow` expects, which binds
/// `O = P`; the eta's dictionary is built at the mint. Measured at the parent commit: it
/// inserted in `OE`'s order. (D) reddens it.
#[test]
fn an_eta_reference_refuses_an_untied_forward() {
    let src = program(
        "  sort R13\n    \
           sort E = ?\n    \
           sort P = ?\n    \
           requires OE: WeakOrd[E]\n    \
           operation grow(f: (SortedSet[T = E, O = P], E) -> SortedSet[T = E, O = P], \
         s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] = f(s, x)\n    \
           operation add(s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] =\n      \
           grow(insert, s, x)\n  \
         end",
    );
    let msg = sole_message(&src, "eta");
    assert_untied(&msg, "probe.wn9p8.R13.P", "eta");
    assert!(
        msg.contains("used as a function value"),
        "the refusal is the eta's: {msg}"
    );
}

/// INTO A CALLEE'S OWN SLOT. `RC2.add[E, OE](…) requires OE: WeakOrd[E]` declares the
/// slot on the OPERATION, so its dictionary is the call's op-scoped half
/// (`build_op_scoped_dicts`), a second answer site. Measured at the parent commit: `R9`'s
/// `OX` answered it, and the set inserted in `OX`'s order. (D) reddens it.
#[test]
fn a_callees_own_slot_refuses_an_untied_forward() {
    let src = program(
        "  sort RC2\n    \
           operation add[E, OE](s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE]\n        \
           requires OE: WeakOrd[E] =\n      \
           SortedSet.insert(s, x)\n  \
         end\n  \
         sort R9\n    \
           sort E = ?\n    \
           sort P = ?\n    \
           requires OX: WeakOrd[E]\n    \
           operation add(s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] =\n      \
           RC2.add(s, x)\n  \
         end",
    );
    let msg = sole_message(&src, "a callee's op-scoped slot");
    assert_untied(&msg, "probe.wn9p8.R9.P", "a callee's op-scoped slot");
    assert!(
        msg.contains("named slot `OE` of `probe.wn9p8.RC2.add`"),
        "the slot refused is the callee's own: {msg}"
    );
}

// ── TIED: runs at two orderings on every channel ──────────────────────

/// TIED, `X`'s own named slot: the forward §7.1 is written for. It ran on every channel
/// before this ticket and must still. PASSES EITHER WAY, BY DESIGN: the control that the
/// refusal did not widen onto the slot shape.
#[test]
fn a_forward_of_a_named_slot_runs_in_every_spelling() {
    for (name, spell) in CHANNELS {
        let src = driven(
            &format!(
                "  sort R\n    \
                   sort E = ?\n    \
                   requires OE: WeakOrd[E]\n    \
                   operation add(s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] =\n      \
                   {}\n  \
                 end",
                spell("E", "OE")
            ),
            "R.add",
            "ByLength",
            "R.add",
            "RevLen",
        );
        assert_runs_both_orders(&src, name);
    }
}

/// TIED THROUGH A REQUIREMENT, the shape "is the binder a slot" could not tell from the
/// untied one. `PolyF` names no ordering. It requires the collection instance at `O = OE`,
/// and that dictionary holds `SortedSet`'s own `WeakOrd` in its provider half.
///
/// MEASURED at the parent commit: only the direct call ran. The spec route was refused
/// (`unresolved: WeakOrd[T = ?]`), because the scope searched the sub-goal by spec and the
/// provider half is not in the scope's entries. Both brackets were refused by TX0G6's
/// conservative gate. All four now run at both orderings. (S) reddens the spec row, (B)
/// the bracket rows.
///
/// `FiniteCollection` and not `PersistentCollection`: requiring the latter makes the
/// spec call's goal the frame's own entry, answered before any sub-goal, and that call
/// then fails on an unrelated effect row. `FiniteCollection`'s provider half holds the
/// same slot, and the spec route has to construct `PersistentCollection` to reach it.
#[test]
fn a_forward_through_a_requirement_runs_in_every_spelling() {
    for (name, spell) in CHANNELS {
        let src = driven(
            &format!(
                "  sort PolyF\n    \
                   sort El = ?\n    \
                   sort OE = ?\n    \
                   requires FiniteCollection[C = SortedSet[T = El, O = OE], Element = El, E = {{}}]\n    \
                   operation add(s: SortedSet[T = El, O = OE], x: El) -> SortedSet[T = El, O = OE] =\n      \
                   {}\n  \
                 end",
                spell("El", "OE")
            ),
            "PolyF.add",
            "ByLength",
            "PolyF.add",
            "RevLen",
        );
        assert_runs_both_orders(&src, name);
    }
}

/// TIED, and answered ONE LEVEL INTO `X`'s own slot: `X` is an `Ord` slot, and the set's
/// `O` needs a `WeakOrd`. `X`'s dictionary carries one (`Ord`'s own chain), and it is still
/// `X`'s, so the forward projects into it, as Strategy 2 did. (P) reddens every row: the
/// forward then finds `X`'s slot, cannot use it whole, and refuses.
#[test]
fn a_forward_of_an_ord_slot_is_projected_out_of_it() {
    for (name, spell) in CHANNELS {
        let src = driven(
            &format!(
                "  sort R15\n    \
                   sort E = ?\n    \
                   requires X: Ord[E]\n    \
                   operation add(s: SortedSet[T = E, O = X], x: E) -> SortedSet[T = E, O = X] =\n      \
                   {}\n  \
                 end",
                spell("E", "X")
            ),
            "R15.add",
            "LenOrd",
            "R15.add",
            "RevOrd",
        );
        assert_runs_both_orders(&src, name);
    }
}

/// TIED, `X` an OPERATION's own slot, written after a VALUE precondition. The slot's
/// declaration index counts the precondition and its dictionary position does not, so the
/// frame slot is found by the spec goals before it. (Q) reddens both rows: the position is
/// then one past the frame, and the forward is refused.
///
/// THE BRACKETS ARE NOT DRIVEN, and that is a limit recorded rather than hidden: an
/// operation's own type parameter written as a bracket value (`SortedSet.insert[T = E, O =
/// OE](s, x)` inside `add[E, OE]`) reaches the σ-read producer with no witness reading and is
/// refused as "must name a WITNESS SORT". It was refused so at the parent commit as well,
/// and before any forward is asked, so it is not this ticket's to change.
#[test]
fn an_operations_own_slot_forwards() {
    for (name, spell) in &CHANNELS[..2] {
        let src = driven(
            &format!(
                "  sort RC\n    \
                   operation add[E, OE](s: SortedSet[T = E, O = OE], x: E, n: Int64) \
                 -> SortedSet[T = E, O = OE]\n        \
                   requires neq(n, 0), OE: WeakOrd[E] =\n      \
                   {}\n  \
                   operation add1[E, OE](s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE]\n        \
                   requires OE: WeakOrd[E] =\n      \
                   add(s, x, 1)\n  \
                 end",
                spell("E", "OE")
            ),
            "RC.add1",
            "ByLength",
            "RC.add1",
            "RevLen",
        );
        assert_runs_both_orders(&src, name);
    }
}

/// TIED, the last two routes: a slot of the CALLEE's own (its op-scoped half) bound to the
/// caller's slot, and an eta'd `insert` whose expected arrow binds `O = OE`. Both ran before
/// this ticket. PASSES EITHER WAY, BY DESIGN: the controls for the two answer sites the
/// untied rows above refuse at.
#[test]
fn a_forward_into_a_callees_own_slot_and_through_an_eta_runs() {
    let op_slot = driven(
        "  sort RC2\n    \
           operation add[E, OE](s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE]\n        \
           requires OE: WeakOrd[E] =\n      \
           SortedSet.insert(s, x)\n  \
         end\n  \
         sort R9t\n    \
           sort E = ?\n    \
           requires OX: WeakOrd[E]\n    \
           operation add(s: SortedSet[T = E, O = OX], x: E) -> SortedSet[T = E, O = OX] =\n      \
           RC2.add(s, x)\n  \
         end",
        "R9t.add",
        "ByLength",
        "R9t.add",
        "RevLen",
    );
    assert_runs_both_orders(&op_slot, "a callee's op-scoped slot");
    let eta = driven(
        "  sort R14\n    \
           sort E = ?\n    \
           requires OE: WeakOrd[E]\n    \
           operation grow(f: (SortedSet[T = E, O = OE], E) -> SortedSet[T = E, O = OE], \
         s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] = f(s, x)\n    \
           operation add(s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] =\n      \
           grow(insert, s, x)\n  \
         end",
        "R14.add",
        "ByLength",
        "R14.add",
        "RevLen",
    );
    assert_runs_both_orders(&eta, "an eta'd insert");
}

// ── Found by /code-review ─────────────────────────────────────────────

/// A SAME-SORT sibling inherits its caller's frame instead of being handed a dictionary,
/// so the forward rule is never asked there unless the inherit asks it. `ins[OE = P](s, x)`
/// inside the sort that declares `OE` and a plain `P` binds `ins`'s `OE` to `P`, and the
/// inherit answered it with the caller's `OE`. MEASURED during this ticket, after the
/// bracket gate was widened and before the inherit was gated: all three spellings LOADED
/// and inserted a `ByLength` set in `RevLen`'s order. (Before this ticket check 1 refused
/// them in the bracket.) (I) reddens it.
#[test]
fn a_same_sort_sibling_refuses_an_untied_forward() {
    for call in ["R.ins[OE = P](s, x)", "ins[OE = P](s, x)", "R[OE = P].ins(s, x)"] {
        let src = program(&format!(
            "  sort R\n    \
               sort E = ?\n    \
               sort P = ?\n    \
               requires OE: WeakOrd[E]\n    \
               operation ins(s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] = \
             SortedSet.insert(s, x)\n    \
               operation add(s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] = {call}\n  \
             end"
        ));
        let msg = sole_message(&src, call);
        assert_untied(&msg, "probe.wn9p8.R.P", call);
    }
}

/// AN OPERATION'S OWN SLOT, OUT OF AN ETA'S REACH: an operation used as a function value
/// builds its dictionary from the enclosing SORT's slots only, so a forward of the
/// enclosing operation's own `OE` has nothing to read there. It was refused before this
/// ticket too. What this pins is the reason: the refusal must not say that nothing holds a
/// dictionary for `OE`, which the operation declares, but that this route cannot read it.
#[test]
fn an_operations_own_slot_is_out_of_an_etas_reach() {
    let src = program(
        "  sort RE\n    \
           operation grow[E, OE](f: (SortedSet[T = E, O = OE], E) -> SortedSet[T = E, O = OE], \
         s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] requires OE: WeakOrd[E] = f(s, x)\n    \
           operation add[E, OE](s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] \
         requires OE: WeakOrd[E] = grow(insert, s, x)\n  \
         end",
    );
    let msg = sole_message(&src, "eta of an op-scoped slot");
    assert!(
        msg.contains("this route reads only the enclosing SORT's slots")
            && !msg.contains("nothing in the enclosing scope holds a dictionary FOR"),
        "the refusal must name the route's reach, not deny the slot exists; got: {msg}"
    );
}
