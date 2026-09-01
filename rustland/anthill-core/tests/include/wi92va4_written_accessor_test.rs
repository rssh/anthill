//! WI-20260901-92VA4 — a hand-written `field_access(…)` is a call to whatever that name
//! denotes, not the desugaring. Provenance decides, exactly as kernel-language.md §8.6
//! words it.
//!
//! WHAT WAS WRONG. `kb/load.rs`'s accessor arm gated on `dt::is`, which admits the SHORT
//! spelling, so a hand-written `field_access(q, x)` that resolved to NOTHING took the
//! WI-280 / WI-714 / WI-749 re-route ladder and was lowered as `q.x` — driven, it answered
//! 7. The byte-analogous `foo_access(q, x)` was a load error; the SAME spelling as a
//! rule-body goal was a load error naming the missing import; in a query pattern it was an
//! ordinary bare intern. One spelling, three positions, and the operation body was the only
//! one that rescued it — against three §8.6 bullets that each say it must not:
//! "A user's same-spelled name cannot capture a desugaring", "No name is reserved", and
//! "provenance, not spelling, decides that".
//!
//! THE GATE IS NOW `is_minted(parse_id) && name == dt::FIELD_ACCESS` — the idiom
//! `parse::desugar_target` prescribes for a provenance-gated reader. The `..` address is
//! unspellable, so the constant alone would answer the same; both are written because the
//! gate is the claim and the constant is the identity.
//!
//! `dot_apply` IS NOT THE SAME QUESTION, and 92VA4's own ticket text got this wrong before
//! the spec was read: §5.3 gives the author that spelling — "a sort-scoped law written
//! against the method-call form, `rule dr: dot_apply(?receiver, member, ?x) = … [simp]`" —
//! so its two arms in `load.rs` take a SHAPE guard, not a mint gate, and their comments
//! record the 8 tests that fall if one is added. §6.7 gives `field_access` no written form
//! at all. `a_written_dot_apply_is_deliberately_untouched` is that asymmetry, driven.
//!
//! TWO CHANGES, TWO CONTROLS, MEASURED SEPARATELY — the halves are independent and a
//! single back-out would credit one for the other.
//!
//!   * THE GATE. Restore `dt::is(&name, dt::FIELD_ACCESS)` at that site: three rows fail —
//!     `a_hand_written_bare_accessor_is_refused`,
//!     `a_qualified_hand_written_call_is_an_ordinary_call` and
//!     `the_refusal_names_the_functor_and_the_repair`. RUN, and the reason is not the one
//!     an earlier draft of this header gave: the two fixtures do NOT load clean under the
//!     back-out, they are rescued into the accessor ladder and then fail dot dispatch with
//!     "`P.q`: expected operation declared on the receiver's sort, got no such member".
//!     "Loads clean" is true of `field_access(q, x)`, the ticket's motivating spelling,
//!     which these fixtures deliberately do not use — see the last paragraph. Corrected
//!     after `/code-review` ran the back-out and read the messages.
//!   * THE MESSAGE. Restore `actual_type: "unknown functor"` in `typing.rs`'s
//!     `UnknownApplyFunctor` arm: exactly ONE row fails,
//!     `the_refusal_names_the_functor_and_the_repair`.
//!   * THE MESSAGE'S GUARD. Append the census unconditionally (drop the
//!     `symbol_declares_nothing` test): exactly ONE row fails,
//!     `a_declared_name_applied_wrongly_keeps_the_terse_message`. A separate control
//!     because it is a separate claim — the message must be added AND withheld.
//!
//! `the_dot_form_still_lowers`, `a_written_dot_apply_is_deliberately_untouched` and
//! `a_declared_dot_apply_is_unreachable_at_the_dot_rule_shape` pass under ALL THREE
//! back-outs BY DESIGN: they are what bound the change, and a run in which they went red
//! would mean the gate had eaten the desugaring itself or the sibling spelling. The last
//! of them pins a SPEC sentence rather than this ticket's code — see its own doc.
//!
//! THE REPLACEMENT for the removed spelling is the DECLARED operation, which
//! WI-20260824-6RXGD made callable — `field_access[Name = "x"](q, "x")`, driven in
//! `wi6rxgd_field_access_call_test`. That is why this narrowing is available now and was
//! not in August: the objection that blocked it was that it removed a capability with no
//! working replacement.
//!
//! NOT CLOSED HERE: a broken SUBEXPRESSION swallows every diagnostic its ANCESTORS would
//! have raised, so `field_access(q, x)` — a bare identifier in the field slot, which is the
//! likeliest way to write this by hand — is reported against `x` and never names the
//! functor. The rows below therefore drive the functor refusal through `(q, q)`, where no
//! descendant fails and the functor error is the one reported.
//!
//! AN EARLIER DRAFT OF THIS PARAGRAPH SAID "the typer reports ONE error per operation body,
//! innermost first". That is FALSE and is corrected here rather than edited away, because
//! the way it was wrong is reusable: it was filed from two fixtures that were both
//! ancestor/descendant pairs, so a policy suppressing only ANCESTORS looked like a policy
//! reporting only one error. Siblings inverted it on the first try —
//! `two(aaa_no(1), bbb_no(1))` reports BOTH, two broken operations report both, and a
//! broken op body plus a broken rule body report both.
//!
//! The live question is narrower and is WI-20260901-P3CZV's: suppression is CORRECT for an
//! ancestor diagnostic that reads the child's type (an op-return mismatch has nothing true
//! to say once the body has none) and WRONG for the two that do not — `unknown functor` and
//! ARITY, both withheld anyway, both measured with a control showing they fire when the
//! child is clean.

use crate::common::{interp_for, scalar_int, try_load_kb_with};

const P: &str = "  import anthill.prelude.{Int64}\n  sort P\n    entity p(x: Int64)\n  end\n";

fn program(ns: &str, body: &str) -> String {
    format!("namespace probe.{ns}\n{P}{body}\nend\n")
}

fn errors_of(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// Call `probe.<ns>.go()` and read its `Int64`.
fn go(src: &str, ns: &str) -> i64 {
    let mut interp = interp_for(src);
    let v = interp
        .call(&format!("probe.{ns}.go"), &[])
        .unwrap_or_else(|e| panic!("probe.{ns}.go: {e}"));
    let kb = interp.kb();
    scalar_int(kb, &v).unwrap_or_else(|| panic!("probe.{ns}.go did not answer an Int64: {v:?}"))
}

/// THE ARM AND ITS CONTROL, side by side and byte-analogous but for the functor's spelling.
/// Before this ticket the arm loaded clean; the control was a load error. They now agree,
/// which is the whole claim.
#[test]
fn a_hand_written_bare_accessor_is_refused() {
    let arm = program("arm", "  operation get(q: P) -> Int64 = field_access(q, q)");
    let control = program("ctl", "  operation get(q: P) -> Int64 = foo_access(q, q)");

    let arm_errs = errors_of(&arm);
    let ctl_errs = errors_of(&control);
    assert!(
        arm_errs.iter().any(|e| e.contains("field_access.apply")),
        "a hand-written `field_access` must be refused as the unknown functor it is; \
         got {arm_errs:?}"
    );
    assert!(
        ctl_errs.iter().any(|e| e.contains("foo_access.apply")),
        "the control must be refused the same way, or it is not a control; got {ctl_errs:?}"
    );
}

/// The FULLY-QUALIFIED hand-written call was rescued too, and §6.7 says it is "a call to
/// whatever `field_access` denotes at that scope". Provenance gating is what distinguishes
/// this from a spelling test: dropping only the short arm would have left this row rescued.
#[test]
fn a_qualified_hand_written_call_is_an_ordinary_call() {
    let src = program(
        "qual",
        "  operation get(q: P) -> Int64 = anthill.reflect.field_access(q, q)",
    );
    let errs = errors_of(&src);
    assert!(
        !errs.is_empty(),
        "a written qualified call is a call to the declared operation — whose result is \
         `FieldOf[…]`, not `Int64` — so it must not load clean as the accessor"
    );
    assert!(
        !errs.iter().any(|e| e.contains("no such member")),
        "…and it must not be reported through the dot-dispatch path, which is what the \
         accessor ladder does; got {errs:?}"
    );
}

/// THE DIAGNOSTIC HALF. The operation body now says what the rule body says about a name
/// nothing declares: the census, and the repair. Shared wording, not a fourth copy —
/// `load::no_declaration_census` / `load::undefined_name_repair`.
#[test]
fn the_refusal_names_the_functor_and_the_repair() {
    let src = program("msg", "  operation get(q: P) -> Int64 = field_access(q, q)");
    let errs = errors_of(&src);
    let e = errs
        .iter()
        .find(|e| e.contains("field_access.apply"))
        .unwrap_or_else(|| panic!("expected the functor refusal; got {errs:?}"));
    assert!(
        e.contains("unknown functor"),
        "the phrase ~15 assertions and `wi557::genuinely_unknown_bare_functor_stays_terse` \
         match on must survive; got {e:?}"
    );
    assert!(
        e.contains("no rule, fact, operation, entity, const or builtin is declared"),
        "the census the rule body gives; got {e:?}"
    );
    assert!(
        e.contains("import the namespace that declares `field_access`"),
        "the repair the rule body gives, naming this functor; got {e:?}"
    );
}

/// THE DESUGARING ITSELF IS UNTOUCHED — the row that says the gate narrowed the written
/// spelling and not the form. Green either way by design.
#[test]
fn the_dot_form_still_lowers() {
    let src = program(
        "dot",
        "  operation get(q: P) -> Int64 = q.x\n  operation go() -> Int64 = get(p(x: 7))",
    );
    assert_eq!(errors_of(&src), Vec::<String>::new());
    assert_eq!(go(&src, "dot"), 7);
}

/// THE ASYMMETRY, and the reason this ticket is not "narrow every desugar target".
/// §5.3 gives the author `dot_apply(?receiver, member, ?x)` as the written form of a
/// sort-scoped dot rule, so its short spelling is a SPELLED KERNEL FORM and its two
/// `load.rs` arms keep a shape guard. A mint gate there would delete the spelling — the
/// arms' own comments record the 8 tests that fell when one was tried. Driven here so the
/// asymmetry is a measurement rather than a citation: this answers 7, its `field_access`
/// twin above is refused, and both are hand-written short spellings.
#[test]
fn a_written_dot_apply_is_deliberately_untouched() {
    let src = program(
        "dotapply",
        "  operation get(q: P) -> Int64 = dot_apply(q, x)\n  operation go() -> Int64 = get(p(x: 7))",
    );
    assert_eq!(errors_of(&src), Vec::<String>::new());
    assert_eq!(go(&src, "dotapply"), 7);
}

/// THE NARROWING ON THE MESSAGE, and it is a correction rather than a feature.
/// `UnknownApplyFunctor` fires on a WIDER condition than "nothing is declared" — its own
/// doc says "neither a known operation, a constructor, nor a var-bound arrow type" — so an
/// applied sort and an applied parameter reach it with the name declared and in scope.
/// Appending the census unconditionally made the message say something FALSE about a name
/// the author can see three lines up. Found by `/code-review`, driven here.
///
/// Backing out `symbol_declares_nothing`'s guard (append unconditionally) reds this row
/// and leaves the other five green.
#[test]
fn a_declared_name_applied_wrongly_keeps_the_terse_message() {
    let sort_applied = "namespace probe.s\n  import anthill.prelude.{Int64}\n  sort S\n    \
                        entity mk(x: Int64)\n  end\n  operation go() -> Int64 = S(1)\nend\n";
    let param_applied = "namespace probe.n\n  import anthill.prelude.{Int64}\n  \
                         operation go(n: Int64) -> Int64 = n(1)\nend\n";
    for (label, src) in [("a declared sort", sort_applied), ("a parameter", param_applied)] {
        let errs = errors_of(src);
        let e = errs
            .iter()
            .find(|e| e.contains(".apply"))
            .unwrap_or_else(|| panic!("{label}: expected the apply refusal; got {errs:?}"));
        assert!(
            e.contains("unknown functor"),
            "{label}: the terse phrase stays; got {e:?}"
        );
        assert!(
            !e.contains("is declared under that name"),
            "{label}: the name IS declared — saying otherwise is a false sentence about \
             code the author can see; got {e:?}"
        );
    }
}

/// THE `dot_apply` WART, driven — and it is here because the §8.6 paragraph this ticket
/// added first stated the OPPOSITE, that "a program that declares its own `dot_apply` gets
/// its own". It does not: the loader's arm is a pure SHAPE guard and consults no scope, so
/// with identifiers in both slots the dot rule form wins and the declaration is
/// unreachable. It IS reachable at a shape whose name slot is not an identifier.
/// `/code-review` measured the contradiction; the spec now records the wart instead.
///
/// Green either way with respect to this ticket's gate — `field_access` is what moved —
/// which is exactly why it is worth pinning: it is the sentence in the spec that a future
/// narrowing of the `dot_apply` arms would silently falsify.
#[test]
fn a_declared_dot_apply_is_unreachable_at_the_dot_rule_shape() {
    let ident_shape = program(
        "own",
        "  operation dot_apply(a: P, b: P) -> Int64 = 5\n  \
         operation go(q: P) -> Int64 = dot_apply(q, q)",
    );
    let errs = errors_of(&ident_shape);
    assert!(
        errs.iter().any(|e| e.contains("no such member")),
        "two identifiers in the slots IS the dot rule form, so the declaration is not \
         reached and `q.q` fails dot dispatch; got {errs:?}"
    );

    let other_shape = "namespace probe.own2\n  import anthill.prelude.{Int64}\n  \
                       operation dot_apply(a: Int64, b: Int64) -> Int64 = 5\n  \
                       operation go() -> Int64 = dot_apply(1, 2)\nend\n";
    assert_eq!(
        errors_of(other_shape),
        Vec::<String>::new(),
        "a name slot that is not an identifier is not the dot rule form, so the \
         declaration IS reached"
    );
}
