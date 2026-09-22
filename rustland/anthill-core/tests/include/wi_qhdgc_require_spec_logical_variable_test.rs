//! WI-20260922-QHDGC — a LOGICAL VARIABLE is admitted in a `require[Spec[T = ?t]]`
//! binding, because a logical variable is a type everywhere else.
//!
//! ## The table that says one site was out of step
//!
//! MEASURED on the pre-fix tree, four spellings over the fixture below:
//!
//! ```text
//!   Desc[?t]                  in a bounding guard          LOADS
//!   ?x: ?t                    as a head parameter type     LOADS
//!   require[Desc[T = A]]      rule type param, guarded     LOADS
//!   require[Desc[T = ?t]]     logical variable             REFUSED
//! ```
//!
//! The refusal read "`Desc`'s type parameter list takes sorts and its own type parameter
//! names; this argument is neither" — the same message a literal `require[Desc[T = 3]]`
//! gets. The first two rows are what make that a BUG rather than a namespace distinction:
//! were a variable genuinely a category error in type position, the guard and the head
//! parameter would refuse it too. They do not, and CLAUDE.md's first paragraph is why —
//! logical variables appear in types as in logical terms, and types unify.
//!
//! The census that chose the narrow rule (WI-20260909-51W18) established that nobody
//! WROTE `?t` here, not that writing it means nothing — the "unread does not imply unowed"
//! inference WI-20260921-3G1YT was filed to reject, one channel over.
//!
//! ## WHAT A VARIABLE MEANS IN THE BRACKET — measured, after a first reading that was wrong
//!
//! `docs/kernel-language.md` §"Clause-level requirement binding" states the rule this
//! ticket had to land inside: "**Every element the bracket NAMES selects the instance**; an
//! element it leaves unwritten is matched abstractly and does not discriminate"
//! (WI-20260913-J38VE). A logical variable reads as the ABSTRACT case — it is admitted, and
//! it does NOT become a selector.
//!
//! A FIRST PASS AT THIS FILE CONCLUDED "nothing reads the bracket at all", on a
//! ONE-PARAMETER fixture where every spelling — including a concrete `Desc[T = Leaf]` —
//! answered both carriers. That conclusion was wrong and the fixture is why: a spec
//! operation names its CARRIER, so on a one-parameter spec the anchor already pins the sole
//! element and the bracket has nothing left to add. J38VE's mechanism is only visible where
//! the spec has an element no call can name. MEASURED on such a spec ([`two_carrier`], `C`
//! pinned by the witness and `P` nameable only in the bracket):
//!
//! ```text
//!   Sp[C = ?c, P = Int64]    -> 7 and 9, both DEFINITE
//!   Sp[C = ?c]              -> residual, both        <-- drop the written element and it delays
//!   Sp                       -> residual, both
//! ```
//!
//! and on the single-carrier fixture, that a variable behaves as the UNWRITTEN spelling
//! does rather than as the written one:
//!
//! ```text
//!   Sp[C = Red, P = Int64]   -> 7, DEFINITE
//!   Sp[C = Red, P = ?p]     -> residual   <-- a variable does NOT select
//!   Sp[C = Red]              -> residual   <-- and this is the spelling it matches
//! ```
//!
//! So the widening admits a spelling; it does not widen what a bracket MATCHES. That is the
//! whole of [`a_variable_element_reads_as_the_abstract_case`], and it is the row that would
//! catch a future change making a variable unify against a provider's concrete binding.
//!
//! IT ALSO DOES NOT TRADE A LOUD ERROR FOR A SILENT DELAY, which was the live hazard: a
//! variable that reached `written_element` as a concrete term would be REFUSED against every
//! provider row, and the clause would delay for ever where it used to be a load error.
//! `written_element` declines anything that is not a `SortRef` / `Parameterized`, so the
//! variable falls to WI-20260830-X9PB4's wildcard instead — and at a genuine provider TIE it
//! DELAYS rather than firing `debug_assert!(false, "find_dictionary: two providers answer …")`.
//! [`a_variable_at_a_provider_tie_delays_rather_than_aborting`] is the reader; an abort
//! would show there as a panic, not as a wrong number.
//!
//! ## What IS driven, and what fails when it is backed out
//!
//!  * [`a_logical_variable_binding_loads`] — the refusal is gone. Fails on the pre-fix
//!    tree with the message quoted above.
//!  * [`the_variable_is_the_clauses_own_variable`] — **THE SHARP ROW.** The stored goal's
//!    binding is the SAME De Bruijn index as the `?t` written in a sibling body goal. This
//!    is what distinguishes going through `build_body_atom_occurrence` (which owns the
//!    `var_map` mint) from a local `kb.fresh_var` at the binding site: a local mint loads
//!    identically, retains a `Var` identically, and produces a DIFFERENT index — a
//!    variable nothing in the clause binds. MEASURED by making that mutation: this row is
//!    the only one in the file that fails.
//!  * [`a_variable_element_composes_with_a_written_one_at_two_carriers`] — THE ACCEPTANCE
//!    ROW. The dictionary is selected PER SOLUTION and answers at two different carriers
//!    (`7`, `9`, both definite) with a variable occupying `C`. Its control is the same
//!    clause at `Sp[C = ?c]`, which residualizes — so the row measures the bracket doing
//!    work, not the fixture.
//!  * [`a_variable_element_reads_as_the_abstract_case`] and
//!    [`a_variable_at_a_provider_tie_delays_rather_than_aborting`] — the two rows that say
//!    the widening did not change what a bracket MATCHES, per the measurements above.
//!  * the four refusal rows — one per carrier, so the widening is attributable rather than
//!    "the check got looser". Each asserts the message NAMES its own carrier.
//!
//! ## The controls that already passed, per CLAUDE.md's control discipline
//!
//! [`the_guard_spelling_already_passed`] and [`the_head_parameter_spelling_already_passed`]
//! pass on the pre-fix tree and on this one. They are the evidence that the refusal was
//! the odd one out, not a duplicate of the rows above.
//! [`the_rule_type_parameter_spelling_keeps_working`] likewise passed before; it is here
//! because the ticket names it as a thing the widening must not disturb.

use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

/// A spec `Desc` with TWO carriers answering DIFFERENT values, so "the dictionary was
/// selected per solution" cannot be satisfied by an accident of ordering: `Leaf` answers
/// `7`, `Twig` answers `9`, and the spec default answers `1` — so a requirement that
/// stopped being grounded would show as `1` rather than as a failure.
fn program(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  sort Twig
    import anthill.prelude.Int64
    entity twig
    provides Desc[T = Twig]
    operation describe(x: Twig) -> Int64 = 9
  end

  fact item(leaf())
  fact item(twig())
{tail}end
"#
    )
}

/// The clause under test: a grounded requirement whose spec instance is `spec`.
fn with_spec(ns: &str, spec: &str) -> String {
    program(
        ns,
        &format!(
            "  rule answer(?r) :- item(?x), ?d = require[{spec}], Desc.describe(?x, ?r)\n"
        ),
    )
}

/// Every `Int` the rule answers, sorted, with definiteness folded in — a non-definite
/// solution would read as a different set rather than silently pass.
fn answers(ns: &str, src: &str) -> Vec<i64> {
    let mut kb = crate::common::load_kb_with(src);
    let mut out: Vec<i64> = crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
        .iter()
        .map(|sol| match sol {
            (anthill_core::eval::Value::Int(i), true) => *i,
            other => panic!("`{ns}.answer` must answer definite Ints, got {other:?}\n{src}"),
        })
        .collect();
    out.sort_unstable();
    out
}

/// The stored `find_dictionary` goal's spec-instance bindings for `rule_qn`, as
/// `(param, rendered value)`, PAIRED WITH every De Bruijn index appearing anywhere in that
/// rule's body.
///
/// The second half is what makes [`the_variable_is_the_clauses_own_variable`] a real
/// assertion rather than a shape check: knowing the binding is *a* variable says nothing,
/// and knowing it is the index a sibling goal also carries says everything.
///
/// `None` when no such goal is stored at all, which is distinct from `Some((vec![], _))`
/// (the goal is there and carries no binding) — conflating the two would pass on a program
/// whose requirement vanished.
fn stored_slot_and_body_vars(
    kb: &KnowledgeBase,
    rule_qn: &str,
) -> Option<(Vec<(String, String)>, Vec<String>)> {
    let head_sym = kb.try_resolve_symbol(rule_qn)?;
    for rid in kb.live_rule_ids() {
        let anthill_core::eval::Value::Term { id: head, .. } = *kb.rule_head_value(rid) else {
            continue;
        };
        if !matches!(kb.get_term(head), Term::Fn { functor, .. } if *functor == head_sym) {
            continue;
        }
        let mut body_vars: Vec<String> = Vec::new();
        let mut slot: Option<Vec<(String, String)>> = None;
        for node in kb.rule_body_nodes(rid) {
            collect_vars(node, &mut body_vars);
            let Some(Expr::Apply {
                functor, pos_args, ..
            }) = node.as_expr()
            else {
                continue;
            };
            if !kb.qualified_name_of(*functor).ends_with("find_dictionary") {
                continue;
            }
            let Some(instance) = pos_args.first() else {
                continue;
            };
            let show = |v: &Rc<NodeOccurrence>| match v.as_expr() {
                Some(Expr::Ref(s)) | Some(Expr::Ident(s)) => kb.local_name_of(*s).to_owned(),
                Some(Expr::Var(x)) => format!("{x:?}"),
                other => format!("{other:?}"),
            };
            // POSITIONALS REPORTED TOO, keyed `#0`, `#1`, … — WI-20260909-51W18's reader
            // is shaped this way because listing named args alone made a positional
            // spelling read `[]`, indistinguishable from a bare base, and the row measured
            // nothing. The same hazard applies here.
            if let Some(Expr::Apply {
                pos_args: bp,
                named_args: bn,
                ..
            }) = instance.as_expr()
            {
                slot = Some(
                    bp.iter()
                        .enumerate()
                        .map(|(i, v)| (format!("#{i}"), show(v)))
                        .chain(bn.iter().map(|(k, v)| (kb.local_name_of(*k).to_owned(), show(v))))
                        .collect(),
                );
            }
        }
        return Some((slot.unwrap_or_default(), body_vars));
    }
    None
}

fn collect_vars(node: &Rc<NodeOccurrence>, out: &mut Vec<String>) {
    let Some(expr) = node.as_expr() else { return };
    if let Expr::Var(v) = expr {
        out.push(format!("{v:?}"));
    }
    for_each_child(expr, |child| collect_vars(child, out));
}

// ── the refusal is gone ──────────────────────────────────────────────────────

#[test]
fn a_logical_variable_binding_loads() {
    // THE ROW THIS TICKET EXISTS FOR. On the pre-fix tree this reported "`Desc`'s type
    // parameter list takes sorts and its own type parameter names; this argument is
    // neither" — a variable spells no name, so it reached neither of the two NAME rungs
    // and the drop rule reported it as a typo.
    let ns = "test.qhdgc.load";
    let errs = crate::common::try_load_kb_with(&with_spec(ns, "Desc[T = ?t]")).err();
    assert!(
        errs.is_none(),
        "`require[Desc[T = ?t]]` must load; got {:?}",
        errs.unwrap().join("\n"),
    );
}

#[test]
fn the_three_other_variable_spellings_load_too() {
    // ONE INTERNAL FORM, THREE SURFACES — the discipline WI-20260909-51W18 established
    // for `Desc[Leaf]` vs `Desc[T = Leaf]`, applied to the variable. The POSITIONAL row is
    // the one worth having: it travels a different loop, and that loop pairs positionals
    // with the spec's declared params by index, so it must land on the NAMED `T` slot.
    for spec in ["Desc[T = ?]", "Desc[?t]", "Desc[?]"] {
        let ns = "test.qhdgc.spellings";
        let kb = crate::common::load_kb_with(&with_spec(ns, spec));
        let (slot, _) = stored_slot_and_body_vars(&kb, &format!("{ns}.answer"))
            .unwrap_or_else(|| panic!("`{spec}`: no stored `find_dictionary` goal"));
        assert_eq!(
            slot.len(),
            1,
            "`{spec}` must store exactly one binding, got {slot:?}",
        );
        assert_eq!(
            slot[0].0, "T",
            "`{spec}` must land on the declared param `T`, not stay positional: {slot:?}",
        );
        assert!(
            slot[0].1.starts_with("DeBruijn("),
            "`{spec}`'s binding must be a closed variable, got {:?}",
            slot[0].1,
        );
    }
}

// ── the sharp row: whose variable is it ──────────────────────────────────────

#[test]
fn the_variable_is_the_clauses_own_variable() {
    // THE ONLY ROW IN THIS FILE THAT A LOCAL MINT FAILS, and the reason the lowering goes
    // through `build_body_atom_occurrence` rather than copying its `Var` arm.
    //
    // `?t` is written TWICE — as `item2`'s second argument and inside the bracket. If the
    // bracket shares the clause's `var_map`, the closing walk gives both ONE De Bruijn
    // index. A `kb.fresh_var` at the binding site loads clean, retains a `Var`, satisfies
    // every other row in this file, and yields a SECOND index — a variable nothing in the
    // clause binds, which is a requirement that could never ground once anything reads it.
    //
    // MEASURED by making that mutation on the delivered tree: this row fails alone.
    let ns = "test.qhdgc.ident";
    let src = program(
        ns,
        "  fact item2(leaf(), Leaf)\n  \
         rule answer(?r) :- item2(?x, ?t), ?d = require[Desc[T = ?t]], Desc.describe(?x, ?r)\n",
    );
    let kb = crate::common::load_kb_with(&src);
    let (slot, body_vars) = stored_slot_and_body_vars(&kb, &format!("{ns}.answer"))
        .unwrap_or_else(|| panic!("no stored `find_dictionary` goal\n{src}"));
    assert_eq!(slot.len(), 1, "one binding expected, got {slot:?}");
    let bound = &slot[0].1;
    // The bracket's index must appear ELSEWHERE in the body — i.e. at least twice overall,
    // once for `item2`'s `?t` and once for the bracket. A stranger index appears once.
    let occurrences = body_vars.iter().filter(|v| *v == bound).count();
    assert!(
        occurrences >= 2,
        "the bracket's `{bound}` must be the SAME variable the body's `?t` is, but it \
         occurs {occurrences}× in a body whose variables are {body_vars:?}",
    );
}

// ── the acceptance row, and the two that bound what a variable MEANS ─────────

/// A TWO-PARAMETER spec with TWO carriers. `C` is the carrier (`crecv(x: C)` names it, so
/// the witness call pins it); `P` is at a DIFFERENT type and NO operation of `Sp` names it,
/// so the bracket is the only thing that can say it. `tag()` is nullary and BODY-LESS in the
/// spec, so a `7` or a `9` can only have come through a selected dictionary.
///
/// THIS FIXTURE IS THE REASON THE ONE-PARAMETER ONE ABOVE CANNOT CARRY THE ACCEPTANCE ROW:
/// on a one-parameter spec the anchor pins the sole element and the bracket adds nothing, so
/// every spelling answers alike and a "driven" row there measures only a clean load.
fn two_carrier(ns: &str, bracket: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Sp
    import anthill.prelude.Int64
    sort C = ?
    sort P = ?
    operation tag() -> Int64
    operation crecv(x: C) -> Int64 = 0
  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Sp[C = Red, P = Int64]
    operation tag() -> Int64 = 7
    operation crecv(x: Red) -> Int64 = 5
  end

  sort Blue
    import anthill.prelude.Int64
    entity blue
    provides Sp[C = Blue, P = Int64]
    operation tag() -> Int64 = 9
    operation crecv(x: Blue) -> Int64 = 6
  end

  fact item(red())
  fact item(blue())

  rule answer(?r) :- item(?x), ?d = require[{bracket}], Sp.crecv(?x, ?c), Sp.tag(?r)
end
"#
    )
}

/// Every solution of `{ns}.answer` as `Some(int)` when DEFINITE and `None` when residual —
/// so a delay reads as a distinct outcome rather than as a missing row.
fn two_carrier_answers(ns: &str, bracket: &str) -> Vec<Option<i64>> {
    let src = two_carrier(ns, bracket);
    let mut kb = crate::common::load_kb_with(&src);
    let mut out: Vec<Option<i64>> = crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
        .iter()
        .map(|sol| match sol {
            (anthill_core::eval::Value::Int(i), true) => Some(*i),
            _ => None,
        })
        .collect();
    out.sort_unstable();
    out
}

#[test]
fn a_variable_element_composes_with_a_written_one_at_two_carriers() {
    // THE ACCEPTANCE ROW: the dictionary is selected PER SOLUTION and answers at TWO
    // DIFFERENT CARRIERS, with a LOGICAL VARIABLE occupying `C`. `7` is `Red`'s `tag()` and
    // `9` is `Blue`'s; the spec's own `tag()` is body-less, so neither number exists unless
    // a dictionary was selected, and BOTH appear, so it was selected twice differently.
    assert_eq!(
        two_carrier_answers("test.qhdgc.two", "Sp[C = ?c, P = Int64]"),
        vec![Some(7), Some(9)],
        "a variable at `C` must not stop the written `P` from selecting, and the selection \
         must still happen per solution",
    );

    // THE CONTROL THAT MAKES IT A MEASUREMENT: drop the written element and the same clause
    // residualizes at both carriers. So the row above is the BRACKET doing work — not the
    // fixture answering on its own, which is the trap a two-carrier row invites.
    assert_eq!(
        two_carrier_answers("test.qhdgc.twoc", "Sp[C = ?c]"),
        vec![None, None],
        "with `P` unwritten the goal must delay — otherwise the row above measures nothing",
    );
}

#[test]
fn a_variable_element_reads_as_the_abstract_case() {
    // THE BOUND ON WHAT THIS TICKET DID: it admits a SPELLING; it does not widen what a
    // bracket MATCHES. `docs/kernel-language.md` — "an element it leaves unwritten is
    // matched abstractly and does not discriminate" — is the rule, and a variable takes
    // that reading.
    //
    // Driven as an EQUALITY BETWEEN TWO SPELLINGS rather than as an absolute: a variable at
    // `P` must behave as the spelling that OMITS `P`, and must NOT behave as the one that
    // writes a sort there. Both halves are needed — asserting only "the variable delays"
    // would also pass if the whole fixture had stopped working.
    let written = two_carrier_answers("test.qhdgc.abs1", "Sp[C = ?c, P = Int64]");
    let omitted = two_carrier_answers("test.qhdgc.abs2", "Sp[C = ?c]");
    let variable = two_carrier_answers("test.qhdgc.abs3", "Sp[C = ?c, P = ?p]");
    assert_eq!(
        variable, omitted,
        "a variable at `P` must match the spelling that omits `P` ({omitted:?}), got \
         {variable:?}",
    );
    assert_ne!(
        variable, written,
        "…and must NOT match the spelling that writes a sort there — if it did, a variable \
         would have become a selector, which is not what a logical variable means here",
    );
}

#[test]
fn a_variable_at_a_provider_tie_delays_rather_than_aborting() {
    // THE HAZARD ROW. `fetch_dictionary` maps a resolution TIE to `FindDictFetch::Defect`
    // with `debug_assert!(false, "find_dictionary: two providers answer …")` — an ABORT in
    // every debug build — but only while the goal was decided ENTIRELY by carried types.
    // WI-20260830-X9PB4's wildcard and WI-20260913-J38VE's written element each clear that
    // flag. A variable must land on one of those paths and not on the carried-type one.
    //
    // `Carrier` reaches `Spec` through TWO providers that score alike, so this program TIES.
    // An abort shows here as a PANIC, not as a wrong number, and `debug_assert!` is live in
    // the test profile. The two concrete spellings are the controls: they tie the same way
    // and are known to delay, so a variable differing from them would be this ticket's doing.
    for bracket in [
        "Spec[C]",                          // control: the X9PB4 wildcard
        "Spec[C = Carrier, Note = Int64]",   // control: J38VE's written element
        "Spec[C = ?c, Note = ?n]",           // both elements variable
        "Spec[C = Carrier, Note = ?n]",      // one written, one variable
    ] {
        let src = format!(
            r#"namespace test.qhdgc.tie
  import anthill.prelude.{{Int64}}

  sort Spec
    sort C = ?
    sort Note = ?
    operation probe(c: C) -> Int64 = 1
  end

  sort MidA
    sort N = ?
    provides Spec[C = MidA, Note = N]
    operation probe(c: MidA) -> Int64 = 7
  end

  sort MidB
    sort N = ?
    provides Spec[C = MidB, Note = N]
    operation probe(c: MidB) -> Int64 = 9
  end

  sort Carrier
    entity carrier
    provides MidA[N = Int64]
    provides MidB[N = Int64]
  end

  rule dict(?x, ?d) :- ?d = require[{bracket}], Spec.probe(?x, ?ignored)
  rule answer(?r) :- dict(carrier(), ?d), Spec.probe(carrier(), ?r)
end
"#
        );
        // Reaching this line at all is most of the assertion — the abort would have fired
        // inside `resolve`. The verdict is then that the tie is INDEFINITE (a delay), which
        // is what "two providers tie for a reason the call never constrained" must produce.
        let mut kb = crate::common::load_kb_with(&src);
        let got = crate::common::query_unary(&mut kb, "test.qhdgc.tie.answer");
        // NON-EMPTY FIRST. `all()` is vacuously true on `[]`, so without this the row would
        // pass on a program that answered NOTHING — and "returned nothing" must never read
        // as a pass (the rule `stored_bindings`' own doc states one file over). A delay is
        // an INDEFINITE solution, so the count is part of the verdict, not a precondition.
        assert!(
            !got.is_empty(),
            "`{bracket}` must answer an indefinite residual; it answered nothing at all, \
             which is a different outcome from a delay",
        );
        assert!(
            got.iter().all(|(_, definite)| !definite),
            "`{bracket}` at a provider tie must DELAY, not decide; got {got:?}",
        );
    }
}

// ── the one-parameter yardstick ──────────────────────────────────────────────

#[test]
fn the_requirement_still_grounds_and_answers_at_both_carriers() {
    // THE YARDSTICK, NOT THE DRIVE, and the header says why: on a ONE-PARAMETER spec the
    // anchor pins the sole element, so this passes for a bare `require[Desc]` too. Its job
    // is only to show the widening did not break threading — `1` is the spec default, so a
    // requirement that stopped grounding would surface here as a `1` in the set.
    //
    // The row that measures the bracket doing work is
    // [`a_variable_element_composes_with_a_written_one_at_two_carriers`], on the fixture
    // that can express it.
    for spec in ["Desc[T = ?t]", "Desc[?t]", "Desc[T = ?]"] {
        let ns = "test.qhdgc.thread";
        assert_eq!(
            answers(ns, &with_spec(ns, spec)),
            vec![7, 9],
            "`{spec}` must keep the requirement grounded at both carriers",
        );
    }
}

// ── the four other carriers stay refused, one row each ───────────────────────
//
// ONE ROW PER CARRIER so the widening is ATTRIBUTABLE — the ticket's own requirement, and
// the reason these are not a single loop: a loop that asserted only `is_err()` would stay
// green if three of the four started reporting the FOURTH one's message, and would say
// nothing about which carrier moved. Each row names its own carrier in the diagnostic.

/// The refusal text for `spec`, or a panic if it loaded.
fn refusal(ns: &str, spec: &str) -> String {
    crate::common::try_load_kb_with(&with_spec(ns, spec))
        .err()
        .unwrap_or_else(|| panic!("`{spec}` must stay refused; it loaded clean"))
        .join("\n")
}

#[test]
fn a_literal_stays_refused() {
    let errs = refusal("test.qhdgc.lit", "Desc[T = 3]");
    assert!(
        errs.contains("`3` in it names neither a sort nor one of `Desc`'s own type parameters"),
        "the diagnostic must name the literal; got:\n{errs}",
    );
}

#[test]
fn an_entity_constructor_stays_refused() {
    let errs = refusal("test.qhdgc.ent", "Desc[T = leaf]");
    assert!(
        errs.contains("`leaf` in it names neither a sort nor one of `Desc`'s own type parameters"),
        "the diagnostic must name the constructor; got:\n{errs}",
    );
}

#[test]
fn a_rule_name_stays_refused() {
    let errs = refusal("test.qhdgc.rule", "Desc[T = item]");
    assert!(
        errs.contains("`item` in it names neither a sort nor one of `Desc`'s own type parameters"),
        "the diagnostic must name the rule; got:\n{errs}",
    );
}

#[test]
fn a_tuple_type_stays_refused() {
    let errs = refusal("test.qhdgc.tup", "Desc[T = (Leaf, Leaf)]");
    assert!(
        errs.contains("names neither a sort nor one of `Desc`'s own type parameters"),
        "a tuple type must stay refused; got:\n{errs}",
    );
}

// ── the controls that ALREADY passed ─────────────────────────────────────────

#[test]
fn the_guard_spelling_already_passed() {
    // CONTROL, per CLAUDE.md: this passes on the pre-fix tree AND on this one. It is the
    // first row of the ticket's table and the evidence that a logical variable is not a
    // category error in type position — a bounding guard takes one and always has.
    let ns = "test.qhdgc.guard";
    let src = program(
        ns,
        "  rule answer(?r) :- item(?x), Desc[?t], Desc.describe(?x, ?r)\n",
    );
    assert!(
        crate::common::try_load_kb_with(&src).is_ok(),
        "the guard control must load on either tree",
    );
}

#[test]
fn the_head_parameter_spelling_already_passed() {
    // CONTROL, and the second row of the table: `?x: ?t` is a head parameter whose TYPE is
    // a logical variable. Loads on either tree.
    let ns = "test.qhdgc.param";
    let src = program(
        ns,
        "  rule answer(?r) :- item(?x), inner(?x, ?r)\n  \
         rule inner(?x: ?t, ?r) :- Desc.describe(?x, ?r)\n",
    );
    assert!(
        crate::common::try_load_kb_with(&src).is_ok(),
        "the head-parameter control must load on either tree",
    );
}

#[test]
fn the_rule_type_parameter_spelling_keeps_working() {
    // The table's third row — a RULE TYPE PARAMETER, guarded. It loaded before and must
    // keep loading AND ANSWERING: the widening added a rung above the two name rungs, and
    // a rung that swallowed a name would show here as a lost `7`/`9`.
    let ns = "test.qhdgc.tparam";
    let src = program(
        ns,
        "  rule answer(?r) :- item(?x), anchored(?x, ?r)\n  \
         rule anchored[A](?x: A, ?r) :- Desc[A], ?d = require[Desc[T = A]], \
         Desc.describe(?x, ?r)\n",
    );
    assert_eq!(
        answers(ns, &src),
        vec![7, 9],
        "`require[Desc[T = A]]` must keep threading at both carriers",
    );
}
