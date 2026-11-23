//! WI-20260827-1ZG70 — a host function that SEES variables: a reflection reader answers off
//! the part of a term it reads, whatever the rest is bound to later.
//!
//! THE DEFECT, measured 2026-11-23 on 6b4e2519e (it was the same on 2026-08-27):
//!
//!   rule ng(?n) :- term_functor_name(as_term(some(?x))) <=> ?n
//!       1 solution, CONDITIONAL — residual unify(term_functor_name(as_term(some(?_))), ?_)
//!
//! The functor of `some(?x)` is `some` whatever `?x` is. The wait came from
//! `Interpreter::call_host`, the one door every host call goes through: since 068 §2 it
//! refused any argument holding one of the rule's unfilled variables ANYWHERE in it. Right
//! for `Int64.add`, wrong for a reader whose answer depends on the head alone — and the
//! population the reflection surface exists for has such terms: four `SortProvidesInfo`
//! rows of the standard library carry an open effect row (`E: {?_, ?_}`, MappedStream,
//! FilteredStream and their `Finite` twins), so a reader over them waited at its first step.
//!
//! THE REPAIR (`eval/mod.rs`, `eval/builtins.rs`): a host function is one of two KINDS, told
//! apart by its signature (`BuiltinFn::Ground` / `BuiltinFn::SeesVars`). A ground one is
//! never handed an unfilled variable — `call_host` waits before calling it, as before. One
//! that sees variables is handed its arguments as they are with a `HostEnv`, and asks it at
//! each position it READS (`HostEnv::read`), waiting there. The runtime's variable-seeing
//! functions are their own table, `HOST_FNS_SEEING_VARS`: `as_term` (reads nothing),
//! `term_functor_name`, `term_as_int`, `term_as_string` (the head), `term_field` (the name
//! and the head; the field it hands back unread). READ-ONLY: the env binds nothing.
//!
//! WHY THE READS ARE THE HALF THAT KEEPS IT SOUND. The ticket's August note measured the
//! exemption without them (policy (a), "exempt the reflect family"): `term_as_int(as_term(
//! ?x)) = none()` answered 1 DEFINITE — a claim that `?x` is no integer, with `?x` free.
//!
//! BACK-OUT LEDGER, measured 2026-11-23 in a temporary binary over this file alone:
//!   (1) the kind backed out — `call_host` gates a `SeesVars` function as a ground one, the
//!       tree as it was — FAIL: `a_reader_answers_off_the_part_it_reads` (`ng` waits),
//!       `a_reader_waits_for_a_variable_bound_later` (`fieldvar` waits),
//!       `a_reader_over_sort_provides_info_reaches_the_open_tail` (every row waits).
//!   (2) the reads backed out — the five functions see variables and ask nothing (the
//!       August note's policy (a)) — FAIL: `what_a_reader_reads_still_waits` (`varA` decided
//!       false, `varB` 1 DEFINITE, `fv` / `sv` / `tv` / `fv2` `none` definite; `nm` stays
//!       conditional but RAISED a type mismatch over the unfilled name, one fault),
//!       `a_reader_waits_for_a_variable_bound_later` (`late1` / `fv3` `none`, `late2` 0),
//!       `an_unrun_call_is_never_read_as_data` (`trap1` a conditional `none`, `trap2`
//!       `none`: the reader took the variable the waiting call's hole leaves for no term
//!       before the call ran).
//!   (3) `as_term` alone back in the ground table — FAIL: `a_reader_answers_off_the_part_it_
//!       reads` (`ng` waits at the inner call), `a_reader_waits_for_a_variable_bound_later`
//!       (`fieldvar`); `a_reader_over_sort_provides_info_...` passes, calling no `as_term`.
//!   PASS EVERY WAY, by design — the control: `wi880_guards_hold`.

// Answers of `qn(?r)`, each rendered and marked whether it is definite.
use crate::common::shown_rows as rows;

const READ: &str = r#"
namespace t1zg.read
  import anthill.prelude.{Int64, String, Bool, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{term_as_int, term_as_string, term_functor_name, term_field, term_to_string, as_term}

  -- Answered off the part read: the head, or a head and one field.
  rule ng(?n)  :- term_functor_name(as_term(some(?x))) <=> ?n
  rule nge(1)  :- term_functor_name(as_term(some(?x))) = some("some")
  rule ofi(?r) :- term_as_int(as_term(some(?x))) <=> ?r
  rule ofs(?r) :- term_as_string(as_term(some(?x))) <=> ?r
  rule fld(?r) :- term_field(as_term(some(?x)), "nope") <=> ?r

  -- A variable at the position read: each waits.
  rule varA(1) :- term_as_int(as_term(?x)) = some(7)
  rule varB(1) :- term_as_int(as_term(?x)) = none()
  rule fv(?n)  :- term_functor_name(as_term(?x)) <=> ?n
  rule sv(?n)  :- term_as_string(as_term(?x)) <=> ?n
  rule tv(?r)  :- term_field(as_term(?x), "value") <=> ?r
  rule nm(?r)  :- term_field(as_term(some(1)), ?nm) <=> ?r
  rule fv2(?n) :- term_field(as_term(some(?x)), "value") <=> some(?v), term_functor_name(?v) <=> ?n
  -- A ground host function reads the whole argument, and still waits on any variable in it.
  rule ts(?s)  :- term_to_string(as_term(some(?x))) <=> ?s

  -- The variable bound LATER: the waiting reader answers on the binding.
  rule late1(?n) :- term_functor_name(as_term(?x)) <=> ?n, ?x <=> some(1)
  rule late2(1)  :- term_as_int(as_term(?x)) = some(7), ?x <=> 7
  rule late3(1)  :- term_as_int(as_term(?x)) = some(7), ?x <=> 8
  rule late4(?r) :- term_field(as_term(some(1)), ?nm) <=> ?r, ?nm <=> "value"
  rule fieldvar(?r) :- term_field(as_term(some(?x)), "value") <=> some(?v), ?v <=> as_term(5), ?r <=> ?x
  rule fv3(?n) :- term_field(as_term(some(?x)), "value") <=> some(?v), term_functor_name(?v) <=> ?n, ?x <=> none()

  -- WI-880's guards: a nested host call reduces, and the un-run call is not read.
  rule g880a(1) :- term_as_int(as_term(7)) = some(7)
  rule g880b(1) :- term_as_int(as_term(7)) = none()

  -- The 4XXSD trap: a stuck inner call held in a reader's argument.
  rule trap1(?n) :- term_field(as_term(some(Int64.add(?x, 1))), "value") <=> some(?v), term_functor_name(?v) <=> ?n
  rule trap2(?n) :- term_field(as_term(some(Int64.add(?x, 1))), "value") <=> some(?v), term_as_int(?v) <=> ?n, ?x <=> 2
  rule trap3(?n) :- term_functor_name(as_term(some(Int64.add(?x, 1)))) <=> ?n
end
"#;

fn read_kb() -> anthill_core::kb::KnowledgeBase {
    crate::common::load_kb_with(READ)
}

/// The faults the search for `t1zg.read.<rel>(?r)` reported — a host function that RAISED
/// rather than waited (a type mismatch over a variable it should not have read) marks the
/// search incomplete and still leaves a conditional row, so a wait is asserted fault-free.
fn faults(kb: &mut anthill_core::kb::KnowledgeBase, rel: &str) -> usize {
    use anthill_core::kb::resolve::ResolveConfig;
    let goal = crate::common::query_pattern_term(kb, &format!("t1zg.read.{rel}(?r)"));
    kb.resolve_with_stats(&[goal], &ResolveConfig::default()).1.errors.len()
}

/// One DEFINITE answer of `t1zg.read.<rel>`, rendered.
fn definite(kb: &mut anthill_core::kb::KnowledgeBase, rel: &str) -> String {
    match rows(kb, &format!("t1zg.read.{rel}")).as_slice() {
        [(v, true)] => v.clone(),
        other => panic!("`{rel}` must answer one definite row, got {other:?}"),
    }
}

/// `t1zg.read.<rel>` waits: one CONDITIONAL answer, rendered `shown`, and no fault. A wait,
/// not a refusal: a reader that cannot answer yet must not decide (0 answers) either. The
/// value is asserted because a reader that answers WRONG beside a sibling that waits leaves a
/// conditional row too — `trap1` answered `none` so under back-out (2) — and `shown` is the
/// unbound `?_` wherever the row's value is the reader's own output.
fn waits(kb: &mut anthill_core::kb::KnowledgeBase, rel: &str, shown: &str) {
    match rows(kb, &format!("t1zg.read.{rel}")).as_slice() {
        [(v, false)] if v == shown => {}
        other => panic!("`{rel}` must wait (one conditional answer `{shown}`), got {other:?}"),
    }
    assert_eq!(faults(kb, rel), 0, "`{rel}` waits; it does not raise");
}

/// THE ACCEPTANCE: the head of `some(?x)` is `some`, and a literal reader of it is `none()`.
/// Back-out (1) or (3): every row waits.
#[test]
fn a_reader_answers_off_the_part_it_reads() {
    let mut kb = read_kb();
    let got: Vec<(&str, String)> = ["ng", "nge", "ofi", "ofs", "fld"]
        .into_iter()
        .map(|rel| (rel, definite(&mut kb, rel)))
        .collect();
    assert_eq!(
        got,
        vec![
            ("ng", "some(value: \"some\")".to_string()),
            ("nge", "1".to_string()),
            ("ofi", "none".to_string()),
            ("ofs", "none".to_string()),
            ("fld", "none".to_string()),
        ],
        "a reader answers off the head it reads, whatever the unfilled `?x` under it is"
    );
}

/// THE CONTROLS the reads exist for: a variable AT the position read waits. Back-out (2)
/// — the reads gone, the exemption kept — answers each row wrong: `varB` 1 DEFINITE (`?x`
/// is no integer, with `?x` free), `varA` decided false, `fv` / `sv` / `tv` / `fv2` `none`
/// definite, and `nm` is still one conditional row but RAISED a type mismatch over the
/// unfilled name — which only the fault check of `waits` sees. `ts` waits either way:
/// `term_to_string` is ground.
#[test]
fn what_a_reader_reads_still_waits() {
    let mut kb = read_kb();
    waits(&mut kb, "varA", "1");
    waits(&mut kb, "varB", "1");
    for rel in ["fv", "sv", "tv", "nm", "fv2", "ts"] {
        waits(&mut kb, rel, "?_");
    }
}

/// A waiting reader is asked again when the variable is bound, and answers then. `late3` is
/// the control that `late2` reads the binding: `8` is not `7`. `fieldvar` is the field
/// handed back AS the variable: binding the field `?v` binds `?x`, which only the variable
/// itself does — a reader that waited for `?x` would still be waiting, nothing binding it
/// (back-outs (1) and (3)). Back-out (2): `late1` and `fv3` answer `none` at the read, and
/// `late2` is decided false.
#[test]
fn a_reader_waits_for_a_variable_bound_later() {
    let mut kb = read_kb();
    assert_eq!(definite(&mut kb, "late1"), "some(value: \"some\")");
    assert_eq!(definite(&mut kb, "late2"), "1");
    assert!(rows(&mut kb, "t1zg.read.late3").is_empty(), "`8` is not `7`");
    assert_eq!(definite(&mut kb, "late4"), "some(value: 1)");
    assert_eq!(definite(&mut kb, "fieldvar"), "5");
    assert_eq!(definite(&mut kb, "fv3"), "some(value: \"none\")");
}

/// WI-880's two guards, driven: the nested call reduces before the reader, so `some(7)`
/// holds and `none()` does not. Pass either way.
#[test]
fn wi880_guards_hold() {
    let mut kb = read_kb();
    assert_eq!(definite(&mut kb, "g880a"), "1");
    assert!(rows(&mut kb, "t1zg.read.g880b").is_empty());
}

/// The trap the widening walks next to (WI-20260827-4XXSD): an un-run call is never read as
/// data. `Int64.add(?x, 1)` cannot run yet, so the reader over it waits — it does not report
/// the call's functor `add` — and answers the call's VALUE once `?x` is bound. The 068
/// evaluation keeps a call over a stuck argument stuck before any host function is reached
/// (`trap1`, `trap3` wait under every back-out), and where the stuck call is left as a
/// variable to fill, the next reader must wait for that variable: back-out (2) answers
/// `trap2` `none` — the hole read as no integer before the call ran. Here so a later
/// widening that hands a stuck call, or its hole, to a reader fails.
#[test]
fn an_unrun_call_is_never_read_as_data() {
    let mut kb = read_kb();
    waits(&mut kb, "trap1", "?_");
    assert_eq!(definite(&mut kb, "trap2"), "some(value: 3)");
    waits(&mut kb, "trap3", "?_");
}

/// The population the ticket was filed for: a reader over the standard library's own
/// `SortProvidesInfo` rows reaches an open effect row, and READS it — the spec's head, the
/// row's `merge`, and the `open` tail under it. Each row a definite answer; the open tail
/// itself (`?_`) is never read, only its holder. On 2026-11-23 four rows answer (MappedStream,
/// FilteredStream, MappedStreamFinite, FilteredStreamFinite), each `(SortView, open)`; which
/// rows there are is the library's, so the test asks that none waits, that every spec reads
/// as a `SortView` (the record's own shape), and that some row reaches an `open` tail.
/// Back-out (1): every row waits at its first `term_functor_name`.
#[test]
fn a_reader_over_sort_provides_info_reaches_the_open_tail() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace t1zg.spi
  import anthill.prelude.{String, Option}
  import anthill.prelude.Option.{some}
  import anthill.reflect.{term_functor_name, term_field, SortProvidesInfo}

  rule open_left(?r) :-
    SortProvidesInfo(sort_ref: ?s, spec: ?p),
    term_field(?p, "E") <=> some(?e),
    term_field(?e, "effects_expr") <=> some(?x),
    term_functor_name(?x) = some("merge"),
    term_field(?x, "left") <=> some(?left),
    term_functor_name(?p) <=> ?head,
    term_functor_name(?left) <=> ?l,
    ?r <=> (?head, ?l)
end
"#,
    );
    let got = rows(&mut kb, "t1zg.spi.open_left");
    for (row, definite) in &got {
        assert!(*definite, "an open effect row is read, not waited on: {row}");
        assert!(row.starts_with("(some(value: \"SortView\"), "), "a spec view's head: {row}");
    }
    assert!(
        got.iter().any(|(row, _)| row == "(some(value: \"SortView\"), some(value: \"open\"))"),
        "the standard library has a provision over an open effect row, read to its tail: {got:?}"
    );
}
