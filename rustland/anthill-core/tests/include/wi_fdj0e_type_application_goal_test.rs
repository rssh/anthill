//! WI-20261107-FDJ0E — a sort's type application written as a goal or a query is a type check:
//! it holds where type checking finds the instance, and no clause is headed by one
//! (kernel-language §5.1, §5.3).
//!
//! On 524eee80 the goal `WeakOrd[T = Int64]` was the atom `WeakOrd(T: Int64)` matched against
//! clauses headed by the sort — only a written `fact WeakOrd[T = Int64]` — and never against the
//! provisions: the query answered nothing for `Int64`, `String`, `Pair[A = Int64, B = Int64]`,
//! and `rule guarded(?c) :- WeakOrd[T = Int64], WeakOrd.compare(1, 5, ?c)` answered nothing,
//! where the guard at a declared parameter read the provisions. And `fact WeakOrd[T = Red]`
//! loaded, so the goal answered true at `Red` where `requires WeakOrd[T = Red]` was refused.
//!
//! What fails with each part backed out (temporary switches, measured, then removed):
//! - the goal answered by the instance search (`BuiltinTag::TypeApplication` in `step_init`):
//!   [`the_goal_holds_where_type_checking_finds_the_instance`],
//!   [`a_guard_with_no_introducer_is_the_check`], [`an_element_written_as_a_variable_is_bound`],
//!   [`a_written_element_that_disagrees_fails`], [`an_unknown_carrier_waits`],
//!   [`a_query_is_the_same_check`], [`a_witness_provision_answers_the_goal_and_the_guard`];
//!   outside this file wi1069's `the_two_spellings_diverge_outside_the_provision`, three of
//!   wi_7exey's goal rows and wi_jb6rs's `a_sort_has_one_reading_and_names_nothing_to_apply`;
//! - the head refused (`LoadError::TypeApplicationHead`):
//!   [`a_clause_headed_by_a_type_application_is_refused`], and the refusal rows of wi1069,
//!   wi1106, wi_7exey, wi_s8jyf and wi_tcsgt; its bare-sort arm
//!   (`refuse_if_head_names_no_relation`): [`a_bare_sort_at_a_head_is_refused`];
//! - an omitted element read off the provisions that answer the rest (`open_slots_said`
//!   where the carrier's sort has no view of the spec):
//!   [`a_witness_provision_answers_the_goal_and_the_guard`] and
//!   [`an_element_written_as_a_variable_is_bound`] (both wait at `Teal`),
//!   [`no_provider_fails_the_goal_and_the_guard`] (both wait at `Float`);
//! - a carrier holding a variable waits (the `value_deep_ground` gate):
//!   [`an_unknown_carrier_waits`] (`Store[State = Buf[T = ?x]]` failed).
//!
//! [`a_sort_as_data_is_not_a_head`] passes under each, by design, and
//! [`no_provider_fails_the_goal_and_the_guard`] passes with the goal's search backed out: no
//! clause answers `Sp[C = Float]` either.

use crate::common::{load_kb_with, shown_rows, try_load_kb_with};

/// Each answer of the unary relation `{ns}.{rel}` over `src`, rendered, and whether definite.
fn rows(src: &str, rel: &str) -> Vec<(String, bool)> {
    let mut kb = load_kb_with(src);
    shown_rows(&mut kb, rel)
}

fn definite(answer: &str) -> Vec<(String, bool)> {
    vec![(answer.to_string(), true)]
}

/// One answer, with goals left to wait.
fn waits(rows: &[(String, bool)]) -> bool {
    matches!(rows, [(_, false)])
}

const ORDERED: &str = r#"namespace test.fdj0e.ord
  import anthill.prelude.{Int64, String, Float, WeakOrd, Ord, Pair}
  rule int(?r) :- WeakOrd[T = Int64], ?r <=> 1
  rule ord(?r) :- Ord[T = Int64], ?r <=> 1
  rule string(?r) :- WeakOrd[T = String], ?r <=> 1
  rule pairs(?r) :- WeakOrd[T = Pair[A = Int64, B = Int64]], ?r <=> 1
  rule pairF(?r) :- WeakOrd[T = Pair[A = Int64, B = Float]], ?r <=> 1
  rule float(?r) :- WeakOrd[T = Float], ?r <=> 1
  rule notFloat(?r) :- not(WeakOrd[T = Float]), ?r <=> 1
  rule notInt(?r) :- not(WeakOrd[T = Int64]), ?r <=> 1
  rule guarded(?c) :- WeakOrd[T = Int64], WeakOrd.compare(1, 5, ?c)
  rule plain(?c) :- WeakOrd.compare(1, 5, ?c)
  rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)
  rule cited(?c) :- cmp(1, 5, ?c)
  rule open(?r) :- WeakOrd[T = ?t], ?r <=> 1
  rule bare(?r) :- WeakOrd, ?r <=> 1
  rule late(?t) :- WeakOrd[T = ?t], ?t <=> Int64
  rule lateF(?t) :- WeakOrd[T = ?t], ?t <=> Float
end
"#;

/// THE GOAL HOLDS WHERE TYPE CHECKING FINDS THE INSTANCE: a provision (`Int64`), a conversion
/// through another spec's (`Ord`'s `provides WeakOrd[T = T]`), a conditional provision whose
/// condition holds (`Pair`'s `:- WeakOrd[A], WeakOrd[B]`); it fails where none is found
/// (`Float`, and `Pair` at a `Float` element), and its negation reads the same verdict.
#[test]
fn the_goal_holds_where_type_checking_finds_the_instance() {
    let one = definite("1");
    for rel in ["int", "ord", "string", "pairs", "notFloat"] {
        assert_eq!(rows(ORDERED, &format!("test.fdj0e.ord.{rel}")), one, "`{rel}`");
    }
    for rel in ["pairF", "float", "notInt"] {
        assert_eq!(rows(ORDERED, &format!("test.fdj0e.ord.{rel}")), vec![], "`{rel}`");
    }
}

/// A GUARD WITH NO INTRODUCER IS THE CHECK: `guarded` gives `-1`, as the call alone and the
/// guard at a declared parameter do.
#[test]
fn a_guard_with_no_introducer_is_the_check() {
    for rel in ["guarded", "plain", "cited"] {
        assert_eq!(rows(ORDERED, &format!("test.fdj0e.ord.{rel}")), definite("-1"), "`{rel}`");
    }
}

/// A CARRIER NOT KNOWN WAITS until it is: `WeakOrd[T = ?t]` and the bare `WeakOrd` answer
/// conditionally, and a later goal that binds `?t` decides it — `Int64` holds, `Float` does
/// not.
#[test]
fn an_unknown_carrier_waits() {
    assert!(waits(&rows(ORDERED, "test.fdj0e.ord.open")));
    assert!(waits(&rows(ORDERED, "test.fdj0e.ord.bare")));
    assert_eq!(rows(ORDERED, "test.fdj0e.ord.late"), definite("Int64"));
    assert_eq!(rows(ORDERED, "test.fdj0e.ord.lateF"), vec![]);
    // A carrier with a variable inside waits too, and holds once it is bound.
    let src = with_tail(
        STORE,
        "  rule partial(?r) :- Store[State = Buf[T = ?x]], ?r <=> 1\n  \
         rule partialBound(?r) :- Store[State = Buf[T = ?x]], ?x <=> Int64, ?r <=> 1\n",
    );
    assert!(waits(&rows(&src, "test.fdj0e.store.partial")));
    assert_eq!(rows(&src, "test.fdj0e.store.partialBound"), definite("1"));
}

const STORE: &str = r#"namespace test.fdj0e.store
  import anthill.prelude.{Int64, String, Bool}
  sort Buf
    sort T = ?
    entity buf(v: T)
  end
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  sort Carrier
    provides Store[State = Buf[T = Int64]]
    operation peek(s: Buf[T = Int64]) -> Int64 = s.v
  end
  rule viaS(?r) :- Store[State = Buf[T = String]], Store.peek(buf(v: 1), ?r)
  rule viaB(?r) :- Store[State = Buf[T = Bool]], Store.peek(buf(v: 1), ?r)
  rule viaI(?r) :- Store[State = Buf[T = Int64]], Store.peek(buf(v: 1), ?r)
end
"#;

/// A WRITTEN ELEMENT THAT DISAGREES FAILS (WI-20260929-9SNR2's addendum on WI-20261021-Z2P21):
/// nothing provides `Store` at `Buf[T = String]` or `Buf[T = Bool]`, and the agreeing element
/// answers `1`.
#[test]
fn a_written_element_that_disagrees_fails() {
    assert_eq!(rows(STORE, "test.fdj0e.store.viaS"), vec![]);
    assert_eq!(rows(STORE, "test.fdj0e.store.viaB"), vec![]);
    assert_eq!(rows(STORE, "test.fdj0e.store.viaI"), definite("1"));
}

/// `Sp`, a carrier `C` and an element `P`. `Red` provides `Sp` at `P = Int64` itself; `Teal` is
/// provided for by one witness, `Green` by two at different elements; nothing provides `Sp` at
/// `Float`.
const ELEMENTS: &str = r#"namespace test.fdj0e.el
  import anthill.prelude.{Int64, Bool, Float}
  sort Sp
    sort C = ?
    sort P = ?
    operation crecv(x: C) -> Int64 = 0
  end
  sort Red
    entity red
    provides Sp[C = Red, P = Int64]
  end
  sort Teal
    entity teal
  end
  sort ByT
    provides Sp[C = Teal, P = Int64]
  end
  sort Green
    entity green
  end
  sort ByA
    provides Sp[C = Green, P = Int64]
  end
  sort ByB
    provides Sp[C = Green, P = Bool]
  end
  rule redP(?p) :- Sp[C = Red, P = ?p]
  rule tealP(?p) :- Sp[C = Teal, P = ?p]
  rule greenP(?p) :- Sp[C = Green, P = ?p]
  rule greenBool(?r) :- Sp[C = Green, P = Bool], ?r <=> 1
  rule redBool(?r) :- Sp[C = Red, P = Bool], ?r <=> 1
  rule tealHolds(?r) :- Sp[C = Teal], ?r <=> 1
  rule floatHolds(?r) :- Sp[C = Float], ?r <=> 1
  rule gg[A](?x: A, ?r) :- Sp[C = A], Sp.crecv(?x, ?r)
  rule ggTeal(?r) :- gg(teal, ?r)
end
"#;

/// AN ELEMENT WRITTEN AS A VARIABLE IS BOUND to the one the provision writes; where two
/// witnesses write two, it waits, and the element written decides (`Bool` holds). An element
/// the provision does not write fails.
#[test]
fn an_element_written_as_a_variable_is_bound() {
    assert_eq!(rows(ELEMENTS, "test.fdj0e.el.redP"), definite("Int64"));
    assert_eq!(rows(ELEMENTS, "test.fdj0e.el.tealP"), definite("Int64"));
    assert!(waits(&rows(ELEMENTS, "test.fdj0e.el.greenP")));
    assert_eq!(rows(ELEMENTS, "test.fdj0e.el.greenBool"), definite("1"));
    assert_eq!(rows(ELEMENTS, "test.fdj0e.el.redBool"), vec![]);
}

/// A WITNESS'S PROVISION ANSWERS THE GOAL AND THE GUARD alike: `Sp[C = Teal]` holds, and the
/// guard at `teal` gives `0`, as an operation's `requires Sp[C = A]` at `Teal` is supplied. Both
/// waited on 524eee80 — the guard's read of the omitted `P` looked at `Teal`'s own provisions
/// only.
#[test]
fn a_witness_provision_answers_the_goal_and_the_guard() {
    assert_eq!(rows(ELEMENTS, "test.fdj0e.el.tealHolds"), definite("1"));
    assert_eq!(rows(ELEMENTS, "test.fdj0e.el.ggTeal"), definite("0"));
    let call = with_tail(
        ELEMENTS,
        "  operation needs[A](x: A) -> Int64 requires Sp[C = A] = 1\n  operation callT() -> Int64 = needs(teal)\n",
    );
    assert!(try_load_kb_with(&call).is_ok(), "the operation twin is supplied at `Teal`");
}

/// NO PROVIDER FAILS THE GOAL AND THE GUARD: a requirement known unavailable is no undecided
/// answer. Both waited on 524eee80, the guard leaving `find_dictionary(Sp[C = Float], …)`. The
/// guard is asked by a query: a rule-body goal `gg(1.5, ?r)` at concrete types is refused at
/// load, nothing providing `Sp[C = Float]`, as an operation's call is.
#[test]
fn no_provider_fails_the_goal_and_the_guard() {
    assert_eq!(rows(ELEMENTS, "test.fdj0e.el.floatHolds"), vec![]);
    let mut kb = load_kb_with(ELEMENTS);
    let goal = crate::common::query_pattern_term(&mut kb, "test.fdj0e.el.gg(1.5, ?r)");
    let sols = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
    assert!(sols.is_empty(), "the guard at `Float` fails: {} solution(s)", sols.len());
    let refused = try_load_kb_with(&with_tail(ELEMENTS, "  rule ggFloat(?r) :- gg(1.5, ?r)\n"))
        .err()
        .expect("the rule-body goal at `Float` is refused at load");
    assert!(refused.iter().any(|e| e.contains("nothing provides `Sp[C = Float]`")), "{refused:?}");
}

/// `src` with `tail` written at the end of its namespace.
fn with_tail(src: &str, tail: &str) -> String {
    format!("{}{tail}end\n", src.strip_suffix("end\n").expect("the namespace closes last"))
}

/// A QUERY IS THE SAME CHECK as the goal in a rule body. The effect-row anchor's rows pass
/// with the goal's search backed out too, by the loader's bridge fact (WI-320), which the
/// search no longer reads.
#[test]
fn a_query_is_the_same_check() {
    let mut kb = load_kb_with(ORDERED);
    let p = "anthill.prelude";
    for (pattern, holds) in [
        (format!("{p}.WeakOrd[T = {p}.Int64]"), true),
        (format!("{p}.WeakOrd[T = {p}.Pair[A = {p}.Int64, B = {p}.String]]"), true),
        (format!("{p}.WeakOrd[T = {p}.Float]"), false),
        // The effect-row kind anchor holds at an effect row, as type checking reads it, and
        // never at a type that is no row.
        (format!("{p}.EffectsRuntime[Effects = {{}}]"), true),
        (format!("{p}.EffectsRuntime[Effects = {p}.Int64]"), false),
    ] {
        let goal = crate::common::query_pattern_term(&mut kb, &pattern);
        let sols = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
        let got = sols.len() == 1 && sols[0].is_definite();
        assert_eq!(got, holds, "`{pattern}`: {} solution(s)", sols.len());
        if !holds {
            assert!(sols.is_empty(), "`{pattern}` fails outright");
        }
    }
}

/// A CLAUSE HEADED BY A TYPE APPLICATION IS REFUSED: a spec's bracket, by name and by position,
/// qualified, as a rule and in a multi-head rule, naming `provides`; a sort with constructors
/// — `Pair`, an eponymous sort's type face — which nothing provides, naming a relation's
/// argument instead, and that advised repair loads and answers. Type checking never read such
/// a clause, so `WeakOrd[T = Red]` answered true from it where `requires WeakOrd[T = Red]` is
/// refused.
#[test]
fn a_clause_headed_by_a_type_application_is_refused() {
    for (head, sort, data) in [
        ("fact WeakOrd[T = Red]", "WeakOrd", false),
        ("fact WeakOrd[Red]", "WeakOrd", false),
        ("fact anthill.prelude.WeakOrd[T = Red]", "WeakOrd", false),
        ("rule WeakOrd[T = Red] :- true", "WeakOrd", false),
        ("rule two: WeakOrd[T = Red], hh(1) :- true", "WeakOrd", false),
        ("fact Pair[A = Int64, B = Red]", "Pair", true),
        ("fact Box[V = Int64]", "Box", true),
    ] {
        let src = heads(head);
        let errs = try_load_kb_with(&src).err().unwrap_or_else(|| panic!("`{head}` loaded clean"));
        let want = format!("`{sort}[…]` heads a clause, which claims an instance of the sort `{sort}`");
        assert_eq!(errs.iter().filter(|e| e.contains(&want)).count(), 1, "`{head}`: {errs:?}");
        let repair = match data {
            false => format!("`provides {sort}[…]`"),
            true => format!("`{sort}` declares constructors, so nothing provides it"),
        };
        assert!(errs.iter().any(|e| e.contains(&repair)), "`{head}`: {errs:?}");
    }
    // The advised repair for a sort with constructors: the type as data in a relation.
    let src = heads("fact holds(Box[V = Int64])\n  rule seenBox(?r) :- holds(Box[V = Int64]), ?r <=> 1");
    assert_eq!(rows(&src, "test.fdj0e.head.seenBox"), definite("1"));
}

/// A BARE SORT AT A HEAD IS ITS TYPE WITH EVERY PARAMETER OPEN, `fact WeakOrd` being `fact
/// WeakOrd[T = ?]`, and is refused as the bracket is: a spec, qualified, as a rule, in a
/// multi-head rule, a sort with constructors at namespace level and in its own body. It was
/// stored as the nullary atom `WeakOrd`, which only the bare goal found — not `WeakOrd[T = ?]`,
/// not `WeakOrd[T = Float]` — and which type checking never read: the goal held where
/// `requires WeakOrd` is refused. A constructor's instance at a head is no sort, and loads.
#[test]
fn a_bare_sort_at_a_head_is_refused() {
    for (head, sort, data) in [
        ("fact WeakOrd", "WeakOrd", false),
        ("fact anthill.prelude.WeakOrd", "WeakOrd", false),
        ("rule WeakOrd :- true", "WeakOrd", false),
        ("rule two: WeakOrd, hh(1) :- true", "WeakOrd", false),
        ("fact Red", "Red", true),
        ("sort Car\n    entity car\n    fact Car\n  end", "Car", true),
    ] {
        let errs = try_load_kb_with(&heads(head)).err().unwrap_or_else(|| panic!("`{head}` loaded clean"));
        let want = format!("`{sort}` heads a clause, which claims an instance of the sort `{sort}`");
        assert_eq!(errs.iter().filter(|e| e.contains(&want)).count(), 1, "`{head}`: {errs:?}");
        let repair = match data {
            false => format!("`provides {sort}[…]`"),
            true => format!("`{sort}` declares constructors, so nothing provides it"),
        };
        assert!(errs.iter().any(|e| e.contains(&repair)), "`{head}`: {errs:?}");
    }
    // The advised repair for the bare sort with constructors: the type as data in a relation.
    let src = heads("fact holds(Red)\n  rule seenRed(?r) :- holds(Red), ?r <=> 1");
    assert_eq!(rows(&src, "test.fdj0e.head.seenRed"), definite("1"));
    let src = heads("fact Box\n  fact red\n  rule seenBare(?r) :- Box(v: ?v), red, ?r <=> 1");
    assert_eq!(rows(&src, "test.fdj0e.head.seenBare").len(), 1, "a constructor's instance at a head loads");
}

/// A SORT AS DATA IS NOT A HEAD: in a relation's argument, and an eponymous constructor's
/// application, load and answer as before.
#[test]
fn a_sort_as_data_is_not_a_head() {
    let src = heads("fact holds(WeakOrd[T = Red])\n  fact Box(v: 1)\n  rule seen(?r) :- holds(WeakOrd[T = Red]), Box(v: ?r)");
    assert_eq!(rows(&src, "test.fdj0e.head.seen"), definite("1"));
}

fn heads(line: &str) -> String {
    format!(
        r#"namespace test.fdj0e.head
  import anthill.prelude.{{Int64, WeakOrd, Pair}}
  sort Red
    entity red
  end
  sort Box
    sort V = ?
    entity Box(v: Int64)
  end
  {line}
end
"#
    )
}
