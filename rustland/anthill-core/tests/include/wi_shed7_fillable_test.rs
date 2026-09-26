//! WI-20260925-SHED7 (proposal 060 §2.3, proposal 067) — `SortDomain provides Fillable`:
//! a sort's domain is its `SortDomain`'s `fill`, derived PER ENTITY and PER FIELD, reached
//! through a DICTIONARY, and a typed head is ONE goal after the body:
//!
//! ```text
//! rule p(?x: T) :- body      ≡      rule p(?x) :- body, SortDomain[T].fill(?x)
//! ```
//!
//! THE MEASURED DEFECT this closes (on `861b3013`): `rule el(?x: T) :- true` in `sort Wrap[T]`
//! answered NOTHING for `Wrap.el(7)` and `Wrap.el([red()])`, and undecided for `[1, 2]`,
//! `none()` and `[]`; `q(?h) :- Wrap.same([?h], [red()])` answered nothing;
//! `Wrap[T = Colour].dom.takeN(5)` floundered and `List[T = Letter].domain` was refused at
//! load. Each row below is one of those, driven.
//!
//! AN INFINITE GENERATOR IS READ LAZILY (`common::first_unary`), never drained: an eager
//! drain stops only at the resolver's depth cap, and a count taken there is a truncation.
//!
//! BACK-OUT, measured one axis at a time over the domain suites of `wi_tests` (`wi743`,
//! `wi_5g28a`, `wi_wt8wg`, `wi_shed7`, `wi_pw9a0`, `wi1040`, `wi742`, `wi476` — 153 rows), each
//! run, not predicted:
//!  * [P] the OPEN pin (`typing::pin_bound_from_value_open` → the closed one) — 0 red since
//!    the EARLY guard (code-review round 2): it pins `?e` from `?b` in front of the body, so
//!    no fill waits on the open pin. `wi_5g28a_rule_head_type_variables_test`'s axis B — all
//!    three pin sites together — reddens `the_second_column_pins_the_first_columns_element`
//!    and nine rows more.
//!  * [L] the SHARED LAYOUT (`SortDomainEntry::sub_offset` forced to 0, the row pass's
//!    layout check off) — exactly `a_dictionary_the_typer_builds_is_read_at_its_layout`.
//!  * [C] PER-FIELD conditions (every parameter a condition) — exactly
//!    `conditions_are_per_field`.
//!  * [F] the bound's FILLABILITY test in the sweep (a bound filled whenever its head has a
//!    domain) — 3, all `wi_pw9a0`'s introducer rows: a spec-recorded bound, filled, errors.
//!  * [S] the STRUCTURAL route of a `SortDomain` read at a citation (the general search) — 3:
//!    `a_citation_at_a_concrete_instance_enumerates`, `a_parameterised_value_face_is_cited`
//!    and WT8WG's `a_parameterised_sorts_value_face_is_cited_through_its_bracket` — no
//!    provision row exists for the search to find, so nothing is routed.
//!  * [T] TRUSTING a filled `SortDomain` read (checked instead, against the value's type) — 6:
//!    every row whose dictionary a citation or a caller hands in.
//!
//! The rows no axis reddens — the six `Wrap.el` values, `[]`-first skeletons, a field that
//! cannot be filled — are the ticket's measured baseline: each answered wrongly on
//! `861b3013`, and each is the mechanism as a whole rather than one of its parts.

use anthill_core::eval::Value;
use anthill_core::persistence::print::TermPrinter;

const PROGRAM: &str = r#"
namespace shed7
  import anthill.prelude.{List, Int64, String, Option, Error, EmptyStream}

  sort Colour
    entity red
    entity green
    entity blue
  end

  sort Letter
    entity a
    entity b
  end

  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
    rule same(?a: T, ?b: T) :- true
    rule dom(?x: Wrap[T = T]) :- true
  end

  rule elRed(1)     :- Wrap.el(red())
  rule elInt(1)     :- Wrap.el(7)
  rule elColours(1) :- Wrap.el([red()])
  rule elInts(1)    :- Wrap.el([1, 2])
  rule elNone(1)    :- Wrap.el(Option.none())
  rule elNil(1)     :- Wrap.el([])
  rule q(?h)        :- Wrap.same([?h], [red()])

  rule ints(?w: List[T = Int64]) :- true

  sort Driver
    operation concrete() -> Int64 effects {Error} = Wrap[T = Colour].dom.takeN(5).length()
    operation letters() -> Int64 effects {Error} = List[T = Letter].domain.takeN(5).length()
    operation oneInt() -> Int64 effects {Error} = ints.takeN(1).length()
    operation threeInts() -> Int64 effects {Error} = ints.takeN(3).length()
  end
end
"#;

fn show(kb: &anthill_core::kb::KnowledgeBase, v: &Value) -> String {
    match v {
        Value::Node(occ) => TermPrinter::new(kb).print_occurrence(occ),
        Value::Term { id, .. } => TermPrinter::new(kb).print_term(*id),
        other => format!("{other:?}"),
    }
}

/// `qn`'s answers, rendered, each marked whether it is definite.
fn rows(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<(String, bool)> {
    crate::common::query_unary(kb, qn)
        .into_iter()
        .map(|(v, d)| (show(kb, &v), d))
        .collect()
}

/// The one DEFINITE answer of a unary relation, as an `Int64` — `None` for anything else.
fn one_definite_int(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Option<i64> {
    match crate::common::query_unary(kb, qn).as_slice() {
        [(v, true)] => crate::common::scalar_int(kb, v),
        _ => None,
    }
}

fn drive(entry: &str) -> Result<i64, String> {
    let mut interp = crate::common::interp_for(PROGRAM);
    match interp.call(&format!("shed7.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => Ok(n),
        other => Err(format!("{other:?}")),
    }
}

/// THE CASE — a type-variable bound reached with no caller DECIDES every value it is handed:
/// one definite row each. Proposal 060 §2's table holds a bound value that conforms and is a
/// member of its type's domain, and every type has one (user, 2026-09-25): `7` is filled by
/// `Int64`'s waiting check, `[red()]` by `List`'s `fill` through its element's, and `[]` and
/// `none()` take the case that reads no element — `[]` is a `List[?]` whose condition is
/// resolved only when `fill` reads it, and its `nil` case never does.
///
/// Passes under [P] BY MEASUREMENT: the closed pin reads `[]`'s `List[T = <placeholder>]` as
/// determined — `value_type_term`'s placeholder is no variable to it — and the `nil` case
/// never reads the element. What the open pin buys is the TIE, below.
#[test]
fn a_type_variable_bound_decides_every_value_it_is_handed() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    for r in ["elRed", "elInt", "elColours", "elInts", "elNone", "elNil"] {
        assert_eq!(
            rows(&mut kb, &format!("shed7.{r}")),
            vec![("1".to_string(), true)],
            "`{r}`: one definite row",
        );
    }
}

/// THE TIE — one bound on two columns. `?a = [?h]` reads `T` as `List[T = ?e]`, the element
/// unknown, and `?h`'s element fill WAITS on `?e`; `?b = [red()]` pins `?e := Colour`, and
/// the fill resumes: `?h` ranges over `Colour`. Filling `?h` from "the domain of any value"
/// instead would answer `?h` free and definite, which is wrong — `?b` makes it a `Colour`.
///
/// All three pin sites backed out together (`wi_5g28a_rule_head_type_variables_test`'s axis
/// B) redden it — the row flounders; [P] alone no longer does, since the early guard pins
/// `?e` from `?b` before any fill waits on `[?h]`'s open type.
#[test]
fn the_second_column_pins_the_first_columns_element() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(
        rows(&mut kb, "shed7.q"),
        vec![
            ("red".to_string(), true),
            ("green".to_string(), true),
            ("blue".to_string(), true),
        ],
    );
}

/// A CITATION AT A CONCRETE INSTANCE: the typer routes `dom`'s `SortDomain` read at
/// `Wrap[T = Colour]` — a dictionary CONSTRUCTED from the type, no provider searched
/// (`typing::sort_domain_route`) — and `Wrap`'s `fill` reads its element's sub-dictionary
/// out of it. On `861b3013` this floundered.
///
/// [S] reddens it: searched among providers instead, the read finds no provision row — none
/// is derived for a program that writes no `SortDomain` requirement — routes nothing, and
/// the citation flounders.
#[test]
fn a_citation_at_a_concrete_instance_enumerates() {
    assert_eq!(drive("concrete"), Ok(3));
}

/// THE PARAMETERISED VALUE FACE — `List`'s `fill` is `List.domain`, cited like any relation;
/// it was a load error naming 5G28A. Lists come out by length: `[]`, `[a]`, `[b]`,
/// `[a, a]`, `[b, a]`. [S] reddens it, as it does the row above.
#[test]
fn a_parameterised_value_face_is_cited() {
    assert_eq!(drive("letters"), Ok(5));
}

/// A PRIMITIVE HAS NO CASES: `Int64`'s `fill` is the waiting type check, so
/// `List[T = Int64]` fills to skeletons — `[]` definitely, then `[?a]`, undecided until
/// something binds `?a`. Read lazily; through a `Relation` the definite prefix is one row
/// and the first undecided row raises, as it did before this ticket.
#[test]
fn a_primitive_fills_to_skeletons() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let first = crate::common::first_unary(&mut kb, "shed7.ints", 3);
    let rendered: Vec<(String, bool)> = first.iter().map(|(v, d)| (show(&kb, v), *d)).collect();
    assert_eq!(rendered.len(), 3, "an infinite generator yields its prefix: {rendered:?}");
    assert!(rendered[0].1, "`[]` is definite: {rendered:?}");
    assert!(
        !rendered[1].1 && !rendered[2].1,
        "`[?a]` and `[?a, ?b]` wait on the `Int64` check: {rendered:?}",
    );
    assert_eq!(drive("oneInt"), Ok(1));
    let three = drive("threeInts").expect_err("a conditional row raises through a `Relation`");
    assert!(three.contains("Raised"), "{three}");
}

/// A RIGID instantiated at a PARAMETRIC sort: `countAt[X = Wrap[T = Colour]]()` resolves
/// `SortDomain[T = Wrap[T = Colour]]` at its call site through the provision rows — the one
/// place the general requirement machinery builds a `SortDomain` dictionary — and `el`'s
/// `fill` reads `Wrap`'s element out of it.
const RIGID: &str = r#"
namespace shed7r
  import anthill.prelude.{Int64, Error, EmptyStream}
  import anthill.reflect.SortDomain

  sort Colour
    entity red
    entity green
    entity blue
  end

  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end

  sort Driver
    operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] =
      Wrap[T = X].el.takeN(9).length()
    operation firstAt[X]() -> X effects {Error, Error[EmptyStream]} requires SortDomain[T = X] =
      Wrap[T = X].el.head.x
    operation wrapped() -> Int64 effects {Error} = countAt[X = Wrap[T = Colour]]()
    operation firstWrapped() -> Wrap[T = Colour] effects {Error, Error[EmptyStream]} =
      firstAt[X = Wrap[T = Colour]]()
  end
end
"#;

/// ONE LAYOUT FOR EVERY `SortDomain` DICTIONARY. The typer lays the call site's dictionary out
/// by its requirement chain — `SortDomain`'s own `Fillable` conversion first, then the
/// condition — and `Wrap`'s derived `fill` reads its element at that offset.
///
/// [L] reddens it, and the VALUE is what shows it: read at sub 0, the element is handed
/// `Wrap`'s own `Fillable` dictionary, which fills it as a `Wrap` again — three rows still,
/// every one `wrap(wrap(…))`. A count alone passes under the back-out.
#[test]
fn a_dictionary_the_typer_builds_is_read_at_its_layout() {
    let mut interp = crate::common::interp_for(RIGID);
    match interp.call("shed7r.Driver.wrapped", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 3, "`wrap(red())`, `wrap(green())`, `wrap(blue())`"),
        other => panic!("expected an Int64, got {other:?}"),
    }
    let first = interp
        .call("shed7r.Driver.firstWrapped", &[])
        .expect("the first row");
    let rendered = match &first {
        Value::Node(occ) => TermPrinter::new(interp.kb()).print_occurrence(occ),
        other => format!("{other:?}"),
    };
    assert_eq!(
        rendered.matches("wrap").count(),
        1,
        "one `wrap` around a colour, got `{rendered}`",
    );
    assert!(rendered.contains("red"), "the first colour, got `{rendered}`");
}

/// A sort with no constructors that is no primitive — nothing fills it.
const FIELDS: &str = r#"
namespace shed7f
  import anthill.prelude.{List, Int64}

  sort Colour
    entity red
    entity green
    entity blue
  end

  sort Opaque = ?

  -- `O` is a parameter no field fills, so it is NO CONDITION of `Tagged`'s `SortDomain`
  sort Tagged[T, O]
    entity tag(v: T)
  end

  sort Holder
    entity hold(o: Opaque)
  end

  sort Box
    entity box(c: Colour, n: Int64)
  end

  rule tagged(?x: Tagged[T = Colour, O = Opaque]) :- true
  rule held(?x: Holder) :- true
end
"#;

/// CONDITIONS ARE PER FIELD, NOT PER PARAMETER (060 §2.3). `Tagged[T = Colour, O = Opaque]`
/// is fillable although `Opaque` has no domain, because no field of `Tagged` is an `O`.
///
/// [C] reddens it: with every parameter a condition, `O = Opaque` is unfillable and the bound
/// keeps only the conformance check — mode (out) flounders.
#[test]
fn conditions_are_per_field() {
    let mut kb = crate::common::load_kb_with(FIELDS);
    let answers = rows(&mut kb, "shed7f.tagged");
    assert_eq!(answers.len(), 3, "one `tag` per colour: {answers:?}");
    assert!(answers.iter().all(|(_, d)| *d), "every row definite: {answers:?}");
}

/// A FIELD NOTHING CAN FILL leaves its sort without a domain, and says why — S3a gave such a
/// sort a row it could not honour. A concrete field that CAN be filled — `Box`'s `Colour`
/// and `Int64` — is no obstacle.
#[test]
fn a_field_that_cannot_be_filled_leaves_its_sort_without_a_domain() {
    let mut kb = crate::common::load_kb_with(FIELDS);
    let holder = kb.try_resolve_symbol("shed7f.Holder").expect("Holder");
    assert!(!kb.has_sort_domain(holder));
    let why = kb
        .sort_domain_decline_reason(holder)
        .expect("a declined sort says why");
    assert!(why.contains("cannot be filled"), "{why}");
    let boxed = kb.try_resolve_symbol("shed7f.Box").expect("Box");
    assert!(kb.has_sort_domain(boxed), "a `Colour` and an `Int64` field can both be filled");
    // With no domain, the bound is the conformance check alone: mode (out) cannot generate,
    // and flounders — undecided, never an empty answer.
    let held = rows(&mut kb, "shed7f.held");
    assert!(
        !held.is_empty() && held.iter().all(|(_, d)| !*d),
        "undecided rows only: {held:?}",
    );
}

// ── Review fixes: each row drives one fix, and fails with it backed out ─────

/// A sort's OWN operation named `fill` beside its derived domain. The `fill` row the operation
/// table once held for the domain relation overwrote the operation's, so `Filler.fill(tank(…))`
/// dispatched to a relation. FAILS with that row recorded over the operation's (`go` raises);
/// and with `lower_apply_domain` reading the provider's `fill` from the operation table instead
/// of its `SortDomain` entry, `tanks` loses its row (the table names the operation).
#[test]
fn a_sorts_own_fill_operation_keeps_its_row() {
    const TANK: &str = r#"
namespace shed7tank
  import anthill.prelude.{List, Int64}

  sort Filler
    sort T = ?
    operation fill(x: T) -> Int64
  end

  sort Tank
    entity tank(level: Int64)
    provides Filler[T = Tank]
    operation fill(x: Tank) -> Int64 = 100
  end

  rule tanks(?w: List[T = Tank]) :- ?w <=> [tank(level: 3)]

  sort Driver
    operation useFill[X](x: X) -> Int64 requires Filler[T = X] = Filler.fill(x)
    operation go() -> Int64 = useFill(tank(level: 1))
  end
end
"#;
    let mut interp = crate::common::interp_for(TANK);
    match interp.call("shed7tank.Driver.go", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 100, "`Tank`'s own `fill`"),
        other => panic!("expected an Int64, got {other:?}"),
    }
    let mut kb = crate::common::load_kb_with(TANK);
    let answers = rows(&mut kb, "shed7tank.tanks");
    assert!(answers.len() == 1 && answers[0].1, "`Tank`'s domain still fills the element: {answers:?}");
}

/// A value whose type has NO domain — a tuple — reached by a derived `fill` and by a
/// type-variable bound. What such a type answers is the CONFORMANCE question, as the retired
/// `domain_leaf` did: `[(1, 2)]` is a `List` whose element conforms, and `(1, 2)` a `T` — and
/// the CONTROL, `tieBad`: an element bound AFTER its tuple type was pinned by the other column
/// is checked when it arrives, and `("x", "y")` is refused.
/// FAILS with the 2-ary `apply_domain` refusing a no-domain type again (`tupleList` becomes an
/// error and a conditional row); with the typed head's read FAILING on one (`elTuple` answers
/// nothing); and with the 2-ary conformance arm answering `Holds` unchecked (`tieBad` answers).
#[test]
fn a_type_with_no_domain_is_checked_not_refused() {
    const NO_DOMAIN: &str = r#"
namespace shed7nd
  import anthill.prelude.{List, Int64}

  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end

  rule anyList(?w: List) :- true
  rule tie(?a: List[T = ?t], ?b: List[T = ?t]) :- true

  rule tupleList(1) :- anyList([(1, 2)])
  rule elTuple(1)   :- Wrap.el((1, 2))
  rule tieBad(?h)   :- tie([(1, 2)], [?h]), ?h <=> ("x", "y")
end
"#;
    let mut kb = crate::common::load_kb_with(NO_DOMAIN);
    for rel in ["shed7nd.tupleList", "shed7nd.elTuple"] {
        let answers = rows(&mut kb, rel);
        assert!(answers.len() == 1 && answers[0].1, "{rel}: one definite row, got {answers:?}");
    }
    let refused = rows(&mut kb, "shed7nd.tieBad");
    assert!(refused.is_empty(), "`(\"x\", \"y\")` is no `(Int64, Int64)`: {refused:?}");
}

/// A typed head over a body with a CUT. A cut commits before a test AFTER it runs:
/// `classify(5, ?c)` pruned the untyped clause, then failed the appended check — no answers.
/// The EARLY guard tests the bound `5` before the body. FAILS with the early guard backed out
/// (`cls` answers nothing where it answers `2`).
#[test]
fn a_cut_does_not_commit_before_the_type_check() {
    const CUT: &str = r#"
namespace shed7cut
  import anthill.prelude.Int64

  sort Colour
    entity red
    entity green
  end

  rule classify(?x: Colour, ?c) :- ?c <=> 1, !
  rule classify(?x, ?c) :- ?c <=> 2
  rule cls(?c) :- classify(5, ?c)
end
"#;
    let mut kb = crate::common::load_kb_with(CUT);
    let answers = rows(&mut kb, "shed7cut.cls");
    assert_eq!(answers, vec![("Int(2)".to_string(), true)], "`5` is no `Colour`: the second clause answers");
}

// ── Review fixes, round 2: each row drives one fix, and fails with it backed out ─────

/// THE TYPE TEST RUNS BEFORE THE BODY on a value the call already bound — the EARLY guard.
/// `inc`'s body `add(?x, 1, ?y)` FAULTS on a `Float` — an arithmetic carrier mismatch is not a
/// refutation — so were the test only after the body, `not(incs(2.5))` would be undecided;
/// with it, `2.5` is refused before `add` runs and the negation holds. FAILS with the early
/// guard backed out (the fill alone, after the body): `noInc` has no definite row.
#[test]
fn a_bound_value_is_type_tested_before_the_body() {
    const EARLY: &str = r#"
namespace shed7early
  import anthill.prelude.{Int64, Float}
  import anthill.prelude.Numeric.{add}

  fact reading(2.5)
  rule inc(?x: Int64, ?y) :- add(?x, 1, ?y)
  rule incs(?x) :- inc(?x, ?)
  rule noInc(?z) :- reading(?v), not(incs(?v)), ?z <=> 1
end
"#;
    let mut kb = crate::common::load_kb_with(EARLY);
    assert_eq!(
        one_definite_int(&mut kb, "shed7early.noInc"),
        Some(1),
        "`2.5` is no `Int64`, refused before `add` runs",
    );
}

/// A type argument a field's type leaves UNWRITTEN is read off the value: `Holder`'s field is
/// `Pair2[A = Int64]`, `B` unwritten, and the bound `holder(p: pr(a: 1, b: 2))` pins `B` from
/// `2` and fills it. FAILS with the `Unpinned` read backed out (the condition waits on its
/// fresh variable for ever): `okOne` is a floundered, conditional row.
#[test]
fn an_unwritten_type_argument_is_read_off_the_value() {
    const UNWRITTEN: &str = r#"
namespace shed7unwritten
  import anthill.prelude.Int64

  sort Pair2
    sort A = ?
    sort B = ?
    entity pr(a: A, b: B)
  end

  sort Holder
    entity holder(p: Pair2[A = Int64])
  end

  rule ok(?h: Holder) :- true
  rule okOne(1) :- ok(holder(p: pr(a: 1, b: 2)))
end
"#;
    let mut kb = crate::common::load_kb_with(UNWRITTEN);
    assert_eq!(
        one_definite_int(&mut kb, "shed7unwritten.okOne"),
        Some(1),
        "a ground, well-typed value, definitely",
    );
}

/// A field typed by an ALIAS has its target's domain: under `sort Radius = Int64`, `Shape`'s
/// `circle(r: Radius)` fills as `circle(r: Int64)` would, so `anyShape` enumerates `dot`
/// definitely and accepts `circle(r: 3)`. FAILS with `dealias_type` backed out in the
/// derivation: `Radius` has no `SortDomain`, `Shape` is declined, and `anyShape`'s bound keeps
/// only the waiting conformance check — no definite row at all.
#[test]
fn an_aliased_field_is_filled_as_its_target() {
    const ALIAS: &str = r#"
namespace shed7alias
  import anthill.prelude.Int64

  sort Radius = Int64

  sort Shape
    entity dot
    entity circle(r: Radius)
  end

  rule anyShape(?x: Shape) :- true
  rule isCircle(1) :- anyShape(circle(r: 3))
end
"#;
    let mut kb = crate::common::load_kb_with(ALIAS);
    let answers = rows(&mut kb, "shed7alias.anyShape");
    assert!(
        answers.iter().any(|(r, d)| *d && r.contains("dot")),
        "`Shape` has a domain, and `dot` is in it: {answers:?}",
    );
    assert_eq!(one_definite_int(&mut kb, "shed7alias.isCircle"), Some(1));
}

/// A sort with a WI-452 MARKED structured parameter declared before the one a field fills: the
/// condition is `A`, `Tagged`'s SECOND declared type parameter. The written `requires
/// SortDomain[T = X]` resolves `SortDomain[T = Tagged[F = List, A = Colour]]` through the
/// provision row, and `el`'s `fill` fills `value` from `Colour`: three rows. FAILS with the row
/// conditioned on the `j`-th declared parameter — `F` — where `A` is meant.
#[test]
fn a_condition_is_the_parameter_the_sort_declares_for_it() {
    const MARKED: &str = r#"
namespace shed7marked
  import anthill.prelude.{Int64, Error, List}
  import anthill.reflect.SortDomain

  sort Colour
    entity red
    entity green
    entity blue
  end

  sort Tagged[F[T], A]
    entity tag(value: A)
  end

  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end

  sort Driver
    operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] =
      Wrap[T = X].el.takeN(9).length()
    operation tagged() -> Int64 effects {Error} = countAt[X = Tagged[F = List, A = Colour]]()
  end
end
"#;
    let mut interp = crate::common::interp_for(MARKED);
    match interp.call("shed7marked.Driver.tagged", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 3, "`tag(value: red())`, `…green()`, `…blue()`"),
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// A provider's `fill` is found through its `SortDomain` entry, so its OPERATION table holds
/// operations only: `Dictionary.ops` over an `Int64` dictionary lists no `Int64.domain`, a
/// relation that cannot be applied. FAILS with the `(S, fill) ↦ S.domain` rows recorded again.
#[test]
fn a_domain_relation_is_no_row_of_the_operation_table() {
    let interp = crate::common::interp_for(PROGRAM);
    let int64 = interp
        .kb()
        .resolve_symbol("anthill.prelude.Int64");
    let rows: Vec<String> = interp
        .kb()
        .sort_ops_for_impl(int64)
        .into_iter()
        .map(|op| interp.kb().qualified_name_of(op).to_string())
        .filter(|qn| qn.ends_with(".domain") || qn.ends_with(".__fill"))
        .collect();
    assert!(rows.is_empty(), "no domain relation among `Int64`'s operations: {rows:?}");
}

/// A sort from an EARLIER load phase that a later phase makes provide a spec with an
/// operation named `fill` dispatches that operation: `Filler.fill(red())` answers the
/// provision's `42`. FAILS with the `fill` rows recorded again: phase 1's `(Colour, fill) ↦
/// Colour.domain` row stands where phase 2's provision would bind `fill`, and the call runs
/// the relation.
#[test]
fn a_later_phases_fill_operation_is_not_shadowed() {
    const PHASE1: &str = r#"
namespace shed7phase
  sort Colour
    entity red
    entity blue
  end
end
"#;
    const PHASE2: &str = r#"
namespace shed7phase2
  import anthill.prelude.Int64
  import shed7phase.Colour
  import shed7phase.Colour.{red}

  sort Filler
    sort T = ?
    operation fill(x: T) -> Int64
  end

  operation colourFill(x: Colour) -> Int64 = 42

  sort Driver
    operation go() -> Int64 = Filler.fill(red())
  end
end

namespace shed7phase.Colour
  import shed7phase2.{Filler, colourFill}
  provides Filler[T = Colour, fill = colourFill]
end
"#;
    let mut kb = crate::common::load_kb_with(PHASE1);
    let second = anthill_core::parse::parse(PHASE2).expect("parse the second phase");
    if let Err(errs) =
        anthill_core::kb::load::load_all(&mut kb, &[&second], &anthill_core::kb::load::NullResolver)
    {
        panic!("the second phase loads: {:?}", errs.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    match interp.call("shed7phase2.Driver.go", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 42, "the provision's `fill`"),
        other => panic!("expected an Int64, got {other:?}"),
    }
}
