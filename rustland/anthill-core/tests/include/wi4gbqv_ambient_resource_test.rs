//! WI-20260823-4GBQV — A NULLARY CONSTRUCTOR NAMED AN AMBIENT RESOURCE; WI-20260902-JB6RS
//! RETIRED IT (user, 2026-10-20: "drop ambient places").
//!
//! 4GBQV made `Modify[counter]` over `sort CounterState … entity counter … end` declare
//! the slot `Env(counter)`, and `set(counter(), n)` re-key onto it — a resource no handle
//! is threaded to. That made the `Modify` bracket the one place in the language where a
//! constructor was read as its INSTANCE and not its TYPE. Under JB6RS a name in a bracket
//! is read by one rule (kernel-language.md §4.4): a constructor is a sort in its own right
//! (§6.3), so `Modify[counter]` is the type `counter†` and is refused as a type, like
//! `Modify[Cell]`. With it goes the other ambient spelling, a zero-argument operation's
//! result (`Modify[slot]` over `operation slot()`): declarable, but no call can write it,
//! since a call is no place to re-key onto. A resource is threaded as a PARAMETER; the
//! place is the parameter.
//!
//! What this file pins now:
//!   * the retired forms are REFUSED, at the declaration and at the call, each with its
//!     own reason — the type, the nullary constructor, the ambient operation;
//!   * the refusals that predate the retirement still hold (an eponymous constructor, a
//!     constructor with fields, a plain sort), and the binder-capture rows are unchanged;
//!   * outside `Modify` a constructor in a type argument is still its TYPE — the label
//!     idiom `Text[L = Untrusted]` — and the facts about labels are written over types,
//!     `flows_to(Untrusted[], Public[])` (JB6RS, user 2026-10-17).
//!
//! WHICH ROWS FAIL ON A BACK-OUT: restoring the loader's ambient arm (a nullary
//! constructor in `Modify`'s target lowered as a denoted place) fails
//! `a_nullary_constructor_is_no_modify_target`; restoring the typer's nullary-constructor
//! re-key fails `neither_spelling_of_a_nullary_constructor_is_a_place`; dropping the
//! `PlaceType::Ambient` arm of `modify_place_type` fails
//! `a_zero_argument_operation_is_no_modify_target`. The remaining rows pass either way BY
//! DESIGN — they are what says the retirement removed one reading and not the checks.

/// Load stdlib + user source together; surface load errors as strings.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    crate::common::try_load_kb_with(source).map(|_| ())
}

/// Did the load fail with the `check_modify_targets` refusal for `label`?
fn refused_as_type(errs: &[String], label: &str) -> bool {
    errs.iter()
        .any(|e| e.contains(&format!("declares effect `Modify[T = {label}]`")) && e.contains("whose target is a TYPE"))
}

/// The DECLARATION: a nullary constructor in `Modify`'s target is the constructor's TYPE,
/// refused as every type is there. This loaded until JB6RS, as the ambient slot.
#[test]
fn a_nullary_constructor_is_no_modify_target() {
    let src = r#"
namespace test.wi4gbqv.retired
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  operation touch(target: CounterState) -> Unit effects Modify[target] = ()
  operation write() -> Unit effects Modify[counter] = ()
end
"#;
    let errs = load_result(src).expect_err("`Modify[counter]` names a type, and must be refused");
    assert!(refused_as_type(&errs, "counter"), "expected the TYPE refusal; got: {errs:#?}");
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = target]")),
        "a parameter of the same sort is still a place; got: {errs:#?}"
    );
}

/// The CALL: neither spelling of a nullary constructor is a place an effect re-keys onto,
/// and both are told as the constant they are — `counter()` is not a fresh value.
#[test]
fn neither_spelling_of_a_nullary_constructor_is_a_place() {
    for (spelling, arg) in [("bare", "counter"), ("applied", "counter()")] {
        let src = format!(
            r#"
namespace test.wi4gbqv.call_{spelling}
  import anthill.prelude.{{Int64, Unit, Modify, Modifiable}}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  operation touch(target: CounterState) -> Unit effects Modify[target] = ()
  operation write() -> Unit = touch({arg})
end
"#
        );
        let errs = load_result(&src).expect_err("a nullary constructor is no place");
        assert!(
            errs.iter().any(|e| e.contains("expected an argument naming a PLACE")
                && e.contains("a nullary constructor")),
            "{spelling}: expected the call refused, naming the constant; got: {errs:#?}"
        );
    }
}

/// The OTHER ambient spelling: a zero-argument operation's result is declarable but no
/// call can write it, so the declaration is refused, naming the operation.
#[test]
fn a_zero_argument_operation_is_no_modify_target() {
    let src = r#"
namespace test.wi4gbqv.ambient_op
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  operation slot() -> CounterState = counter()
  operation write() -> Unit effects Modify[slot] = ()
end
"#;
    let errs = load_result(src).expect_err("an ambient operation place must be refused");
    assert!(
        errs.iter().any(|e| e.contains("Modify[T = slot]")
            && e.contains("the zero-argument operation `test.wi4gbqv.ambient_op.slot`")
            && e.contains("AMBIENT place")),
        "expected the ambient refusal naming `slot`; got: {errs:#?}"
    );
}

/// THE WI-926 TRAP, unchanged in verdict: an eponymous constructor IS its sort, so
/// `Modify[Slot]` is a TYPE, which is the verdict WI-20260823-39AD2 established. 4GBQV had
/// to exclude it from the ambient reading by name; since JB6RS every constructor is its
/// type in this bracket and the exclusion is the rule.
#[test]
fn an_eponymous_nullary_constructor_stays_a_type() {
    let src = r#"
namespace test.wi4gbqv.eponymous
  import anthill.prelude.{Int64, Unit, Modify}

  sort Slot
    entity Slot
  end

  operation write(n: Int64) -> Unit effects Modify[Slot] = n
end
"#;
    let errs = load_result(src).expect_err("an eponymous constructor must stay a TYPE target");
    assert!(
        refused_as_type(&errs, "Slot"),
        "expected `Modify[Slot]` refused as a TYPE target; got: {errs:#?}"
    );
}

/// A CONSTRUCTOR WITH FIELDS IS A FUNCTION, not a value: `wrap` names no slot until it is
/// applied, so it is not a place. The nullary half of the predicate, on its own fixture.
#[test]
fn a_constructor_with_fields_is_not_a_place() {
    let src = r#"
namespace test.wi4gbqv.with_fields
  import anthill.prelude.{Int64, Unit, Modify}

  sort Wrapper
    entity wrap(rep: Int64)
  end

  operation write(n: Int64) -> Unit effects Modify[wrap] = n
end
"#;
    let errs = load_result(src).expect_err("a field-bearing constructor names no place");
    assert!(
        refused_as_type(&errs, "wrap"),
        "expected `Modify[wrap]` refused as a TYPE target; got: {errs:#?}"
    );
}

/// THE WI-20260823-39AD2 CONTROL, unmoved: a SORT in a `Modify` target is still a type
/// error. Passes both before and after this ticket, by design — it is what says the
/// ambient admission did not reopen the type target.
#[test]
fn a_plain_sort_in_a_modify_target_is_still_refused() {
    let src = r#"
namespace test.wi4gbqv.plain_sort
  import anthill.prelude.{Int64, Unit, Modify}

  sort Reg
    entity mkReg
  end

  operation write(n: Int64) -> Unit effects Modify[Reg] = n
end
"#;
    let errs = load_result(src).expect_err("a sort in a Modify target is still refused");
    assert!(
        refused_as_type(&errs, "Reg"),
        "expected `Modify[Reg]` refused as a TYPE target; got: {errs:#?}"
    );
}

/// THE SCOPE CONTROL, and the row this ticket's first cut broke. An entity name in a type
/// argument is a TYPE (WI-313; and in `Modify`'s too since JB6RS), and the taint vocabulary
/// depends on it: `Untrusted` / `Public` are nullary entities carried as the type
/// parameter `Text[L = …]`, which is what makes `flows_to(?l, Public)` a real obligation.
/// Reading them as places instead makes the label unreadable and the obligation vacuous.
///
/// Passes both before and after by design. It fails only if the ambient admission escapes
/// the `Modify` target — which is exactly how the first cut failed, across 9 rows in three
/// other files.
#[test]
fn an_entity_in_an_ordinary_type_slot_is_still_a_type() {
    let src = r#"
enum test.wi4gbqv.scope.Level
  entity Untrusted
  entity Public
end

enum test.wi4gbqv.scope.Text
  import anthill.prelude.{String}
  sort L = ?
  entity mk(raw: String)
end

namespace test.wi4gbqv.scope
  import anthill.prelude.{Unit}
  import test.wi4gbqv.scope.Level.{Untrusted, Public}
  import test.wi4gbqv.scope.Text

  fact flows_to(Public[], Public[])
  -- ABSENT on purpose: flows_to(Untrusted[], Public[])

  operation fetch() -> Text[L = Untrusted]
  operation send(body: Text[L = ?l]) -> Unit
    requires flows_to(?l, Public[])

  operation leak() -> Unit = send(fetch())
end
"#;
    let errs = load_result(src)
        .expect_err("`Untrusted` must still read as the TYPE the obligation is decided by");
    assert!(
        errs.iter().any(|e| e.contains("unsatisfied precondition")
            && e.contains("flows_to(Untrusted[], Public[])")),
        "expected the label to reach the obligation as a type; got: {errs:#?}"
    );
}

/// AN ARROW BINDER IS NOT CAPTURED BY A NAME IN THE ENCLOSING SCOPE — the unsound ACCEPT
/// this ticket briefly created, found by `/code-review` on WI-341's own `each` fixture.
///
/// `f: (a: Cell) -> Unit @ Modify[a]` binds `a` on the ARROW. The `Modify`-target lowering
/// resolves names in the ENCLOSING scope, so running it before the delegate's
/// `arrow_binder_scope` arm does not add a reading, it STEALS one.
///
/// THE DISCRIMINATOR IS WHICH RESOURCE THE ROW NAMES, and nothing weaker separates the two
/// states: applying `f` to an element of `l` is undeclared under `effects {}` EITHER WAY,
/// so a test asserting only "some Modify escaped" passes with the capture in place. It has
/// to read the LABEL. Correct: `Modify[T = l]` — the callback's binder, re-keyed onto the
/// element, coarsened to the list it came from. Captured: `Modify[T = a]`, a resource the
/// callback never touches — and declaring THAT loads clean while the op still mutates the
/// caller's list.
///
/// TWO ARMS ON ONE PROGRAM, differing by a `sort Amb { entity a }` written elsewhere in
/// the file and nothing else. That is the whole point: under the capture a declaration's
/// meaning depends on an unrelated name somewhere else in the namespace. MEASURED — back
/// the guard out and the second arm reports `Modify[T = a]` while the first still reports
/// `Modify[T = l]`.
#[test]
fn an_arrow_binder_is_not_captured_by_an_enclosing_name() {
    fn each_program(extra: &str, ns: &str) -> String {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{List, Unit, Int64, Cell, Modify}}
  import anthill.prelude.List.{{nil, cons}}
{extra}
  operation each(l: List[T = Cell[V = Int64]], f: (a: Cell[V = Int64]) -> Unit @ Modify[a])
    -> Unit
    effects {{}}
  =
    match l
      case nil() -> f(Cell.new(0))
      case cons(h, t) -> f(h)
end
"#
        )
    }

    // CONTROL — no colliding name. Passes both with and without the guard, by design: it
    // is what says the arm below measures the CAPTURE and not the re-key.
    let errs = load_result(&each_program("", "test.wi4gbqv.binder_clean"))
        .expect_err("applying `f` to an element of `l` incurs a Modify the empty row lacks");
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Modify[T = l]")),
        "the callback's `Modify[a]` must re-key onto the element and coarsen to `l`; \
         got: {errs:#?}"
    );

    // THE ARM — the identical program, plus an unrelated nullary entity spelled `a`.
    let errs = load_result(&each_program(
        "  sort Amb\n    entity a\n  end\n",
        "test.wi4gbqv.binder_capture",
    ))
    .expect_err("the same program, still undeclared");
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Modify[T = l]")),
        "an unrelated `entity a` must not re-point the callback's `Modify[a]`; got: {errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = a]")),
        "`Modify[T = a]` names a resource the callback never touches; got: {errs:#?}"
    );
}

/// THE ARROW-BINDER SHADOW, DRIVEN rather than asserted to load. The `Modify` target
/// lowering resolves a bare name in the ENCLOSING scope, so a `-Modify[x]`
/// lacks-constraint — whose `x` is the ARROW's own binder, a name this scope does not
/// know — sits one lookup away from being captured by an unrelated nullary entity that
/// happens to be spelled `x`. Captured, the constraint would silently become a lacks
/// about the entity and a pred that DOES modify its own parameter would pass.
///
/// So the pred modifies its parameter and must still be REFUSED, exactly as
/// `wi441_iterable_arrow_pred_test::modifying_pred_rejected_by_find` demands with no
/// entity in scope. "It loads clean" measures nothing here — a captured constraint loads
/// clean too, which is why the first cut of this row was the wrong test. Raised by
/// `/code-review`.
///
/// This is also why the lowering resolves with `resolve_in_scope` and not `remap_name`:
/// the latter REPORTS an unresolved name, and `prelude/iterable.anthill`'s `-Modify[x]`
/// then put four copies of "unresolved place `x`" on every program that merely loads the
/// prelude. Not-found must delegate, silently.
#[test]
fn an_arrow_binder_is_not_captured_by_an_entity_of_the_same_name() {
    let src = r#"
namespace test.wi4gbqv.shadow
  import anthill.prelude.{List, Option, Bool, Int64, Cell, Modify}
  import anthill.prelude.Iterable.{find}

  -- A nullary entity spelled exactly like `Iterable.find`'s arrow binder.
  sort Amb
    entity x
  end

  operation touchy(c: Cell[V = Int64]) -> Bool effects Modify[c] = true
  operation boom(xs: List[T = Cell[V = Int64]]) -> Option[T = Cell[V = Int64]] =
    find(xs, touchy)
end
"#;
    let errs = load_result(src)
        .expect_err("the lacks-constraint must still bind the ARROW's `x`, not the entity");
    assert!(
        errs.iter()
            .any(|e| e.contains("lack") && e.contains("Modify")),
        "expected `-Modify[x]` to still reject a modifying pred; got: {errs:#?}"
    );
}

/// A RE-KEY MAY NOT MINT A LABEL THE DECLARATION CANNOT SPELL, and before
/// `names_modify_place` was one predicate it did. `stable_receiver_path` answers the
/// §4.1 ALIAS-STABILITY question and takes any bare name, constructors included — so a
/// paren-less field-bearing constructor re-keyed `ModifyRuntime.set`'s `Modify[target]`
/// onto `wrap`, producing `undeclared effect: Modify[T = wrap]`. `touch` stands for that
/// callee since WI-200 retired `ModifyRuntime`: generic in its target, as `set` was, and
/// writing nothing, since a row is an upper bound. The only declaration
/// that would satisfy it, `effects Modify[wrap]`, is itself a load error
/// (`a_constructor_with_fields_is_not_a_place`), so the program was unwritable and
/// neither message said so.
///
/// Both halves in one row, because the pair IS the claim: the incurred label must NOT
/// name the constructor, and the refusal must name it as the caller's own. Raised by
/// `/code-review`; no fixture reached it.
#[test]
fn a_parenless_fieldful_constructor_does_not_mint_an_undeclarable_label() {
    let src = r#"
namespace test.wi4gbqv.parenless_fieldful
  import anthill.prelude.{Int64, Unit, Modify}

  sort Wrapper
    entity wrap(rep: Int64)
  end

  operation touch[T](target: T, n: Int64) -> Unit effects Modify[target] = ()
  operation write(n: Int64) -> Unit effects {} = touch(wrap, n)
end
"#;
    let errs = load_result(src).expect_err("a constructor function names no place");
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = wrap]")),
        "the re-key must not mint `Modify[T = wrap]`, which no declaration can spell; \
         got: {errs:#?}"
    );
    // Since WI-20260902-JB6RS the bare `wrap` is the construction `wrap()` (a constructor's
    // bare name is its instance, kernel-language.md §4.4), refused for the field it lacks
    // before anything asks whether it is a place — and that refusal names `wrap` too.
    assert!(
        errs.iter().any(|e| e.contains("`wrap` is constructed without its field `rep`")),
        "expected the refusal to name the caller's own `wrap`; got: {errs:#?}"
    );
}

/// The EPONYMOUS twin of the row above — the WI-926 exclusion reaching the CALL, not only
/// the declaration. `set(Slot, n)` (`touch` here, as above) used to re-key onto `Slot` and demand
/// `effects Modify[Slot]`, which `an_eponymous_nullary_constructor_stays_a_type` refuses:
/// the two sides of one ticket disagreeing, in the exact population the ticket's CARE note
/// singled out.
#[test]
fn a_parenless_eponymous_constructor_does_not_mint_an_undeclarable_label() {
    let src = r#"
namespace test.wi4gbqv.parenless_eponymous
  import anthill.prelude.{Int64, Unit, Modify}

  sort Slot
    entity Slot
  end

  operation touch[T](target: T, n: Int64) -> Unit effects Modify[target] = ()
  operation write(n: Int64) -> Unit effects {} = touch(Slot, n)
end
"#;
    let errs = load_result(src).expect_err("an eponymous constructor is its sort, not a place");
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = Slot]")),
        "the re-key must not mint `Modify[T = Slot]`, which no declaration can spell; \
         got: {errs:#?}"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("names no resource") && e.contains("Slot")),
        "expected the refusal to name the caller's own `Slot`; got: {errs:#?}"
    );
}

/// A FIELD-PATH DECLARATION LEAKS THROUGH A SPELLING ONE SEGMENT LONGER. `poke` declares
/// `Modify[d.contents]`, and the refusal's check read only a bare `Ref` off the denoted —
/// so `d`, the callee's own parameter, sailed out as `undeclared effect:
/// Modify[T = d.contents]`: the very leak this ticket closes, wearing a `.contents`.
/// Fixed by reading the path HEAD, which is also the resource (`Modify[c]` covers
/// `Modify[c.rep]`, WI-506). Raised by `/code-review`.
#[test]
fn a_field_path_declaration_is_refused_at_the_call_too() {
    let src = r#"
namespace test.wi4gbqv.field_path
  import anthill.prelude.{Int64, Modify, Modifiable}

  -- The written field must be a resource: a `Modify` fires only on a modifiable type.
  sort Res
    entity res
    provides Modifiable[T = Self]
  end

  sort Box
    entity mkBox(contents: Res)
  end

  operation poke(d: Box) -> Box effects Modify[d.contents] = d
  operation fresh() -> Box = mkBox(contents: res())
  operation caller() -> Box effects {} = poke(fresh())
end
"#;
    let errs = load_result(src).expect_err("a placeless argument under a field-path Modify");
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = d.contents]")),
        "`poke`'s own parameter must not leak through the field path; got: {errs:#?}"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("names no resource") && e.contains("fresh")),
        "expected the refusal to name the caller's own `fresh(…)`; got: {errs:#?}"
    );
    // The declaration quoted as written: by its head alone it was `Modify[d]` (MEASURED;
    // BACK-OUT: the head's local name printed again fails this assertion alone).
    assert!(
        errs.iter().any(|e| e.contains("declares `Modify[d.contents]` over this parameter")),
        "expected the field-path declaration quoted whole; got: {errs:#?}"
    );
}

/// THE GUARD DIRECTION, arm: a `{Modify[c] :- g}` whose guard HOLDS at the call site IS
/// incurred, so an argument naming no place is refused exactly as a bare atom's is.
///
/// This is what the refusal's condition being the EFFECT rather than a proxy buys. The
/// first cut asked "does the callee DECLARE a `Modify` over a parameter whose argument
/// named no place" and had to skip guarded atoms wholesale to avoid refusing the control
/// below — which left this row leaking `undeclared effect: Modify[T = c]`, the very
/// defect the ticket is about, one wrapper away. Asking instead "did a `Modify` naming a
/// CALLEE parameter SURVIVE the re-key and the discharge" answers both rows correctly
/// with no wrapper case at all.
#[test]
fn a_holding_guard_still_refuses_a_placeless_argument() {
    let src = r#"
namespace test.wi4gbqv.guard_holds
  import anthill.prelude.{Unit, Int64, Bool, Cell, Modify}
  import anthill.prelude.PartialEq.{eq}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)

  operation touch(c: Cell[V = Int64], flag: Bool) -> Unit
    effects { Modify[c] :- eq(flag, true) }
  = Cell.set(c, 1)

  operation via_app() -> Unit effects {} = touch(mk(), true)
end
"#;
    let errs = load_result(src).expect_err("a holding guard incurs the Modify; it must refuse");
    assert!(
        errs.iter()
            .any(|e| e.contains("names no resource") && e.contains("mk")),
        "expected the refusal to name the caller's own `mk(…)`; got: {errs:#?}"
    );
}

/// THE GUARD DIRECTION, control — IN ITS OWN FIXTURE, because a shared namespace would
/// let the arm above's error stand for this one's silence. A guard REFUTED at the call
/// site drops the atom before it is ever incurred, so the same placeless argument is
/// FINE. Refusing it would refuse a correct program, which is why the check runs AFTER
/// `drop_refuted_guarded_labels` and not beside the declaration.
///
/// Passes under every back-out of this ticket, by design.
#[test]
fn a_refuted_guard_admits_the_same_placeless_argument() {
    let src = r#"
namespace test.wi4gbqv.guard_refuted
  import anthill.prelude.{Unit, Int64, Bool, Cell, Modify}
  import anthill.prelude.PartialEq.{eq}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)

  operation touch(c: Cell[V = Int64], flag: Bool) -> Unit
    effects { Modify[c] :- eq(flag, true) }
  = Cell.set(c, 1)

  operation via_app() -> Unit effects {} = touch(mk(), false)
end
"#;
    assert!(
        load_result(src).is_ok(),
        "a refuted guard drops the atom, so the placeless argument incurs nothing"
    );
}

// ---------------------------------------------------------------------------------------
// THE CALL'S REFUSAL, ASKED OF THE CALLEE'S OWN ATOM AND TOLD BY THE ARGUMENT'S SHAPE.
// Found by the review of the arm reorder in `placeless_arg_reason` (2026-10-20). Each row's
// back-out is at its site, every one measured as a temporary switch in one build over the
// whole `wi_tests` binary: each turned red the rows its site names, and nothing else.
// ---------------------------------------------------------------------------------------

use crate::common::replace_in_fixture;

/// The refusals of `touch` below, one per caller.
fn refusals_of(src: &str) -> Vec<String> {
    load_result(src).expect_err("the fixture is refused on purpose")
}

/// Is one of `errs` the call's own refusal, telling the argument with every one of `parts`?
fn told_as(errs: &[String], parts: &[&str]) -> bool {
    errs.iter()
        .any(|e| e.contains("expected an argument naming a PLACE") && parts.iter().all(|p| e.contains(p)))
}

/// A bare nullary OPERATION is its call (§5.4) and a `const` is a constant: neither holds a
/// place, and each is refused at the call as what it is. Read as a place, `touch(mk)` re-keyed
/// `Modify[target]` onto `mk` and was refused, with no location, as the undeclared `Modify[T =
/// mk]` — whose one declaration is refused as an ambient place — and `touch(k0)` the same over
/// `k0` (MEASURED). Bound first, the call loads.
///
/// BACK-OUT: `names_no_place` reduced to `is_unplaceable_constructor` fails this row.
#[test]
fn a_bare_nullary_operation_or_a_const_is_no_place() {
    let src = r#"
namespace test.wi4gbqv.bare_op
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort W
    provides Modifiable[T = Self]
    entity counter
  end

  operation mk() -> W = counter
  const k0: W = counter()
  operation touch(target: W) -> Unit effects Modify[target] = ()
  operation viaOp() -> Unit = touch(mk)
  operation viaConst() -> Unit = touch(k0)
end
"#;
    let errs = refusals_of(src);
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = mk]") || e.contains("Modify[T = k0]")),
        "no label may be minted over a call or a constant; got: {errs:#?}"
    );
    assert!(
        told_as(
            &errs,
            &["the call `test.wi4gbqv.bare_op.mk` (a zero-argument operation named bare)", "Bind it first"]
        ),
        "`touch(mk)` is refused at the call as the call it is; got: {errs:#?}"
    );
    assert!(
        told_as(&errs, &["the name `test.wi4gbqv.bare_op.k0`, a `const` — a constant"]),
        "`touch(k0)` is refused at the call as a constant; got: {errs:#?}"
    );
    let bound = replace_in_fixture(
        src,
        "operation viaOp() -> Unit = touch(mk)\n  operation viaConst() -> Unit = touch(k0)",
        "operation viaOp() -> Unit =\n    let x = mk()\n    touch(x)",
    );
    if let Err(errs) = load_result(&bound) {
        panic!("the call bound first loads; got: {errs:#?}");
    }
}

/// An ABSENCE (`-Modify[c]`) says the callee does NOT modify `c`; it is no effect the call
/// incurs, and an argument naming no place is fine there. Read through its wrapper, the call
/// was refused naming a `Modify[c]` nothing declares (MEASURED).
///
/// BACK-OUT: the absence read through (`effect_atom_is_absence` not asked) fails this row.
#[test]
fn an_absence_is_no_modify_the_call_incurs() {
    let src = r#"
namespace test.wi4gbqv.absent
  import anthill.prelude.{Unit, Int64, Bool, Cell, Modify}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)
  operation readOnly(c: Cell[V = Int64]) -> Int64 effects -Modify[c] = 1
  operation user() -> Int64 effects {} = readOnly(mk())
end
"#;
    if let Err(errs) = load_result(src) {
        panic!("a denial over `c` asks nothing of `c`'s argument; got: {errs:#?}");
    }
}

/// A SELF-RECURSIVE call is judged on the callee's OWN atom, before the re-key: there the
/// caller's variables are the callee's parameters. After it, `swap(b, mk(), false)`'s
/// `Modify[a]`, re-keyed onto the caller's `b`, read as the callee's own `Modify[b]` — whose
/// guard the call refutes — and the call was refused naming it. The unguarded twin is refused
/// for what it does incur, `Modify[a]` re-keyed onto `b`, which `swap` does not declare — as
/// the same call to a copy of `swap` is; it was refused claiming `swap` declares `Modify[b]`
/// (MEASURED).
///
/// BACK-OUT: the atom judged after the re-key fails this row.
#[test]
fn a_self_recursive_call_is_judged_on_the_callees_own_atom() {
    let guarded = r#"
namespace test.wi4gbqv.selfrec
  import anthill.prelude.{Unit, Int64, Bool, Cell, Modify}
  import anthill.prelude.PartialEq.{eq}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)

  operation swap(a: Cell[V = Int64], b: Cell[V = Int64], fb: Bool) -> Unit
    effects { Modify[a], Modify[b] :- eq(fb, true) }
  = if fb then Cell.set(b, 1) else swap(b, mk(), false)
end
"#;
    if let Err(errs) = load_result(guarded) {
        panic!("the refuted guard drops the callee's `Modify[b]`; got: {errs:#?}");
    }
    let unguarded = r#"
namespace test.wi4gbqv.selfrec2
  import anthill.prelude.{Unit, Int64, Bool, Cell, Modify}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)

  operation swap(a: Cell[V = Int64], b: Cell[V = Int64], go: Bool) -> Unit
    effects Modify[a]
  = if go then Cell.set(a, 1) else swap(b, mk(), true)
end
"#;
    let errs = refusals_of(unguarded);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Modify[T = b]")),
        "the write the call does make, to the caller's `b`, is undeclared; got: {errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("declares `Modify[b]`")),
        "`swap` declares no `Modify[b]`; got: {errs:#?}"
    );
}

/// A constructor TAKING FIELDS, applied to none or named bare, is its application with every
/// field left out (§4.4) — complete here, its one field an `Option` — a value no name denotes,
/// and the repair is to bind it. Told as the bare name ("a constructor taking fields … no row
/// could name this effect"), the refusal withheld that repair while `let x = wrap()` then
/// `touch(x)` loaded; `wrap(rep: none())`, the same value, was told to bind it (MEASURED).
///
/// BACK-OUT: the nullary arm's test of the declared fields dropped fails this row.
#[test]
fn a_constructor_taking_fields_applied_to_none_is_a_value_no_name_denotes() {
    let src = r#"
namespace test.wi4gbqv.optfields
  import anthill.prelude.{Int64, Unit, Modify, Modifiable, Option}

  sort Res
    provides Modifiable[T = Self]
    entity wrap(rep: Option[T = Int64])
  end

  operation touch(target: Res) -> Unit effects Modify[target] = ()
  operation applied() -> Unit = touch(wrap())
  operation bare() -> Unit = touch(wrap)
end
"#;
    let errs = refusals_of(src);
    let fresh = |e: &&String| {
        e.contains("the constructor `test.wi4gbqv.optfields.Res.wrap(…)`, a value no name denotes")
            && e.contains("Bind it first")
    };
    assert_eq!(errs.iter().filter(fresh).count(), 2, "both spellings are one construction; got: {errs:#?}");
    let bound = replace_in_fixture(
        src,
        "operation applied() -> Unit = touch(wrap())\n  operation bare() -> Unit = touch(wrap)",
        "operation applied() -> Unit =\n    let x = wrap()\n    touch(x)",
    );
    if let Err(errs) = load_result(&bound) {
        panic!("the construction bound first loads; got: {errs:#?}");
    }
}

/// An EMPTY LITERAL is named by the literal. Its node is a reflect form applied to nothing,
/// which is not that form's name (§6), and it was told as "the name
/// `anthill.reflect.ListLiteral`, which is its own sort"; a non-empty one as "the constructor
/// `anthill.reflect.ListLiteral(…)`" (MEASURED).
///
/// BACK-OUT: the literal forms not asked of (`collection_literal`) fails this row.
#[test]
fn an_empty_literal_is_named_by_the_literal() {
    let src = r#"
namespace test.wi4gbqv.literals
  import anthill.prelude.{Int64, Unit, Modify}

  operation touchg[X](target: X) -> Unit effects Modify[target] = ()
  operation emptyList() -> Unit = touchg([])
  operation emptyTuple() -> Unit = touchg(())
  operation emptySet() -> Unit = touchg({})
  operation oneList() -> Unit = touchg([1])
end
"#;
    let errs = refusals_of(src);
    for told in ["the empty list `[]`", "the empty tuple `()`", "the empty set `{}`", "the list `[…]`"] {
        assert!(told_as(&errs, &[told, "a value no name denotes"]), "{told}; got: {errs:#?}");
    }
    assert!(
        !errs.iter().any(|e| e.contains("anthill.reflect.")),
        "a literal is named as written, not by its reflect form; got: {errs:#?}"
    );
}

/// A TYPE in a value position is a constant. It fell to the last arm, "this argument
/// expression, which produces a fresh value" (MEASURED).
///
/// BACK-OUT: the `TypeValue` arm dropped fails this row, and so does a constructor's type
/// printed without its bracket.
#[test]
fn a_type_value_is_a_constant() {
    let src = r#"
namespace test.wi4gbqv.typeval
  import anthill.prelude.{Int64, Unit, Modify, Modifiable, List}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  operation touchg[X](target: X) -> Unit effects Modify[target] = ()
  operation bareType() -> Unit = touchg(CounterState)
  operation appliedType() -> Unit = touchg(List[T = Int64])
  operation faceType() -> Unit = touchg(counter[])
end
"#;
    let errs = refusals_of(src);
    assert!(
        told_as(&errs, &["the type `test.wi4gbqv.typeval.CounterState` — a constant"]),
        "got: {errs:#?}"
    );
    assert!(told_as(&errs, &["the type `anthill.prelude.List[…]` — a constant"]), "got: {errs:#?}");
    // A constructor's type is written with its bracket; bare, its name is the instance (§4.4).
    // It was printed bare (MEASURED).
    assert!(
        told_as(&errs, &["the type `test.wi4gbqv.typeval.CounterState.counter[]` — a constant"]),
        "got: {errs:#?}"
    );
}

/// A CHOICE between places names none itself; the repair is the call in each branch, which
/// names each branch's own place and loads. Told as a fresh value, the refusal advised a
/// `let`, whose binder aliases a place the effect check does not follow yet
/// (WI-20261015-809JN): the advised program loaded with nothing declared (MEASURED).
///
/// BACK-OUT: the `if`/`match` arms back on the fresh-value advice fails this row, and so does
/// the `let` arm told to call in each branch.
#[test]
fn a_choice_between_places_is_called_in_each_branch() {
    let src = r#"
namespace test.wi4gbqv.choice
  import anthill.prelude.{Unit, Int64, Bool, Cell, Modify}

  operation touch(c: Cell[V = Int64]) -> Unit effects Modify[c] = Cell.set(c, 1)
  operation pick(x: Cell[V = Int64], y: Cell[V = Int64], b: Bool) -> Unit effects {Modify[x], Modify[y]} =
    touch(if b then x else y)
end
"#;
    let errs = refusals_of(src);
    assert!(
        told_as(&errs, &["an `if` expression, which names no resource itself", "Call `touch` in each branch"]),
        "got: {errs:#?}"
    );
    let branched = replace_in_fixture(src, "touch(if b then x else y)", "if b then touch(x) else touch(y)");
    if let Err(errs) = load_result(&branched) {
        panic!("the advised call in each branch loads; got: {errs:#?}");
    }
    // A `let` has no branches: it is told to pass the place it evaluates to. It was told to
    // call `touch` in each branch (MEASURED).
    let let_arg = replace_in_fixture(src, "touch(if b then x else y)", "touch(let z = x\n          z)");
    assert!(
        told_as(
            &refusals_of(&let_arg),
            &["a `let` expression, which names no resource itself. Pass the place it evaluates to"]
        ),
        "a `let` argument names no place of its own"
    );
}

/// A nullary constructor APPLIED is the constant its bare name is (§4.4), in the spelling no
/// loader converts as well: an `Apply`, from a macro's `make_apply` splice. The arm for a call
/// stood before the arm written for it and took it — "the call `…counter(…)`, which produces a
/// fresh value", while `rustc` reported the other arm unreachable (MEASURED).
///
/// The macro builds the constructor alone, and `touch` is the caller's call. It built
/// `touch(counter())` as well until a call a macro builds to an effectful operation was refused
/// at the expansion (WI-905), which stopped the typing before the argument was read.
///
/// BACK-OUT, over the whole `wi_tests` binary: the arm for a call put back before the nullary
/// arm fails this row and [`a_construction_a_rewrite_leaves_an_application_is_a_constructor`],
/// whose construction it takes for a call too, and nothing else.
#[test]
fn a_spliced_nullary_constructor_is_the_constant() {
    let src = r#"
namespace test.wi4gbqv.splice
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}
  import anthill.prelude.List.{nil}
  import anthill.reflect.{NodeOccurrence, make_apply}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  operation touch(target: CounterState) -> Unit effects Modify[target] = ()
  operation mkctr(x: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi4gbqv.splice.CounterState.counter", nil(), x)
  operation ctr(c: Int64) -> CounterState
  rule ctr(?c) <=> mkctr(?c) @[simp]

  operation w() -> Unit = touch(ctr(1))
end
"#;
    let errs = refusals_of(src);
    assert!(
        told_as(&errs, &["the name `test.wi4gbqv.splice.CounterState.counter`, a nullary constructor — a constant"]),
        "got: {errs:#?}"
    );
}

/// A CONSTRUCTION a rewrite leaves an application is named a constructor: `wrap()` in a
/// `@[simp]` right-hand side reaches the call as an `Apply` carrying its slots, and was "the
/// call `…wrap(…)`" (MEASURED). The program is refused by the effectful-rewrite rule as well.
///
/// BACK-OUT: the arm for a construction with arguments dropped fails this row, and so does the
/// arm for a call put back first ([`a_spliced_nullary_constructor_is_the_constant`]).
#[test]
fn a_construction_a_rewrite_leaves_an_application_is_a_constructor() {
    let src = r#"
namespace test.wi4gbqv.simpctor
  import anthill.prelude.{Int64, Unit, Modify, Modifiable, Option}
  sort Res
    provides Modifiable[T = Self]
    entity wrap(rep: Option[T = Int64])
  end
  operation touch(target: Res) -> Unit effects Modify[target] = ()
  operation doIt() -> Unit
  rule doIt() <=> touch(wrap()) @[simp]
  operation write() -> Unit = doIt()
end
"#;
    let errs = refusals_of(src);
    assert!(told_as(&errs, &["the constructor `test.wi4gbqv.simpctor.Res.wrap(…)`"]), "got: {errs:#?}");
}

/// The refusal reads as one sentence, its advice last. A suffix ", so it names no resource."
/// used to follow every reason, after the advice ("…or pass a parameter or a field path off one,
/// so it names no resource.") and after the reason's own conclusion ("…so no row could name this
/// effect either, so it names no resource."), and " and not a place" followed the constant's
/// relative clause (MEASURED).
///
/// BACK-OUT: the suffix restored fails this row.
#[test]
fn the_refusal_reads_as_one_sentence() {
    let src = r#"
namespace test.wi4gbqv.sentence
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort W
    provides Modifiable[T = Self]
    entity counter
  end

  operation mk() -> W = counter
  operation touch(target: W) -> Unit effects Modify[target] = ()
  operation viaCall() -> Unit = touch(mk())
  operation viaConstant() -> Unit = touch(counter)
end
"#;
    let errs = refusals_of(src);
    assert!(
        errs.iter().any(|e| e.ends_with(
            "the call `test.wi4gbqv.sentence.mk(…)`, a value no name denotes, so it names no \
             resource. Bind it first (`let x = …`) and pass `x`, or pass a parameter or a field \
             path off one"
        )),
        "got: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.ends_with(
            "the name `test.wi4gbqv.sentence.W.counter`, a nullary constructor — a constant, so it \
             names no resource: kernel-language.md §5.6 admits a parameter, `result`, or a field \
             path off one, and a resource is threaded as a parameter"
        )),
        "got: {errs:#?}"
    );
}

/// A ZERO-ARGUMENT DOT CALL is the call it dispatches to, `h.fresh()` the call `Holder.fresh(h)`,
/// and is refused at the call as the written call is. Classified as written, it read as the
/// field path `h.fresh` and re-keyed the callee's `Modify` onto the receiver `h`: under
/// `effects Modify[h]` it loaded, declaring a write the program never makes, and under `effects
/// {}` it was refused, unlocated, as the undeclared `Modify[T = h]` (MEASURED). A field path
/// (`h.rep`) is still the place it names.
///
/// BACK-OUT: the written argument classified again (`typed_arg` not asked) fails this row and
/// [`an_argument_a_rewrite_makes_a_place_is_that_place`].
#[test]
fn a_zero_argument_dot_call_is_the_call_it_dispatches_to() {
    let src = r#"
namespace test.wi4gbqv.dotcall
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort Box
    provides Modifiable[T = Self]
    entity full(v: Int64)
  end

  sort Holder
    provides Modifiable[T = Self]
    entity holder(rep: Box)
    operation fresh(h: Holder) -> Box = full(v: 1)
  end

  operation touch(target: Box) -> Unit effects Modify[target] = ()
  operation declared(h: Holder) -> Unit effects Modify[h] = touch(h.fresh())
  operation pure(h: Holder) -> Unit effects {} = touch(h.fresh())
end
"#;
    let errs = refusals_of(src);
    assert_eq!(
        errs.iter()
            .filter(|e| told_as(&[(*e).clone()], &["the call `test.wi4gbqv.dotcall.Holder.fresh(…)`"]))
            .count(),
        2,
        "both callers are refused at the call; got: {errs:#?}"
    );
    assert!(!errs.iter().any(|e| e.contains("Modify[T = h]")), "nothing is charged to `h`; got: {errs:#?}");
    let field = replace_in_fixture(
        &replace_in_fixture(src, "touch(h.fresh())\n  operation pure", "touch(h.rep)\n  operation pure"),
        "operation pure(h: Holder) -> Unit effects {} = touch(h.fresh())\n",
        "",
    );
    if let Err(errs) = load_result(&field) {
        panic!("a field path off `h` is a place under `h`; got: {errs:#?}");
    }
}

/// An argument a `@[simp]` rewrite turns into a place IS that place: `same(c)` under `rule
/// same(?c) <=> ?c` is `c`, at a call's own site and at a dispatched override's. Classified as
/// written, it was refused as "the call `…same(…)`, which produces a fresh value" while its type
/// was read off the rewrite; and with nothing declared the refusal named that call, where the
/// write the program makes — to `c` — is what goes undeclared (MEASURED).
///
/// BACK-OUT: as [`a_zero_argument_dot_call_is_the_call_it_dispatches_to`]'s.
#[test]
fn an_argument_a_rewrite_makes_a_place_is_that_place() {
    let src = r#"
namespace test.wi4gbqv.rewritten
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  operation same(c: CounterState) -> CounterState
  rule same(?c) <=> ?c @[simp]
  operation touch(target: CounterState) -> Unit effects Modify[target] = ()
  operation write(c: CounterState) -> Unit effects Modify[c] = touch(same(c))
end
"#;
    if let Err(errs) = load_result(src) {
        panic!("`same(c)` is `c`, a parameter; got: {errs:#?}");
    }
    let undeclared = replace_in_fixture(src, "effects Modify[c] = touch(same(c))", "effects {} = touch(same(c))");
    let errs = refusals_of(&undeclared);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Modify[T = c]")),
        "the write to `c` is what goes undeclared; got: {errs:#?}"
    );
    let dispatched = r#"
namespace test.wi4gbqv.rewritten_override
  import anthill.prelude.{Int64, Modify, EffectsRuntime, Modifiable}

  sort Box
    effects Effect = ?
    operation peek(b: Self) -> Int64 effects Effect
  end

  sort MutBox
    provides Modifiable[T = Self]
    entity mb(fd: Int64)
    provides Box
    operation peek(b: MutBox) -> Int64 effects Modify[b] =
      match b
        case mb(x) -> x
  end

  operation same(b: MutBox) -> MutBox
  rule same(?b) <=> ?b @[simp]

  operation read_it(b: MutBox) -> Int64 effects Modify[b] = Box.peek(same(b))
end
"#;
    if let Err(errs) = load_result(dispatched) {
        panic!("the override's `Modify[b]` lands on the caller's `b`; got: {errs:#?}");
    }
}

/// A body holding the typer's own `some(…)` coercion is judged the same when it is typed
/// AGAIN: `poke(x)` at an `Option`-typed `Modify` parameter is `x`, a parameter. The typed body
/// stores the wrap, and read again it was the construction "`Option.some(…)`, which produces a
/// fresh value" — a later load (`KB.loaded` from `anthill run`) refused what the first one
/// accepted, in the first one's file (MEASURED). An author's own `some(x)` is a construction,
/// refused the first time.
///
/// BACK-OUT: the coercion not seen through (`through_option_coercion` not asked) fails this row.
#[test]
fn a_body_typed_again_reads_through_the_typers_own_option_coercion() {
    use anthill_core::kb::typing::{type_check_sorts, Loaded};
    let src = r#"
namespace test.wi4gbqv.retyped
  import anthill.prelude.{Int64, Unit, Bool, Modify, Modifiable, Option}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  operation poke(target: Option[T = CounterState]) -> Unit effects Modify[target] = ()
  operation user(x: CounterState) -> Unit effects Modify[x] = poke(x)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let again = type_check_sorts(&mut kb, Loaded::nothing());
    assert!(again.is_empty(), "typed again, the body is judged as it was; got: {again:#?}");
    let written = replace_in_fixture(
        &replace_in_fixture(src, "= poke(x)", "= poke(some(x))"),
        "import anthill.prelude.{Int64, Unit, Bool, Modify, Modifiable, Option}",
        "import anthill.prelude.{Int64, Unit, Bool, Modify, Modifiable, Option}\n  import anthill.prelude.Option.{some}",
    );
    assert!(
        told_as(&refusals_of(&written), &["the constructor `anthill.prelude.Option.some(…)`"]),
        "an author's `some(x)` is a construction and names no place"
    );
}

/// A field path off a value no name denotes is told as the field path, in the form the typer
/// leaves it (`field_access(receiver, "rep")`). Classified as typed, it was "the call
/// `anthill.reflect.field_access(…)`", a name the author never wrote (MEASURED).
///
/// BACK-OUT: the `field_access` arm dropped fails this row.
#[test]
fn a_field_path_off_a_value_no_name_denotes_is_told_as_one() {
    let src = r#"
namespace test.wi4gbqv.fieldoff
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort Box
    provides Modifiable[T = Self]
    entity full(v: Int64)
  end

  sort Holder
    entity holder(rep: Box)
  end

  operation mkh() -> Holder = holder(rep: full(v: 1))
  operation touch(target: Box) -> Unit effects Modify[target] = ()
  operation viaCall() -> Unit = touch(mkh().rep)
  operation viaCtor() -> Unit = touch(holder(rep: full(v: 2)).rep)
end
"#;
    let errs = refusals_of(src);
    let told = |e: &&String| {
        told_as(
            &[(*e).clone()],
            &["the field path `.rep`, whose receiver is a value no name denotes", "pass `x.rep`"],
        )
    };
    assert_eq!(errs.iter().filter(told).count(), 2, "both receivers name nothing; got: {errs:#?}");
    assert!(!errs.iter().any(|e| e.contains("field_access")), "got: {errs:#?}");
}

/// An argument passed BY NAME is classified as the call's typing left it too: `touch(target:
/// same(c))` is `c`, and `touch(target: h.fresh())` the call `Holder.fresh(h)`.
///
/// BACK-OUT: the named loop's argument classified as written fails this row alone; the rows
/// above pass the argument positionally.
#[test]
fn a_named_argument_is_classified_as_typed() {
    let src = r#"
namespace test.wi4gbqv.named
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort CounterState
    provides Modifiable[T = Self]
    entity counter
  end

  sort Holder
    provides Modifiable[T = Self]
    entity holder(rep: CounterState)
    operation fresh(h: Holder) -> CounterState = counter
  end

  operation same(c: CounterState) -> CounterState
  rule same(?c) <=> ?c @[simp]
  operation touch(target: CounterState) -> Unit effects Modify[target] = ()
  operation viaRewrite(c: CounterState) -> Unit effects Modify[c] = touch(target: same(c))
  operation viaDot(h: Holder) -> Unit effects {} = touch(target: h.fresh())
end
"#;
    let errs = refusals_of(src);
    assert!(
        !errs.iter().any(|e| e.contains("same(…)") || e.contains("Modify[T = h]")),
        "`same(c)` is `c`, and nothing is charged to `h`; got: {errs:#?}"
    );
    assert!(told_as(&errs, &["the call `test.wi4gbqv.named.Holder.fresh(…)`"]), "got: {errs:#?}");
}

/// A SELF-RECURSIVE call through a DISPATCHED override is judged on the override's own atom
/// too: inside `MutBox.poke(a, other)`, `Box.poke(other, mb(fd: 1))` re-keys the override's
/// `Modify[a]` onto the caller's `other`, and read after the re-key it was the override's own
/// `Modify[other]` — which it does not declare — so the call was refused naming it. It is
/// refused for the write it makes, to `other`, which the caller does not declare (MEASURED).
///
/// BACK-OUT: the override's atom judged after the re-key (`dispatched_impl_effects_of`) fails
/// this row alone; [`a_self_recursive_call_is_judged_on_the_callees_own_atom`] drives the
/// call's own site.
#[test]
fn a_self_recursive_dispatch_is_judged_on_the_overrides_own_atom() {
    let src = r#"
namespace test.wi4gbqv.ovrrec
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}

  sort Box
    sort T = ?
    effects Effect = ?
    operation poke(a: Self, other: T) -> Int64 effects Effect
  end

  sort MutBox
    provides Modifiable[T = Self]
    entity mb(fd: Int64)
    provides Box[T = MutBox]
    operation poke(a: MutBox, other: MutBox) -> Int64 effects Modify[a] = Box.poke(other, mb(fd: 1))
  end
end
"#;
    let errs = refusals_of(src);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Modify[T = other]")),
        "the write to `other` is undeclared; got: {errs:#?}"
    );
    assert!(!errs.iter().any(|e| e.contains("declares `Modify[other]`")), "got: {errs:#?}");
}
