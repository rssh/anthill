//! WI-20260823-4GBQV — A NULLARY CONSTRUCTOR NAMES AN AMBIENT RESOURCE.
//!
//! `prelude/effects.anthill`'s runtime note has always described the shape — "one arena
//! keyed by the target's FUNCTOR SYMBOL: `set(store, v)` and `set(counter, v)` share the
//! same handler but live in separate slots" — and it was not writable. Both halves
//! failed, which is why one fix in one place repairs nothing:
//!
//!   * THE DECLARATION. `Modify[counter]` classified as a TYPE, so `check_modify_targets`
//!     refused it (`a `Modify` target is a PLACE`, WI-20260823-39AD2).
//!   * THE CALL. `set(counter(), n)` passes an APPLICATION, a shape the effect re-key did
//!     not read, so `ModifyRuntime.set`'s own `Modify[target]` survived into the caller's
//!     row as an undeclared effect naming a parameter the author never wrote.
//!
//! WHAT DECIDES IT is [`KnowledgeBase::is_ambient_resource_name`], read by BOTH sides —
//! the loader's `Modify`-target lowering and the typer's argument re-key. NULLARY, because
//! arity is what separates a value from a function; NOT EPONYMOUS, because an eponymous
//! constructor IS its sort (WI-926) and admitting it would silently un-refuse the type
//! target WI-20260823-39AD2 exists to refuse.
//!
//! THE EPONYMOUS POPULATION, measured across the whole tree before the set was touched
//! (the ticket asked for it either way): 200 eponymous constructor sites, of which 3 are
//! in loadable `.anthill` sources — `stdlib/anthill/geometry.anthill`'s `Vec3` and two
//! `anthill-cli` fixtures' `Person`. Exactly TWO of the 200 are NULLARY, both test
//! fixtures (`parse_test.rs`'s `Error`, `wi933_carrierless_provision_test.rs`'s
//! `Wi933Unit`), and neither is written in a `Modify` target. So the exclusion closes the
//! whole population by construction and costs nothing in use —
//! `an_eponymous_nullary_constructor_stays_a_type` is its trip-wire.
//!
//! SCOPED TO `Modify`'S OWN TARGET SLOT, and that scope is measured rather than cautious.
//! The first cut widened the loader's general single-segment value-in-type arm; 9 tests
//! across three files fell, every one of them on the LABEL-AS-TYPE-PARAMETER idiom
//! (`Text[L = Untrusted]`, where `Untrusted` is a nullary entity standing for a type).
//! `an_entity_in_an_ordinary_type_slot_is_still_a_type` is that idiom in miniature and is
//! the control for the scope; kernel-language.md §5.6 is why the `Modify` slot alone
//! differs — its argument is a resource NAME, not a type.
//!
//! WHICH ROWS FAIL ON A BACK-OUT (repo rule "assert the CONTROL too"). Three independent
//! axes, each measured:
//!   * THE LOADER (`type_expr_to_child_modify_target` delegating unconditionally) —
//!     `an_ambient_slot_is_declarable`, `two_ambient_slots_are_distinct_places` and
//!     `an_undeclared_ambient_write_is_still_refused` fall, and
//!     `eval_test::m5_modify_an_ambient_resource_write_then_read` with them.
//!   * THE TYPER (`arg_place_head` dropping its `nullary_constructor_arg` leg) — the same
//!     rows fall, at the CALL instead of the declaration.
//!   * THE EXCLUSIONS (`is_ambient_resource_name` dropping its `!has_kind(Sort)` or its
//!     nullary test) — `an_eponymous_nullary_constructor_stays_a_type` /
//!     `a_constructor_with_fields_is_not_a_place` fall, and nothing else does.
//! `a_plain_sort_in_a_modify_target_is_still_refused` and
//! `an_entity_in_an_ordinary_type_slot_is_still_a_type` pass under ALL THREE by design:
//! they are what say this ticket widened one slot and not the language.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + user source together; surface load errors as strings.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

/// Did the load fail with the `check_modify_targets` refusal for `label`?
fn refused_as_type(errs: &[String], label: &str) -> bool {
    errs.iter()
        .any(|e| e.contains(&format!("declares effect `Modify[T = {label}]`")) && e.contains("whose target is a TYPE"))
}

/// THE ACCEPTANCE, load side: a nullary constructor names a slot, the declaration spells
/// it, and the call re-keys onto it. Driven end-to-end (through the arena) by
/// `eval_test::m5_modify_an_ambient_resource_write_then_read`.
#[test]
fn an_ambient_slot_is_declarable() {
    let src = r#"
namespace test.wi4gbqv.ambient
  import anthill.prelude.{Int64, Unit, Modify}
  import ModifyRuntime.{get, set}

  sort CounterState
    entity counter
  end

  operation write(n: Int64) -> Unit effects Modify[counter] = set(counter(), n)
  operation read() -> Int64 = get(counter())
end
"#;
    assert!(
        load_result(src).is_ok(),
        "`Modify[counter]` over a nullary constructor is an ambient PLACE and must load"
    );
}

/// The PAREN-LESS spelling is the same place. Both allocate to one term (the WI-511
/// `Fn{c,[],[]}`→`Ref(c)` canon), so the idiom must not depend on its parentheses — and
/// the two arms reach it by DIFFERENT code paths (`Expr::Ref` via `stable_receiver_path`,
/// `Expr::Constructor` via `nullary_constructor_arg`), which is why both are driven.
#[test]
fn the_parenless_ambient_spelling_is_the_same_place() {
    let src = r#"
namespace test.wi4gbqv.parenless
  import anthill.prelude.{Int64, Unit, Modify}
  import ModifyRuntime.{set}

  sort CounterState
    entity counter
  end

  operation write(n: Int64) -> Unit effects Modify[counter] = set(counter, n)
end
"#;
    assert!(
        load_result(src).is_ok(),
        "`set(counter, n)` must re-key exactly as `set(counter(), n)` does"
    );
}

/// TWO AMBIENT SLOTS ARE TWO RESOURCES. Declaring one and writing the other is refused,
/// and the diagnostic names BOTH — which is what says the re-key reached the argument's
/// own constructor rather than coarsening every ambient write onto one label.
#[test]
fn two_ambient_slots_are_distinct_places() {
    let src = r#"
namespace test.wi4gbqv.two_slots
  import anthill.prelude.{Int64, Unit, Modify}
  import ModifyRuntime.{set}

  sort Cells
    entity a
    entity b
  end

  operation write(n: Int64) -> Unit effects Modify[a] = set(b(), n)
end
"#;
    let errs = load_result(src).expect_err("declaring `Modify[a]` while writing `b` must fail");
    assert!(
        errs.iter()
            .any(|e| e.contains("Modify[T = a]") && e.contains("undeclared effect: Modify[T = b]")),
        "expected the declared `a` and the incurred `b` to be told apart; got: {errs:#?}"
    );
}

/// THE ROW IS STILL ENFORCED over an ambient place. Without this the two rows above would
/// be satisfied by "ambient writes incur nothing", which is not what they measure.
#[test]
fn an_undeclared_ambient_write_is_still_refused() {
    let src = r#"
namespace test.wi4gbqv.undeclared
  import anthill.prelude.{Int64, Unit, Modify}
  import ModifyRuntime.{set}

  sort CounterState
    entity counter
  end

  operation write(n: Int64) -> Unit effects {} = set(counter(), n)
end
"#;
    let errs = load_result(src).expect_err("an undeclared ambient write must be refused");
    assert!(
        errs.iter()
            .any(|e| e.contains("undeclared effect: Modify[T = counter]")),
        "expected the re-keyed ambient label to be reported undeclared; got: {errs:#?}"
    );
}

/// THE WI-926 TRAP, and the reason `is_ambient_resource_name` excludes a sort. An
/// eponymous constructor IS its sort — one symbol, no nested `Slot.Slot` — so `Modify[Slot]`
/// cannot be read as the constructor without also reading it as the sort. It stays a TYPE,
/// which is the verdict WI-20260823-39AD2 established.
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

/// THE SCOPE CONTROL, and the row this ticket's first cut broke. Outside `Modify`'s target
/// slot an entity name in a type argument is a TYPE (WI-313), and the taint vocabulary
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

  fact flows_to(Public, Public)
  -- ABSENT on purpose: flows_to(Untrusted, Public)

  operation fetch() -> Text[L = Untrusted]
  operation send(body: Text[L = ?l]) -> Unit
    requires flows_to(?l, Public)

  operation leak() -> Unit = send(fetch())
end
"#;
    let errs = load_result(src)
        .expect_err("`Untrusted` must still read as the TYPE the obligation is decided by");
    assert!(
        errs.iter().any(|e| e.contains("unsatisfied precondition")
            && e.contains("flows_to(Untrusted, Public)")),
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
/// onto `wrap`, producing `undeclared effect: Modify[T = wrap]`. The only declaration
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
  import ModifyRuntime.{set}

  sort Wrapper
    entity wrap(rep: Int64)
  end

  operation write(n: Int64) -> Unit effects {} = set(wrap, n)
end
"#;
    let errs = load_result(src).expect_err("a constructor function names no place");
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = wrap]")),
        "the re-key must not mint `Modify[T = wrap]`, which no declaration can spell; \
         got: {errs:#?}"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("names no resource") && e.contains("wrap")),
        "expected the refusal to name the caller's own `wrap`; got: {errs:#?}"
    );
}

/// The EPONYMOUS twin of the row above — the WI-926 exclusion reaching the CALL, not only
/// the declaration. `set(Slot, n)` used to re-key onto `Slot` and demand
/// `effects Modify[Slot]`, which `an_eponymous_nullary_constructor_stays_a_type` refuses:
/// the two sides of one ticket disagreeing, in the exact population the ticket's CARE note
/// singled out.
#[test]
fn a_parenless_eponymous_constructor_does_not_mint_an_undeclarable_label() {
    let src = r#"
namespace test.wi4gbqv.parenless_eponymous
  import anthill.prelude.{Int64, Unit, Modify}
  import ModifyRuntime.{set}

  sort Slot
    entity Slot
  end

  operation write(n: Int64) -> Unit effects {} = set(Slot, n)
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
  import anthill.prelude.{Int64, Modify}

  sort Box
    entity mkBox(contents: Int64)
  end

  operation poke(d: Box) -> Box effects Modify[d.contents] = d
  operation fresh() -> Box = mkBox(contents: 0)
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
