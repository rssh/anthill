//! WI-20260831-RSRP5 — A PER-LABEL EFFECT GATE MUST ASK ITS QUESTION OF THE LABEL, NOT
//! OF THE ELEMENT THAT NAMES IT.
//!
//! Four load-time gates read an operation's declared effect row and ask a question about
//! one LABEL: is this `Modify`'s target a PLACE (`check_modify_targets`); is this a
//! REGISTERED effect kind (`check_effect_registration`); does this row both ADMIT and
//! LACK a label (`check_declared_row_contradiction`, fixed under WI-20260830-APWM3); may
//! a macro carry it (`check_macro_purity`). The list they walk holds ELEMENTS, and an
//! element is the label only in the simplest spelling.
//!
//! ## The census that changed the fix
//!
//! The ticket was filed to teach these gates to read a PROJECTION through — `effects
//! {llm.E}` at a concrete carrier — the way WI-20260830-APWM3 taught the op-effects
//! coverage check. Enumerating how a concrete row actually REACHES a projection said
//! otherwise. Three routes exist, and they are measured here rather than assumed:
//!
//! | route | how the label gets in | before | after |
//! |---|---|---|---|
//! | A | `provides Spec[E = {bad}]` — a carrier's row binding | judged by NOTHING | refused AT THE BINDING |
//! | B | `effects E = bad` — a sort's bound row alias | registration refused, `Modify` did not | both refuse |
//! | C | a written type argument in a signature | not measurable (see below) | judged by NOTHING |
//!
//! (Row C's verdict is later than this ticket: WI-20260831-PYNS2 made the route drivable,
//! and it turned out to be unjudged. Filed as WI-20260831-V25N3 — see below.)
//!
//! Route A is the finding. A label can only reach a projected row by being WRITTEN
//! somewhere, and for a carrier's row parameter that somewhere is the binding — so
//! judging it there covers THAT origin entirely (route C is a second origin and is not
//! covered; see below), with a better diagnostic (it names the line the author wrote, not
//! a distant caller) and a verdict for a carrier no caller has projected yet. It also leaves `docs/kernel-language.md` §5.5's exemption of
//! "a receiver projection (`s.E`)" TRUE AS WRITTEN, which the widening first proposed
//! would have contradicted.
//!
//! ROUTE C WAS NOT MEASURABLE WHEN THIS WAS WRITTEN, AND NOW IS. `operation ask(s: Spec[E
//! = {…}]) effects {s.E}` calling `Spec.go(s, …)` was refused `got undeclared effect: ?_`
//! — and so was its CONTROL at a benign `E = {}` or `E = {Error}` — because a written row
//! type-argument did not reach the call's effect instantiation. That was a separate defect
//! and it swallowed any verdict this ticket's gates would have given.
//!
//! WI-20260831-PYNS2 FIXED IT, and the route is now drivable: the fixture above loads, and
//! it turned out the refusal was never universal — a spec with a CARRIER already accepted
//! the shape, so route C had been reachable all along wherever a spec was implemented.
//!
//! IT IS JUDGED BY NOTHING, which this ticket's argument requires it to be judged by
//! something: `operation ask(s: Spec[E = {Beep}], …)` and `… [E = {Modify[Thing]}]` both
//! LOAD CLEAN, at labels the two gates above refuse in a `provides` binding. So the "a
//! label can only reach a projected row by being WRITTEN somewhere, and that somewhere is
//! judged" claim holds for routes A and B and NOT for C. Measured on guardians' `Llm` too,
//! where it predates PYNS2. Filed as WI-20260831-V25N3 rather than fixed here, because the
//! work is the census of type positions a row can be written in, not the gate.
//!
//! ## What fails when it is backed out
//!
//! Every back-out below KEEPS `peel_effect_atom` and removes only the alias-following and
//! row-explosion, because a coarser one measures the wrong thing — dropping the peel too
//! makes `check_effect_registration` refuse the stdlib's seven guarded `Error[DivisionByZero]`
//! rows and every test reds for a reason that has nothing to do with this ticket.
//!
//! ```text
//!   back-out (sharp)                              reds
//!   provision-binding pass inert                  both route-A tests
//!   provision-binding pass peel-only              both route-A tests
//!   check_modify_targets peel-only                the route-B `Modify` test
//!   check_macro_purity peel-only                  the macro test
//!   check_effect_registration peel-only           NOTHING  <- so it was reverted
//! ```
//!
//! THE LAST ROW IS WHY THIS GATE IS UNCHANGED. Routing `check_effect_registration`
//! through the shared walk was built and backed out with every test green: its alias half
//! already lives in `effect_label_kind`, and its row half targets a shape the grammar
//! cannot express (`sort E = {A, B}` and `effects E = merge(A, B)` are both PARSE
//! ERRORS). A widening that survives its own back-out is a branch that fires nowhere.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

fn expect_refused(what: &str, needle: &str, srcs: &[&str]) {
    let errs = load_errors(srcs);
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{what}: expected a refusal containing `{needle}`; got: {errs:#?}"
    );
}

fn expect_loads(what: &str, srcs: &[&str]) {
    let errs = load_errors(srcs);
    assert!(errs.is_empty(), "{what} must load; got: {errs:#?}");
}

/// A spec with a row parameter and a DEFAULT body, so a carrier can provide it without
/// writing an operation of its own — which is what keeps the bad label confined to the
/// `provides` binding. (With an own operation the label is written literally there, and
/// the operation-row gates catch it; that fixture measures nothing about route A.)
const SPEC: &str = r#"
namespace test.rsrp5.spec
  import anthill.prelude.{Error, String, EffectsRuntime}
  sort Out
    entity out(v: String)
  end
  sort Spec
    import test.rsrp5.spec.Out.{out}
    sort C = ?
    effects E = ?
    operation go(self: C, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
end
"#;

/// ROUTE A, `Modify` TARGET — a carrier binds the spec's row to a TYPE-targeted `Modify`.
///
/// `Modify[Thing]` names a SORT, and §5.6 requires a PLACE. Written in an operation's own
/// row it has been refused since WI-20260823-39AD2; written HERE it was judged by nothing
/// and every operation projecting `c.E` inherited it.
///
/// BACKED OUT, two ways, both measured: the pass returning `Vec::new()`, and the pass
/// keeping only `peel_effect_atom` where it now calls `effect_element_labels`. Each reds
/// this and the sibling route-A test, and NOTHING else — the route-B tests go through the
/// operation-row gate, a different site. The second back-out is the one that says the ROW
/// EXPLOSION is load-bearing here and not just the alias walk: `E = {Modify[Thing]}` binds
/// a row, and peeled-but-unexploded it is one opaque atom that names no `Modify`.
#[test]
fn a_provision_row_binding_may_not_name_a_type_targeted_modify() {
    let carrier = r#"
namespace test.rsrp5.mt
  import anthill.prelude.{Error, String, Modify, EffectsRuntime}
  import test.rsrp5.spec.{Spec}
  sort Thing
    entity thing(v: String)
  end
  sort CarrierMT
    import test.rsrp5.mt.{Thing}
    entity cmt(tag: String)
    provides Spec[E = {Modify[Thing]}]
  end
end
"#;
    expect_refused(
        "a `Modify` target written in a provides row binding",
        "whose target is a TYPE",
        &[SPEC, carrier],
    );
}

/// ROUTE A, REGISTRATION — a carrier binds the spec's row to a sort that no
/// `fact Effect[T = K]` admits.
///
/// BOTH SPELLINGS, and that pair is the reason the pass filters on the DECLARATION rather
/// than on the binding value's shape: `E = {Beep}` is row-shaped and `E = Beep` is not,
/// both bind the row, and a value-shape filter would silently miss the second.
///
/// BACKED OUT (either way — the pass inert, or peel-only): both red.
#[test]
fn a_provision_row_binding_may_not_name_an_unregistered_kind_in_either_spelling() {
    let braced = r#"
namespace test.rsrp5.sp1
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.rsrp5.spec.{Spec}
  sort Beep1
    entity beep1
  end
  sort C1
    import test.rsrp5.sp1.{Beep1}
    entity c1(t: String)
    provides Spec[E = {Beep1}]
  end
end
"#;
    let bare = r#"
namespace test.rsrp5.sp2
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.rsrp5.spec.{Spec}
  sort Beep2
    entity beep2
  end
  sort C2
    import test.rsrp5.sp2.{Beep2}
    entity c2(t: String)
    provides Spec[E = Beep2]
  end
end
"#;
    expect_refused(
        "an unregistered kind in a BRACED row binding",
        "is not a REGISTERED effect kind",
        &[SPEC, braced],
    );
    expect_refused(
        "an unregistered kind in a BRACE-LESS row binding",
        "is not a REGISTERED effect kind",
        &[SPEC, bare],
    );
}

/// THE FALSE-POSITIVE CONTROL FOR ROUTE A, and the one that makes the two tests above
/// mean "row bindings are judged" rather than "bindings are judged".
///
/// `Spec[C = Int64]` binds a TYPE parameter. `Int64` is not a registered effect kind and
/// is not a place, so a pass that judged every binding would refuse this — the exact
/// failure the value-shape filter and the naive "judge all bindings" both produce. It
/// must load, and the row binding beside it (`E = {Error}`) must still be judged.
///
/// PASSES UNDER EVERY BACK-OUT IN THIS FILE — it is a control, not coverage, and what it
/// guards is a FUTURE widening of `effect_row_params_of_spec`, the only thing that could
/// make it red. (It DOES red under a coarser back-out that also drops `peel_effect_atom`,
/// which is an artifact of that back-out reaching the stdlib's guarded rows, not a
/// property of this fixture. Recorded because it briefly read as this control failing.)
#[test]
fn a_type_parameter_binding_is_not_read_as_an_effect_row() {
    let carrier = r#"
namespace test.rsrp5.sp3
  import anthill.prelude.{Error, String, Int64, EffectsRuntime}
  import test.rsrp5.spec.{Spec}
  sort C3
    entity c3(t: String)
    provides Spec[C = Int64, E = {Error}]
  end
end
"#;
    expect_loads("a TYPE-parameter binding beside a legal row binding", &[SPEC, carrier]);
}

/// ROUTE B — a sort's BOUND row alias, where the two gates disagreed.
///
/// `effects E = X` is documented as a name for `X` (§5.5: "A **bound** alias is followed
/// rather than exempted"), and an operation of that sort writes `effects {E}`.
/// `check_effect_registration` followed the chain; `check_modify_targets` did not. Same
/// sort, same route, same fact — refused for an unregistered label, admitted for a
/// type-targeted `Modify`.
///
/// BACKED OUT (`check_modify_targets` keeping only `peel_effect_atom`): the `Modify` half
/// reds and the registration half stays green — which IS the asymmetry, so the
/// registration row is the control that dates it.
///
/// THE BACK-OUT THAT DOES *NOT* WORK, recorded because it was tried first and passed:
/// removing an alias walk from `classify_modify_target` itself. That walk was added, made
/// this test green, and then survived its own removal — because the caller already
/// resolves the alias. It was deleted rather than kept; see that function's own note.
#[test]
fn a_bound_row_alias_is_followed_by_the_modify_gate_as_it_already_was_by_registration() {
    let mt = r#"
namespace test.rsrp5.bmt
  import anthill.prelude.{Error, String, Modify, EffectsRuntime}
  import test.rsrp5.spec.{Out}
  import test.rsrp5.spec.Out.{out}
  sort Thing2
    entity thing2(v: String)
  end
  sort BoundMT
    import test.rsrp5.bmt.{Thing2}
    effects E = Modify[Thing2]
    entity bmt(tag: String)
    operation go(self: BoundMT, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
end
"#;
    let ur = r#"
namespace test.rsrp5.bur
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.rsrp5.spec.{Out}
  import test.rsrp5.spec.Out.{out}
  sort Boop
    entity boop
  end
  sort BoundUR
    import test.rsrp5.bur.{Boop}
    effects E = Boop
    entity bur(tag: String)
    operation go(self: BoundUR, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
end
"#;
    // BOTH HALVES OF THE MESSAGE ARE ASSERTED. The author wrote `effects {E}`; the
    // label is `Modify[Thing2]`. A refusal naming only the resolved form points at a
    // string that is nowhere in their file, so the written token must appear too — the
    // shape the sibling registration gate already had. (/code-review)
    let errs = load_errors(&[SPEC, mt]);
    assert!(
        errs.iter().any(|e| e.contains("whose target is a TYPE")),
        "a type-targeted `Modify` reached through a bound row alias must be refused; got: {errs:#?}"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("`E`, which names `Modify[T = Thing2]`")),
        "the refusal must name the element AS WRITTEN (`E`) beside the label it resolves \
         to — naming only the resolved form points at a token absent from the source; \
         got: {errs:#?}"
    );
    // THE CONTROL that dates the asymmetry: this one already worked.
    expect_refused(
        "an unregistered kind reached through a bound row alias",
        "is not a REGISTERED effect kind",
        &[SPEC, ur],
    );
}

/// `check_macro_purity`'s blindness pointed the OTHER WAY, which is why it outlived the
/// others: it refuses anything that is not `Error`, so failing to follow an alias makes
/// it refuse a PURE macro rather than admit an impure one. A loud false refusal, not a
/// silent admission — and still the same defect.
///
/// THE CORPUS CENSUS THIS TICKET ASKED FOR: exactly two macros exist
/// (`Relation.conjoin_of`, `Relation.guarded_of`), both declaring an EMPTY row. So
/// nothing in the tree exercised this either way, and the fixture below is the only
/// witness. Recorded because "no population" was the reason to leave it, and it is not a
/// reason once the shape is drivable.
///
/// BACKED OUT (`check_macro_purity` keeping only `peel_effect_atom`): the alias row reds;
/// the literal control stays green.
#[test]
fn a_macros_pure_row_is_recognized_through_a_bound_alias() {
    let alias = r#"
namespace test.rsrp5.mac
  import anthill.prelude.{Error, String, EffectsRuntime}
  import anthill.reflect.{NodeOccurrence}
  sort MacHost
    effects E = Error
    entity mh
    operation mac_of(o: NodeOccurrence) -> NodeOccurrence
      effects {E}
  end
end
"#;
    // THE CONTROL: the same macro with `Error` written literally. It loaded before this
    // ticket and after, so it is what says the alias row's refusal was about the ALIAS.
    let literal = r#"
namespace test.rsrp5.mac2
  import anthill.prelude.{Error, String}
  import anthill.reflect.{NodeOccurrence}
  sort MacHost2
    entity mh2
    operation mac_of(o: NodeOccurrence) -> NodeOccurrence
      effects {Error}
  end
end
"#;
    expect_loads("a macro whose `Error` row is reached through a bound alias", &[alias]);
    expect_loads("a macro with a literal `Error` row", &[literal]);
}

/// A PLACE IN A ROW BINDING IS LAWFUL, and this is the control that keeps the refusal
/// above from being read as "a row binding may not mention `Modify`".
///
/// §5.6 lists a NULLARY CONSTRUCTOR naming an ambient resource among the things that
/// DENOTE a value, and that is the one place-form available where there is no parameter
/// list — so `provides Spec[E = {Modify[clock2]}]` over an `entity clock2` must load, and
/// does. It also dates the diagnostic: the first version of the type-target message said
/// "a row binding cannot name one … there is no parameter list here for a place to live
/// in", which this program contradicts, and the advice sent an author to give up on a
/// construct that works. Found by /code-review, measured loading, message rewritten.
///
/// PASSES BOTH WAYS — a control for the refusal's WIDTH, not coverage of it.
#[test]
fn a_nullary_ambient_place_is_lawful_in_a_row_binding() {
    let place = r#"
namespace test.rsrp5.pl
  import anthill.prelude.{Error, String, Modify, Modifiable, EffectsRuntime}
  import test.rsrp5.spec.{Spec}
  sort Clock2
    entity clock2
  end
  fact Modifiable[T = Clock2]
  sort CPlace
    import test.rsrp5.pl.{Clock2}
    import test.rsrp5.pl.Clock2.{clock2}
    entity cpl(t: String)
    provides Spec[E = {Modify[clock2]}]
  end
end
"#;
    expect_loads(
        "a `Modify` over a nullary ambient constructor in a provides row binding",
        &[SPEC, place],
    );
}

/// TWO ROW PARAMETERS, TWO REFUSALS, EACH NAMING ITS OWN SLOT.
///
/// A spec may declare more than one row (`effects E = ?` beside `effects F = ?`). The
/// first version of this pass keyed its dedup on `(carrier, spec, label)`, so binding the
/// SAME bad label into both slots reported ONCE, in a message that named neither `E` nor
/// `F` — and if only one half were wrong the author still got no pointer to which. Found
/// by /code-review; the row parameter is now in the key and in the message.
///
/// BACKED OUT (`param` dropped from the dedup key): one error instead of two.
#[test]
fn each_bad_row_parameter_is_reported_against_its_own_slot() {
    let two = r#"
namespace test.rsrp5.two
  import anthill.prelude.{Error, String, EffectsRuntime}
  sort Beep9
    entity beep9
  end
  sort TwoRows
    import test.rsrp5.two.{Beep9}
    sort C = ?
    effects E = ?
    effects F = ?
    operation go(self: C) -> String effects {E, F, Error} = "x"
  end
  sort C9
    import test.rsrp5.two.{Beep9}
    entity c9(t: String)
    provides TwoRows[E = {Beep9}, F = {Beep9}]
  end
end
"#;
    let errs = load_errors(&[two]);
    for slot in ["`E` to an effect row", "`F` to an effect row"] {
        assert!(
            errs.iter().any(|e| e.contains(slot)),
            "each bad row binding must name its own slot — expected one mentioning \
             {slot}; got: {errs:#?}"
        );
    }
}
