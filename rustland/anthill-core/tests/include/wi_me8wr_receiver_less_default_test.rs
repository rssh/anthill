//! WI-20261102-ME8WR — A RECEIVER-LESS CALL OF A SPEC'S DEFAULT BODY RUNS AT THE INSTANCE ITS
//! BRACKET NAMES, whichever parameters of the spec its members take values of (kernel-language
//! §5.2: "the dictionary picks the target only for a receiver-less sibling … The dictionary is
//! the call site's").
//!
//! Measured on da37b553, the program below: `Pc2[C = Bag, Element = Int64].both()` died
//! "operation has no body: Pc2.emp" in an operation body and floundered in a rule. The typer
//! reads the carrier of a call with no receiver and no carrier-typed argument off the spec's
//! carrier parameter — the one a member takes a value of, else a sole parameter — and `Pc2`
//! has two parameters and no member taking a value of either, so the call had no carrier, no
//! instance was resolved, and the default was entered with no dictionary. A member taking an
//! `Element` (`one(e: Element)`) made `Element` the carrier parameter, so the full bracket
//! answered and `Pc2[C = Bag].both()` did not. Now (`carrier_the_call_binds`): where the call
//! binds no carrier parameter, its carrier is the provider of the instance its bracket names,
//! as a provision with no carrier parameter is dispatched at its provider — a witness too —
//! and a parameter the bracket leaves out is the one the provisions answering the rest say,
//! bound in the call's substitution (`bind_params_the_provisions_say`), so `Pc2[C = Bag]` is
//! `Bag`'s instance and `Pc2[C = Bag].pick()` an `Int64`. A bracket writing every parameter at
//! an instance nothing answers is refused where it is written.
//!
//! A default with a `requires` of its own, reached in a rule through the typer's dictionary,
//! was handed the call's stamps for that `requires` OR the dictionary, never both
//! (WI-20261102-Y9HSG's `DictionaryOwed::OwnSlots`): `__req_self` or `__req_unit` was missing.
//! The resolver's classified route now hands both (`WovenDispatch::Classified.stamps`), and
//! the bridge's dictionary entry places them after the dictionary's half and derives the rest
//! from the argument values, as every entry into a body does (`call_op_bridged`). That
//! derivation is also what a WOVEN call of such a default had none of: under `Sat[C] requires
//! Pc2[C = C, Element = Bit]`, `Pc2.both()` died `__req_unit not bound`.
//!
//! ## Back-out
//!
//! Measured 2026-11-02 in one build, a temporary switch each:
//!
//! - the carrier out (`carrier_the_call_binds` answering `None` where the call binds no
//!   carrier parameter): every row of `the_bracket_names_the_instance`,
//!   `a_parametric_provision_says_the_unwritten_parameter`,
//!   `a_member_naming_one_parameter_does_not_make_it_the_carrier`,
//!   `the_call_answers_at_every_site` and `the_carrier_is_the_provider_of_the_instance` dies
//!   "operation has no body" or flounders, `the_result_is_read_at_the_said_parameter` is
//!   refused, and `a_default_with_its_own_requirement_answers_in_a_rule` raises `__req_unit not
//!   bound`;
//! - the completion out (`bind_params_the_provisions_say`): the rows leaving a parameter out of
//!   the bracket — `opBothC`, `opRevC`, `ruleBothC`, `ruleBothCOther`, `opBox`, `ruleBox`,
//!   `ruleBoxOther`, `opWitness`, `ruleWitness`, `opElementOnly`, every row of
//!   `a_member_naming_one_parameter_does_not_make_it_the_carrier` and of
//!   `the_call_answers_at_every_site` — and the two above;
//! - the result read again after it: `the_result_is_read_at_the_said_parameter` is refused,
//!   `<unresolved receiver>.add`;
//! - the refusal of a bracket naming no instance: `a_bracket_no_provision_answers_is_refused`
//!   loads clean;
//! - the completion where a requirement of the spec is in scope (`requirement_in_scope`
//!   false): `a_requirement_in_scope_answers_what_the_bracket_leaves_open`'s `selected` runs
//!   `Red`'s own member, 7;
//! - the completion of a bracket that writes no parameter (`params_the_provisions_say`'s
//!   empty-written return): `wi1040_require_clause_dictionary_test::
//!   a_carrier_less_defaulted_call_answers_through_the_clause_dictionary` and
//!   `wi_8dxvk_provider_representation_test::
//!   rigid_caller_threads_selected_dictionary_to_introduced_requirement` run the one
//!   provider's member, 7, where nothing names it;
//! - the stamps out of the classified route (a callee with a `requires` of its own left to the
//!   stamps alone, as before): the five rule rows of
//!   `a_default_with_its_own_requirement_answers_in_a_rule`;
//! - the op-scoped half out of the bridge's dictionary entry (`call_op_bridged`):
//!   `a_default_with_its_own_requirement_answers_in_a_rule` and
//!   `a_woven_default_derives_its_own_requirement` raised `__req_unit not bound`. Since
//!   WI-20261103-D5WFQ both carry the call's stamps for it, and the derivation drives no row
//!   of this file (measured 2026-11-03); it stays the last gate of that entry, as of every
//!   entry into a body.
//!
//! PASS EITHER WAY, BY DESIGN: `the_full_bracket_at_a_member_naming_its_parameter` (the shapes
//! that answered before: `one(e: Element)` or `size(c: C)` declared, every parameter in the
//! bracket), `a_generic_caller_defers_to_its_requirement` and
//! `a_requirement_in_scope_answers_what_the_bracket_leaves_open` but for the switch named
//! above. A bracket that leaves a parameter out under a requirement of the spec at another
//! instance (`Pc2[C = Bag].both()` inside `Gen[X] requires Pc2[C = X, …]`) is not completed:
//! the bracket is then read as written.
//!
//! A woven call of such a default whose requirement's spec has a second provider (`Num
//! provides Unit[T = Num]` beside `Bit`'s) died `__req_unit not bound` here; it is
//! WI-20261103-D5WFQ's (wi_d5wfq_default_frame_test).

use anthill_core::eval::value::Value;

const SRC: &str = r#"
namespace me8wr
  import anthill.prelude.{Int64, Error, List, String}
  import anthill.prelude.List.{length}

  sort Pc2
    sort C = ?
    sort Element = ?
    operation emp() -> C
    operation both() -> C = emp()
    operation both2(xs: List[T = Element]) -> C = emp()
  end
  sort Bag
    entity bnil
    entity bfull
    provides Pc2[C = Bag, Element = Int64]
    operation emp() -> Bag = bnil()
  end
  sort Rev
    entity rnil
    provides Pc2[C = Rev, Element = Int64]
    operation emp() -> Rev = rnil()
  end
  -- A parametric provision: its `Element` is read at the `T` the bracket's `C` binds.
  sort Box[T]
    entity bxnil
    entity bxone(v: T)
    provides Pc2[C = Box[T = T], Element = T]
    operation emp() -> Box[T = T] = bxnil()
  end
  sort Gen[X]
    requires Pc2[C = X, Element = Int64]
    operation g() -> X = Pc2[C = X].both()
    rule r(x: X) :- x <=> Pc2[C = X].both()
    operation atBag() -> Bag = Pc2[C = Bag, Element = Int64].both()
  end

  const kBag: Bag = Pc2[C = Bag].both()
  operation idb(b: Bag) -> Bag = b

  rule rBoth(?n) :- ?n <=> Pc2[C = Bag, Element = Int64].both()
  rule rBothC(?n) :- ?n <=> Pc2[C = Bag].both()
  rule rRev(?n) :- ?n <=> Pc2[C = Rev, Element = Int64].both()
  rule rArg(?n) :- ?n <=> Pc2[C = Bag].both2([1])
  rule rBox(?n) :- ?n <=> Pc2[C = Box[T = Int64]].both()
  rule rNested(?n) :- ?n <=> idb(Pc2[C = Bag].both())

  sort Driver
    operation opBoth() -> Bag = Pc2[C = Bag, Element = Int64].both()
    operation opBothC() -> Bag = Pc2[C = Bag].both()
    operation opRev() -> Rev = Pc2[C = Rev, Element = Int64].both()
    operation opRevC() -> Rev = Pc2[C = Rev].both()
    operation opArg() -> Bag = Pc2[C = Bag].both2([1])
    operation ruleBoth() -> Int64 effects {Error} = rBoth(bnil()).takeN(5).length()
    operation ruleBothC() -> Int64 effects {Error} = rBothC(bnil()).takeN(5).length()
    operation ruleBothCOther() -> Int64 effects {Error} = rBothC(bfull()).takeN(5).length()
    operation ruleRev() -> Int64 effects {Error} = rRev(rnil()).takeN(5).length()
    operation ruleRevOpen() -> Int64 effects {Error} = rRev.takeN(5).length()
    operation ruleArg() -> Int64 effects {Error} = rArg(bnil()).takeN(5).length()

    operation opBox() -> Box[T = Int64] = Pc2[C = Box[T = Int64]].both()
    operation opBoxFull() -> Box[T = Int64] = Pc2[C = Box[T = Int64], Element = Int64].both()
    operation ruleBox() -> Int64 effects {Error} = rBox(bxnil()).takeN(5).length()
    operation ruleBoxOther() -> Int64 effects {Error} = rBox(bxone(v: 1)).takeN(5).length()

    operation genBag() -> Bag = Gen[X = Bag].g()
    operation genRev() -> Rev = Gen[X = Rev].g()
    operation genRule() -> Int64 effects {Error} = Gen[X = Rev].r(rnil()).takeN(5).length()
    operation genAtBag() -> Bag = Gen[X = Rev].atBag()

    operation viaConst() -> Bag = kBag
    operation viaLambda() -> Bag =
      let f = lambda () -> Pc2[C = Bag].both()
      f()
    operation viaArg() -> Bag = idb(Pc2[C = Bag].both())
    operation viaMatch() -> Int64 = match Pc2[C = Bag].both()
      case bnil() -> 1
      case bfull() -> 2
    operation ruleNested() -> Int64 effects {Error} = rNested(bnil()).takeN(5).length()
  end
end
"#;

/// Providers the bracket does not name as written: a witness, and a sort providing the spec
/// itself, written at the element position of another's instance.
const PROVIDERS: &str = r#"
namespace me8wr.providers
  import anthill.prelude.{Int64, Error, List, String}
  import anthill.prelude.List.{length}

  sort Pc2
    sort C = ?
    sort Element = ?
    operation emp() -> C
    operation both() -> C = emp()
  end
  sort WBag
    entity wnil
  end
  sort W
    provides Pc2[C = WBag, Element = String] where
      operation emp() -> WBag = wnil()
    end
  end
  sort X
    entity xnil
    entity xown
    provides Pc2[C = X, Element = Int64]
    operation emp() -> X = xnil()
    operation both() -> X = xown()
  end
  sort XBag
    entity xbnil
    provides Pc2[C = XBag, Element = X]
    operation emp() -> XBag = xbnil()
  end
  rule rWitness(?n) :- ?n <=> Pc2[C = WBag].both()
  rule rElement(?n) :- ?n <=> Pc2[C = XBag, Element = X].both()

  sort Driver
    operation opWitness() -> WBag = Pc2[C = WBag].both()
    operation opWitnessFull() -> WBag = Pc2[C = WBag, Element = String].both()
    operation ruleWitness() -> Int64 effects {Error} = rWitness(wnil()).takeN(5).length()
    operation opElement() -> XBag = Pc2[C = XBag, Element = X].both()
    operation opElementOnly() -> Int64 = match Pc2[Element = X].both()
      case xbnil() -> 1
    operation opX() -> X = Pc2[C = X].both()
    operation ruleElement() -> Int64 effects {Error} = rElement(xbnil()).takeN(5).length()
  end
end
"#;

/// A default whose result is the parameter the provision says.
const RESULT: &str = r#"
namespace me8wr.result
  import anthill.prelude.{Int64}

  sort Pc2
    sort C = ?
    sort Element = ?
    operation zero() -> Element
    operation pick() -> Element = zero()
  end
  sort Bag
    entity bnil
    provides Pc2[C = Bag, Element = Int64]
    operation zero() -> Int64 = 7
  end
  sort Driver
    operation viaDot() -> Int64 = Pc2[C = Bag].pick().add(1)
    operation viaLet() -> Int64 =
      let x = Pc2[C = Bag].pick()
      x.add(2)
  end
end
"#;

/// The default body's own `requires`, with a second provider of `Unit` beside `Bit`'s, so no
/// derivation from the provider facts alone could supply it: the call's stamps must.
const OWN_REQUIRES: &str = r#"
namespace me8wr.own
  import anthill.prelude.{Int64, Error, List}
  import anthill.prelude.List.{length, nil, cons}

  sort Unit
    sort T = ?
    operation unit() -> T
  end
  sort Bit
    entity t
    entity f
    provides Unit[T = Bit]
    operation unit() -> Bit = t()
  end
  sort Num
    entity num(n: Int64)
    provides Unit[T = Num]
    operation unit() -> Num = num(n: 0)
  end
  sort Pc2
    sort C = ?
    sort Element = ?
    operation fill(xs: List[T = Element]) -> C
    operation both() -> C requires Unit[T = Element] = fill([Unit.unit[T = Element]()])
  end
  sort Bag
    entity bnil
    entity bsome(b: Bit)
    provides Pc2[C = Bag, Element = Bit]
    operation fill(xs: List[T = Bit]) -> Bag = match xs
      case nil() -> bnil()
      case cons(x, rest) -> bsome(b: x)
  end
  sort Rev
    entity rnil
    entity rsome(b: Bit)
    provides Pc2[C = Rev, Element = Bit]
    operation fill(xs: List[T = Bit]) -> Rev = match xs
      case nil() -> rnil()
      case cons(x, rest) -> rsome(b: x)
  end
  rule rBoth(?n) :- ?n <=> Pc2[C = Bag, Element = Bit].both()
  rule rBothC(?n) :- ?n <=> Pc2[C = Bag].both()
  rule rRev(?n) :- ?n <=> Pc2[C = Rev, Element = Bit].both()

  sort Driver
    operation opBoth() -> Bag = Pc2[C = Bag, Element = Bit].both()
    operation opBothC() -> Bag = Pc2[C = Bag].both()
    operation opRev() -> Rev = Pc2[C = Rev, Element = Bit].both()
    operation ruleBoth() -> Int64 effects {Error} = rBoth(bsome(b: t())).takeN(5).length()
    operation ruleBothC() -> Int64 effects {Error} = rBothC(bsome(b: t())).takeN(5).length()
    operation ruleBothOther() -> Int64 effects {Error} = rBoth(bsome(b: f())).takeN(5).length()
    operation ruleRev() -> Int64 effects {Error} = rRev(rsome(b: t())).takeN(5).length()
    operation ruleOpen() -> Int64 effects {Error} = rBoth.takeN(5).length()
  end
end
"#;

/// A fixture edit whose anchor must occur exactly once: one that has drifted fails here, instead
/// of leaving the program it was meant to change as it was.
trait Swap {
    fn swap(&self, from: &str, to: &str) -> String;
}

impl Swap for str {
    fn swap(&self, from: &str, to: &str) -> String {
        assert_eq!(
            self.matches(from).count(),
            1,
            "the anchor occurs once: {from:?}"
        );
        self.replace(from, to)
    }
}

/// What each entry answered, as `Int` or the entity's constructor name, beside the one it
/// should have: every mismatch reported at once.
fn assert_answers(src: &str, ns: &str, rows: &[(&str, &str)]) {
    let mut interp = crate::common::interp_for(src);
    let wrong: Vec<String> = rows
        .iter()
        .filter_map(|&(entry, want)| {
            let got = match interp.call(&format!("{ns}.Driver.{entry}"), &[]) {
                Ok(Value::Int(n)) => n.to_string(),
                Ok(v @ Value::Entity { .. }) => {
                    anthill_core::eval::error::render_raised_payload(interp.kb(), &v)
                }
                other => format!("{other:?}"),
            };
            (got != want).then(|| format!("`{entry}`: expected {want}, got {got}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The ticket's program: the full bracket, the bracket the provision completes, a second
/// provider building its own value, the argument form, each in an operation body and in a rule.
#[test]
fn the_bracket_names_the_instance() {
    assert_answers(
        SRC,
        "me8wr",
        &[
            ("opBoth", "bnil"),
            ("opBothC", "bnil"),
            ("opRev", "rnil"),
            ("opRevC", "rnil"),
            ("opArg", "bnil"),
            ("ruleBoth", "1"),
            ("ruleBothC", "1"),
            ("ruleBothCOther", "0"),
            ("ruleRev", "1"),
            ("ruleRevOpen", "1"),
            ("ruleArg", "1"),
        ],
    );
}

/// `Box[T] provides Pc2[C = Box[T = T], Element = T]` says `Element` at the `T` the bracket's
/// `C` binds.
#[test]
fn a_parametric_provision_says_the_unwritten_parameter() {
    assert_answers(
        SRC,
        "me8wr",
        &[
            ("opBox", "bxnil"),
            ("opBoxFull", "bxnil"),
            ("ruleBox", "1"),
            ("ruleBoxOther", "0"),
        ],
    );
}

/// A member taking a value of `Element` made `Element` the spec's carrier parameter, which the
/// receiver-less call read: the bracket that left it out named no carrier.
#[test]
fn a_member_naming_one_parameter_does_not_make_it_the_carrier() {
    let with_one = SRC
        .swap(
            "    operation emp() -> C\n",
            "    operation emp() -> C\n    operation one(e: Element) -> C\n",
        )
        .swap(
            "    operation emp() -> Bag = bnil()\n",
            "    operation emp() -> Bag = bnil()\n    operation one(e: Int64) -> Bag = bfull()\n",
        )
        .swap(
            "    operation emp() -> Rev = rnil()\n",
            "    operation emp() -> Rev = rnil()\n    operation one(e: Int64) -> Rev = rnil()\n",
        )
        .swap(
            "    operation emp() -> Box[T = T] = bxnil()\n",
            "    operation emp() -> Box[T = T] = bxnil()\n    \
             operation one(e: T) -> Box[T = T] = bxone(v: e)\n",
        );
    assert_answers(
        &with_one,
        "me8wr",
        &[
            ("opBothC", "bnil"),
            ("opRevC", "rnil"),
            ("ruleBothC", "1"),
            ("ruleBothCOther", "0"),
            ("opBox", "bxnil"),
            ("ruleBox", "1"),
        ],
    );
}

/// CONTROL. With `one(e: Element)` or `size(c: C)` declared, the full bracket answered before.
#[test]
fn the_full_bracket_at_a_member_naming_its_parameter() {
    let members = [
        (
            "    operation one(e: Element) -> C\n",
            "    operation one(e: Int64) -> Bag = bfull()\n",
            "    operation one(e: Int64) -> Rev = rnil()\n",
            "    operation one(e: T) -> Box[T = T] = bxone(v: e)\n",
        ),
        (
            "    operation size(c: C) -> Int64\n",
            "    operation size(c: Bag) -> Int64 = 0\n",
            "    operation size(c: Rev) -> Int64 = 0\n",
            "    operation size(c: Box[T = T]) -> Int64 = 0\n",
        ),
    ];
    for (spec, bag, rev, boxed) in members {
        let src = SRC
            .swap(
                "    operation emp() -> C\n",
                &format!("    operation emp() -> C\n{spec}"),
            )
            .swap(
                "    operation emp() -> Bag = bnil()\n",
                &format!("    operation emp() -> Bag = bnil()\n{bag}"),
            )
            .swap(
                "    operation emp() -> Rev = rnil()\n",
                &format!("    operation emp() -> Rev = rnil()\n{rev}"),
            )
            .swap(
                "    operation emp() -> Box[T = T] = bxnil()\n",
                &format!("    operation emp() -> Box[T = T] = bxnil()\n{boxed}"),
            );
        assert_answers(
            &src,
            "me8wr",
            &[
                ("opBoth", "bnil"),
                ("opRev", "rnil"),
                ("ruleBoth", "1"),
                ("ruleRev", "1"),
            ],
        );
    }
}

/// The same call in a `const`, a lambda, an argument, a scrutinee, and as a rule's argument.
#[test]
fn the_call_answers_at_every_site() {
    assert_answers(
        SRC,
        "me8wr",
        &[
            ("viaConst", "bnil"),
            ("viaLambda", "bnil"),
            ("viaArg", "bnil"),
            ("viaMatch", "1"),
            ("ruleNested", "1"),
        ],
    );
}

/// A witness's instance, whose provider the bracket does not name; and a sort that provides the
/// spec itself written at the element position of another's (`Pc2[C = XBag, Element = X]`),
/// which is no call at `X`, whose own `both` answers only at `X`'s instance.
#[test]
fn the_carrier_is_the_provider_of_the_instance() {
    assert_answers(
        PROVIDERS,
        "me8wr.providers",
        &[
            ("opWitness", "wnil"),
            ("opWitnessFull", "wnil"),
            ("ruleWitness", "1"),
            ("opElement", "xbnil"),
            ("opElementOnly", "1"),
            ("opX", "xown"),
            ("ruleElement", "1"),
        ],
    );
}

/// The result is read at the parameter the provision says: `Pc2[C = Bag].pick()` is an
/// `Int64`, whose `add` the dot finds.
#[test]
fn the_result_is_read_at_the_said_parameter() {
    assert_answers(RESULT, "me8wr.result", &[("viaDot", "8"), ("viaLet", "9")]);
}

/// CONTROL. A bracket at a type parameter is dispatched through the caller's requirement.
/// One writing every parameter of another instance is at that instance (`genAtBag`).
#[test]
fn a_generic_caller_defers_to_its_requirement() {
    assert_answers(
        SRC,
        "me8wr",
        &[
            ("genBag", "bnil"),
            ("genRev", "rnil"),
            ("genRule", "1"),
            ("genAtBag", "bnil"),
        ],
    );
}

/// CONTROL. A requirement in scope answers what the bracket leaves open, as it did: the
/// caller's selection of `Other` reaches `Other.code`, where the provisions alone, `Red`'s and
/// `Other`'s at `C = Red`, would say `C = Red` and run `Red`'s own member.
#[test]
fn a_requirement_in_scope_answers_what_the_bracket_leaves_open() {
    let src = r#"
namespace me8wr.scope
  import anthill.prelude.{Int64}
  sort Tagger
    sort C = ?
    sort Out = ?
    operation tag(x: C) -> Out
    operation code() -> Int64 = 1
  end
  sort Red
    entity red
    provides Tagger[C = Red, Out = Int64]
    operation tag(x: Red) -> Int64 = 7
    operation code() -> Int64 = 7
  end
  sort Other
    provides Tagger[C = Red, Out = Int64]
    operation tag(x: Red) -> Int64 = 17
    operation code() -> Int64 = 17
  end
  sort Driver
    operation generic[A](x: A) -> Int64 requires Tagger[C = A, Out = Int64] =
      Tagger[Out = Int64].code()
    operation selected() -> Int64 = generic[A = Red, Tagger = Other](red())
    operation plain() -> Int64 = generic(red())
  end
end
"#;
    assert_answers(src, "me8wr.scope", &[("selected", "17"), ("plain", "7")]);
}

/// A bracket writing an instance no provision answers is refused where it is written, at a
/// provider of another instance and at a sort that provides nothing: each loaded and died
/// "operation has no body" before, the call having no instance to run at.
#[test]
fn a_bracket_no_provision_answers_is_refused() {
    let at_another_instance = SRC.swap(
        "    operation opBoth() -> Bag = Pc2[C = Bag, Element = Int64].both()\n",
        "    operation opBoth() -> Bag = Pc2[C = Bag, Element = String].both()\n",
    );
    let at_no_provider = SRC.swap(
        "  sort Driver\n",
        "  sort Foo\n    entity foo\n  end\n  sort Driver\n    \
         operation opFoo() -> Foo = Pc2[C = Foo, Element = Int64].both()\n",
    );
    for (src, instance) in [
        (at_another_instance, "Element = anthill.prelude.String"),
        (at_no_provider, "C = me8wr.Foo"),
    ] {
        let errors = crate::common::load_errors_of(&src);
        assert!(
            errors.len() == 1
                && errors[0].contains("no impl matches")
                && errors[0].contains(instance),
            "one refusal naming the bracket's instance `{instance}`; got {errors:#?}"
        );
    }
}

/// The default's own `requires` in a rule: the typer's dictionary and its stamps, together.
#[test]
fn a_default_with_its_own_requirement_answers_in_a_rule() {
    assert_answers(
        OWN_REQUIRES,
        "me8wr.own",
        &[
            ("opBoth", "bsome(b: t)"),
            ("opBothC", "bsome(b: t)"),
            ("opRev", "rsome(b: t)"),
            ("ruleBoth", "1"),
            ("ruleBothC", "1"),
            ("ruleBothOther", "0"),
            ("ruleRev", "1"),
            ("ruleOpen", "1"),
        ],
    );
}

/// The same default called through the clause's dictionary: its own `requires` read at the
/// sort's requirement, `Unit[T = Bit]`.
#[test]
fn a_woven_default_derives_its_own_requirement() {
    let src = OWN_REQUIRES
        .swap(
            "  sort Num\n    entity num(n: Int64)\n    provides Unit[T = Num]\n    \
             operation unit() -> Num = num(n: 0)\n  end\n",
            "",
        )
        .swap(
            "  sort Driver\n",
            "  sort Sat[C]\n    requires Pc2[C = C, Element = Bit]\n    \
             rule model(vs: C) :- vs <=> Pc2.both()\n  end\n  sort Driver\n    \
             operation woven() -> Int64 effects {Error} = \
             Sat[C = Bag].model(bsome(b: t())).takeN(5).length()\n    \
             operation wovenOther() -> Int64 effects {Error} = \
             Sat[C = Bag].model(bsome(b: f())).takeN(5).length()\n    \
             operation wovenRev() -> Int64 effects {Error} = Sat[C = Rev].model.takeN(5).length()\n",
        );
    assert_answers(
        &src,
        "me8wr.own",
        &[("woven", "1"), ("wovenOther", "0"), ("wovenRev", "1")],
    );
}
