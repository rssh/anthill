//! WI-20261103-D5WFQ — A RECEIVER-LESS CALL OF A SPEC'S DEFAULT BODY IS REFUSED WHERE ITS
//! BRACKET NAMES NO ONE INSTANCE, AND IS READ AT THE REQUIREMENT IT IS ANSWERED BY.
//!
//! Measured on 372ec4fa, the two programs below.
//!
//! 1. `Pc2[C = Bag].both()` beside `WInt provides Pc2[C = Bag, Element = Int64]` and `WStr
//!    provides Pc2[C = Bag, Element = String]` loaded clean and died "operation has no body:
//!    Pc2.emp" (floundered in a rule): the provisions answering the bracket's `C` say its
//!    `Element` apart, so nothing completed it, and the refusal of a bracket naming no
//!    instance asked only a complete one. Now the bracket is refused where it is written,
//!    naming the parameter and the providers (`OpenSlotsNamedApart::of_bracket`), in an
//!    operation body, a const, and a rule body's call, which is typed as an operation body is
//!    (068 §3) — so is a full bracket at an instance nothing provides, refused before in an
//!    operation body alone.
//!
//! 2. Under `sort Sat[C] requires Pc2[C = C, Element = Bit]`, the default `both() -> C
//!    requires Unit[T = Element]` called as `Pc2.both()` — in a rule, and in an operation body
//!    — was entered with no `__req_unit` once `Unit` had a second provider: the call's
//!    `Element` was left open, so its own requirement was `Unit[T = ?]`, stamped nothing, and
//!    the derivation from the argument values (there are none) could not choose. Now the
//!    parameters the call leaves open are those the requirement answering it writes
//!    (`bind_params_the_requirement_says`) — the deferral's entry in an operation body, the
//!    one requirement of the spec the rule's sort writes in a rule — so the requirement is
//!    `Unit[T = Bit]` and is stamped; the woven route carries the stamps to the default it
//!    enters (`WovenDispatch::Dispatched.stamps`).
//!
//! ## Back-out
//!
//! Measured 2026-11-03 in one build, a temporary switch each:
//!
//! - the bracket's refusal out (`OpenSlotsNamedApart::of_bracket` not asked): every row of
//!   `a_bracket_the_provisions_say_apart_is_refused` loads clean;
//! - the rule body's call out of the refusal (the block gated on an evaluated body, as
//!   before): its `rule`, `ruleArg`, `ruleIf` and `ruleLambda` rows, and
//!   `a_full_bracket_no_provision_answers_is_refused_in_a_rule`, load clean;
//! - the refusal asked where a requirement of the spec is in scope:
//!   `a_requirement_in_scope_answers_the_bracket` is refused, and so is every woven call
//!   whose `Element` the sort's requirement says — `Pc2[C = ?, Element = Bit]`, which `Bag`
//!   and `Rev` answer naming different `C`s: `the_default_is_read_at_the_requirement_
//!   answering_it` and `wi_me8wr…::a_woven_default_derives_its_own_requirement`;
//! - the deferral's binding out: the operation-body rows of
//!   `the_default_is_read_at_the_requirement_answering_it` (`opSat`, `opRev`, `opNum`,
//!   `opReq`) die `__req_unit not bound`;
//! - the rule sort's binding out, and the woven route's stamps out: its rule rows panic
//!   `__req_unit not bound` (the first, `woven`, ends the test).
//!
//! - the rule's exemption out (the full bracket refused in a rule whatever its sort
//!   requires): `a_rule_whose_sort_requires_the_instance_is_not_refused`'s rule row is
//!   refused `no impl matches`.
//!
//! PASS EITHER WAY, BY DESIGN: `the_full_bracket_and_a_lone_provision_answer` (a bracket that
//! names one instance, by writing it or by one provision completing it), and the
//! operation-body row of `a_rule_whose_sort_requires_the_instance_is_not_refused` (the
//! caller's `requires` covers it, `op_requires_covers_call`).
//!
//! NOT COVERED, measured before and after alike: under `sort Sat[C, E] requires Pc2[C = C,
//! Element = E]` the requirement writes no ground `Element`, so `Pc2.both()` in an operation
//! body still dies `__req_unit not bound` with two providers of `Unit` (it answers with one,
//! from the derivation); its rule twin flounders at `find_dictionary(Pc2, …)` before the
//! default is reached, with one provider as with two.

use anthill_core::eval::value::Value;

const APART: &str = r#"
namespace d5wfq.apart
  import anthill.prelude.{Int64, String, Error, Bool, Function, List}
  import anthill.prelude.List.{length}

  sort Pc2
    sort C = ?
    sort Element = ?
    operation emp() -> C
    operation both() -> C = emp()
  end
  sort Bag
    entity bint
    entity bstr
  end
  sort WInt
    provides Pc2[C = Bag, Element = Int64]
    operation emp() -> Bag = bint()
  end
  sort WStr
    provides Pc2[C = Bag, Element = String]
    operation emp() -> Bag = bstr()
  end
  rule rUse(?b) :- ?b = bint()
  operation ap(f: Function[(), Bag]) -> Bag = f()

  sort Driver
    operation opFull() -> Bag = Pc2[C = Bag, Element = String].both()
    operation opFullInt() -> Bag = Pc2[C = Bag, Element = Int64].both()
  end
end
"#;

const WOVEN: &str = r#"
namespace d5wfq.woven
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
  sort NBag
    entity nnil
    entity nsome(n: Num)
    provides Pc2[C = NBag, Element = Num]
    operation fill(xs: List[T = Num]) -> NBag = match xs
      case nil() -> nnil()
      case cons(x, rest) -> nsome(n: x)
  end
  sort Sat[C]
    requires Pc2[C = C, Element = Bit]
    rule model(vs: C) :- vs <=> Pc2.both()
    operation m() -> C = Pc2.both()
  end
  sort NSat[C]
    requires Pc2[C = C, Element = Num]
    rule model(vs: C) :- vs <=> Pc2.both()
    operation m() -> C = Pc2.both()
  end
  operation viaReq[X]() -> X requires Pc2[C = X, Element = Bit] = Pc2.both()

  sort Driver
    operation woven() -> Int64 effects {Error} = Sat[C = Bag].model(bsome(b: t())).takeN(5).length()
    operation wovenOther() -> Int64 effects {Error} =
      Sat[C = Bag].model(bsome(b: f())).takeN(5).length()
    operation wovenOpen() -> Int64 effects {Error} = Sat[C = Bag].model.takeN(5).length()
    operation wovenRev() -> Int64 effects {Error} = Sat[C = Rev].model(rsome(b: t())).takeN(5).length()
    operation wovenNum() -> Int64 effects {Error} =
      NSat[C = NBag].model(nsome(n: num(n: 0))).takeN(5).length()
    operation opSat() -> Bag = Sat[C = Bag].m()
    operation opRev() -> Rev = Sat[C = Rev].m()
    operation opNum() -> NBag = NSat[C = NBag].m()
    operation opReq() -> Bag = viaReq[X = Bag]()
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

/// `APART` with `decl` written before the driver.
fn apart_with(decl: &str) -> String {
    APART.swap("  sort Driver\n", &format!("{decl}  sort Driver\n"))
}

/// The bracket leaves `Element` out, and the two provisions answering `C = Bag` say it apart:
/// refused at every site that runs the call, each of which loaded and died, or never ran it.
#[test]
fn a_bracket_the_provisions_say_apart_is_refused() {
    let sites = [
        ("op", "  operation op() -> Bag = Pc2[C = Bag].both()\n"),
        ("const", "  const k: Bag = Pc2[C = Bag].both()\n"),
        (
            "opIf",
            "  operation opIf(b: Bool) -> Bag = if b then Pc2[C = Bag].both() else bint()\n",
        ),
        (
            "opLambda",
            "  operation opLambda() -> Bag = ap(lambda () -> Pc2[C = Bag].both())\n",
        ),
        ("rule", "  rule r(?n) :- ?n <=> Pc2[C = Bag].both()\n"),
        (
            "ruleArg",
            "  rule r(?n) :- rUse(Pc2[C = Bag].both()), ?n = 1\n",
        ),
        (
            "ruleIf",
            "  rule r(?n) :- rUse(if true then Pc2[C = Bag].both() else bint()), ?n = 1\n",
        ),
        (
            "ruleLambda",
            "  rule r(?n) :- ?f <=> (lambda () -> Pc2[C = Bag].both()), ?n = 1\n",
        ),
    ];
    let wrong: Vec<String> = sites
        .iter()
        .filter_map(|(site, decl)| {
            let errors = crate::common::load_errors_of(&apart_with(decl));
            let named = errors.len() == 1
                && errors[0].contains("the bracket leaves `Element` unwritten")
                && errors[0].contains("d5wfq.apart.WInt")
                && errors[0].contains("d5wfq.apart.WStr");
            (!named).then(|| format!("{site}: {errors:#?}"))
        })
        .collect();
    assert!(
        wrong.is_empty(),
        "one refusal naming `Element` and both providers; {wrong:#?}"
    );
}

/// A full bracket at an instance nothing provides, in a rule body's call: refused as in an
/// operation body (WI-20261102-ME8WR), where it floundered at run time before.
#[test]
fn a_full_bracket_no_provision_answers_is_refused_in_a_rule() {
    let src = apart_with(
        "  sort Foo\n    entity foo\n  end\n  rule r(?n) :- ?n <=> Pc2[C = Foo, Element = Int64].both()\n",
    );
    let errors = crate::common::load_errors_of(&src);
    assert!(
        errors.len() == 1
            && errors[0].contains("no impl matches")
            && errors[0].contains("C = d5wfq.apart.Foo"),
        "one refusal naming the bracket's instance; got {errors:#?}"
    );
}

/// A rule whose sort requires the instance the bracket names is not refused: the citation
/// supplies its dictionary, as the caller's `requires` does for the operation-body twin, which
/// loads too. Refused at first by the rule body's refusal, which reads no sort's `requires`
/// (found by /code-review).
#[test]
fn a_rule_whose_sort_requires_the_instance_is_not_refused() {
    for body in [
        "    rule r(?n) :- ?n <=> Pc2[C = Foo, Element = Int64].both()\n",
        "    operation g() -> Foo = Pc2[C = Foo, Element = Int64].both()\n",
    ] {
        let src = apart_with(&format!(
            "  sort Foo\n    entity foo\n  end\n  sort Gen\n    \
             requires Pc2[C = Foo, Element = Int64]\n{body}  end\n"
        ));
        let errors = crate::common::load_errors_of(&src);
        assert!(errors.is_empty(), "`{body}` loads clean; got {errors:#?}");
    }
}

/// CONTROL: a bracket that names one instance — written in full, or completed by the one
/// provision answering it — answers as it did.
#[test]
fn the_full_bracket_and_a_lone_provision_answer() {
    assert_answers(
        APART,
        "d5wfq.apart",
        &[("opFull", "bstr"), ("opFullInt", "bint")],
    );
    let lone = APART
        .swap(
            "  sort WStr\n    provides Pc2[C = Bag, Element = String]\n    \
             operation emp() -> Bag = bstr()\n  end\n",
            "",
        )
        .swap(
            "    operation opFull() -> Bag = Pc2[C = Bag, Element = String].both()\n",
            "    operation opFull() -> Bag = Pc2[C = Bag].both()\n",
        );
    assert_answers(&lone, "d5wfq.apart", &[("opFull", "bint")]);
}

/// CONTROL: a requirement of the spec in scope answers what the bracket leaves out, so the
/// bracket is not refused there, and the call runs at the requirement.
#[test]
fn a_requirement_in_scope_answers_the_bracket() {
    let src = apart_with(
        "  sort Gen\n    requires Pc2[C = Bag, Element = String]\n    \
         operation g() -> Bag = Pc2[C = Bag].both()\n  end\n",
    )
    .swap(
        "    operation opFull() -> Bag = Pc2[C = Bag, Element = String].both()\n",
        "    operation opFull() -> Bag = Gen.g()\n",
    );
    assert_answers(&src, "d5wfq.apart", &[("opFull", "bstr")]);
}

/// The default's own `requires Unit[T = Element]`, read at the `Element` the requirement
/// answering the call writes, with two providers of `Unit`: in a rule through the clause's
/// dictionary, in an operation body through the sort's requirement and the operation's own,
/// at two providers of `Pc2` and at a requirement naming the second provider of `Unit`.
#[test]
fn the_default_is_read_at_the_requirement_answering_it() {
    assert_answers(
        WOVEN,
        "d5wfq.woven",
        &[
            ("woven", "1"),
            ("wovenOther", "0"),
            ("wovenOpen", "1"),
            ("wovenRev", "1"),
            ("wovenNum", "1"),
            ("opSat", "bsome(b: t)"),
            ("opRev", "rsome(b: t)"),
            ("opNum", "nsome(n: num(n: 0))"),
            ("opReq", "bsome(b: t)"),
        ],
    );
}
