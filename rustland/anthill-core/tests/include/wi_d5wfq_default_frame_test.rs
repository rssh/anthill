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
//! 3. The same, where the requirement writes `Element` as the caller's own parameter (`sort
//!    GSat[C, E] requires Pc2[C = C, Element = E]`, `viaG[X, Y]() requires Pc2[C = X, Element
//!    = Y]`), measured on c0444525: in an operation body the call died `__req_unit not bound`
//!    whether or not the caller declared `requires Unit[T = E]`, and its rule twin floundered
//!    at `find_dictionary(Pc2, …)`. Now the parameter is read at the body's rigid for it
//!    (`bind_params_the_requirement_says`, at any depth), so the call's own requirement is
//!    `Unit[T = E]`, forwarded from the caller or refused naming the clause to add (§5.2). In
//!    a rule, the citation's bracket writes `E`, which no column mentions: it reaches the
//!    route of the clause's read of `Pc2` (`bracket_params_no_column_reads`), and the default
//!    entered through that dictionary reads `Element` off its provider's provision
//!    (`resolve_bridge_requirements_through`).
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
//! - the rule sort's binding out, and the woven route's stamps out:
//!   `a_parametric_provision_takes_the_call_sites_evidence` panics `__req_unit not bound`.
//!   The rule rows of `the_default_is_read_at_the_requirement_answering_it` answer either way
//!   since the provision read below: `Bag`'s provision says `Element = Bit` too;
//! - the rigid reading out (the requirement's binding taken where ground, as before):
//!   `the_default_is_read_at_the_callers_parameter` dies `__req_unit not bound`, and
//!   `a_call_owing_evidence_at_the_callers_parameter_is_refused` loads clean — with one
//!   provider of `Unit` that program answered, through the bridge's derivation;
//! - the bracket's unopened parameters out of the citation's route: the rows of
//!   `a_rule_reads_the_parameter_its_citation_writes` cited from outside the sort flounder at
//!   `find_dictionary(Pc2, …)` (`ruleInner` answers either way, its citation reads the
//!   enclosing instance);
//! - the provision read out: every row of `a_rule_reads_the_parameter_its_citation_writes`
//!   panics `__req_unit not bound` (the first, `ruleT`, ends the test);
//! - the rule's exemption out (the full bracket refused in a rule whatever its sort
//!   requires): `a_rule_whose_sort_requires_the_instance_is_not_refused`'s rule row is
//!   refused `no impl matches`.
//!
//! PASS EITHER WAY, BY DESIGN: `the_full_bracket_and_a_lone_provision_answer` (a bracket that
//! names one instance, by writing it or by one provision completing it), and the
//! operation-body row of `a_rule_whose_sort_requires_the_instance_is_not_refused` (the
//! caller's `requires` covers it, `op_requires_covers_call`).
//!
//! NOT COVERED: a rule of `GSat[C, E]` cited at `GSat[C = PBox[T = Bit], E = Bit]` — a
//! provision whose `Element` is its own parameter, under a requirement that writes `Element`
//! as the sort's — panics `__req_unit not bound` where it floundered at `find_dictionary(Pc2,
//! …)` before: neither the clause's typing nor the provision says `Element`, and only the
//! citation knows it. A citation that leaves `E` unwritten, or writes one nothing provides
//! `Pc2` at, floundered before and still does, as a citation of `Sat[C]` at an instance
//! nothing provides does.

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

/// The requirement answering the call writes `Element` as the caller's own parameter, which a
/// citation's bracket or a call's arguments fix: two providers of `Unit` throughout, three of
/// `Pc2`, a witness among them, and a provision whose `Element` is its own parameter.
const GENERIC: &str = r#"
namespace d5wfq.generic
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
    operation fillOne(xs: List[T = Element]) -> C requires Unit[T = Element] =
      fill([Unit.unit[T = Element]()])
  end
  sort Bag
    entity bnil
    entity bsome(b: Bit)
    provides Pc2[C = Bag, Element = Bit]
    operation fill(xs: List[T = Bit]) -> Bag = match xs
      case nil() -> bnil()
      case cons(x, rest) -> bsome(b: x)
  end
  sort NBag
    entity nnil
    entity nsome(n: Num)
    provides Pc2[C = NBag, Element = Num]
    operation fill(xs: List[T = Num]) -> NBag = match xs
      case nil() -> nnil()
      case cons(x, rest) -> nsome(n: x)
  end
  sort WBag
    entity wnil
    entity wsome(n: Num)
  end
  sort W
    provides Pc2[C = WBag, Element = Num] where
      operation fill(xs: List[T = Num]) -> WBag = match xs
        case nil() -> wnil()
        case cons(x, rest) -> wsome(n: x)
    end
  end
  sort PBox[T]
    entity pnil
    entity psome(x: T)
    provides Pc2[C = PBox[T = T], Element = T]
    operation fill(xs: List[T = T]) -> PBox[T = T] = match xs
      case nil() -> pnil()
      case cons(x, rest) -> psome(x: x)
  end
  sort GSat[C, E]
    requires Pc2[C = C, Element = E]
    requires Unit[T = E]
    operation m() -> C = Pc2.both()
    rule model(vs: C) :- vs <=> Pc2.both()
    rule modelArg(vs: C) :- vs <=> Pc2.fillOne([])
    operation count() -> Int64 effects {Error} = model.takeN(5).length()
  end
  sort OSat[C, E]
    requires Pc2[C = C, Element = E]
    operation m() -> C requires Unit[T = E] = Pc2.both()
  end
  sort RSat[C, E]
    requires Pc2[C = C, Element = E]
    rule model(vs: C) :- vs <=> Pc2.both()
  end
  sort Sat[C]
    requires Pc2[C = C, Element = Bit]
    rule model(vs: C) :- vs <=> Pc2.both()
  end
  operation viaG[X, Y]() -> X requires Pc2[C = X, Element = Y], Unit[T = Y] = Pc2.both()

  sort Driver
    operation opBag() -> Bag = GSat[C = Bag, E = Bit].m()
    operation opNum() -> NBag = GSat[C = NBag, E = Num].m()
    operation opWit() -> WBag = GSat[C = WBag, E = Num].m()
    operation opOwn() -> Bag = OSat[C = Bag, E = Bit].m()
    operation opFn() -> Bag = viaG[X = Bag, Y = Bit]()
    operation ruleT() -> Int64 effects {Error} = GSat[C = Bag, E = Bit].model(bsome(b: t())).takeN(5).length()
    operation ruleF() -> Int64 effects {Error} = GSat[C = Bag, E = Bit].model(bsome(b: f())).takeN(5).length()
    operation ruleOpen() -> Int64 effects {Error} = GSat[C = Bag, E = Bit].model.takeN(5).length()
    operation ruleNum() -> Int64 effects {Error} =
      GSat[C = NBag, E = Num].model(nsome(n: num(n: 0))).takeN(5).length()
    operation ruleWit() -> Int64 effects {Error} =
      GSat[C = WBag, E = Num].model(wsome(n: num(n: 0))).takeN(5).length()
    operation ruleInner() -> Int64 effects {Error} = GSat[C = Bag, E = Bit].count()
    operation ruleArg() -> Int64 effects {Error} =
      GSat[C = Bag, E = Bit].modelArg(bsome(b: t())).takeN(5).length()
    operation ruleNoReq() -> Int64 effects {Error} = RSat[C = Bag, E = Bit].model(bsome(b: t())).takeN(5).length()
    operation boxT() -> Int64 effects {Error} = Sat[C = PBox[T = Bit]].model(psome(x: t())).takeN(5).length()
    operation boxF() -> Int64 effects {Error} = Sat[C = PBox[T = Bit]].model(psome(x: f())).takeN(5).length()
  end
end
"#;

/// One provider of `Unit`, and a generic caller holding no `Unit[T = E]`.
const ONE_UNIT: &str = r#"
namespace d5wfq.one
  import anthill.prelude.{List}
  import anthill.prelude.List.{nil, cons}

  sort Unit
    sort T = ?
    operation unit() -> T
  end
  sort Bit
    entity t
    provides Unit[T = Bit]
    operation unit() -> Bit = t()
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
  sort NoUnit[C, E]
    requires Pc2[C = C, Element = E]
    operation m() -> C = Pc2.both()
  end
  sort Driver
    operation op() -> Bag = NoUnit[C = Bag, E = Bit].m()
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

/// An operation body: the requirement answering the call writes `Element` as the caller's
/// parameter, so the call's own requirement is `Unit[T = E]`, which the caller's `requires`
/// answers — the sort's, the operation's own, a generic operation's — at both providers of
/// `Unit`, and at a witness.
#[test]
fn the_default_is_read_at_the_callers_parameter() {
    assert_answers(
        GENERIC,
        "d5wfq.generic",
        &[
            ("opBag", "bsome(b: t)"),
            ("opNum", "nsome(n: num(n: 0))"),
            ("opWit", "wsome(n: num(n: 0))"),
            ("opOwn", "bsome(b: t)"),
            ("opFn", "bsome(b: t)"),
        ],
    );
}

/// The same calls where the caller holds no `Unit[T = E]`: refused where they are written,
/// naming the requirement and the clause to add — the caller's frame is the only thing that
/// could supply it (kernel-language §5.2). Each loaded and died `__req_unit not bound`.
#[test]
fn a_call_owing_evidence_at_the_callers_parameter_is_refused() {
    for (decl, requirement, owner) in [
        (
            "  sort NoUnit[C, E]\n    requires Pc2[C = C, Element = E]\n    \
             operation m() -> C = Pc2.both()\n  end\n",
            "d5wfq.generic.Unit[T = E]",
            "d5wfq.generic.NoUnit",
        ),
        (
            "  operation viaNo[X, Y]() -> X requires Pc2[C = X, Element = Y] = Pc2.both()\n",
            "d5wfq.generic.Unit[T = Y]",
            "d5wfq.generic.viaNo",
        ),
    ] {
        let src = GENERIC.swap("  sort Driver\n", &format!("{decl}  sort Driver\n"));
        assert_owes(&src, requirement, owner);
    }
    // One provider of `Unit`: the bridge's derivation chose it, and the call answered
    // `bsome(b: t)`; the evidence is still the caller's to hold (§5.2).
    assert_owes(ONE_UNIT, "d5wfq.one.Unit[T = E]", "d5wfq.one.NoUnit");
}

/// `src` loads with the one refusal of a call whose requirement `requirement` only `owner`'s
/// frame could supply.
fn assert_owes(src: &str, requirement: &str, owner: &str) {
    let errors = crate::common::load_errors_of(src);
    assert!(
        errors.len() == 1
            && errors[0].contains(&format!("requirement `{requirement}` cannot be supplied"))
            && errors[0].contains(&format!("Declare `requires {requirement}` on `{owner}`")),
        "one refusal naming `{requirement}` and `{owner}`; got {errors:#?}"
    );
}

/// A rule: the citation's bracket writes `E`, which no column of the clause mentions, so the
/// clause's read of `Pc2` is routed at it, and the default entered through that dictionary
/// reads `Element` at the provider's provision — from outside the sort and from a member of
/// it, at two providers of `Pc2`, at a witness, and where the sort requires no `Unit` (the
/// citation's `Unit[T = Bit]` is constructed when the default enters).
#[test]
fn a_rule_reads_the_parameter_its_citation_writes() {
    assert_answers(
        GENERIC,
        "d5wfq.generic",
        &[
            ("ruleT", "1"),
            ("ruleF", "0"),
            ("ruleOpen", "1"),
            ("ruleNum", "1"),
            ("ruleWit", "1"),
            ("ruleInner", "1"),
            ("ruleNoReq", "1"),
            ("ruleArg", "1"),
        ],
    );
}

/// A provision whose `Element` is its own parameter says no type for it, so the default is
/// read at the call's stamps: the rule sort's requirement writes `Element = Bit`.
#[test]
fn a_parametric_provision_takes_the_call_sites_evidence() {
    assert_answers(GENERIC, "d5wfq.generic", &[("boxT", "1"), ("boxF", "0")]);
}
