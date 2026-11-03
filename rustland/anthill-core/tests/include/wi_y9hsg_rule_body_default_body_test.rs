//! WI-20261102-Y9HSG — A RULE-BODY CALL THAT CARRIES ITS DICTIONARY RUNS THE DEFAULT BODY ITS
//! PROVIDER INHERITS, at the instance the dictionary names (kernel-language §8.7, "Defaulted
//! operations … carry over automatically"; §5.2, "A spec's default body is not such a
//! dispatch").
//!
//! Found on WI-20260925-SHED7 step 3 (the `fromList` default body). Measured on ee37ed91, the
//! program below: `Sat[C = Bag[T = Bit]].model` raised `relation_floundered(goals:
//! [unify(bnil, apply_within(fn: fromL, …, requirements: [Dictionary(impl: Bag)]))])`. The
//! woven call's dictionary was bound and the resolver selected the default for it, but
//! handed the bridge no dictionary (`call_op_bridged`'s `dispatched_through`): the default
//! reads none of `Bag`'s slots, which was the whole of the test, so its frame had no
//! `__req_self` and the receiver-less `emp()` had nothing to be dispatched by. The test is
//! now the typer's (`classify_pin_or_apply_within`'s `threads_instance`): a member declared
//! in a sort that is not the dictionary's provider takes the dictionary as its dispatch
//! environment (`DictionaryOwed::Environment`, kb/resolve.rs).
//!
//! The same default reached by a call the TYPER classified with its dictionary — a bracket
//! in a rule with no enclosing requirement, `Pc2[C = Bag[T = Bit]].fromL([t(), f()])` — had
//! the same defect on another route: the bridge derived the callee's frame from the argument
//! types, which fix no `C`, and ignored the dictionary the class carries
//! (`CalleeFrame::Dict`). It is handed over now (`WovenDispatch::Classified`), where the
//! callee needs it and the dictionary covers what the callee reads; a refining spec's default
//! (`Mid.viaMid`, whose `Mk` slot the derivation left without a provider) is the `Slots` case
//! of it.
//!
//! ## Back-out
//!
//! Measured 2026-11-02 in one build, a temporary switch each:
//!
//! - the `Environment` answer out (`dictionary_owed_to` answering `Nothing` for it): every
//!   row of `a_woven_call_runs_the_default_its_provider_inherits` and
//!   `a_conditional_provider_answers_through_the_woven_call` flounders, and the direct rows
//!   of `a_classified_call_runs_the_default_through_its_dictionary` but `Mid.viaMid`;
//! - the classified dictionary out (`classified` always `None`): every row of
//!   `a_classified_call_runs_the_default_through_its_dictionary` fails, the woven tests pass;
//! - the classified dictionary for `Environment` alone (the `Slots` case out): only
//!   `Mid.viaMid` fails;
//! - the classified dictionary for a callee with a `requires` of its own (`OwnSlots` taken,
//!   as a first cut did): `spec_op_requirement_at_member_test`'s two rule-body rows raise
//!   `DeferToRequirement: requirement param `__req_tagger` not bound` — the dictionary fills
//!   the sort's half of the frame and nothing derives the operation's own slot.
//!
//! No row drives the two narrowings that keep both engines on one member: the classified
//! dictionary only where the provider's table answers the classified callee itself, and
//! `Environment` only for a member of a spec the provider provides (both backed out, the full
//! workspace passed: 11,554, 0 failed).
//!
//! PASS EITHER WAY, BY DESIGN: `the_member_the_provider_writes_and_the_operation_body_answer`
//! — the body-less spec operation written by each provider, through the woven call and the
//! bracket, and the operation-body call of the default, which eval enters through its own
//! dictionary.

use anthill_core::eval::value::Value;

const SRC: &str = r#"
namespace y9hsg
  import anthill.prelude.Int64.{add}
  import anthill.prelude.List.{length, nil, cons}
  import anthill.prelude.{Int64, List, Error}

  sort Bit
    entity t
    entity f
  end
  fact neg(t(), f())
  fact neg(f(), t())
  rule or2(?a, ?)  :- ?a <=> t()
  rule or2(?a, ?b) :- ?a <=> f(), ?b <=> t()

  sort Pc2
    sort C = ?
    sort Element = ?
    operation ins(c: C, elem: Element) -> C
    operation emp() -> C
    operation fromL(xs: List[T = Element]) -> C =
      match xs
        case nil() -> emp()
        case cons(x, rest) -> ins(fromL(rest), x)
    operation viaDefault(xs: List[T = Element]) -> C = fromL(xs)
  end

  sort Bag[T]
    entity bnil
    entity badd(e: T, rest: Bag[T = T])
    provides Pc2[C = Bag[T = T], Element = T]
    operation ins(c: Bag[T = T], elem: T) -> Bag[T = T] = badd(e: elem, rest: c)
    operation emp() -> Bag[T = T] = bnil()
  end

  -- `Bag`'s shape under other names: run at the wrong instance, the default builds a value
  -- of the other sort.
  sort Rev[T]
    entity rnil
    entity rcons(e: T, rest: Rev[T = T])
    provides Pc2[C = Rev[T = T], Element = T]
    operation ins(c: Rev[T = T], elem: T) -> Rev[T = T] = rcons(e: elem, rest: c)
    operation emp() -> Rev[T = T] = rnil()
  end

  sort Weight
    sort T = ?
    operation weight(x: T) -> Int64
  end
  sort Coin
    entity heads
    entity tails
    provides Weight[T = Coin]
    operation weight(x: Coin) -> Int64 = match x
      case heads() -> 10
      case tails() -> 1
  end
  -- A conditional provider: its members read the element's `Weight` out of their frame.
  sort Tally[T]
    entity tally(n: Int64)
    provides Pc2[C = Tally[T = T], Element = T] :- Weight[T = T] where
      operation ins(c: Tally[T = T], elem: T) -> Tally[T = T] = match c
        case tally(n) -> tally(n: add(n, Weight.weight(elem)))
      operation emp() -> Tally[T = T] = tally(n: 0)
    end
  end

  sort Sat[C]
    requires Pc2[C = C, Element = Bit]
    rule model(vs: C)
      :- vs <=> Pc2.fromL([?p, ?q, ?r]),
         neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
         or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
    rule viaDef(vs: C)
      :- vs <=> Pc2.viaDefault([?p, ?q, ?r]),
         neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
         or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
    rule bracket(vs: C)
      :- vs <=> Pc2[C = C].fromL([?p, ?q, ?r]),
         neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
         or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
  end
  sort Use[C]
    requires Pc2[C = C, Element = Coin]
    rule total(vs: C) :- vs <=> Pc2.fromL([heads(), tails(), heads()])
  end

  -- A default with no argument at all, and a refining spec's own default.
  sort Mk
    sort C = ?
    operation e() -> C
    operation viaDefault() -> C = e()
  end
  sort Mid
    sort C = ?
    provides Mk[C = C]
    operation viaMid() -> C = e()
  end
  sort A
    entity a(n: Int64)
    provides Mid[C = A]
    operation e() -> A = a(n: 1)
  end
  sort B
    entity b(n: Int64)
    provides Mid[C = B]
    operation e() -> B = b(n: 2)
  end
  sort Gen[X]
    requires Mk[C = X]
    rule g(x: X) :- x <=> Mk.viaDefault()
  end

  rule rBagTF(?v) :- ?v <=> Pc2[C = Bag[T = Bit]].fromL([t(), f()])
  rule rBagOpen(?v) :- ?v <=> Pc2[C = Bag[T = Bit]].fromL([?p, ?q]), neg(?p, ?q)
  rule rRevViaDefault(?v) :- ?v <=> Pc2[C = Rev[T = Bit]].viaDefault([t(), f()])
  rule rTallyHT(?v) :- ?v <=> Pc2[C = Tally[T = Coin]].fromL([heads(), tails()])
  rule rMkA(?x) :- ?x <=> Mk[C = A].viaDefault()
  rule rMkB(?x) :- ?x <=> Mk[C = B].viaDefault()
  rule rMidB(?x) :- ?x <=> Mid[C = B].viaMid()

  sort Driver
    operation model() -> Int64 effects {Error} = Sat[C = Bag[T = Bit]].model.takeN(100).length()
    operation given() -> Int64 effects {Error} =
      Sat[C = Bag[T = Bit]].model(badd(e: t(), rest: badd(e: t(), rest: badd(e: f(), rest: bnil())))).takeN(5).length()
    operation refuted() -> Int64 effects {Error} =
      Sat[C = Bag[T = Bit]].model(badd(e: t(), rest: badd(e: t(), rest: badd(e: t(), rest: bnil())))).takeN(5).length()
    operation revModel() -> Int64 effects {Error} = Sat[C = Rev[T = Bit]].model.takeN(100).length()
    operation revGiven() -> Int64 effects {Error} =
      Sat[C = Rev[T = Bit]].model(rcons(e: f(), rest: rcons(e: f(), rest: rcons(e: t(), rest: rnil())))).takeN(5).length()
    operation viaDef() -> Int64 effects {Error} = Sat[C = Bag[T = Bit]].viaDef.takeN(100).length()
    operation bracket() -> Int64 effects {Error} = Sat[C = Bag[T = Bit]].bracket.takeN(100).length()
    operation genA() -> Int64 effects {Error} = Gen[X = A].g(a(n: 1)).takeN(5).length()
    operation genB() -> Int64 effects {Error} = Gen[X = B].g(b(n: 2)).takeN(5).length()
    operation tallyHeld() -> Int64 effects {Error} = Use[C = Tally[T = Coin]].total(tally(n: 21)).takeN(5).length()
    operation tallyRefuted() -> Int64 effects {Error} = Use[C = Tally[T = Coin]].total(tally(n: 3)).takeN(5).length()
    operation bagTF() -> Int64 effects {Error} =
      rBagTF(badd(e: t(), rest: badd(e: f(), rest: bnil()))).takeN(5).length()
    operation bagFT() -> Int64 effects {Error} =
      rBagTF(badd(e: f(), rest: badd(e: t(), rest: bnil()))).takeN(5).length()
    operation bagOpen() -> Int64 effects {Error} = rBagOpen.takeN(5).length()
    operation revViaDefault() -> Int64 effects {Error} =
      rRevViaDefault(rcons(e: t(), rest: rcons(e: f(), rest: rnil()))).takeN(5).length()
    operation tallyHT() -> Int64 effects {Error} = rTallyHT(tally(n: 11)).takeN(5).length()
    operation mkA() -> Int64 effects {Error} = rMkA(a(n: 1)).takeN(5).length()
    operation mkB() -> Int64 effects {Error} = rMkB(b(n: 2)).takeN(5).length()
    operation mkBWrong() -> Int64 effects {Error} = rMkB(b(n: 1)).takeN(5).length()
    operation midB() -> Int64 effects {Error} = rMidB(b(n: 2)).takeN(5).length()
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

/// Each entry's answer beside the one it should be, every mismatch reported at once.
fn assert_answers(src: &str, ns: &str, rows: &[(&str, i64)]) {
    let mut interp = crate::common::interp_for(src);
    let wrong: Vec<String> = rows
        .iter()
        .filter_map(
            |&(entry, want)| match interp.call(&format!("{ns}.Driver.{entry}"), &[]) {
                Ok(Value::Int(n)) if n == want => None,
                other => Some(format!("`{entry}`: expected {want}, got {other:?}")),
            },
        )
        .collect();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The ticket's rows: tiny-sat's two models through a woven `Pc2.fromL` at `Bag`, the model
/// `t t f` held and `t t t` refuted; at `Rev`, whose two models are built of `rcons`; a default
/// calling a default; the call's own bracket; a default with no argument (`Mk.viaDefault()`)
/// at each provider of a refining spec.
#[test]
fn a_woven_call_runs_the_default_its_provider_inherits() {
    assert_answers(
        SRC,
        "y9hsg",
        &[
            ("model", 2),
            ("given", 1),
            ("refuted", 0),
            ("revModel", 2),
            ("revGiven", 1),
            ("viaDef", 2),
            ("bracket", 2),
            ("genA", 1),
            ("genB", 1),
        ],
    );
}

/// The provider's members read their element's dictionary out of the frame the default
/// enters them with: `heads, tails, heads` weighs 21.
#[test]
fn a_conditional_provider_answers_through_the_woven_call() {
    assert_answers(SRC, "y9hsg", &[("tallyHeld", 1), ("tallyRefuted", 0)]);
}

/// The bracket written in a rule with no enclosing requirement: the typer's dictionary.
#[test]
fn a_classified_call_runs_the_default_through_its_dictionary() {
    assert_answers(
        SRC,
        "y9hsg",
        &[
            ("bagTF", 1),
            ("bagFT", 0),
            ("bagOpen", 2),
            ("revViaDefault", 1),
            ("tallyHT", 1),
            ("mkA", 1),
            ("mkB", 1),
            ("mkBWrong", 0),
            ("midB", 1),
        ],
    );
}

/// CONTROLS. `fromL` body-less and written by each provider: the woven call and the bracket
/// reach `Bag`'s member. The default called from an operation body: eval enters it through
/// the dictionary its own apply builds.
#[test]
fn the_member_the_provider_writes_and_the_operation_body_answer() {
    let written = SRC
        .swap(
            "    operation fromL(xs: List[T = Element]) -> C =\n      match xs\n        \
             case nil() -> emp()\n        case cons(x, rest) -> ins(fromL(rest), x)\n    \
             operation viaDefault(xs: List[T = Element]) -> C = fromL(xs)\n",
            "    operation fromL(xs: List[T = Element]) -> C\n",
        )
        .swap(
            "    operation emp() -> Bag[T = T] = bnil()\n",
            "    operation emp() -> Bag[T = T] = bnil()\n    \
             operation build(xs: List[T = T]) -> Bag[T = T] = match xs\n      \
             case nil() -> bnil()\n      case cons(x, rest) -> badd(e: x, rest: build(rest))\n    \
             operation fromL(xs: List[T = T]) -> Bag[T = T] = build(xs)\n",
        )
        .swap(
            "    operation emp() -> Rev[T = T] = rnil()\n",
            "    operation emp() -> Rev[T = T] = rnil()\n    \
             operation build(xs: List[T = T]) -> Rev[T = T] = match xs\n      \
             case nil() -> rnil()\n      case cons(x, rest) -> rcons(e: x, rest: build(rest))\n    \
             operation fromL(xs: List[T = T]) -> Rev[T = T] = build(xs)\n",
        )
        .swap(
            "      operation emp() -> Tally[T = T] = tally(n: 0)\n",
            "      operation emp() -> Tally[T = T] = tally(n: 0)\n      \
             operation fromL(xs: List[T = T]) -> Tally[T = T] = tally(n: weigh(xs))\n",
        )
        .swap(
            "    entity tally(n: Int64)\n",
            "    entity tally(n: Int64)\n    \
             operation weigh(xs: List[T = T]) -> Int64 requires Weight[T = T] = match xs\n      \
             case nil() -> 0\n      \
             case cons(x, rest) -> add(weigh(rest), Weight.weight(x))\n",
        )
        .swap("    operation viaDef() -> Int64 effects {Error} = Sat[C = Bag[T = Bit]].viaDef.takeN(100).length()\n", "")
        .swap("    rule viaDef(vs: C)\n      :- vs <=> Pc2.viaDefault([?p, ?q, ?r]),\n         neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),\n         or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)\n", "")
        .swap("  rule rRevViaDefault(?v) :- ?v <=> Pc2[C = Rev[T = Bit]].viaDefault([t(), f()])\n", "")
        .swap(
            "    operation revViaDefault() -> Int64 effects {Error} =\n      \
             rRevViaDefault(rcons(e: t(), rest: rcons(e: f(), rest: rnil()))).takeN(5).length()\n",
            "",
        );
    assert_answers(
        &written,
        "y9hsg",
        &[
            ("model", 2),
            ("given", 1),
            ("refuted", 0),
            ("revModel", 2),
            ("bracket", 2),
            ("tallyHeld", 1),
            ("bagTF", 1),
            ("bagFT", 0),
            ("tallyHT", 1),
        ],
    );
    let op_body = SRC.swap(
        "  sort Driver\n",
        "  sort Driver\n    \
         operation opBody() -> Int64 = match Pc2[C = Tally[T = Coin]].fromL([heads(), tails(), heads()])\n      \
         case tally(n) -> n\n",
    );
    assert_answers(&op_body, "y9hsg", &[("opBody", 21)]);
}
