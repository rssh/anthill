//! WI-20260911-5G28A — a requirement DICTIONARY reaching a RULE: the measurements the
//! type-domains direction (`docs/design/060-typedomains-implementation.md`) stands on, and
//! `060-implementation.md` §7.3's S2, which carries the caller's dictionary across a rule
//! citation.
//!
//! 1. A RULE CITATION PASSES THE CALLER'S DICTIONARY (§7.3 S2). An operation with a rigid
//!    `A` and `requires WeakOrd[T = A]` cites a rule that calls `compare` on its values.
//!    Selected `[WeakOrd = Descending]`, the operation's OWN call answers through
//!    `Descending` — and so, since S2, does the RULE: the citation routes the clause's
//!    requirement read to the caller's slot, eval captures the dictionary in the
//!    relation's goal, and the resolver binds it when it opens the clause. Before S2 the
//!    rule answered `Int64`'s own ordering whichever rival the caller selected — nothing
//!    carried the dictionary across (`op-to-rule-requirement-channel.md` §5.1, crossing 2),
//!    so the clause DERIVED one at the value's type, where 058 §3.2's default rung takes
//!    the carrier's own provision. A rule body cannot select a provider itself — the loader
//!    refuses a bracket there ("call an operation whose body carries the bracket") — so a
//!    passed dictionary is the only route a caller's choice has into a rule. §1b is the
//!    WEAVE: a carrier-bearing call in the clause dispatches through the passed dictionary,
//!    at its own carrier only.
//!
//! 2. (GONE.) A DICTIONARY AS AN ORDINARY RULE ARGUMENT, ITS SUBTREE PROJECTED — the gate the
//!    ticket set on 2026-09-12: a dictionary derived in one clause, `?d = require[X]`, rode a
//!    generative call as a head argument, and `Dictionary.sub(?d, 0)` projected the element's.
//!    Proposal 060.1 §5 removed the form, and no clause binds a dictionary to a column now;
//!    the element's dictionary reaching a call is
//!    `nar1x_carrier_less_spec_op_test::the_selected_impls_own_requirement_is_filled_from_the_dictionary`.
//!
//! 3. THE WHOLE CASE — demo2: a GENERATIVE citation of a parameterised sort whose clause
//!    both ENUMERATES its values and CALLS AN OPERATION on each, the operation's provider
//!    chosen by the caller among two rivals. Both of today's answers are PINNED, and since
//!    S2 both are the drain's `relation_floundered` — undecided, and said so, where the
//!    count said `0` and the projected spelling found no row. `060-implementation.md` §7.3
//!    names the steps that flip each.
//!
//! BACK-OUT, measured one axis at a time over the whole `wi_tests` binary (each run, not
//! predicted):
//!  * [V] the `from_view` fallback in `expect_dictionary` (`eval/builtins.rs`) — section 2's
//!    rows failed, which went with `require[X]`; no row here reaches that fallback now.
//!  * S2's four links, each alone: [T] no routes (`settle_citation_routes` not run), [E] no
//!    capture (`citation_requirements` answering nothing), [R] no bind
//!    (`bind_citation_reads` binding nothing), [D] a supplied dictionary checked on the
//!    DEFAULT rung. The same 4 red under each: `a_rule_citation_passes_the_callers_dictionary`
//!    and `a_returned_relation_keeps_the_callers_dictionary` (`-1`, or under [D] no answer —
//!    the default refuses the caller's choice), `a_carrier_bearing_call_dispatches_through_
//!    the_passed_dictionary`, and `a_call_at_another_carrier_keeps_its_own_dispatch`'s `30`.
//!  * [W] the weave's old carrier-LESS gate (a carrier-bearing body-less call left to value
//!    dispatch). Those 4, and both demo2 pins: the unwoven `Score.score(?v, 3)` answers
//!    nothing with `?v` unbound, so the count is `0` again and `.head` finds no row.
//!  * [C] the weave's carrier DIRECTION (every covered call woven, whatever it carries). 2
//!    red: `a_call_at_another_carrier_keeps_its_own_dispatch` (`30` at `dark()`) and
//!    `wi_hrfr5_witness_attribution_test::a_typed_head_carrier_is_readable_too` (refused:
//!    each of its two calls covered by both `require`s).
//!
//! PASS EITHER WAY, BY DESIGN: `an_operation_passes_its_dictionary_to_an_operation` (op→op
//! passing, which is what makes section 1's number about the RULE edge),
//! `a_caller_without_a_dictionary_answers_as_before` and
//! `a_carrier_bearing_call_without_a_passed_dictionary_answers_as_before` (no dictionary is
//! passed, so the clause derives its own — the carrier's). Nothing else in `wi_tests` moved
//! under any S2 axis.
//!
//! The axes above were measured while the clauses wrote `require[X]`; since proposal 060.1
//! §5 each declares its requirement at its head's introducer (`cmp[A](?a: A, ?b: A, ?c) :-
//! WeakOrd[T = A]`, `cmpBare` under a name), and the answers are the same. They were not
//! backed out again.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

// ── 1. the op→rule citation ─────────────────────────────────────────────────

/// Two opposite `Ord[Int64]` rivals beside `Int64`'s own provision — WI-870's pair, so
/// the three answers differ: `Descending` gives `4`, `Ascending` `-4`, and `Int64`'s own
/// `compare` `-1`, for `compare(1, 5)`.
const ORD_PROGRAM: &str = r#"
namespace wi5g28a.ord
  import anthill.prelude.{Int64, Error, EmptyStream, Relation, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end

  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  -- a RULE that calls an operation of the requirement on its values, the guard unnamed and
  -- under a name
  rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)
  rule cmpBare[A](?a: A, ?b: A, ?c) :- require w: WeakOrd[T = A], w.compare(?a, ?b, ?c)

  sort Driver
    -- rigid `A`, with the requirement at `A`
    operation direct[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
    operation viaRule[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = cmp(x, y).head.c
    operation viaBare[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = cmpBare(x, y).head.c
    -- the relation RETURNED: it is run after `made`'s frame has popped
    operation made[A](x: A, y: A) -> Relation[T = (c: Int64), E = {Error}]
      requires WeakOrd[T = A] = cmp(x, y)

    operation directDesc() -> Int64 = direct[A = Int64, WeakOrd = Descending](1, 5)
    operation directAsc() -> Int64 = direct[A = Int64, WeakOrd = Ascending](1, 5)
    operation ruleDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Int64, WeakOrd = Descending](1, 5)
    operation ruleAsc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Int64, WeakOrd = Ascending](1, 5)
    operation bareDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaBare[A = Int64, WeakOrd = Descending](1, 5)
    operation bareAsc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaBare[A = Int64, WeakOrd = Ascending](1, 5)
    operation madeDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      made[A = Int64, WeakOrd = Descending](1, 5).head.c
    -- a caller that holds NO dictionary: the edge constructs what the clause would derive
    operation plain() -> Int64 effects {Error, Error[EmptyStream]} = cmp(1, 5).head.c
  end
end
"#;

/// Call a nullary driver on a FRESH interpreter — a trapped call poisons later calls on
/// a shared one, and `interp_for` panics on a dirty load, so a value here is also a
/// clean-load assertion.
fn drive(entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(ORD_PROGRAM);
    match interp.call(&format!("wi5g28a.ord.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// THE CONTROL for the pin below — passes either way, BY DESIGN. Between two OPERATIONS
/// the selected dictionary does travel: `direct`'s `compare` answers through whichever
/// rival its caller named. So when the rule below answers otherwise, the loss is at the
/// rule edge, not in the selection.
#[test]
fn an_operation_passes_its_dictionary_to_an_operation() {
    assert_eq!(drive("directDesc"), 4, "Descending: compare(1, 5) = 5 - 1");
    assert_eq!(drive("directAsc"), -4, "Ascending: compare(1, 5) = 1 - 5");
}

/// THE CASE — a rigid `A` passed WITH `WeakOrd[A]` into a rule (§7.3 S2). Before S2 both
/// selections answered `-1`, `Int64`'s own `compare`: the citation `cmp(x, y)` built its
/// query from the head alone, `viaRule`'s `WeakOrd[A]` dictionary stayed in `viaRule`'s
/// frame, and `cmp`'s read re-derived at the value's type, where the carrier's own provision
/// is the default among three. Now the citation routes the read to `viaRule`'s slot, eval
/// captures the dictionary, and the resolver binds it in the clause — so the answers are the
/// ones the operation-to-operation control above gives. Both spellings of the requirement,
/// the guard and the guard under a name (they were `?d = require[…]` and the bare
/// `require[…]`, removed by proposal 060.1 §5).
#[test]
fn a_rule_citation_passes_the_callers_dictionary() {
    assert_eq!(
        (drive("ruleDesc"), drive("ruleAsc")),
        (4, -4),
        "the rule answers through the rival the CALLER selected (the guard)",
    );
    assert_eq!(
        (drive("bareDesc"), drive("bareAsc")),
        (4, -4),
        "and through the guard under a name alike",
    );
}

/// THE CAPTURE — the relation is RETURNED by the operation that cited it and run after that
/// frame has popped, so its dictionary cannot be read from a frame at run time: it has to be
/// in the value (op-to-rule-requirement-channel.md §5.1, and §7 step 4's own acceptance
/// row). `4` is `Descending`'s answer.
#[test]
fn a_returned_relation_keeps_the_callers_dictionary() {
    assert_eq!(drive("madeDesc"), 4, "the captured dictionary outlives `made`'s frame");
}

/// CONTROL — passes either way, BY DESIGN. A caller that holds NO dictionary gets what the
/// clause derives on its own: the edge constructs `Int64`'s own provision (058 §3.2's
/// default, which a caller that chose nothing leaves in charge), and the clause's read, now
/// CHECKING a supplied dictionary, finds rivals and lets it stand.
#[test]
fn a_caller_without_a_dictionary_answers_as_before() {
    assert_eq!(drive("plain"), -1, "`Int64`'s own `compare`, the default among three");
}

// ── 1b. the weave: a carrier-bearing call dispatches through the passed dictionary ──

/// `Rank` is a spec whose operation is BODY-LESS and CARRIER-BEARING (`rank(x: T)`), with
/// the carrier's own provision beside two rival witnesses — the shape WI-1040's weave used
/// to leave to value-directed dispatch, on the ground that "the value-directed route
/// already decides it". It does not, once a clause can be handed a dictionary its caller
/// CHOSE: the value names `Colour`, and only the dictionary names `ByHeat`. `Shade` is a
/// second carrier with its own provision, for the row that says the dictionary reaches the
/// call at ITS carrier and no other.
const RANK_PROGRAM: &str = r#"
namespace wi5g28a.rank
  import anthill.prelude.{Int64, Error, EmptyStream}

  sort Rank
    sort T = ?
    operation rank(x: T) -> Int64
  end

  sort Colour
    import anthill.prelude.Int64
    entity red
    provides Rank[T = Colour]
    operation rank(x: Colour) -> Int64 = 1
  end

  sort ByHeat
    import anthill.prelude.Int64
    provides Rank[T = Colour]
    operation rank(x: Colour) -> Int64 = 30
  end

  sort ByName
    import anthill.prelude.Int64
    provides Rank[T = Colour]
    operation rank(x: Colour) -> Int64 = 20
  end

  sort Shade
    import anthill.prelude.Int64
    entity dark
    provides Rank[T = Shade]
    operation rank(x: Shade) -> Int64 = 5
  end

  rule rankOf[A](?a: A, ?r) :- Rank[T = A], Rank.rank(?a, ?r)
  -- one requirement at `?a`'s type, and another at `?b`'s
  rule rankBoth[A, B](?a: A, ?b: B, ?r1, ?r2) :- Rank[T = A], Rank[T = B], Rank.rank(?a, ?r1), Rank.rank(?b, ?r2)

  sort Driver
    operation viaRule[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires Rank[T = A] = rankOf(x).head.r
    operation heat() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Colour, Rank = ByHeat](red())
    operation name() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Colour, Rank = ByName](red())
    operation own() -> Int64 effects {Error, Error[EmptyStream]} = rankOf(red()).head.r
    operation bothAt[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires Rank[T = A] = rankBoth(x, dark()).head.r1
    operation bothOther[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires Rank[T = A] = rankBoth(x, dark()).head.r2
    operation heatAt() -> Int64 effects {Error, Error[EmptyStream]} =
      bothAt[A = Colour, Rank = ByHeat](red())
    operation heatOther() -> Int64 effects {Error, Error[EmptyStream]} =
      bothOther[A = Colour, Rank = ByHeat](red())
    operation ownOther() -> Int64 effects {Error, Error[EmptyStream]} =
      rankBoth(red(), dark()).head.r2
  end
end
"#;

fn drive_rank(entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(RANK_PROGRAM);
    match interp.call(&format!("wi5g28a.rank.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// The passed dictionary reaches a carrier-bearing, body-less call inside the rule: `30` is
/// `ByHeat`'s, `20` is `ByName`'s. Value-directed dispatch would answer `1` for both — the
/// carrier's own — which is what this row answered with the weave's old carrier gate.
#[test]
fn a_carrier_bearing_call_dispatches_through_the_passed_dictionary() {
    assert_eq!((drive_rank("heat"), drive_rank("name")), (30, 20));
}

/// CONTROL — passes either way, BY DESIGN: with no dictionary passed, the woven call
/// dispatches through the one the clause derives, which is the carrier's own, as the
/// value-directed route did.
#[test]
fn a_carrier_bearing_call_without_a_passed_dictionary_answers_as_before() {
    assert_eq!(drive_rank("own"), 1);
}

/// THE WEAVE IS CARRIER-DIRECTED: a dictionary covers the calls AT ITS OWN CARRIER, and a
/// call at another argument keeps the dispatch its value gives it. `rankBoth` reads its one
/// requirement at `?a`; `?b` is `dark()`, a `Shade`, whose own answer is `5`.
///
/// Without the direction the weave is carrier-blind, and each dictionary is threaded into
/// BOTH calls: the passed `ByHeat` answers `30` at `dark()`, and the dictionary the clause
/// derives from `red()` answers `1` there — a clean load and a definite wrong number either
/// way. `30` at `?a` is the half that says the direction did not simply un-weave the call.
#[test]
fn a_call_at_another_carrier_keeps_its_own_dispatch() {
    assert_eq!(drive_rank("heatAt"), 30, "the passed dictionary reaches the call at its carrier");
    assert_eq!(drive_rank("heatOther"), 5, "and not the call at `dark()`");
    assert_eq!(drive_rank("ownOther"), 5, "nor does a DERIVED one");
}

/// The sort a symbol answer names, by qualified name — read through the view, since an
/// answer may ride a `SymbolRef` or a nullary term.
fn sort_named(kb: &KnowledgeBase, v: &Value) -> String {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Ident(s)
        | ViewHead::Functor {
            functor: s,
            pos_arity: 0,
            ..
        } => kb.qualified_name_of(s).to_string(),
        _ => panic!("expected an answer naming a sort, got {v:?}"),
    }
}

// ── 3. demo2: enumerate, and call the caller's operation on each value ──────

/// `Score` has two RIVAL witnesses at `Colour` and no provision on `Colour` itself, so
/// nothing but the caller's selection says which one a call means. Under `ByHeat` only
/// `red` scores 3, under `ByName` only `blue` does — so `top` has ONE row either way, and
/// WHICH row it is names the provider that reached the clause.
const DEMO2_PROGRAM: &str = r#"
namespace wi5g28a.demo2
  import anthill.prelude.{Int64, Error, EmptyStream}

  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end

  sort Colour
    entity red
    entity green
    entity blue
  end

  sort ByName
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 1
        case green() -> 2
        case blue() -> 3
  end

  sort ByHeat
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 3
        case green() -> 1
        case blue() -> 2
  end

  -- ENUMERATES `Wrap[T = T]` (its typed head) and CALLS `score` on each element, whose
  -- requirement is the sort's (060.1 §8.2)
  sort Wrap[T]
    requires Score[T = T]
    entity wrap(v: T)
    rule top(?x: Wrap[T = T]) :- ?x <=> wrap(?v), Score.score(?v, 3)
  end

  sort Driver
    operation countAt[X]() -> Int64 effects {Error} requires Score[T = X] =
      Wrap[T = X].top.takeN(5).length()
    operation countHeat() -> Int64 effects {Error} = countAt[X = Colour, Score = ByHeat]()
    operation countName() -> Int64 effects {Error} = countAt[X = Colour, Score = ByName]()
{projected}  end
end
"#;

/// The projected spelling — the one whose answer NAMES the provider (`wrap(red())` under
/// `ByHeat`, `wrap(blue())` under `ByName`) once the case works end to end.
const DEMO2_PROJECTED: &str = "    operation topAt[X]() -> Wrap[T = X] effects {Error, Error[EmptyStream]}\n      \
     requires Score[T = X] = Wrap[T = X].top.head.x\n    \
     operation topHeat() -> Wrap[T = Colour] effects {Error, Error[EmptyStream]} =\n      \
     topAt[X = Colour, Score = ByHeat]()\n";

fn demo2(projected: bool) -> String {
    DEMO2_PROGRAM.replace("{projected}", if projected { DEMO2_PROJECTED } else { "" })
}

/// Assert `call` RAISES `relation_floundered` — the drain's verdict on a relation that was
/// left with goals it could neither prove nor refute.
fn raises_relation_floundered(program: &str, entry: &str) {
    let mut interp = crate::common::interp_for(program);
    let err = interp
        .call(&format!("wi5g28a.demo2.Driver.{entry}"), &[])
        .expect_err("PINNED: the relation is undecided; if an answer comes back, flip this row");
    match &err {
        anthill_core::eval::EvalError::Raised { payload, .. } => {
            let raised = sort_named(interp.kb(), payload);
            assert!(
                raised.ends_with(".relation_floundered"),
                "{entry}: the clause is left suspended, so the drain raises \
                 `relation_floundered`; got `{raised}`",
            );
        }
        other => panic!("{entry}: expected a raised `relation_floundered`, got {other:?}"),
    }
}

/// PINNED — the projected spelling LOADS and FLOUNDERS. §7.3's S1 flipped its load verdict
/// (the citation typed `top`'s column at `Wrap`'s own `T` and refused the return the author
/// wrote, `expected Wrap[T = ?X], got Wrap[T = ?T]`); S2 flipped its run-time one, from
/// `.head` raising `empty_stream` on an empty relation to the drain raising
/// `relation_floundered` — the causes are `demo2_the_count_flounders`'. The row the whole
/// case flips to is `wrap(red())` under `ByHeat` and `wrap(blue())` under `ByName`.
#[test]
fn demo2_the_projected_spelling_loads_and_flounders() {
    raises_relation_floundered(&demo2(true), "topHeat");
}

/// PINNED — UNDECIDED, and SAID SO: `countAt` raises `relation_floundered` under both
/// providers, where the answer is `1` under each. Before §7.3's S2 it answered `0`, a
/// SILENT wrong answer: `Score.score(?v, 3)` ran value-directed while `?v` was still
/// unbound — the typed head's generator is appended after it — and answered nothing
/// (WI-20260924-35E14), so the clause failed. S2 WEAVES that call, which sits at its
/// read's own witness `?v`, so it now waits for its dictionary, and the read waits for
/// `?v`; nothing binds `?v`, so both goals are left suspended and the drain raises.
///
/// WHAT IS STILL MISSING, each named so the flip is read right: `X`'s domain in the clause
/// to bind `?v` (§7.3 S3); the caller's `Score` dictionary for this read — its witness is a
/// BODY variable, so only the bracket `Score[T]`, written with `Wrap`'s own `T`, says which
/// instance it is, and S2 routes a read from its witness's column; reading the bracket
/// under the citation's σ is observable only once S3(d) lets a clause typed at the sort's
/// parameter answer at all. (The clause wrote that bracket as `?d = require[Score[T]]`; since
/// proposal 060.1 §5 the requirement is the sort's own, `requires Score[T = T]`, which a rule
/// of the sort uses as its operations do (§8.2) — measured, the count flounders the same
/// with it and with no requirement written.) (A `require` whose only provider is a WITNESS sort answered
/// nothing, WI-20260924-DG57J; that is closed, `wi_dg57j_witness_only_requirement_test`.)
#[test]
fn demo2_the_count_flounders() {
    for entry in ["countHeat", "countName"] {
        raises_relation_floundered(&demo2(false), entry);
    }
}
