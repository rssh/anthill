//! WI-20260924-GP8JC — a clause's dictionary reaches a DEFAULTED spec operation's call as it
//! reaches a body-less one's: only at the carrier the dictionary was read from, and read at
//! the call the direct witness scan chooses (body order, the bracket read).
//!
//! Two halves were backed out on `require[X]` while this file was written: the weave made
//! carrier-blind for a bodied call, and the defaulted witness scanned last. Proposal 060.1 §5
//! removed the form. The clause declares its dictionary at its head's introducer, the first
//! call's argument typed at the parameter — `two[A](?x: A, ?y, …) :- Desc[T = A]` — so the
//! dictionary is still read at that carrier and woven only into calls there. The witness scan
//! is not the guard's, and the rows its back-out failed pass either way now. The weave's
//! back-out, measured again on the guard (the carrier check of `collect_covered_calls` skipped
//! for a bodied call):
//!
//! | row | weave carrier-blind for a bodied call |
//! |---|---|
//! | `a_defaulted_call_at_another_carrier_keeps_its_own_dispatch` | FAILS (`7, 7, 9, 9`) |
//! | `a_nested_defaulted_call_at_another_carrier_keeps_its_own_dispatch` | FAILS (`7, 7`) |
//! | `a_passed_dictionary_reaches_the_defaulted_call_at_its_carrier` | FAILS (`heatOther` `30`) |
//! | `a_passed_dictionary_reaches_a_defaulted_call_beside_a_requiring_call` | ok |
//! | `two_bracket_chosen_requires_read_each_its_own_carrier` | FAILS (load refused: "covered by distinct carrier requirements") |
//! | `a_defaulted_call_no_goal_runs_is_still_a_witness` | FAILS (`7, 7`) |
//! | `the_body_less_twin_answers_the_same` | ok — the control |
//! | `a_typed_head_bracket_answers_at_each_carrier` | ok — the control |
//!
//! With the check skipped for a body-less call too, the twin fails as well (`7, 7, 9, 9, 7, 7`).
//! WI-1040's two calls at ONE carrier, both woven, are
//! `wi1040_require_clause_dictionary_test::every_covered_call_in_the_clause_is_woven`. The two
//! `require`s at concrete carriers, and the dictionaries they bound, went with the form: a call
//! at a concrete type needs no requirement, and two requirements of one spec are two
//! introducers' guards.

use anthill_core::eval::Value;

fn desc_program(ns: &str, defaulted: bool) -> String {
    let describe = if defaulted { " = 1" } else { "" };
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64{describe}
  end

  sort Thing
    import anthill.prelude.Int64
    entity thing
    provides Desc[T = Thing]
    operation describe(x: Thing) -> Int64 = 7
  end

  sort Gadget
    import anthill.prelude.Int64
    entity gadget
    provides Desc[T = Gadget]
    operation describe(x: Gadget) -> Int64 = 9
  end

  rule two[A, B](?x: A, ?y: B, ?r1, ?r2) :- Desc[T = A], Desc[T = B], Desc.describe(?x, ?r1), Desc.describe(?y, ?r2)
  rule twoTyped(a: Thing, b: Gadget, ?r1, ?r2) :- Desc.describe(a, ?r1), Desc.describe(b, ?r2)
  rule nested[A, B](?x: A, ?y: B, ?r1, ?r2) :-
    Desc[T = A], Desc[T = B], ?r1 <=> Int64.add(Desc.describe(?x), 0), Desc.describe(?y, ?r2)

  rule tgFirst(?r) :- two(thing(), gadget(), ?r, ?)
  rule tgSecond(?r) :- two(thing(), gadget(), ?, ?r)
  rule gtFirst(?r) :- two(gadget(), thing(), ?r, ?)
  rule gtSecond(?r) :- two(gadget(), thing(), ?, ?r)
  rule typedFirst(?r) :- twoTyped(thing(), gadget(), ?r, ?)
  rule typedSecond(?r) :- twoTyped(thing(), gadget(), ?, ?r)
  rule nestedFirst(?r) :- nested(thing(), gadget(), ?r, ?)
  rule nestedSecond(?r) :- nested(thing(), gadget(), ?, ?r)
end
"#
    )
}

/// The single definite Int each of `{ns}.{rel}` for `rels` answers.
fn ints(src: &str, ns: &str, rels: &[&str]) -> Vec<i64> {
    let mut kb = crate::common::load_kb_with(src);
    rels.iter()
        .map(|rel| {
            let qn = format!("{ns}.{rel}");
            match crate::common::query_unary(&mut kb, &qn).as_slice() {
                [(Value::Int(i), true)] => *i,
                other => panic!("`{qn}` must answer exactly one definite Int, got {other:?}"),
            }
        })
        .collect()
}

/// The ticket's acceptance: each call answers its own carrier's member, in either order.
/// Carrier-blind, the dictionary read at the first call reached the second too.
#[test]
fn a_defaulted_call_at_another_carrier_keeps_its_own_dispatch() {
    let ns = "test.gp8jc.two";
    let src = desc_program(ns, true);
    assert_eq!(
        ints(&src, ns, &["tgFirst", "tgSecond", "gtFirst", "gtSecond"]),
        vec![7, 9, 9, 7],
    );
}

/// The same, with the first call an argument of another call.
#[test]
fn a_nested_defaulted_call_at_another_carrier_keeps_its_own_dispatch() {
    let ns = "test.gp8jc.nested";
    let src = desc_program(ns, true);
    assert_eq!(ints(&src, ns, &["nestedFirst", "nestedSecond"]), vec![7, 9]);
}

/// CONTROL — passes either way, by design: the body-less twin of the two rows above, the
/// answers the defaulted program is held to.
#[test]
fn the_body_less_twin_answers_the_same() {
    let ns = "test.gp8jc.bodyless";
    let src = desc_program(ns, false);
    assert_eq!(
        ints(&src, ns, &["tgFirst", "tgSecond", "gtFirst", "gtSecond", "nestedFirst", "nestedSecond"]),
        vec![7, 9, 9, 7, 7, 9],
    );
}

/// CONTROL — passes either way, by design: the head bindings are typed, so each call's
/// carrier is known where the clause is typed, and a call at a concrete type needs no
/// requirement (the clause wrote `?d = require[Desc[T = Thing]]`, which proposal 060.1 §5
/// removed). The ticket measured `9, 9` here on 2026-09-24; the tree answered `7, 9` before
/// this change.
#[test]
fn a_typed_head_bracket_answers_at_each_carrier() {
    let ns = "test.gp8jc.typed";
    let src = desc_program(ns, true);
    assert_eq!(ints(&src, ns, &["typedFirst", "typedSecond"]), vec![7, 9]);
}

/// Two requirements on `Desc`, each at its own type parameter, and a call at each: each call
/// reads its own parameter's dictionary, in either order of the guards. The row was two
/// `require`s at the concrete `Leaf` and `Other`, each bracket choosing its call, refused
/// with the defaulted witness scanned last ("at most one `require` on spec `Desc` per rule
/// …"); and it read the dictionaries bound, `Dictionary.impl(?d1)`. Proposal 060.1 §5 removed
/// the form: a call at a concrete type needs no requirement, two requirements of one spec are
/// two introducers' guards, and what a dictionary is is read by the answer it gives. Its
/// `untyped` twin — two requirements no call could be attributed to — is two guards at one
/// parameter now, which 060.1 §8.5 admits (`wi_hrfr5_witness_attribution_test`).
#[test]
fn two_bracket_chosen_requires_read_each_its_own_carrier() {
    let ns = "test.gp8jc.tworeq";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end
  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation describe(x: Other) -> Int64 = 9
  end
  rule both[A, B](?x: A, ?y: B, ?a, ?b) :- Desc[T = A], Desc[T = B],
    Desc.describe(?x, ?a), Desc.describe(?y, ?b)
  rule rev[A, B](?x: A, ?y: B, ?a, ?b) :- Desc[T = B], Desc[T = A],
    Desc.describe(?x, ?a), Desc.describe(?y, ?b)
  rule bothA(?r) :- both(leaf(), other(), ?r, ?)
  rule bothB(?r) :- both(leaf(), other(), ?, ?r)
  rule revA(?r) :- rev(leaf(), other(), ?r, ?)
  rule revB(?r) :- rev(leaf(), other(), ?, ?r)
end
"#
    );
    assert_eq!(ints(&src, ns, &["bothA", "bothB", "revA", "revB"]), vec![7, 9, 7, 9]);
}

/// A defaulted call that no goal runs reads the clause's dictionary: one in a negand, and two
/// in the branches of a disjunction, the first at the guard's parameter and the second at a
/// carrier of its own. It was the witness of a `require[Desc[T]]` (removed by proposal 060.1
/// §5) and FAILED with that scan backed out (the load refused: "no such call in the rule
/// body"), which the introducer's guard does not use. With the weave carrier-blind it answers
/// `7, 7`, measured on the guard.
#[test]
fn a_defaulted_call_no_goal_runs_is_still_a_witness() {
    let ns = "test.gp8jc.nested_form";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end
  sort Thing
    import anthill.prelude.Int64
    entity thing
    provides Desc[T = Thing]
    operation describe(x: Thing) -> Int64 = 7
  end
  sort Gadget
    import anthill.prelude.Int64
    entity gadget
    provides Desc[T = Gadget]
    operation describe(x: Gadget) -> Int64 = 9
  end
  rule notOne[A](?x: A) :- Desc[T = A], not(Desc.describe(?x, 1))
  rule disj[A](?x: A, ?y, ?r) :- Desc[T = A], (Desc.describe(?x, ?r) | Desc.describe(?y, ?r))
  rule thingIsNotOne(?r) :- notOne(thing()), ?r <=> 1
  rule both(?r) :- disj(thing(), gadget(), ?r)
end
"#
    );
    let mut kb = crate::common::load_kb_with(&src);
    let ints_of = |kb: &mut anthill_core::kb::KnowledgeBase, rel: &str| -> Vec<(i64, bool)> {
        crate::common::query_unary(kb, &format!("{ns}.{rel}"))
            .into_iter()
            .map(|(v, definite)| match v {
                Value::Int(i) => (i, definite),
                other => panic!("`{rel}` must answer Ints, got {other:?}"),
            })
            .collect()
    };
    assert_eq!(ints_of(&mut kb, "thingIsNotOne"), vec![(1, true)]);
    assert_eq!(ints_of(&mut kb, "both"), vec![(7, true), (9, true)]);
}

/// `wi_5g28a_rule_dictionary_test`'s Rank program with `rank` DEFAULTED: a citation hands
/// `rankBoth` the caller's `ByHeat`, which reaches the call at the caller's carrier `?a`
/// (`30`) and not the call at `dark()` (`Shade`'s own `5`). And `mixed` calls `rank` beside
/// `Util.twice`, an operation that `requires Rank`, and the passed dictionary reaches it.
/// Each clause declares `Rank[T = A]` at its head's introducer, `?a: A`; it wrote
/// `require[Rank[T]]`, which proposal 060.1 §5 removed.
const RANK_PROGRAM: &str = r#"
namespace gp8jc.rank
  import anthill.prelude.{Int64, Error, EmptyStream}

  sort Rank
    sort T = ?
    operation rank(x: T) -> Int64 = 0
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

  sort Shade
    import anthill.prelude.Int64
    entity dark
    provides Rank[T = Shade]
    operation rank(x: Shade) -> Int64 = 5
  end

  sort Util
    import anthill.prelude.Int64
    sort T = ?
    entity mk(t: T)
    operation twice(x: T) -> Int64 requires Rank[T] = Int64.add(Rank.rank(x), Rank.rank(x))
  end

  rule rankBoth[A](?a: A, ?b, ?r1, ?r2) :- Rank[T = A], Rank.rank(?a, ?r1), Rank.rank(?b, ?r2)
  rule mixed[A](?a: A, ?r1, ?r2) :- Rank[T = A], Util.twice(?a, ?r1), Rank.rank(?a, ?r2)

  sort Driver
    operation bothAt[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires Rank[T = A] = rankBoth(x, dark()).head.r1
    operation bothOther[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires Rank[T = A] = rankBoth(x, dark()).head.r2
    operation mixedDirect[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires Rank[T = A] = mixed(x).head.r2
    operation heatAt() -> Int64 effects {Error, Error[EmptyStream]} =
      bothAt[A = Colour, Rank = ByHeat](red())
    operation heatOther() -> Int64 effects {Error, Error[EmptyStream]} =
      bothOther[A = Colour, Rank = ByHeat](red())
    operation ownOther() -> Int64 effects {Error, Error[EmptyStream]} =
      rankBoth(red(), dark()).head.r2
    operation heatMixed() -> Int64 effects {Error, Error[EmptyStream]} =
      mixedDirect[A = Colour, Rank = ByHeat](red())
    operation ownMixed() -> Int64 effects {Error, Error[EmptyStream]} = mixed(red()).head.r2
  end
end
"#;

fn drive_rank(entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(RANK_PROGRAM);
    match interp.call(&format!("gp8jc.rank.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// `heatAt` failed with the defaulted witness scanned last (`1`: the dictionary was read at
/// `dark()`'s call, and `red()`'s answered by value), measured on `require[X]` — the witness
/// scan's, which the introducer's guard does not use. With the weave carrier-blind `heatOther`
/// answers `30`, the clause's dictionary reaching `dark()`'s call, measured on the guard.
#[test]
fn a_passed_dictionary_reaches_the_defaulted_call_at_its_carrier() {
    assert_eq!(drive_rank("heatAt"), 30, "the passed dictionary reaches the call at its carrier");
    assert_eq!(drive_rank("heatOther"), 5, "and not the call at `dark()`");
    assert_eq!(drive_rank("ownOther"), 5, "nor does a derived one");
}

/// Failed with the defaulted witness scanned last (`1`), measured on `require[X]`: `Util.twice`
/// was then the witness, and a witness that is not a call of `Rank`'s covers no call, so the
/// direct call answered by value. On the guard it passes under both back-outs. `ownMixed`
/// passes either way, by design: no dictionary is passed.
#[test]
fn a_passed_dictionary_reaches_a_defaulted_call_beside_a_requiring_call() {
    assert_eq!(drive_rank("heatMixed"), 30);
    assert_eq!(drive_rank("ownMixed"), 1);
}
