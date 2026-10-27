//! WI-20260924-DG57J — a rule-body requirement whose only provider is a WITNESS sort.
//!
//! `sort ByHeat provides Score[T = Colour]` is filed under `ByHeat`, and `Colour` provides
//! nothing itself. A written `requires(Score[T])` or `?d = require[Score[T]]` in front of
//! `Score.score(red(), ?r)` made the clause answer nothing, silently, where the call alone
//! answered `3`: the guard core (`simp_guard_decision`) asked the carrier's own provisions
//! (`sort_provides`) and not a provision another sort files for it. WI-20260925-P7VP4
//! (`18cca07a`) made it ask both (`carrier_provides_spec`); on that commit's parent the
//! guarded and bound clauses answer nothing, MEASURED.
//!
//! The ticket's second half — two rival witnesses and nothing selecting one — is refused at
//! load, not delayed (kernel-language §5.4: a rule-body goal no route discharges is refused
//! at load). Its refusal names a bracket the call can take where it is written
//! (`render_call_tie`): a call of a rule's own term takes none, so it goes on the call inside
//! a `let` or in an operation's body; a call there takes one, written applicatively or as a
//! dot (WI-20261026-8K7W0). Each advised program is run here.
//!
//! BACK-OUTS, measured. With the guard core asking `sort_provides` alone, the three
//! written-requirement rows answer nothing, and every row with an applicative `Score.score`
//! call in a rule — the call-alone row, the advised repairs, the two goal refusals and the
//! compound-expression control — fails at load on a second refusal, "`Colour` provides no
//! `Score`", the typer's requirement check asking the same core; the own-spec carrier row and
//! the two dot rows pass. With `render_call_tie` reading no rule's own term, the four
//! rule-term refusal rows fail on the advice; every other row passes by design.

const ONE_WITNESS: &str = r#"
namespace dg57j.one
  import anthill.prelude.{Int64}

  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end

  sort Colour
    entity red
  end

  sort ByHeat
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 = 3
  end

  sort Hue
    entity teal
    provides Score[T = Hue]
    operation score(x: Hue) -> Int64 = 7
  end

{rule}
end
"#;

/// `ByName` beside `ByHeat`: two witnesses for `Colour`, and the rule selects neither.
const TWO_WITNESSES: &str = r#"
namespace dg57j.two
  import anthill.prelude.{Int64}

  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end

  sort Colour
    entity red
  end

  sort ByHeat
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 = 3
  end

  sort ByName
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 = 1
  end

{rule}
end
"#;

/// One program per row, so a row the back-out refuses at load does not take the others with it.
fn one(rule: &str) -> String {
    ONE_WITNESS.replace("{rule}", rule)
}

fn two(rule: &str) -> String {
    TWO_WITNESSES.replace("{rule}", rule)
}

fn answer(src: &str, qn: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(src);
    crate::common::one_definite_int(&mut kb, qn)
}

/// The sort `impl` of the one dictionary `qn(?d)` answers.
fn dictionary_impl(src: &str, qn: &str) -> String {
    let mut kb = crate::common::load_kb_with(src);
    let rows = crate::common::query_unary(&mut kb, qn);
    let [(v, true)] = rows.as_slice() else {
        panic!("{qn}: expected one definite dictionary, got {rows:?}");
    };
    crate::wi1040_require_clause_dictionary_test::dictionary_parts(&kb, v).1
}

/// The one load error of `src`, which must be the unselected-instance refusal naming both
/// witnesses.
fn the_tie_refusal(src: &str) -> String {
    let errs = crate::common::load_errors_of(src);
    let [err] = errs.as_slice() else {
        panic!("expected exactly the tie's refusal, got {errs:#?}");
    };
    assert!(
        err.contains("ambiguous dispatch of `dg57j.two.Score.score`")
            && err.contains("dg57j.two.ByHeat")
            && err.contains("dg57j.two.ByName"),
        "the refusal names the call and both witnesses: {err}",
    );
    err.clone()
}

/// The refusal's repair, whichever witness it names: `write` is what it says to write,
/// cut where the provider's name starts.
fn assert_advises(err: &str, opening: &str, write: &str, place: &str) {
    let advice =
        format!("{opening} cannot carry call-site type arguments, so {write}dg57j.two.By");
    assert!(err.contains(&advice) && err.contains(place), "expected `{advice}…{place}`: {err}");
}

const RULE_TERM: &str = "inside a `let` or in an operation's body that the rule calls";

#[test]
fn a_written_guard_finds_a_witness_provision() {
    let src = one("  rule guarded(?r) :- requires(Score[T]), Score.score(red(), ?r)");
    assert_eq!(answer(&src, "dg57j.one.guarded"), Some(3), "`ByHeat`'s `score`");
}

#[test]
fn a_written_read_finds_a_witness_provision() {
    let src = one("  rule bound(?r) :- ?d = require[Score[T]], Score.score(red(), ?r)");
    assert_eq!(answer(&src, "dg57j.one.bound"), Some(3), "`ByHeat`'s `score`");
}

#[test]
fn the_read_names_the_witness() {
    let src = one("  rule dict(?d) :- ?d = require[Score[T]], Score.score(red(), ?)");
    assert_eq!(dictionary_impl(&src, "dg57j.one.dict"), "dg57j.one.ByHeat");
}

/// The ticket's twin with no requirement written. Not a control of the guard core: backed
/// out, the typer's requirement check refuses this call at load.
#[test]
fn the_call_alone_answers() {
    let src = one("  rule plain(?r) :- Score.score(red(), ?r)");
    assert_eq!(answer(&src, "dg57j.one.plain"), Some(3), "`ByHeat`'s `score`");
}

/// CONTROL: a carrier providing its own spec answers through the read either way.
#[test]
fn a_carrier_providing_its_own_spec_answers() {
    let src = one(
        "  rule hue(?r) :- ?d = require[Score[T]], Score.score(teal(), ?r)\n  \
         rule hueDict(?d) :- ?d = require[Score[T]], Score.score(teal(), ?)",
    );
    assert_eq!(answer(&src, "dg57j.one.hue"), Some(7), "`Hue`'s own `score`");
    assert_eq!(dictionary_impl(&src, "dg57j.one.hueDict"), "dg57j.one.Hue");
}

/// Two witnesses and nothing selecting one: each spelling of the ticket's clause is refused
/// at load, and a goal takes no bracket.
#[test]
fn two_witnesses_refuse_a_goal_and_send_the_bracket_elsewhere() {
    for rule in [
        "  rule plain(?r) :- Score.score(red(), ?r)",
        "  rule guarded(?r) :- requires(Score[T]), Score.score(red(), ?r)",
        "  rule bound(?r) :- ?d = require[Score[T]], Score.score(red(), ?r)",
    ] {
        let err = the_tie_refusal(&two(rule));
        assert_advises(&err, "a call written as a rule's own term", "write `[Score = ", RULE_TERM);
    }
}

/// A call standing in a rule body's value slot is the rule's own term too.
#[test]
fn two_witnesses_refuse_a_value_slot_call_and_send_the_bracket_elsewhere() {
    let err = the_tie_refusal(&two("  rule v(?r) :- ?r <=> Score.score(red())"));
    assert_advises(&err, "a call written as a rule's own term", "write `[Score = ", RULE_TERM);
}

/// A dot in a rule's own term is a call of it, as its applicative spelling is.
#[test]
fn two_witnesses_refuse_a_rule_term_dot_and_send_the_bracket_elsewhere() {
    let err = the_tie_refusal(&two("  rule v(?r) :- ?r <=> red().score()"));
    assert_advises(&err, "a call written as a rule's own term", "write `[Score = ", RULE_TERM);
}

/// A dot in an operation's body takes the bracket, as the call written applicatively does.
#[test]
fn two_witnesses_refuse_a_dot_and_advise_its_own_bracket() {
    let err = the_tie_refusal(&two(
        "  sort Driver\n    operation go() -> Int64 = red().score()\n  end",
    ));
    assert!(
        err.contains("so say which: write `[Score = dg57j.two.By")
            && err.contains("(or another of them) in the call's bracket list"),
        "{err}",
    );
    assert!(!err.contains(RULE_TERM), "an operation's body is no rule's own term: {err}");
}

/// The repairs advised, run: the applicative bracket in an operation's body, the rule
/// calling it, and the same call under a `let` in the rule, applicative and as a dot.
#[test]
fn the_advised_repairs_select_each_witness() {
    let src = two(
        "  sort Driver\n    \
           operation heat() -> Int64 = Score.score[Score = ByHeat](red())\n    \
           operation name() -> Int64 = Score.score[Score = ByName](red())\n  \
         end\n  \
         rule viaHeat(?r) :- ?r <=> Driver.heat()\n  \
         rule viaName(?r) :- ?r <=> Driver.name()\n  \
         rule viaLet(?r) :- ?r <=> (let s = Score.score[Score = ByName](red())  s + 0)\n  \
         rule viaLambda(?r) :- \
         ?r <=> (let f = lambda (c: Colour) -> Score.score[Score = ByName](c)  f(red()))\n  \
         rule viaDot(?r) :- ?r <=> (let s = red().score[Score = ByHeat]()  s + 0)",
    );
    let mut kb = crate::common::load_kb_with(&src);
    for (qn, want) in [
        ("viaHeat", 3),
        ("viaName", 1),
        ("viaLet", 1),
        ("viaLambda", 1),
        ("viaDot", 3),
    ] {
        let got = crate::common::one_definite_int(&mut kb, &format!("dg57j.two.{qn}"));
        assert_eq!(got, Some(want), "{qn}");
    }
}

/// CONTROL: under a compound expression a call is written as in an operation body, where the
/// bracket is read — so the advice stays the call's own bracket.
#[test]
fn under_a_compound_expression_the_bracket_stays_on_the_call() {
    let err = the_tie_refusal(&two("  rule v(?r) :- ?r <=> (let s = Score.score(red())  s + 0)"));
    assert!(
        err.contains("so say which: write `[Score = dg57j.two.By")
            && err.contains("(or another of them) in the call's bracket list"),
        "{err}",
    );
}
