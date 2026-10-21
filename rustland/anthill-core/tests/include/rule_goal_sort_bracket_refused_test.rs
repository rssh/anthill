//! A SORT'S BRACKET ON A RELATION NAMED IN A RULE BODY, AS A GOAL OR AS A VALUE, IS REFUSED
//! (`Loader::refuse_rule_goal_receiver`), as kernel-language §5.4's "read or refused" rule
//! says of a bracket written on a rule-body goal.
//!
//! THE DEFECT (found 2026-10-21 while designing WI-20261013-GGXCX): the rule-body walk lowered
//! the bracket onto the goal as its receiver type, which marked it read, and nothing that
//! answers a rule goal reads it — a rule goal passes its callee nothing. So
//! `Wrap[T = Int64].el(?x)` over `rule el(?x: T) :- src(?x)` answered `"a"` beside `1`, the
//! same through an alias fixing `T`, and `SortDomain[T = Colour].fill(?x)` answered nothing
//! (`fill` is a spec's rule with no clause of its own), so `not(…)` over it held. Reading the
//! bracket — a hidden head slot per sort parameter — is WI-20260911-5G28A's decision B.
//!
//! BACK-OUT, measured: with the `refuse_rule_goal_receiver` call removed, every row here fails
//! except `the_spellings_that_read_or_need_no_bracket_load`, which passes either way by design.

const PROGRAM: &str = r#"
namespace rgbr
  import anthill.prelude.{Int64, String, Map, Relation}
  import anthill.reflect.SortDomain
  sort Colour
    entity red
    entity green
  end
  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- src(?x)
  end
  sort WI = Wrap[T = Int64]
  fact src(1)
  fact src("a")
"#;

fn errors_of(rule: &str) -> Vec<String> {
    crate::common::load_errors_of(&format!("{PROGRAM}  {rule}\nend\n"))
}

#[test]
fn a_bracket_on_a_relation_goal_is_refused() {
    for rule in [
        "rule r(?x) :- Wrap[T = Int64].el(?x)",
        "rule r(1) :- not(Wrap[T = Int64].el(\"a\"))",
        "rule r(?v) :- ?v <=> Wrap[T = Int64].el",
    ] {
        crate::common::assert_refused_naming(
            &errors_of(rule),
            &["type bracket on `rgbr.Wrap.el` in a rule body", "operation body"],
            rule,
        );
    }
}

/// An alias that fixes `T` is the bracket written another way.
#[test]
fn an_alias_fixing_the_parameter_is_refused_as_the_bracket_is() {
    crate::common::assert_refused_naming(
        &errors_of("rule r(?x) :- WI.el(?x)"),
        &["type bracket on `rgbr.Wrap.el` in a rule body"],
        "through the alias",
    );
}

#[test]
fn a_sorts_domain_written_as_its_fill_is_refused_naming_the_domain() {
    crate::common::assert_refused_naming(
        &errors_of("rule r(?x) :- SortDomain[T = Colour].fill(?x)"),
        &["anthill.reflect.Fillable.fill", "`Colour.domain(?x)`"],
        "the domain's spelling",
    );
}

/// CONTROL, PASSES EITHER WAY: the goal with no bracket, an operation's goal with one, the
/// relation cited from an operation body with one, and a sort's domain.
#[test]
fn the_spellings_that_read_or_need_no_bracket_load() {
    let mut kb = crate::common::load_kb_with(&format!(
        "{PROGRAM}  rule bare(?x) :- Wrap.el(?x)\n  \
         rule op(?m) :- Map[K = String, V = Int64].empty(?m)\n  \
         rule dom(?x) :- Colour.domain(?x)\n  \
         operation cited() -> Int64 effects {{Error}} = Wrap[T = Int64].el.takeN(5).length()\n\
         end\n"
    ));
    assert_eq!(crate::common::query_unary(&mut kb, "rgbr.bare").len(), 2);
    assert_eq!(crate::common::query_unary(&mut kb, "rgbr.dom").len(), 2);
}
