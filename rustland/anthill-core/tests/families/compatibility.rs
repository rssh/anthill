//! FAMILY (g) — MAY A VALUE OF TYPE A STAND WHERE B IS EXPECTED: the subtype relation, asked
//! at every position that asks it (`kernel-language.md` §8.2, §4.5, §5.2; the map is
//! `docs/design/compatibility-question-map.md`).
//!
//! A pair is a type `A`, a literal of it and a type `B`. The value is always `mkA()`, declared
//! `-> A`, so its static type is `A` and no constructor is classified at the expectation
//! (§8.2, *Which sort a constructor application is classified at*). The positions: an
//! operation's argument, an annotated `let`, a return, an entity field, a list element, a
//! lambda's argument, a provision at `B` answering `Desc.d(mkA())`, and the run-time
//! `type_admits(B, A)`.
//!
//! ONE QUESTION, MANY SPELLINGS (P4): the six typing positions, the provision and
//! `type_admits` are one question for a sort-headed pair. For a tuple or an arrow the spec
//! gives provision lookup a rule of its own — a binding compared by its parts, "a tuple with a
//! component more is another binding … though it conforms to it as a type" (§5.2) — so there
//! the provision is `provision-by-parts`, an option of its own, held to that rule by P3.
//!
//! NOT PROGRAMS, and skipped ([`skips`]): each provision option at the pairs the other one
//! covers; `type_admits` at a tuple or an arrow, which it leaves unjudged by design, and at a
//! variant, whose type the matrix has no value spelling for (`Colour.red` bare is a
//! construction).
//!
//! AN ANSWER IS ADMITTED OR NOT ([`judge`]): a position that runs is admitted; one refused by
//! a type mismatch — whatever the position's context kind — is not, and so is `type_admits`
//! answering 2 (`go` returns 1 where it admits, 2 where it does not). The subject holds `A`
//! and `B` themselves to being written for a value (`mkA`, and a parameter typed `B`), so a
//! type that cannot be is a refusal of its own class at every position, never "not
//! admitted". What the reading can still hide is a mismatch at one position for a reason
//! other than `A` at `B` — the return position's avoidance rule, for a `B` with a member left
//! open, is one — and P4 shows it wherever the other positions admit.
//!
//! SOUNDNESS (P3): the template marks refused every pair the spec says is not admitted, and
//! every `provision-by-parts` program ([`Program::refused`]).
//!
//! CONTROL: run with [`EXCEPTIONS`] empty, the family names exactly the programs they cover —
//! measured when it was written and again after the `param-spec` decision (2026-10-25,
//! `1373e04f`): 13 findings, over the six rows the exceptions name.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program, Property, Verdict};

/// (label, A, a literal of A, B, what the spec says).
const PAIRS: &[(&str, &str, &str, &str, Spec)] = &[
    ("variant-to-sort", "Colour.red", "red(v: 1)", "Colour", Spec::Yes),
    ("sort-to-variant", "Colour", "red(v: 1)", "Colour.red", Spec::No),
    ("sibling-variant", "Colour.blue", "blue(v: 2)", "Colour.red", Spec::No),
    ("self-carrier", "List[T = Int64]", "[1, 2]", "Stream[T = Int64, E = {}]", Spec::Yes),
    // A provider of a spec over a parameter at the spec: admitted by the user's decision of
    // 2026-10-25, ahead of §8.2's text, which says a `Bk` is no `Tagger` until WI-20261025-053QV
    // rewords it.
    ("param-spec", "Bk", "bk(k: 0)", "Tagger", Spec::Yes),
    ("refinement", "Narrow", "narrow()", "Wide[W = Int64]", Spec::Yes),
    ("refinement-other-args", "Narrow", "narrow()", "Wide[W = String]", Spec::No),
    ("open-slot", "Box[V = Int64]", "box(v: 1)", "Box", Spec::Yes),
    ("slot-mismatch", "Box[V = Int64]", "box(v: 1)", "Box[V = String]", Spec::No),
    ("alias", "Option[T = Int64]", "Option.some(1)", "IntOpt", Spec::Yes),
    ("alias-reverse", "IntOpt", "Option.some(1)", "Option[T = Int64]", Spec::Yes),
    ("tuple-width", "(a: Int64, b: String, c: Bool)", "(a: 1, b: \"s\", c: true)", "(a: Int64, c: Bool)", Spec::Yes),
    ("tuple-permutation", "(b: String, a: Int64)", "(b: \"s\", a: 1)", "(a: Int64, b: String)", Spec::Yes),
    ("tuple-order", "(String, Int64)", "(\"s\", 1)", "(Int64, String)", Spec::No),
    ("covariant-list", "List[T = Colour.red]", "[red(v: 1)]", "List[T = Colour]", Spec::Yes),
    ("no-variance-fact", "Box[V = Colour.red]", "box(v: red(v: 1))", "Box[V = Colour]", Spec::Open),
    ("arrow-parameter-wider", "(Colour) -> Int64", "lambda (x: Colour) -> 1", "(Colour.red) -> Int64", Spec::Yes),
    ("arrow-parameter-narrower", "(Colour.red) -> Int64", "lambda (x: Colour.red) -> 1", "(Colour) -> Int64", Spec::No),
    ("arrow-fewer-effects", "(Int64) -> Int64", "lambda (x: Int64) -> x", "(Int64) -> Int64 @ {Error[String]}", Spec::Yes),
    ("arrow-more-effects", "(Int64) -> Int64 @ {Error[String]}", "lambda (x: Int64) -> x", "(Int64) -> Int64", Spec::No),
];

#[derive(Clone, Copy, PartialEq)]
enum Spec {
    Yes,
    No,
    /// `Box` declares no variance; the spec does not say (WI-20261017-DYX5E).
    Open,
}

fn pair(label: &str) -> (&'static str, &'static str, &'static str, Spec) {
    let (_, a, lit, b, spec) = PAIRS
        .iter()
        .find(|p| p.0 == label)
        .unwrap_or_else(|| panic!("no pair `{label}`"));
    (a, lit, b, *spec)
}

fn is_former(label: &str) -> bool {
    label.starts_with("tuple-") || label.starts_with("arrow-")
}

fn is_variant(label: &str) -> bool {
    matches!(label, "variant-to-sort" | "sort-to-variant" | "sibling-variant")
}

pub static FAMILY: Family = Family {
    name: "g-compatibility",
    rule: "a value of type A where B is expected, at every position that asks",
    holes: &[
        Hole {
            name: "pair",
            options: &[
                opt("variant-to-sort", ""),
                opt("sort-to-variant", ""),
                opt("sibling-variant", ""),
                opt("self-carrier", ""),
                opt("param-spec", ""),
                opt("refinement", ""),
                opt("refinement-other-args", ""),
                opt("open-slot", ""),
                opt("slot-mismatch", ""),
                opt("alias", ""),
                opt("alias-reverse", ""),
                opt("tuple-width", ""),
                opt("tuple-permutation", ""),
                opt("tuple-order", ""),
                opt("covariant-list", ""),
                opt("no-variance-fact", ""),
                opt("arrow-parameter-wider", ""),
                opt("arrow-parameter-narrower", ""),
                opt("arrow-fewer-effects", ""),
                opt("arrow-more-effects", ""),
            ],
        },
        Hole {
            name: "position",
            options: &[
                spelt("argument", "", "admitted"),
                spelt("let", "", "admitted"),
                spelt("return", "", "admitted"),
                spelt("field", "", "admitted"),
                spelt("list-element", "", "admitted"),
                spelt("lambda-argument", "", "admitted"),
                spelt("provision", "", "admitted"),
                opt("provision-by-parts", ""),
                spelt("type-admits", "", "admitted"),
            ],
        },
    ],
    render,
    skips: Some(skips),
    judge,
    exceptions: EXCEPTIONS,
};

const TICKET_27050: &str = "WI-20261025-27050";
const TICKET_053QV: &str = "WI-20261025-053QV";
const TICKET_G37HS: &str = "WI-20261020-G37HS";
const TICKET_05ZQE: &str = "WI-20260929-05ZQE";
const TICKET_DYX5E: &str = "WI-20261017-DYX5E";

const EXCEPTIONS: &[Exception] = &[
    // The typer's refinement through `requires` ignores the clause's arguments: every typing
    // position admits `Narrow` at `Wide[W = String]`; the provision and `type_admits` do not.
    Exception {
        property: Property::Sound,
        when: &["pair=refinement-other-args"],
        ticket: TICKET_G37HS,
        why: "a `Narrow` is admitted at `Wide[W = String]` although it requires `Wide[W = Int64]`",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=refinement-other-args"],
        ticket: TICKET_G37HS,
        why: "the six typing positions admit what the provision and `type_admits` do not",
    },
    // A value whose own sort provides the spec's instance is admitted at the spec. Provision
    // lookup does so already and is held; the typing positions (WI-20261025-053QV) and
    // `type_admits` (27050's C5) refuse it. P4 calls each of these live while any spelling of the
    // row still differs, so they come off together once both tickets have landed.
    Exception {
        property: Property::OneVerdict,
        when: &["pair=param-spec", "position=argument"],
        ticket: TICKET_053QV,
        why: "a `Bk` is refused at `Tagger`, which provision lookup admits",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=param-spec", "position=let"],
        ticket: TICKET_053QV,
        why: "a `Bk` is refused at `Tagger`, which provision lookup admits",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=param-spec", "position=return"],
        ticket: TICKET_053QV,
        why: "a `Bk` is refused at `Tagger`, which provision lookup admits",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=param-spec", "position=field"],
        ticket: TICKET_053QV,
        why: "a `Bk` is refused at `Tagger`, which provision lookup admits",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=param-spec", "position=list-element"],
        ticket: TICKET_053QV,
        why: "a `Bk` is refused at `Tagger`, which provision lookup admits",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=param-spec", "position=lambda-argument"],
        ticket: TICKET_053QV,
        why: "a `Bk` is refused at `Tagger`, which provision lookup admits",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=param-spec", "position=type-admits"],
        ticket: TICKET_27050,
        why: "`type_admits(Tagger, Bk)` answers no; a pattern admits a provider (C5)",
    },
    // C6 — a `requires` refinement with written arguments is not climbed.
    Exception {
        property: Property::OneVerdict,
        when: &["pair=refinement", "position=provision"],
        ticket: TICKET_27050,
        why: "a provision at `Wide[W = Int64]` does not answer a call at a `Narrow` that requires it",
    },
    // C5 — a type pattern has no provider leg.
    Exception {
        property: Property::OneVerdict,
        when: &["pair=self-carrier", "position=type-admits"],
        ticket: TICKET_27050,
        why: "`type_admits` refuses a `List` at a `Stream` that every other position admits",
    },
    // A provision head's type arguments are not compared.
    Exception {
        property: Property::Sound,
        when: &["pair=slot-mismatch", "position=provision"],
        ticket: TICKET_05ZQE,
        why: "a provision at `Box[V = String]` answers a call at `Box[V = Int64]`",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["pair=slot-mismatch", "position=provision"],
        ticket: TICKET_05ZQE,
        why: "provision lookup admits what every typing position refuses",
    },
    // Provision lookup reads the whole head covariantly; the typer reads `Box` as invariant.
    Exception {
        property: Property::OneVerdict,
        when: &["pair=no-variance-fact", "position=provision"],
        ticket: TICKET_DYX5E,
        why: "a provision at `Box[V = Colour]` answers a call at `Box[V = Colour.red]`",
    },
];

fn skips(picks: &Picks<'_>) -> bool {
    let p = picks.label("pair");
    match picks.label("position") {
        "provision" => is_former(p),
        "provision-by-parts" => !is_former(p),
        "type-admits" => is_former(p) || is_variant(p),
        _ => false,
    }
}

/// [`super::judge_program`], read as admitted or not: a type mismatch refusing the position,
/// whatever its context kind, and `type_admits` answering 2, are both "not admitted".
fn judge(program: &Program) -> Verdict {
    const NOT_ADMITTED: &str = "NotAdmitted";
    let not_admitted = || Verdict::DriveRefused(NOT_ADMITTED.to_string());
    match super::judge_program(program) {
        Verdict::Runs(value) if value == "2" => not_admitted(),
        Verdict::Unsound(admitted) if admitted == "runs 2" => not_admitted(),
        Verdict::DriveRefused(classes) if classes.split('+').all(|c| c.starts_with("TypeMismatch")) => not_admitted(),
        verdict => verdict,
    }
}

fn render(picks: &Picks<'_>) -> Program {
    let label = picks.label("pair");
    let (a, lit, b, spec) = pair(label);
    let (above, body) = match picks.label("position") {
        "argument" => (format!("  operation take(x: {b}) -> Int64 = 1\n"), "take(mkA())".to_string()),
        "let" => (String::new(), format!("let y: {b} = mkA()\n    1")),
        "return" => (format!("  operation conv() -> {b} = mkA()\n"), "let _ = conv()\n    1".to_string()),
        "field" => (
            format!("  sort H\n    entity h(x: {b})\n  end\n"),
            "let _ = h(x: mkA())\n    1".to_string(),
        ),
        "list-element" => (String::new(), format!("let ys: List[T = {b}] = [mkA()]\n    1")),
        "lambda-argument" => (String::new(), format!("let f = lambda (x: {b}) -> 1\n    f(mkA())")),
        "provision" | "provision-by-parts" => (
            format!("  sort W\n    provides Desc[T = {b}]\n    operation d(x: {b}) -> Int64 = 1\n  end\n"),
            "Desc.d(mkA())".to_string(),
        ),
        "type-admits" => (String::new(), format!("if type_admits({b}, {a}) then 1 else 2")),
        other => panic!("no position `{other}`"),
    };
    let declarations = format!(
        r#"namespace family.g
  import anthill.prelude.{{Int64, String, Bool, List, Option, Stream, Error}}
  import anthill.reflect.{{type_admits}}
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort IntOpt = Option[T = Int64]
  sort Tagger
    sort C = ?
    operation probe(x: C) -> Int64
  end
  sort Bk
    entity bk(k: Int64)
    provides Tagger[C = Bk]
    operation probe(x: Bk) -> Int64 = 7
  end
  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort Wide
    sort W = ?
  end
  sort Narrow
    requires Wide[W = Int64]
    entity narrow
  end
  sort WP
    provides Wide[W = Int64]
  end
  operation mkA() -> {a} = {lit}
  operation written(x: {b}) -> Int64 = 1
"#
    );
    // The spec refuses a pair it says is not admitted, and a provision at a tuple or an arrow
    // answers only at its own binding (§5.2) — every former pair here is another binding.
    let refused = spec == Spec::No || picks.is("position", "provision-by-parts");
    Program {
        source: format!("{declarations}{above}  operation go() -> Int64 =\n    {body}\nend\n"),
        entry: Some("family.g.go"),
        subject: Some(format!("{declarations}end\n")),
        refused,
    }
}
