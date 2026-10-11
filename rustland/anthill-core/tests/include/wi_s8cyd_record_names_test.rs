//! WI-20261011-S8CYD — A PROOF RECORD'S NAME SAYS WHICH CLAUSE IT IS OF.
//!
//! A `requires <SE>` clause of a scope and a provision `X provides <PE>` each owe the
//! registry records (proposal 030, α.6 and α.8), and a record is found, skipped and
//! cited by its NAME. The names were made of SHORT names: `<scope>.requires.Eq_T`, the
//! spec's last segment and the last segment of each binding's head joined by `_`; and
//! `<X>.provides.<A-short>.<SE>`, the provided spec's last segment and NOT its bindings.
//! So two clauses could make one name, and then:
//!
//! * two provisions seen by ONE pass both emitted, and two records shared a `rule`;
//! * the second provision brought by a LATER load was taken for the first — the pass
//!   skips a record whose name the registry holds — so that load emitted nothing for
//!   it, and one call and two loads over the same files left different registries;
//! * two `requires` clauses of one scope that flattened alike were one record, their
//!   witnesses being the same `ScopeAxiom` too, and a provider got one specialization
//!   for the two laws.
//!
//! A name is the QUALIFIED TEXT of the spec at its bindings now
//! (`load::qualified_spec_text`): `<scope-qn>.requires.<SE>` and
//! `<X-qn>.provides.<PE>.<SE>`, `<PE>` and `<SE>` written like
//! `anthill.prelude.Eq[T = test.s8.P]` — every sort by its qualified name, every binding
//! in full. A `Specialization` witness's `substitution` is the same decode, so a name
//! fixes its record. Decided with the user, 2026-10-11.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT — measured 2026-10-11, the dev profile, each
//! back-out made on the tree as delivered, over 47 rows: this file's 7, ZVPXS's 7, and
//! 33 that load a provision or a requirement written through an alias or holding a
//! value — `wi366_…`, the two `…_written_through_alias` files and three more
//! (`docs/measurements/test-infrastructure/proof-record-names-2026-10-11.txt` §5).
//!
//! * THE WHOLE CHANGE — the sources as they were, run when this file had six rows
//!   (`a_provision_written_twice_is_one_record` came after): all 6 FAIL, and 5 of
//!   ZVPXS's 7. What the old sources left is at each row below, read off its failure.
//! * the provided spec by its LAST SEGMENT in a specialization's name, its bindings
//!   kept: 12 FAIL, 6 of them here. `no_two_records_share_a_name` PASSES — a law of
//!   these fixtures names its own spec's parameter (`Eq[T = …s8a.Conv.T]`), so the two
//!   `Conv`s still differ in `<SE>`; the rows that spell the names are what see it.
//! * the provision's bindings left OUT of its records' names: 13 FAIL, all 7 here.
//! * a required spec by its last segment (`<SE>`): 16 FAIL, all 7 here.
//! * a sort inside a binding by its LOCAL name: 16 FAIL, all 7 here; and the same 16
//!   with a hash-consed child of the text written in the diagnostic's spelling.
//! * a binding's value by its HEAD alone: 2 FAIL — `one_spec_at_several_bindings_…`
//!   and `no_two_records_share_a_name`, and nothing else in the 47.
//! * a binding's own bindings in DECLARED order: 1 FAILS —
//!   `one_spec_at_several_bindings_…`, on its `Two` provision.
//! * the prelude's type forms keyed on the LOCAL name, as a diagnostic keys them:
//!   1 FAILS — the same row, on its `x.Nothing` provision.
//! * the witness's `substitution` by short heads, the names as they are: 11 FAIL, 6 here
//!   (`no_two_records_share_a_name` reads names and passes).
//! * the witness made to say which ROW of the provision relation it came from, the
//!   names as they are: 12 FAIL, all 7 here — and `a_provision_written_twice_is_one_record`
//!   is the row that fails on two records under one name.
//!
//! BY DESIGN, none of this file's rows fails — other files hold these, and the
//! fixtures here have no such binding: a spec's bindings in the carrier's order (3
//! FAIL: `wi366_…` twice and the requirement written through an alias, each a spec
//! with two bindings); operation auto-bindings written into the text (6 FAIL: 4 of
//! ZVPXS's, the two `…_written_through_alias` rows). And NOTHING fails, in the 47 or
//! anywhere measured, with the interned child of the occurrence-only shape
//! (`display::type_display_name_occ`: a parameterized type whose base is itself an
//! occurrence) left in the diagnostic's spelling: no stored spec has been seen to hold
//! that shape, and the spelling is threaded there as everywhere, unmeasured.
//!
//! The reader that was moved with the names — `anthill prove`'s implicit citation —
//! has its row beside it (`prove::s8cyd_implicit_cite_tests`), with its two back-outs.
//!
//! WHAT /code-review ADDED, each backed out on the tree as delivered over this file's 8
//! rows, ZVPXS's 7 and the same 33, and over the three unit rows of the text
//! (`typing::tests::s8cyd_qualified_text_test`):
//!
//! * a spec's laws taken BY NAME — the scope cut out of a record's name at
//!   `.requires.`, whatever its witness: `a_specs_laws_are_its_own_requirements` FAILS,
//!   and it alone. Each provider of `Outer` is then specialized at three "laws": the
//!   requirement of `Outer`, the requirement of `Outer.requires.Held`, and the record
//!   the program wrote.
//! * an arrow written without its row: `one_spec_at_several_bindings_…` and
//!   `no_two_records_share_a_name` FAIL, and the arrow's unit row.
//! * the type forms keyed on the local name: `one_spec_at_several_bindings_…` FAILS
//!   (as before the review, when the forms were keyed on a prefix of the qualified
//!   name), and the rigid projection's unit row.
//! * a guarded effect atom by its label, a rigid projection as `var.member`: each
//!   fails its unit row and none here — no provision can be written at either.
//!
//! BY DESIGN nothing fails with a spec's law taken from ANY scope axiom of the spec,
//! its aspect not tested: the one other aspect is an enum's `induction`, and an enum
//! is refused as a provided spec (`provides test.s8e.Mode` cannot hold — measured). The
//! test is for the aspects the schema says may come.
//!
//! PINNED TO RECIPES BY NAME, every row: the subject is what a LATER load's pass emits
//! against what one call does, so no row may follow the switch. A row's later load is
//! made into the standard library as the suite's recipe gives it (`load_stdlib_kb`: a
//! copy of the shared base by default), by `load_in_a_later_call`.

use std::collections::BTreeMap;

use crate::common::{
    load_stdlib_kb, proof_record_rows as records,
    proof_records_brought_by_a_later_load as brought_by_a_later_load, proof_records_of_one_call,
    ProofRecordRow as Record,
};

fn sorted(mut records: Vec<Record>) -> Vec<Record> {
    records.sort();
    records
}

/// The names more than one record of `records` goes by, each with how many.
fn shared_names(records: &[Record]) -> Vec<(String, usize)> {
    let mut count: BTreeMap<&str, usize> = BTreeMap::new();
    for record in records {
        *count.entry(&record.rule).or_default() += 1;
    }
    count
        .into_iter()
        .filter(|&(_, n)| n > 1)
        .map(|(rule, n)| (rule.to_owned(), n))
        .collect()
}

// ── (1), (3) Two specs of one short name ─────────────────────────────

/// `test.s8a.Conv` and `test.s8b.Conv`, each with the law `requires Eq[T = T]`, and
/// `test.s8c.A`, which provides the first — and the second too, in its own declaration,
/// when `both` is set.
fn two_specs_of_one_short_name(both: bool) -> String {
    let second = if both { "provides test.s8b.Conv[T = A]" } else { "" };
    format!(
        r#"
namespace test.s8a
  sort Conv
    sort T = ?
    requires anthill.prelude.Eq[T = T]
  end
end

namespace test.s8b
  sort Conv
    sort T = ?
    requires anthill.prelude.Eq[T = T]
  end
end

namespace test.s8c
  import anthill.prelude.{{Bool, PartialEq, Eq}}

  sort A
    entity a
    provides PartialEq[T = A]
    provides Eq[T = A]
    provides test.s8a.Conv[T = A]
    {second}
    operation eq(x: A, y: A) -> Bool = true
  end
end
"#
    )
}

/// The second provision, written where a later load can bring it on its own.
const THE_SECOND_PROVISION: &str = r#"
namespace test.s8c.A
  provides test.s8b.Conv[T = test.s8c.A]
end
"#;

/// What `Conv` of namespace `ns` requires, as a record's name writes it.
fn conv_law(ns: &str) -> String {
    format!("anthill.prelude.Eq[T = test.{ns}.Conv.T]")
}

/// The scope axiom of `test.<ns>.Conv`'s law.
fn conv_requirement(ns: &str) -> Record {
    Record::requirement(&format!("test.{ns}.Conv"), &conv_law(ns))
}

/// `test.s8c.A`'s record for its provision of `test.<ns>.Conv`.
fn a_provides_conv(ns: &str) -> Record {
    Record::specialization(
        "test.s8c.A",
        &format!("test.{ns}.Conv"),
        ("T", "test.s8c.A"),
        &conv_law(ns),
    )
}

/// THE FORM, SPELLED OUT ONCE — every other row builds its names from
/// `ProofRecordRow`'s constructors, which this one pins: a requirement's scope axiom is
/// `<scope-qn>.requires.<SE>`, a specialization `<X-qn>.provides.<PE>.<SE>`, and `<SE>`
/// and `<PE>` are a spec's qualified name with its bindings in brackets, each binding's
/// value qualified. The witness says the same: the `aspect` is `requires.<SE>`, the
/// `parametric` the law's own record, the `substitution` the provision's bindings.
///
/// BACKED OUT (the sources as they were): FAILS — `…Conv.requires.Eq_T`,
/// `test.s8c.A.provides.Conv.Eq_T` twice, `concrete_sort: "A"`.
#[test]
fn a_record_is_named_by_the_qualified_text_of_its_spec() {
    let mut kb = load_stdlib_kb();
    let brought = brought_by_a_later_load(&mut kb, &two_specs_of_one_short_name(true));
    let said: Vec<(&str, &str)> =
        brought.iter().map(|r| (r.rule.as_str(), r.witness.as_str())).collect();
    assert_eq!(
        said,
        vec![
            (
                "test.s8a.Conv.requires.anthill.prelude.Eq[T = test.s8a.Conv.T]",
                "ScopeAxiom(scope_kind: \"sort\", scope_qn: \"test.s8a.Conv\", \
                 aspect: \"requires.anthill.prelude.Eq[T = test.s8a.Conv.T]\")",
            ),
            (
                "test.s8b.Conv.requires.anthill.prelude.Eq[T = test.s8b.Conv.T]",
                "ScopeAxiom(scope_kind: \"sort\", scope_qn: \"test.s8b.Conv\", \
                 aspect: \"requires.anthill.prelude.Eq[T = test.s8b.Conv.T]\")",
            ),
            (
                "test.s8c.A.provides.test.s8a.Conv[T = test.s8c.A]\
                 .anthill.prelude.Eq[T = test.s8a.Conv.T]",
                "Specialization(parametric: \
                 \"test.s8a.Conv.requires.anthill.prelude.Eq[T = test.s8a.Conv.T]\", \
                 substitution: [SortBinding(abstract_param: \"T\", concrete_sort: \"test.s8c.A\")], \
                 instances: nil)",
            ),
            (
                "test.s8c.A.provides.test.s8b.Conv[T = test.s8c.A]\
                 .anthill.prelude.Eq[T = test.s8b.Conv.T]",
                "Specialization(parametric: \
                 \"test.s8b.Conv.requires.anthill.prelude.Eq[T = test.s8b.Conv.T]\", \
                 substitution: [SortBinding(abstract_param: \"T\", concrete_sort: \"test.s8c.A\")], \
                 instances: nil)",
            ),
        ]
    );
}

/// (1) TWO SPECS OF ONE SHORT NAME ARE TWO RECORDS UNDER TWO NAMES — by a later load
/// that brings both provisions, and in one call.
///
/// BACKED OUT: FAILS — the two records are both there and both named
/// `test.s8c.A.provides.Conv.Eq_T`, one specializing `test.s8a.Conv.requires.Eq_T` and
/// one `test.s8b.…`.
#[test]
fn two_specs_of_one_short_name_are_two_records() {
    let program = two_specs_of_one_short_name(true);
    let owed = vec![
        conv_requirement("s8a"),
        conv_requirement("s8b"),
        a_provides_conv("s8a"),
        a_provides_conv("s8b"),
    ];

    let mut kb = load_stdlib_kb();
    assert_eq!(brought_by_a_later_load(&mut kb, &program), owed);

    let one_call = proof_records_of_one_call(&[&program]);
    let the_programs: Vec<Record> =
        one_call.iter().filter(|r| r.rule.starts_with("test.s8")).cloned().collect();
    assert_eq!(the_programs, owed);
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}

/// (3) ONE CALL AND TWO LOADS AGREE. The second provision is brought by a load of its
/// own: that load emits the provision's record, and the registry is the one a single
/// call over the same two files leaves.
///
/// BACKED OUT: FAILS, at the first load's names. What the old sources did past that,
/// by a temporary probe of the same loads: the later load brought NOTHING for the second
/// provision — its record's name was the first one's, and the registry held that — where
/// one call over the two files left four records, two of them under one name.
#[test]
fn a_provision_brought_by_a_later_load_gets_its_own_record() {
    let first = two_specs_of_one_short_name(false);
    let mut kb = load_stdlib_kb();
    assert_eq!(
        brought_by_a_later_load(&mut kb, &first),
        vec![conv_requirement("s8a"), conv_requirement("s8b"), a_provides_conv("s8a")]
    );
    assert_eq!(
        brought_by_a_later_load(&mut kb, THE_SECOND_PROVISION),
        vec![a_provides_conv("s8b")]
    );
    // And presented again, it brings nothing: the record is there under its own name.
    assert_eq!(brought_by_a_later_load(&mut kb, THE_SECOND_PROVISION), vec![]);

    let one_call = proof_records_of_one_call(&[&first, THE_SECOND_PROVISION]);
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}

// ── (2) One spec at several bindings ─────────────────────────────────

/// `W` provides `Holds` eight times: at two sorts of ONE SHORT NAME (`x.P`, `y.P`); at
/// two types that differ BELOW THE HEAD (`List[T = x.P]`, `List[T = y.P]`); at a type
/// whose sort declares its parameters in another order than their names' (`Two`: `Z`,
/// then `A`); at a user sort that shares the short name of one of the prelude's type
/// forms (`x.Nothing`); and at two arrows that differ in their effect ROW alone. `Holds`
/// has one law, which does not mention its parameter.
const ONE_SPEC_AT_EIGHT_BINDINGS: &str = r#"
namespace test.s8n.x
  sort P
    entity p
  end

  sort Nothing
    entity not_a_thing
  end
end

namespace test.s8n.y
  sort P
    entity p
  end
end

namespace test.s8n
  import anthill.prelude.{Bool, PartialEq, Eq, List, Int64, Error}

  sort Key
    entity key
    provides PartialEq[T = Key]
    provides Eq[T = Key]
    operation eq(x: Key, y: Key) -> Bool = true
  end

  sort Holds
    sort T = ?
    requires anthill.prelude.Eq[T = Key]
  end

  sort Two
    sort Z = ?
    sort A = ?
  end

  sort W
    provides Holds[T = test.s8n.x.P]
    provides Holds[T = test.s8n.y.P]
    provides Holds[T = List[T = test.s8n.x.P]]
    provides Holds[T = List[T = test.s8n.y.P]]
    provides Holds[T = Two[Z = test.s8n.x.P, A = test.s8n.y.P]]
    provides Holds[T = test.s8n.x.Nothing]
    provides Holds[T = (Int64) -> Int64]
    provides Holds[T = (Int64) -> Int64 @ Error]
  end
end
"#;

/// `W`'s record for its provision of `Holds` at `binding`.
fn w_provides_holds_at(binding: &str) -> Record {
    Record::specialization(
        "test.s8n.W",
        "test.s8n.Holds",
        ("T", binding),
        "anthill.prelude.Eq[T = test.s8n.Key]",
    )
}

/// (2) ONE SPEC AT SEVERAL BINDINGS IS A RECORD FOR EACH — the bindings are in the name,
/// qualified and in full, and in the witness's `substitution` as the name has them. By a
/// later load and in one call.
///
/// A binding's own bindings are written in the order of their NAMES (`Two[A = …, Z = …]`
/// where `Two` declares `Z` first): the one order that is the same whatever was loaded
/// before. A sort is the prelude's type form only by its qualified name: `x.Nothing`
/// is `test.s8n.x.Nothing`, where a diagnostic's text has `nothing` for it. And an
/// arrow is written WITH ITS ROW, which a diagnostic's `param -> result` leaves out:
/// two arrows that differ in it alone are two bindings (/code-review found them one).
///
/// BACKED OUT (the sources as they were, when the fixture had its first six bindings):
/// FAILS — FOUR records where six are owed, every one named
/// `test.s8n.W.provides.Holds.Eq_Key`: they say `concrete_sort: "P"`, `"List"`, `"Two"`
/// and `"Nothing"`. The pass emitted six, and `x.P`'s and `y.P`'s were one fact, and the
/// two lists' another.
#[test]
fn one_spec_at_several_bindings_is_a_record_for_each() {
    let owed = vec![
        Record::requirement("test.s8n.Holds", "anthill.prelude.Eq[T = test.s8n.Key]"),
        w_provides_holds_at("test.s8n.x.P"),
        w_provides_holds_at("test.s8n.y.P"),
        w_provides_holds_at("anthill.prelude.List[T = test.s8n.x.P]"),
        w_provides_holds_at("anthill.prelude.List[T = test.s8n.y.P]"),
        w_provides_holds_at("test.s8n.Two[A = test.s8n.y.P, Z = test.s8n.x.P]"),
        w_provides_holds_at("test.s8n.x.Nothing"),
        w_provides_holds_at("anthill.prelude.Int64 -> anthill.prelude.Int64 @ {}"),
        w_provides_holds_at(
            "anthill.prelude.Int64 -> anthill.prelude.Int64 @ {anthill.prelude.Error}",
        ),
    ];

    let mut kb = load_stdlib_kb();
    assert_eq!(brought_by_a_later_load(&mut kb, ONE_SPEC_AT_EIGHT_BINDINGS), owed);

    let one_call = proof_records_of_one_call(&[ONE_SPEC_AT_EIGHT_BINDINGS]);
    let the_programs: Vec<Record> =
        one_call.iter().filter(|r| r.rule.starts_with("test.s8n.")).cloned().collect();
    assert_eq!(the_programs, owed);
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}

// ── The same one pass up: two requirements of one scope ──────────────

/// `Both` requires the two `Conv`s at one binding — two clauses that flattened to one
/// `Conv_T` — and `test.s8c.A`, which provides both, provides `Both`.
const TWO_REQUIREMENTS_OF_ONE_FLATTENING: &str = r#"
namespace test.s8r
  sort Both
    sort T = ?
    requires test.s8a.Conv[T = T]
    requires test.s8b.Conv[T = T]
  end
end

namespace test.s8c.A
  provides test.s8r.Both[T = test.s8c.A]
end
"#;

/// TWO REQUIREMENTS OF ONE SCOPE ARE TWO SCOPE AXIOMS, and a provider of the scope is
/// specialized at each. The ticket had read this off the code and not reproduced it; it
/// is the same defect one pass up, and quieter — the two records had one name AND one
/// witness, so they were one fact, and nothing showed a clause had no record.
///
/// BACKED OUT: FAILS — ONE `test.s8r.Both.requires.Conv_T` and ONE
/// `test.s8c.A.provides.Both.Conv_T`, where two of each are owed.
#[test]
fn two_requirements_of_one_scope_are_two_records() {
    let both_requires = |ns: &str| format!("test.{ns}.Conv[T = test.s8r.Both.T]");
    let a_provides_both = |ns: &str| {
        Record::specialization(
            "test.s8c.A",
            "test.s8r.Both",
            ("T", "test.s8c.A"),
            &both_requires(ns),
        )
    };
    let owed = vec![
        Record::requirement("test.s8r.Both", &both_requires("s8a")),
        Record::requirement("test.s8r.Both", &both_requires("s8b")),
        a_provides_both("s8a"),
        a_provides_both("s8b"),
    ];

    let convs = two_specs_of_one_short_name(true);
    let mut kb = load_stdlib_kb();
    brought_by_a_later_load(&mut kb, &convs);
    assert_eq!(brought_by_a_later_load(&mut kb, TWO_REQUIREMENTS_OF_ONE_FLATTENING), owed);

    let one_call = proof_records_of_one_call(&[&convs, TWO_REQUIREMENTS_OF_ONE_FLATTENING]);
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}

// ── A spec's laws are its own requirements ───────────────────────────

/// What stands under the NAME `test.s8w.Outer.requires.` without being a requirement of
/// `Outer`: a record the program WROTE there, with another witness; and a sort declared
/// in a namespace whose last segment is `requires` — its own requirement's scope axiom,
/// and the record of its provision of `Outer`.
const WHAT_IS_NO_LAW_OF_A_SPEC: &str = r#"
namespace test.s8w
  import anthill.prelude.{Bool, PartialEq, Eq}

  sort Key
    entity key
    provides PartialEq[T = Key]
    provides Eq[T = Key]
    operation eq(x: Key, y: Key) -> Bool = true
  end

  sort Outer
    sort T = ?
    requires anthill.prelude.Eq[T = Key]
  end

  sort X
    provides Outer[T = X]
  end

  fact anthill.realization.ProofRecord(
    rule: "test.s8w.Outer.requires.written_by_hand",
    strategy: anthill.realization.ProofStrategyOpen,
    body: anthill.realization.ProofBodyNone,
    result: anthill.realization.Pending,
    dependencies: nil,
    using: nil,
    witness: anthill.realization.witness.ProofWitness.TrustedAxiom(reason: "a record a program wrote"),
    state_hash: "by-hand",
    parametric_context: nil)
end

namespace test.s8w.Outer.requires
  sort Held
    sort W = ?
    requires anthill.prelude.Eq[T = test.s8w.Key]
    provides test.s8w.Outer[T = Held]
  end
end
"#;

/// A file that brings no provision and no requirement.
const A_PROGRAM_THAT_BRINGS_NOTHING: &str = r#"
namespace test.s8w_none
  import anthill.prelude.{Int64}

  operation twice(n: Int64) -> Int64 = n + n
end
"#;

/// A SPEC'S LAWS ARE THE SCOPE AXIOMS OF ITS OWN `requires` CLAUSES, read off each
/// record's witness — `ScopeAxiom.scope_qn` is the spec — and not the names under
/// `<spec-qn>.requires.`: each provider of `Outer` is specialized at `Outer`'s one law,
/// and a load that then brings nothing emits nothing.
///
/// BACKED OUT (a spec's laws taken by NAME, the scope cut out at `.requires.`): FAILS —
/// `X` and `Held` are each specialized at three laws where `Outer` has one: `Held`'s
/// own requirement and the record written by hand beside it.
#[test]
fn a_specs_laws_are_its_own_requirements() {
    let key_eq = "anthill.prelude.Eq[T = test.s8w.Key]";
    let held = "test.s8w.Outer.requires.Held";
    let owed = vec![
        Record {
            rule: "test.s8w.Outer.requires.written_by_hand".to_owned(),
            witness: "TrustedAxiom(reason: \"a record a program wrote\")".to_owned(),
        },
        Record::requirement("test.s8w.Outer", key_eq),
        Record::requirement(held, key_eq),
        Record::specialization("test.s8w.X", "test.s8w.Outer", ("T", "test.s8w.X"), key_eq),
        Record::specialization(held, "test.s8w.Outer", ("T", held), key_eq),
    ];

    let mut kb = load_stdlib_kb();
    assert_eq!(brought_by_a_later_load(&mut kb, WHAT_IS_NO_LAW_OF_A_SPEC), owed);
    // The records the load left are under the spec's name now, `Held`'s provision's too.
    assert_eq!(brought_by_a_later_load(&mut kb, A_PROGRAM_THAT_BRINGS_NOTHING), vec![]);

    let one_call = proof_records_of_one_call(&[WHAT_IS_NO_LAW_OF_A_SPEC, A_PROGRAM_THAT_BRINGS_NOTHING]);
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}

// ── One provision written twice ──────────────────────────────────────

/// `W` provides `Holds` at `Int64` twice: written out, and through the alias `Money`.
/// Two rows of the provision relation — the alias rides its own carrier — and one
/// provision.
const ONE_PROVISION_WRITTEN_TWICE: &str = r#"
namespace test.s8d
  import anthill.prelude.{Bool, PartialEq, Eq, Int64}

  sort Money = Int64

  sort Holds
    sort T = ?
    requires anthill.prelude.Eq[T = Int64]
  end

  sort W
    provides Holds[T = Money]
    provides Holds[T = Int64]
  end
end
"#;

/// The same provision, where a later load can bring it once more.
const THE_PROVISION_ONCE_MORE: &str = r#"
namespace test.s8d.W
  provides test.s8d.Holds[T = test.s8d.Money]
end
"#;

/// A NAME FIXES ITS RECORD: two rows that make one name are one provision, and its
/// record is one — a provision written through an alias and written out is named by the
/// type, and says the type. In one pass, in one call, and with the provision presented
/// once more by a later load.
///
/// BACKED OUT (the witness made to say which ROW it came from, the name as it is):
/// FAILS — two records under the one name: the provision IS two rows.
#[test]
fn a_provision_written_twice_is_one_record() {
    let owed = vec![
        Record::requirement("test.s8d.Holds", "anthill.prelude.Eq[T = anthill.prelude.Int64]"),
        Record::specialization(
            "test.s8d.W",
            "test.s8d.Holds",
            ("T", "anthill.prelude.Int64"),
            "anthill.prelude.Eq[T = anthill.prelude.Int64]",
        ),
    ];
    let mut kb = load_stdlib_kb();
    assert_eq!(brought_by_a_later_load(&mut kb, ONE_PROVISION_WRITTEN_TWICE), owed);
    assert_eq!(brought_by_a_later_load(&mut kb, THE_PROVISION_ONCE_MORE), vec![]);

    let one_call = proof_records_of_one_call(&[ONE_PROVISION_WRITTEN_TWICE, THE_PROVISION_ONCE_MORE]);
    let the_programs: Vec<Record> =
        one_call.iter().filter(|r| r.rule.starts_with("test.s8d.")).cloned().collect();
    assert_eq!(the_programs, owed);
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}

// ── One name, one record ─────────────────────────────────────────────

/// NO TWO RECORDS SHARE A NAME — in the standard library's own registry, and with every
/// program of this file loaded after it, and with all of them in one call.
///
/// BACKED OUT: FAILS for the programs — they bring 11 records where 15 are owed, and
/// of the 11 `test.s8c.A.provides.Conv.Eq_T` is two and `test.s8n.W.provides.Holds.Eq_Key`
/// four. BY DESIGN the standard library's part passes either way: none of its 127
/// records shared a name before, and the row holds it to that.
#[test]
fn no_two_records_share_a_name() {
    let mut kb = load_stdlib_kb();
    assert!(records(&kb).len() > 100, "the standard library's records are in the KB");
    assert_eq!(shared_names(&records(&kb)), vec![], "the standard library's own records");

    let convs = two_specs_of_one_short_name(true);
    let programs: [&str; 3] =
        [&convs, ONE_SPEC_AT_EIGHT_BINDINGS, TWO_REQUIREMENTS_OF_ONE_FLATTENING];
    let mut brought = 0;
    for program in programs {
        brought += brought_by_a_later_load(&mut kb, program).len();
    }
    assert_eq!(brought, 17, "the programs' records: 4, 9 and 4");
    assert_eq!(shared_names(&records(&kb)), vec![], "after the programs, each a later load");

    let one_call = proof_records_of_one_call(&programs);
    assert_eq!(shared_names(&one_call), vec![], "the programs and the library in one call");
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}
