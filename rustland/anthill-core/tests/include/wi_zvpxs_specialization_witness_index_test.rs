//! WI-20261011-ZVPXS — A PROVISION ASKS FOR THE LAWS OF ITS OWN SPEC.
//!
//! `register_specialization_witnesses` walks every provision of the KB at every load,
//! and for each one found its spec's requires-laws by filtering EVERY `ProofRecord` name
//! for `<spec>.requires.`, the prefix built by a `format!` per name: 392 rows x 127 names
//! on a load after the standard library's, 9.0–9.9 ms of a pass of 9.5–10.5 and a
//! quarter of a 37 ms load
//! (`docs/measurements/test-infrastructure/specialization-witnesses-2026-10-11.txt`).
//! The names are sorted now and a spec's laws are one range of them, taken once per
//! spec. The pass still walks every row (user, 2026-10-11: an index and no rule about
//! loads), so what it emits is what it emitted — and the rows here are for what an index
//! can get wrong in silence: a record NOT emitted is no load error, a record emitted
//! under a neighbour's law is none either, and the scan put back emits the same records.
//!
//! SINCE WI-20261011-S8CYD A SPEC'S LAWS ARE READ OFF THE RECORDS' WITNESSES, an index by
//! scope built by one walk of the registry a pass (`load::requires_laws_by_scope`), and
//! not a range of the sorted names: a name under `<spec>.requires.` need not be a
//! requirement of the spec (`wi_s8cyd_record_names_test::a_specs_laws_are_its_own_requirements`).
//! The rows are the same seven — the counter was renamed with what it counts — and what
//! fails for the index, measured on that tree (2026-10-11, the dev profile):
//!
//! * the registry walked again for every provision — the scan back:
//!   `a_later_load_tests_rows_plus_names_and_not_rows_times_names` FAILS, and it alone;
//! * a scope's laws in the order of the relation and not of their names:
//!   `the_records_of_one_provision_are_emitted_in_name_order` FAILS, and it alone;
//! * the scope not compared — every requirement a law of every spec: 6 of the 7 FAIL
//!   (not the order row), and the 8 rows of the S8CYD file.
//!
//! The list below is of the RANGE, as this ticket delivered it, and is kept for what it
//! measured; the three unit rows it names went with the function they were of.
//!
//! WHAT FAILED WHEN THE CHANGE WAS BACKED OUT — measured, each by making the change and
//! running this file's 7 rows and the 3 unit rows beside the code
//! (`load::wi_zvpxs_law_range_tests`), 2026-10-11, the dev profile, on the tree as
//! delivered:
//!
//! * THE SCAN PUT BACK — every name tested for every provision, as it was, over the
//!   sorted set: `a_later_load_tests_rows_plus_names_and_not_rows_times_names` FAILS,
//!   and it alone; the same with every name tested once a SPEC. No other row can see
//!   it: the scan finds the same laws, and in the same order now that the names are
//!   sorted (/code-review found the suite green over the 10 ms the change is for). The
//!   lookups left uncounted, that row FAILS too — it asserts that something was tested.
//! * the laws of a spec handed back in the order a `HashSet` iterates them — the order
//!   the scan had before the names were sorted — run three times:
//!   `the_records_of_one_provision_are_emitted_in_name_order` FAILS every time (the
//!   standard library has thirteen provisions of specs with several laws, and a hash
//!   order has to fall right for all of them), and one or two unit rows. Once in the
//!   three a row that lists the program's records in order failed with it, on the
//!   order of `WeakOrd`'s two laws alone: the records are the same records.
//! * the range taken from the spec's NAME and not from its `requires.` prefix
//!   (`requires_law_records`): `a_provision_takes_its_own_specs_laws_and_no_neighbours`
//!   FAILS, and one unit row. It is the back-out that fails in SILENCE — the walk stops
//!   at the first name under the spec that is not a law, so a spec that has a record of
//!   its own sorting before its laws (its induction principle, a provision it makes)
//!   has no law, and its providers get no record. The other six rows pass: no spec of
//!   theirs has such a record when their pass runs. In that row it is the SECOND load
//!   that fails, the one made once `Spec`'s own provision is a record.
//! * the prefix `<spec>.` in place of `<spec>.requires.`: 6 FAIL — all but the order
//!   row, whose records are then misnamed and still in order — and the 3 unit rows.
//! * the first law of a spec only: 4 FAIL — the three that list the program's records
//!   and the order row, which finds no provision with several — and 2 unit rows.
//! * one entry of the pass's memo for every spec (`laws_of_spec` keyed by a constant):
//!   all 7 FAIL; the unit rows pass, the range being untouched.
//! * the name of a record not asked of the registry before the record is built — the
//!   `contains` test of any ONE of the three passes removed:
//!   `a_record_whose_verdict_was_written_is_not_emitted_again` FAILS, each time, and
//!   nothing else does (see that row for why).
//!
//! BY DESIGN — each of these passes all 10, and is a saving and no verdict:
//! * a provision of a spec with no law not skipped where its laws are looked up: the
//!   row is then read to the end and owes nothing, which is what the pass did;
//! * a provision that is owed no record kept as a target all the same: its bindings are
//!   decoded and nothing is built from them;
//! * the range taken again for every provision instead of once a spec: still rows plus
//!   names (a range a row), so the count row passes — it is the scan it is for.
//!
//! PINNED TO RECIPES BY NAME, every row: the subject is what a LATER load's pass emits
//! against what one call does, so no row may follow the switch. A row's later load is
//! made into the standard library as the suite's recipe gives it (`load_stdlib_kb`: a
//! copy of the shared base by default), by `load_in_a_later_call`.

use anthill_core::kb::load::witness_law_records_read_by_this_thread;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{
    load_stdlib_kb, named_field_term, proof_record_heads, proof_record_rows as records,
    proof_records_brought_by_a_later_load as brought_by_a_later_load, proof_records_of_one_call,
    ProofRecordRow as Record,
};

/// The field `key` of a record's head, or of its witness — read by the field's NAME.
fn field(kb: &KnowledgeBase, term: TermId, key: &str) -> TermId {
    named_field_term(kb, term, key).unwrap_or_else(|| {
        panic!("`{}` has a `{key}`", TermPrinter::new(kb).print_term(term))
    })
}

/// The field `key` of `term`, which is a string.
fn text_field(kb: &KnowledgeBase, term: TermId, key: &str) -> String {
    match kb.get_term(field(kb, term, key)) {
        Term::Const(Literal::String(text)) => text.clone(),
        other => panic!("`{key}` is a string; got {other:?}"),
    }
}

/// How many provision rows the KB holds.
fn provisions(kb: &KnowledgeBase) -> usize {
    let relation = kb
        .try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("the provision relation is declared");
    kb.rules_by_functor(relation).len()
}

fn sorted(mut records: Vec<Record>) -> Vec<Record> {
    records.sort();
    records
}

/// The law `requires <spec>[T = T]` of the sort `of`, as a record's name writes it
/// (WI-20261011-S8CYD: the required spec's qualified text at its bindings).
fn law_at_own_t(spec: &str, of: &str) -> String {
    format!("{spec}[T = {of}.T]")
}

// ── A later load emits for the provisions it brought ─────────────────

/// A spec of the program's own with a law and the program's provider of it; and a
/// provider of two LIBRARY specs that have laws — `PartialOrd requires PartialEq[T]`,
/// one, and `WeakOrd requires Eq[T]` and `PartialOrd[T]`, two.
const A_PROGRAM_WITH_LAWS: &str = r#"
namespace test.zvpxs
  import anthill.prelude.{Bool, PartialEq, Eq, PartialOrd, WeakOrd, Int64}

  sort Lawful
    sort T = ?
    requires anthill.prelude.Eq[T = T]
  end

  sort Thing
    entity thing
    provides PartialEq[T = Thing]
    provides Eq[T = Thing]
    provides Lawful[T = Thing]
    operation eq(x: Thing, y: Thing) -> Bool = true
  end

  enum Half
    entity half(v: Int64)
  end

  sort ByValue
    provides PartialOrd[T = Half]
    provides WeakOrd[T = Half]
    operation compare(a: Half, b: Half) -> Int64 = 0
  end
end
"#;

/// What [`A_PROGRAM_WITH_LAWS`] owes the registry, in the order a load asserts it: the
/// scope axiom of its `requires`, the induction principle of its enum, and a
/// `Specialization` for each law of each spec a provision of its own is of — by NAME,
/// with the parametric record it specializes and the provision's bindings.
fn the_programs_records() -> Vec<Record> {
    let lawful_eq = law_at_own_t("anthill.prelude.Eq", "test.zvpxs.Lawful");
    let at_half = ("T", "test.zvpxs.Half");
    vec![
        Record::requirement("test.zvpxs.Lawful", &lawful_eq),
        Record::induction("test.zvpxs.Half"),
        Record::specialization(
            "test.zvpxs.Thing",
            "test.zvpxs.Lawful",
            ("T", "test.zvpxs.Thing"),
            &lawful_eq,
        ),
        Record::specialization(
            "test.zvpxs.ByValue",
            "anthill.prelude.PartialOrd",
            at_half,
            &law_at_own_t("anthill.prelude.PartialEq", "anthill.prelude.PartialOrd"),
        ),
        Record::specialization(
            "test.zvpxs.ByValue",
            "anthill.prelude.WeakOrd",
            at_half,
            &law_at_own_t("anthill.prelude.Eq", "anthill.prelude.WeakOrd"),
        ),
        Record::specialization(
            "test.zvpxs.ByValue",
            "anthill.prelude.WeakOrd",
            at_half,
            &law_at_own_t("anthill.prelude.PartialOrd", "anthill.prelude.WeakOrd"),
        ),
    ]
}

/// A LATER LOAD MUST EMIT: the program's provisions are of specs with laws — one of its
/// own, whose law record the same load registers a pass earlier, and two of the
/// library's, whose law records an earlier load left — and the load that brings them
/// emits each record, and nothing else.
#[test]
fn a_later_load_emits_the_records_of_its_own_provisions() {
    let mut kb = load_stdlib_kb();
    assert!(
        records(&kb).len() > 100,
        "the standard library's records are in the KB: {}",
        records(&kb).len()
    );
    assert_eq!(
        brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_LAWS),
        the_programs_records()
    );
}

/// IN ONE CALL, the same records: the program's by name, and the whole registry as a
/// set — the standard library's own records are what they are after its own load.
#[test]
fn one_call_emits_the_records_a_later_load_does() {
    let one_call = proof_records_of_one_call(&[A_PROGRAM_WITH_LAWS]);
    let the_programs: Vec<Record> = one_call
        .iter()
        .filter(|r| r.rule.starts_with("test.zvpxs."))
        .cloned()
        .collect();
    assert_eq!(the_programs, the_programs_records());

    let mut kb = load_stdlib_kb();
    brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_LAWS);
    assert_eq!(sorted(one_call), sorted(records(&kb)));
}

/// The bench's user file: one operation, no provision, no sort.
const A_PROGRAM_WITH_NO_PROVISION: &str = r#"
namespace test.zvpxs_none
  import anthill.prelude.{Int64, Cell, Unit}

  operation overwrite(c: Cell[V = Int64], n: Int64) -> Unit effects Modify[c] = Cell.set(c, n)
end
"#;

/// A later load that brings no provision emits NOTHING: the pass walks every row of the
/// library again and finds every record it would name — before the program with laws is
/// there and after. And that program PRESENTED AGAIN to a KB that has it emits nothing
/// either: its provisions are rows the registry has every record of.
#[test]
fn a_later_load_emits_nothing_for_the_provisions_that_were_there() {
    let mut kb = load_stdlib_kb();
    assert_eq!(brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_NO_PROVISION), vec![]);
    assert_eq!(
        brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_LAWS),
        the_programs_records()
    );
    assert_eq!(brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_NO_PROVISION), vec![]);
    assert_eq!(brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_LAWS), vec![]);
}

/// THE PASS LOOKS A SPEC'S LAWS UP AND DOES NOT SCAN FOR THEM — what the change is, and
/// what no record can show: the scan emitted the same ones. A later load that brings
/// nothing reads, to find its provisions' laws, at most as many records as the KB has
/// provisions and records TOGETHER — every record once, by the walk that files the laws
/// by scope, and each law once for a provision of its spec. The scan read their
/// PRODUCT: every name for every provision, 49 784 after the standard library's own load.
#[test]
fn a_later_load_tests_rows_plus_names_and_not_rows_times_names() {
    let mut kb = load_stdlib_kb();
    let (rows, names) = (provisions(&kb), records(&kb).len());
    assert!(rows > 400 && names > 100, "the standard library is loaded: {rows} provisions, {names} records");
    let before = witness_law_records_read_by_this_thread();
    assert_eq!(brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_NO_PROVISION), vec![]);
    let tested = witness_law_records_read_by_this_thread() - before;
    assert!(tested > 0, "the pass ran, and asked for the laws of the specs provided");
    assert!(
        tested <= rows + names,
        "{tested} records read for laws, in a KB of {rows} provisions and {names} records"
    );
}

/// A RECORD THAT IS THERE IS NOT EMITTED AGAIN, WHATEVER HAS BEEN WRITTEN ON IT. The
/// three passes skip a record by its NAME, read off the registry, and that is what
/// decides it once a verdict is on the record: `anthill prove` writes one
/// (`proof_verify::set_proof_result`), the record is then no longer the `Pending` fact a
/// pass would build, and a pass that built it again would leave a second record of the
/// same name, `Pending`, beside the judged one. While a record is as the loader left it
/// the name is only a saving — asserting the same fact twice is one fact — which is why
/// no other row here fails without the check.
#[test]
fn a_record_whose_verdict_was_written_is_not_emitted_again() {
    use anthill_core::kb::proof_verify::{set_proof_result, VerdictWrite};

    let mut kb = load_stdlib_kb();
    brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_LAWS);
    let relation = kb
        .try_resolve_symbol("anthill.realization.ProofRecord")
        .expect("the standard library declares ProofRecord");
    // One of each pass's: a scope axiom, an induction principle, a specialization.
    let owed = the_programs_records();
    for record in [&owed[0], &owed[1], &owed[4]] {
        let name = record.rule.as_str();
        let rid = kb
            .rules_by_functor(relation)
            .into_iter()
            .find(|&rid| text_field(&kb, kb.rule_head(rid), "rule") == name)
            .unwrap_or_else(|| panic!("the record `{name}` is there"));
        let verdict = VerdictWrite::FailedUnknown {
            reason: "a verdict".to_owned(),
        };
        assert!(set_proof_result(&mut kb, rid, verdict), "a verdict is written on `{name}`");
    }
    assert_eq!(brought_by_a_later_load(&mut kb, A_PROGRAM_WITH_NO_PROVISION), vec![]);
}

// ── A spec's laws, and what sorts next to them ───────────────────────

/// `Spec` has ONE law. Three record names sort next to `test.zvpxs_near.Spec.requires.`
/// without being under it, each one a law record or made from one:
///   `…Spec.provides.…SpecX[T = …Spec.T].…`   `Spec`'s own provision — BELOW the range
///   `…Spec.zed.requires.…PartialEq[T = …U]`  a member's law — the first name past its end
///   `…SpecX.requires.…PartialEq[T = …T]`     a longer name's law — past that
const SPECS_WITH_NEIGHBOURS: &str = r#"
namespace test.zvpxs_near
  import anthill.prelude.{Bool, PartialEq, Eq}

  sort SpecX
    sort T = ?
    requires anthill.prelude.PartialEq[T = T]
  end

  sort Spec
    sort T = ?
    requires anthill.prelude.Eq[T = T]
    provides SpecX[T = T]

    sort zed
      sort U = ?
      requires anthill.prelude.PartialEq[T = U]
    end
  end

  sort Thing
    entity thing
    provides PartialEq[T = Thing]
    provides Eq[T = Thing]
    provides Spec[T = Thing]
    operation eq(x: Thing, y: Thing) -> Bool = true
  end
end
"#;

/// A second provider of `Spec`, for a load made when all three neighbours are records.
const ANOTHER_PROVIDER_OF_THE_SPEC: &str = r#"
namespace test.zvpxs_far
  import anthill.prelude.{Bool, PartialEq, Eq}
  import test.zvpxs_near.{Spec}

  sort Other
    entity other
    provides PartialEq[T = Other]
    provides Eq[T = Other]
    provides Spec[T = Other]
    operation eq(x: Other, y: Other) -> Bool = true
  end
end
"#;

/// A PROVISION IS SPECIALIZED BY ITS OWN SPEC'S LAWS AND NO NEIGHBOUR'S. The load that
/// brings the specs has the member's and the longer name's law records in the registry
/// when its pass runs; the load after it has `Spec`'s own provision record there too.
/// Each provider of `Spec` gets `Spec`'s one law.
#[test]
fn a_provision_takes_its_own_specs_laws_and_no_neighbours() {
    let mut kb = load_stdlib_kb();
    let spec_x_law = law_at_own_t("anthill.prelude.PartialEq", "test.zvpxs_near.SpecX");
    let spec_law = law_at_own_t("anthill.prelude.Eq", "test.zvpxs_near.Spec");
    assert_eq!(
        brought_by_a_later_load(&mut kb, SPECS_WITH_NEIGHBOURS),
        vec![
            Record::requirement("test.zvpxs_near.SpecX", &spec_x_law),
            Record::requirement("test.zvpxs_near.Spec", &spec_law),
            Record::requirement(
                "test.zvpxs_near.Spec.zed",
                "anthill.prelude.PartialEq[T = test.zvpxs_near.Spec.zed.U]",
            ),
            Record::specialization(
                "test.zvpxs_near.Spec",
                "test.zvpxs_near.SpecX",
                ("T", "test.zvpxs_near.Spec.T"),
                &spec_x_law,
            ),
            Record::specialization(
                "test.zvpxs_near.Thing",
                "test.zvpxs_near.Spec",
                ("T", "test.zvpxs_near.Thing"),
                &spec_law,
            ),
        ]
    );
    assert_eq!(
        brought_by_a_later_load(&mut kb, ANOTHER_PROVIDER_OF_THE_SPEC),
        vec![Record::specialization(
            "test.zvpxs_far.Other",
            "test.zvpxs_near.Spec",
            ("T", "test.zvpxs_far.Other"),
            &spec_law,
        )]
    );
}

// ── The order of a provision's records ───────────────────────────────

/// A PROVISION'S RECORDS ARE EMITTED IN THE ORDER OF THEIR NAMES. They were emitted in
/// the iteration order of a `HashSet` of every record name, another order in every
/// process — the listing of one load's records came out differently run after run, and
/// with it the rule ids of every fact asserted after them. The standard library has
/// provisions of specs with two laws and with three; each one's records stand in the
/// relation in name order.
#[test]
fn the_records_of_one_provision_are_emitted_in_name_order() {
    let kb = load_stdlib_kb();
    let printer = TermPrinter::new(&kb);
    // The specialization records by the PROVISION they are of: who provides, which spec,
    // at which bindings. A record is named `<X>.provides.<PE>.<SE>` and specializes
    // `<A>.requires.<SE>`, so the two names share their `<SE>` — a spec's qualified
    // text, with a `.` in it: the key is read off both, not off the last segment of one.
    let mut by_provision: Vec<((String, String, String), Vec<String>)> = Vec::new();
    for head in proof_record_heads(&kb) {
        let witness = field(&kb, head, "witness");
        if named_field_term(&kb, witness, "parametric").is_none() {
            continue; // a scope axiom
        }
        let (rule, parametric) = (text_field(&kb, head, "rule"), text_field(&kb, witness, "parametric"));
        let (spec, law) = parametric
            .split_once(".requires.")
            .unwrap_or_else(|| panic!("`{parametric}` is a spec's `requires` record"));
        let provider_and_spec = rule
            .strip_suffix(law)
            .and_then(|r| r.strip_suffix('.'))
            .unwrap_or_else(|| panic!("`{rule}` is named by the law of `{parametric}`"));
        let key = (
            provider_and_spec.to_owned(),
            spec.to_owned(),
            printer.print_term(field(&kb, witness, "substitution")),
        );
        match by_provision.iter_mut().find(|(k, _)| *k == key) {
            Some((_, laws)) => laws.push(law.to_owned()),
            None => by_provision.push((key, vec![law.to_owned()])),
        }
    }
    let with_several = by_provision.iter().filter(|(_, laws)| laws.len() > 1).count();
    assert!(
        with_several >= 10,
        "the fixture: the standard library has provisions of specs with several laws — \
         {with_several} of {}",
        by_provision.len()
    );
    for (provision, laws) in &by_provision {
        let mut in_name_order = laws.clone();
        in_name_order.sort();
        assert_eq!(laws, &in_name_order, "the laws of {provision:?}, as their records were asserted");
    }
}
