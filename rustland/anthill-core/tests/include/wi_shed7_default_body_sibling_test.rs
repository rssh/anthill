//! A SPEC'S DEFAULT BODY CALLS ITS RECEIVER-LESS SIBLING AT THE INSTANCE IT RUNS AT
//! (kernel-language.md §5.2, "A spec's default body is not such a dispatch": the dictionary
//! picks the target "for a receiver-less sibling, which no argument can classify").
//!
//! Found starting WI-20260925-SHED7: `PersistentCollection.fromList`'s default body calls
//! `empty()`, and the stdlib stopped loading. Measured on f0d38c95: with two providers of
//! `Mk`, `operation viaDefault() -> C = e()` was refused at `e()`, "ambiguous dispatch of
//! `Mk.e`: 2 instances provide `Mk` (A, B) and the call selects none", where the same body
//! with one provider loaded and answered `a(n: 1)`, and `e(5)` over `e(n: Int64) -> C`
//! loaded with two. The typer's call of a sibling with no parameter and no carrier pinned
//! (`resolve_nullary_result_carrier`) counted the providers; a body that runs at an instance
//! of the spec (`entered_at_an_instance_of`) now leaves it to that instance.
//!
//! ## Back-out
//!
//! With the instance reading backed out of `resolve_nullary_result_carrier` (measured
//! 2026-11-02, one build, a temporary switch): `each_provider_answers_with_its_own_sibling`
//! and `every_site_that_enters_the_default_answers` fail, the program refused at load.
//!
//! PASS EITHER WAY, BY DESIGN: `a_call_outside_the_specs_members_still_ties` and
//! `a_rule_and_a_const_written_in_the_spec_still_tie` (the refusals the change must not
//! move), `one_provider_and_a_sibling_with_an_argument_load_either_way` (what loaded before).

use crate::common::{load_errors_of, load_kb_with, shown_rows};

const SRC: &str = "
namespace dbs
  import anthill.prelude.Int64
  sort Mk
    sort C = ?
    operation e() -> C
    operation viaDefault() -> C = e()
    operation viaNested() -> C = viaDefault()
    operation viaLambda() -> C =
      let f = lambda () -> e()
      f()
    operation viaLet() -> C =
      let x = e()
      x
    operation viaRecv(c: C) -> C = e()
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
  operation gen[X]() -> X requires Mk[C = X] = Mk[C = X].viaDefault()
  operation pa() -> A = Mk[C = A].viaDefault()
  operation pb() -> B = Mk[C = B].viaDefault()
  operation pinferred() -> A = Mk.viaDefault()
  operation pnested() -> B = Mk[C = B].viaNested()
  operation plambda() -> B = Mk[C = B].viaLambda()
  operation plet() -> B = Mk[C = B].viaLet()
  operation precv() -> B = b(n: 9).viaRecv()
  operation pqualified() -> B = Mk.viaRecv(b(n: 9))
  operation pgen() -> B = gen[X = B]()
  operation pmid() -> B = Mid[C = B].viaMid()
  rule ra(?x) :- ?x <=> pa()
  rule rb(?x) :- ?x <=> pb()
  rule rinferred(?x) :- ?x <=> pinferred()
  rule rnested(?x) :- ?x <=> pnested()
  rule rlambda(?x) :- ?x <=> plambda()
  rule rlet(?x) :- ?x <=> plet()
  rule rrecv(?x) :- ?x <=> precv()
  rule rqualified(?x) :- ?x <=> pqualified()
  rule rgen(?x) :- ?x <=> pgen()
  rule rmid(?x) :- ?x <=> pmid()
end
";

fn one(shown: &str) -> Vec<(String, bool)> {
    vec![(shown.to_owned(), true)]
}

/// Two providers, one default body: each instance's own `e` answers.
#[test]
fn each_provider_answers_with_its_own_sibling() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(shown_rows(&mut kb, "dbs.ra"), one("a(n: 1)"));
    assert_eq!(shown_rows(&mut kb, "dbs.rb"), one("b(n: 2)"));
}

/// Every way a default body is entered: the instance read off the expected result, a default
/// calling a default, a lambda and a `let` in the body, a default with a receiver reached by
/// the value and by the spec's name, a generic caller's requirement, and a spec that refines
/// `Mk` (a sort without constructors, whose member runs at its provider's instance).
#[test]
fn every_site_that_enters_the_default_answers() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(shown_rows(&mut kb, "dbs.rinferred"), one("a(n: 1)"));
    for rel in [
        "dbs.rnested",
        "dbs.rlambda",
        "dbs.rlet",
        "dbs.rrecv",
        "dbs.rqualified",
        "dbs.rgen",
        "dbs.rmid",
    ] {
        assert_eq!(shown_rows(&mut kb, rel), one("b(n: 2)"), "{rel}");
    }
}

/// A CONTROL: outside the spec's own members the call still has nothing to name its instance
/// by — in another spec's default, in a member of a sort with constructors, in a free
/// operation — and the tie stays a refusal.
#[test]
fn a_call_outside_the_specs_members_still_ties() {
    let errs = load_errors_of(
        "
namespace dbt
  import anthill.prelude.Int64
  sort Mk
    sort C = ?
    operation e() -> C
  end
  sort Other
    sort C = ?
    operation viaOther() -> C = Mk.e()
  end
  sort A
    entity a(n: Int64)
    provides Mk[C = A]
    provides Other[C = A]
    operation e() -> A = a(n: 1)
    operation inData() -> Int64 =
      let x = Mk.e()
      0
  end
  sort B
    entity b(n: Int64)
    provides Mk[C = B]
    provides Other[C = B]
    operation e() -> B = b(n: 2)
  end
  operation free() -> Int64 =
    let x = Mk.e()
    0
end
",
    );
    assert_eq!(errs.len(), 3, "{errs:#?}");
    for e in &errs {
        assert!(
            e.contains("ambiguous dispatch of `dbt.Mk.e`: 2 instances provide `dbt.Mk` (dbt.A, dbt.B)"),
            "{errs:#?}"
        );
    }
}

/// A CONTROL: a rule and a const written in the spec are its members too, but neither runs
/// at an instance the way an operation body is entered at one, and the tie stays a refusal.
#[test]
fn a_rule_and_a_const_written_in_the_spec_still_tie() {
    let errs = load_errors_of(
        "
namespace dbr
  import anthill.prelude.Int64
  sort Mk
    sort C = ?
    operation e() -> C
    rule viaRule(?x) :- ?x <=> e()
    const k: C = e()
  end
  sort A
    entity a(n: Int64)
    provides Mk[C = A]
    operation e() -> A = a(n: 1)
  end
  sort B
    entity b(n: Int64)
    provides Mk[C = B]
    operation e() -> B = b(n: 2)
  end
end
",
    );
    assert_eq!(errs.len(), 2, "{errs:#?}");
    for e in &errs {
        assert!(
            e.contains("ambiguous dispatch of `dbr.Mk.e`: 2 instances provide `dbr.Mk` (dbr.A, dbr.B)"),
            "{errs:#?}"
        );
    }
}

/// A CONTROL: what loaded before — the body with one provider, and a sibling taking an
/// argument (`e(5)`), which the typer leaves to the run with two.
#[test]
fn one_provider_and_a_sibling_with_an_argument_load_either_way() {
    let single = "
namespace dbo
  import anthill.prelude.Int64
  sort Mk
    sort C = ?
    operation e() -> C
    operation viaDefault() -> C = e()
  end
  sort A
    entity a(n: Int64)
    provides Mk[C = A]
    operation e() -> A = a(n: 1)
  end
  operation pa() -> A = Mk[C = A].viaDefault()
  rule ra(?x) :- ?x <=> pa()
end
";
    let mut kb = load_kb_with(single);
    assert_eq!(shown_rows(&mut kb, "dbo.ra"), one("a(n: 1)"));
    let with_arg = "
namespace dbu
  import anthill.prelude.Int64
  sort Mk
    sort C = ?
    operation e(n: Int64) -> C
    operation viaDefault() -> C = e(5)
  end
  sort A
    entity a(n: Int64)
    provides Mk[C = A]
    operation e(n: Int64) -> A = a(n: n)
  end
  sort B
    entity b(n: Int64)
    provides Mk[C = B]
    operation e(n: Int64) -> B = b(n: n)
  end
  operation pb() -> B = Mk[C = B].viaDefault()
  rule rb(?x) :- ?x <=> pb()
end
";
    let mut kb = load_kb_with(with_arg);
    assert_eq!(shown_rows(&mut kb, "dbu.rb"), one("b(n: 5)"));
}
