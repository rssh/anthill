//! WI-20260911-5G28A S3a — A TYPE VARIABLE'S DOMAIN RIDES THE REQUIREMENT CHANNEL
//! (`docs/design/060-implementation.md` §7.3, S3; `060-typedomains-implementation.md`).
//!
//! `rule el(?x: T) :- true` inside `sort Wrap[T]` has a bound no term can name: `T` is the
//! instance its CITATION means, and inside `countAt[X]` that instance is a rigid `X` known
//! only to `countAt`'s caller. So the typed-head sweep gives such a bound an IMPLICIT
//! PARAMETER instead of a member goal — since WI-20260925-SHED7 `apply_domain(?d, ?x, T),
//! find_dictionary(SortDomain, SortDomain, ?x, out: ?d)` — and a citation fills it from the caller's own
//! `requires SortDomain[T = X]` slot (§7.3 S2's channel). `apply_domain` runs the domain the
//! dictionary names: its provider's `domain` relation, `Colour.domain` here. The spec is
//! `anthill.reflect.SortDomain`; its instances are DERIVED per sort with a domain
//! (`kb::sort_domain_derive`), and only on demand.
//!
//! What a bound that NAMES its sort does is unchanged in answers: it calls that sort's
//! `domain` directly, the provider being written in the bound.
//!
//! BACK-OUT, measured one axis at a time over the whole `wi_tests` binary (each run, not
//! predicted) — see the rows' own notes for which axis each one answers to:
//!  * [A] `step_init`'s `apply_domain` lowering (the goal left to the builtin, which
//!    delays). 2 red: `a_type_variable_bound_enumerates_the_domain_its_caller_holds` and
//!    `a_bound_value_is_read_through_its_carried_type` — `apply_domain` never runs, so
//!    neither the enumeration nor the membership check decides.
//!  * [V] the sweep's type-variable branch (no implicit read, no `apply_domain`).
//!    1 red: the enumeration row, which flounders as it did before S3. The mode-(in) row
//!    passes — with no member goal the conformance goal alone accepts `red()`.
//!  * [D] §7.3 S3(d), the enclosing sort's parameter per activation
//!    (`bound_var_joins_frame` answering as before). 3 red: both rows above and
//!    `wi_5g28a_citation_bracket_test::a_bound_value_pins_the_parameter_per_activation` —
//!    the shared `T` cannot be pinned, so the conformance goal suspends.
//!  * [G] (RETIRED by WI-20260925-SHED7) the derivation gate's type-variable arm. A
//!    `SortDomain` read is now built from a type — at run time by the resolver, at a
//!    citation by the typer — and never from a provision row, so the arm is gone and
//!    `nothing_is_derived_until_something_can_read_it` pins the narrower gate.
//!  * [S] (RETIRED by WI-20260925-SHED7) the ground bound's static `S.domain(?x)`, which
//!    backed out to `domain_member(?x, S)` — a relation SHED7 deleted, so there is nothing
//!    left to back out to: `S.domain` IS the sort's derived `fill` now, not a call into
//!    `domain_member`. SHED7's own axes are in `wi_shed7_fillable_test`.
//!
//! Nothing else in `wi_tests` moved under any axis.

use anthill_core::eval::Value;

/// `Colour` has three values and `Letter` two, so a count cannot be satisfied by the other
/// instance's domain.
const PROGRAM: &str = r#"
namespace wi5g28a.s3
  import anthill.prelude.{Int64, Error, EmptyStream}
  import anthill.reflect.SortDomain

  sort Colour
    entity red
    entity green
    entity blue
  end

  sort Letter
    entity a
    entity b
  end

  -- `el`'s bound is `Wrap`'s own parameter: a TYPE VARIABLE, which no term names
  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end

  sort Driver
    operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] =
      Wrap[T = X].el.takeN(5).length()
    operation colours() -> Int64 effects {Error} = countAt[X = Colour]()
    operation letters() -> Int64 effects {Error} = countAt[X = Letter]()
  end
end
"#;

fn drive(entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(PROGRAM);
    match interp.call(&format!("wi5g28a.s3.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// THE CASE — §7.3 S3's RIGID row. `countAt[X]` holds `SortDomain[T = X]` for its rigid
/// `X`; the citation `Wrap[T = X].el` routes `el`'s implicit read to that slot; the clause
/// runs `apply_domain` on it, which enumerates `X`'s domain. Two instances, two counts, so
/// a fill with the wrong instance cannot pass. Before S3 the citation floundered: `el`'s
/// bound had only the conformance goal, which cannot generate.
#[test]
fn a_type_variable_bound_enumerates_the_domain_its_caller_holds() {
    assert_eq!(drive("colours"), 3, "`Colour`'s three values, through the caller's dictionary");
    assert_eq!(drive("letters"), 2, "and `Letter`'s two, through the other instance's");
}

/// A program that CITES nothing and WRITES no `SortDomain`: `el` is reached from a rule
/// body, so no caller hands it a dictionary.
fn uncited(extra: &str) -> String {
    format!(
        "namespace wi5g28a.s3u\n\
         \x20 sort Colour\n\
         \x20   entity red\n\
         \x20   entity green\n\
         \x20   entity blue\n\
         \x20 end\n\
         \x20 sort Wrap[T]\n\
         \x20   entity wrap(v: T)\n\
         \x20   rule el(?x: T) :- true\n\
         \x20 end\n\
         {extra}\
         end\n"
    )
}

/// MODE (in) NEEDS NO CALLER: with `?x` bound, the implicit read DERIVES the dictionary
/// from the value's carried type, as any anchored `require` does, and `apply_domain` checks
/// membership through it. That derivation reads the `SortDomain` rows, which this program
/// never asks for by name — the gate opens on `el`'s type-variable bound.
#[test]
fn a_bound_value_is_read_through_its_carried_type() {
    let mut kb =
        crate::common::load_kb_with(&uncited("  rule inEl(1) :- Wrap.el(red())\n"));
    let answers = crate::common::definite_unary(&mut kb, "wi5g28a.s3u.inEl");
    let ints: Vec<Option<i64>> = answers.iter().map(|v| crate::common::scalar_int(&kb, v)).collect();
    assert!(
        ints == [Some(1)],
        "`red()` is read as a `Colour` and checked against `Colour`'s domain: one definite \
         row, got {answers:?}",
    );
}

/// CONTROL — passes either way, BY DESIGN: with `?x` free and no caller, nothing names a
/// domain, so the clause cannot generate. It flounders LOUDLY — an undecided answer, never
/// an empty set — which is what the conformance goal alone did before S3.
#[test]
fn a_free_type_variable_with_no_caller_stays_undecided() {
    let mut kb = crate::common::load_kb_with(&uncited("  rule anyEl(?x) :- Wrap.el(?x)\n"));
    let answers = crate::common::query_unary(&mut kb, "wi5g28a.s3u.anyEl");
    assert!(
        !answers.is_empty() && answers.iter().all(|(_, definite)| !*definite),
        "no domain and no caller: undecided rows only, got {answers:?}",
    );
}

/// CONTROL — a bound that NAMES its sort. The sweep calls `Colour.domain(?x)` — the member
/// of `Colour`'s `SortDomain`, dispatched statically because the bound names the provider;
/// it called the retired `domain_member(?x, Colour)` before SHED7, and the three rows are the
/// same. The row is here so a change that broke the static call could not pass as a no-op.
#[test]
fn a_bound_that_names_its_sort_enumerates_as_before() {
    let mut kb = crate::common::load_kb_with(&uncited("  rule pick(?x: Colour) :- true\n"));
    assert_eq!(crate::common::definite_unary(&mut kb, "wi5g28a.s3u.pick").len(), 3);
}

/// THE GATE: the `SortDomain` rows cost ~115 ms per load (debug) in the typer's provision
/// walks, so they are derived only when something reads them — a WRITTEN requirement
/// (`kb::sort_domain_derive`). WI-20260925-SHED7: a type-variable bound no longer opens it;
/// its citation's route is built from the type (`typing::sort_domain_route`), and its
/// uncited read from the value, neither through a row.
#[test]
fn nothing_is_derived_until_something_can_read_it() {
    let domain_rows = |src: &str| -> Vec<String> {
        crate::common::sort_provisions_all(&crate::common::load_kb_with(src))
            .into_iter()
            .filter(|(_, spec)| spec == "anthill.reflect.SortDomain")
            .map(|(carrier, _)| carrier)
            .collect()
    };
    let closed = domain_rows(
        "namespace wi5g28a.s3g\n\
         \x20 sort Colour\n\
         \x20   entity red\n\
         \x20 end\n\
         \x20 rule pick(?x: Colour) :- true\n\
         end\n",
    );
    assert!(closed.is_empty(), "a named-sort bound reads no row, so none is derived: {closed:?}");
    let still_closed = domain_rows(&uncited(""));
    assert!(
        still_closed.is_empty(),
        "a type-variable bound reads no row either: {still_closed:?}",
    );
    let open = domain_rows(PROGRAM);
    assert!(
        open.iter().any(|c| c == "wi5g28a.s3.Colour") && open.iter().any(|c| c == "wi5g28a.s3.Wrap"),
        "a written `requires SortDomain[…]` opens the gate, for every sort with a domain: \
         {open:?}",
    );
}
