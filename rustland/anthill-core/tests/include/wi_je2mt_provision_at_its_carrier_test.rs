//! WI-20261121-JE2MT — THE DERIVATIONS READ A PROVISION AT ITS CARRIER (stage 1 of
//! `docs/design/spec-carrier-set.md`; filed with the user 2026-11-21, scope decided 2026-11-22).
//!
//! Two readings of which sort a provision is about disagreed for a spec no operation of which
//! receives on its parameter — `Eq`, `SortDomain`, `TypeValue`: the parameter an operation
//! receives on (`provision_carriers_of_spec`, the witness criterion's), which such a spec has
//! none of, so a witness was filed under the WITNESS; and that parameter or the sole one
//! (`provisions_about`). Both are gone. The owner is `typing::sort_carrier`, the spec's
//! type-vars, all of them (decision 4); `typing::ProvisionsOfSpec` files each provision at its
//! carrier, the spec at its bindings (decision 5), and answers "is a provision at the carrier a
//! derivation would add" by the default rows' unification. Its readers: `eq_derive`'s
//! `EqualityProvisions::speak_for` (was `spoken_for`), `equality_signatures`,
//! `equality_reaching_no_eq` and `written_spec_of`; `load::EqProviders::of`; `sort_domain_derive`
//! and `type_value_derive`'s `already`. `LoadError::HandWrittenTypeValue` names the PROVIDER.
//!
//! WHAT MOVED, MEASURED 2026-11-22 on the selected binary (design §5: one verdict, b1):
//! * [`a_witness_of_sort_domain_is_its_carriers_domain`] — `sort_domain_derive`'s `already` read
//!   by provider again (what the witness criterion answered for `SortDomain`) FAILS it: the call
//!   answers 3, the derived row's `red`, `green`, `blue`, and `Colour` has a derived row beside
//!   `W`'s.
//! * [`a_provision_that_leaves_its_type_var_out_is_refused_once`] — a left-out binding read as
//!   `?` (decision 3's reading, which lands with stage 2) FAILS it: one refusal and about 150
//!   equality-closure errors, one per stdlib composite.
//!
//! READERS MOVED WITH NO VERDICT TO MOVE, each on the reading it already had for these specs:
//! `eq_derive`'s four and `EqProviders` read `Eq`'s sole parameter before (TV0PA), and a binding
//! headed by a sort is at that sort's carrier now. `wi_tv0pa_eq_gives_partial_eq_test` drives
//! them, and stays green. `type_value_derive`'s `already` moves only for a refused program (a
//! written `TypeValue` is refused wherever it stands), and `written_spec_of`, which now follows a
//! forwarded row to its source AT THE SAME CARRIER rather than to the provider's first, names
//! the same spec in every program the suite has: no provider writes the equality family at two
//! carriers with no `eq` at either.
//!
//! PASS EITHER WAY BY DESIGN: [`a_sort_no_provision_speaks_for_derives_its_own_domain`] (the
//! derivation where nothing stands) and [`a_written_type_value_is_refused_naming_its_writer`]
//! (b2: the witness criterion still filed `W`'s row under `W`, so the carrier reading and the
//! provider name `W` alike today — the guard for stage 2, WI-20261122-CXR5B, when the criterion
//! moves).

use crate::common::{interp_for, load_errors_of, load_kb_with, sort_provisions};

/// `Colour`, a `Wrap` whose `el` fills its element through a `SortDomain` dictionary, a driver
/// counting what `fill` yields at `Colour`, and `decls`.
fn domain_program(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Error}}
  import anthill.reflect.{{SortDomain}}

  sort Colour
    entity red
    entity green
    entity blue
  end

{decls}

  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end

  sort Driver
    operation countAt[X]() -> Int64 effects {{Error}} requires SortDomain[T = X] =
      Wrap[T = X].el.takeN(9).length()
    operation colours() -> Int64 effects {{Error}} = countAt[X = Colour]()
  end
end
"#
    )
}

/// What `Driver.colours()` answers.
fn colours(src: &str, ns: &str) -> i64 {
    let mut interp = interp_for(src);
    match interp.call(&format!("{ns}.Driver.colours"), &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("`{ns}.Driver.colours` did not answer an Int64: {other:?}"),
    }
}

/// Does `provider` provide `SortDomain` by a row of its own?
fn provides_sort_domain(src: &str, provider: &str) -> bool {
    sort_provisions(&load_kb_with(src))
        .iter()
        .any(|(p, spec)| p == provider && spec == "anthill.reflect.SortDomain")
}

/// b1. `W` writes `Colour`'s domain, and a call at `Colour` reads it: `red` alone. Read at the
/// parameter an operation receives on — `SortDomain` declares none — `W`'s provision was filed
/// under `W`, nothing seemed to provide `SortDomain` at `Colour`, and the loader derived it a
/// second row, which answered: three colours, `W`'s domain never read.
#[test]
fn a_witness_of_sort_domain_is_its_carriers_domain() {
    let ns = "wije2mt.witness";
    // `W` has a constructor: a provider's `fill` is its `SortDomain` entry, recorded for a sort
    // with constructors — here its written `domain`.
    let src = domain_program(
        ns,
        "  sort W\n    entity w\n    provides SortDomain[T = Colour]\n    rule domain(?x) :- ?x <=> red()\n  end",
    );
    assert_eq!(colours(&src, ns), 1, "`W`'s domain answers at `Colour`: `red` alone");
    assert!(
        !provides_sort_domain(&src, &format!("{ns}.Colour")),
        "`Colour` is given no derived `SortDomain` beside `W`'s, which is at its carrier"
    );
}

/// The control: with nothing at `Colour`'s carrier, `Colour` derives its own domain, and the
/// call answers all three.
#[test]
fn a_sort_no_provision_speaks_for_derives_its_own_domain() {
    let ns = "wije2mt.own";
    let src = domain_program(ns, "");
    assert_eq!(colours(&src, ns), 3);
    assert!(provides_sort_domain(&src, &format!("{ns}.Colour")));
}

/// A provision that leaves its spec's one type-var out is refused (`ProvisionNamesNoCarrier`),
/// and refused ONCE: read as at its provider, as §5.2 says of a left-out carrier parameter, it
/// is about `A` alone. Read as `?`, it was at every carrier, and every composite of the stdlib
/// had its closed equality changed by it.
#[test]
fn a_provision_that_leaves_its_type_var_out_is_refused_once() {
    let src = r#"
namespace wije2mt.leftout
  import anthill.prelude.{PartialEq, Int64}
  sort A
    entity a(v: Int64)
    provides PartialEq
  end
end
"#;
    let errs = load_errors_of(src);
    assert!(errs.iter().any(|e| e.contains("names no carrier")), "{errs:#?}");
    assert!(
        !errs.iter().any(|e| e.contains("is closed, and has changed")),
        "no composite's equality is changed by a provision about `A`: {errs:#?}"
    );
}

/// b2. A written `TypeValue` is refused naming who WROTE it: the witness `W`, not `C`, which
/// wrote nothing.
#[test]
fn a_written_type_value_is_refused_naming_its_writer() {
    let src = r#"
namespace wije2mt.tv
  import anthill.reflect.{TypeValue}
  sort C
    entity c
  end
  sort W
    provides TypeValue[T = C]
  end
end
"#;
    let errs = load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("'wije2mt.tv.W' writes `provides anthill.reflect.TypeValue")),
        "{errs:#?}"
    );
    assert!(!errs.iter().any(|e| e.contains("'wije2mt.tv.C' writes")), "{errs:#?}");
}
