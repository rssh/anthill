//! WI-430 — CARRIER-PRECISE `requires` matching for `ExprCarried` neutrals.
//!
//! WI-400 forms an abstract-receiver projection (`s.provider.K`, `s.provider : P` an
//! abstract type-parameter of `State`) as a rigid NEUTRAL when the member is declared on
//! the receiver's interface — lent by a `requires Spec[param]` bound on the declaring sort.
//! The pre-WI-430 gate (`abstract_member_declared_by_requires`) consulted the declaring
//! sort's WHOLE `requires` chain: a member declared by ANY required spec licensed the
//! projection, even when that spec's carrier is a SIBLING parameter, not the receiver's.
//!
//! A sort with several parameters each carrying their own `requires` therefore
//! over-accepted: `State[P, Q] requires DataProvider[P], OtherProvider[Q]` wrongly accepted
//! `s.provider.M` (`M` is `OtherProvider`'s member, carried by `Q`) off the `P`-typed
//! `s.provider`. Runtime-sound today (the mistyped signature is uncallable), but an
//! over-acceptance, and the neutral's licensing carrier is ambiguous.
//!
//! The fix keys the receiver's CARRIER identity (the param's alias var-id, the WI-428
//! `SubjectKey`) and gates each `requires` bound on `spec_mentions_key` — the
//! `ExprCarried`-side counterpart of `resolve_rigid_projection`'s WI-428 candidate filter.
//! Only a bound whose carrier IS the receiver param lends the member.
//!
//! Design: `docs/design/path-dependent-types.md` §4.1 / §5.3 (the carrier-precise
//! convergence); ticket WI-430.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// A two-provider sort whose params each carry their own `requires`. `s.provider : P`
/// carries `DataProvider` (member `K`); `s.other : Q` carries `OtherProvider` (member
/// `M`). Shared fixture for the carrier-precision tests below.
const TWO_PROVIDER_STATE: &str = r#"
  sort DataProvider
    sort K = ?
  end
  sort OtherProvider
    sort M = ?
  end
  sort State
    sort P = ?
    sort Q = ?
    requires DataProvider[P]
    requires OtherProvider[Q]
    entity state(provider: P, other: Q)
  end
"#;

/// THE BUG: `M` is declared by `OtherProvider`, carried by `Q` — NOT by `s.provider`'s
/// `P` (which carries `DataProvider`). Projecting `s.provider.M` must be a LOUD error: no
/// `requires` bound WHOSE CARRIER IS `P` declares `M`. Pre-WI-430 this was wrongly accepted
/// because the whole-chain reading saw `OtherProvider` declare `M` somewhere on `State`.
#[test]
fn wrong_param_member_projection_rejected() {
    let bad = format!(
        r#"
namespace test.wi430.wrong_carrier
{TWO_PROVIDER_STATE}
  operation bad(s: State, x: s.provider.M) -> s.provider.M = x
end
"#
    );
    let errs = load_errors(&[&bad]);
    assert!(
        errs.iter().any(|e| e.contains("cannot project 'M'") && e.contains("carrier")),
        "s.provider.M projects OtherProvider's member off the DataProvider-carrying P — no \
         `requires` bound whose carrier is P declares M, so it must be a loud carrier-precise \
         error; got: {errs:?}",
    );
}

/// NO REGRESSION: each member projected off its OWN carrier still forms a neutral and the
/// identity body type-checks. `s.provider.K` (P carries DataProvider.K) and `s.other.M`
/// (Q carries OtherProvider.M) are both well-formed — the carrier-precise gate matches the
/// bound whose carrier IS the receiver param.
#[test]
fn right_param_member_projections_accepted() {
    let ok = format!(
        r#"
namespace test.wi430.right_carrier
{TWO_PROVIDER_STATE}
  operation getK(s: State, k: s.provider.K) -> s.provider.K = k
  operation getM(s: State, m: s.other.M) -> s.other.M = m
end
"#
    );
    assert!(
        load_errors(&[&ok]).is_empty(),
        "s.provider.K and s.other.M project each member off its OWN carrier — both must \
         form clean neutrals; got: {:?}",
        load_errors(&[&ok]),
    );
}

/// The carrier-precise gate is SYMMETRIC: the mirror projection `s.other.K` (K is
/// DataProvider's member, carried by P — not by Q-typed `s.other`) is ALSO a loud error.
/// Together with the positive test this pins that the gate routes each member to exactly
/// its carrier, not "any member declared anywhere on the sort".
#[test]
fn mirror_wrong_param_member_rejected() {
    let bad = format!(
        r#"
namespace test.wi430.mirror_wrong
{TWO_PROVIDER_STATE}
  operation bad(s: State, k: s.other.K) -> s.other.K = k
end
"#
    );
    let errs = load_errors(&[&bad]);
    assert!(
        errs.iter().any(|e| e.contains("cannot project 'K'") && e.contains("carrier")),
        "s.other.K projects DataProvider's member off the OtherProvider-carrying Q — must \
         be a loud carrier-precise error; got: {errs:?}",
    );
}

/// The added carrier-precise conjunct must NOT let a GENUINELY-missing member slip through.
/// `s.provider.Bogus` — `Bogus` is declared by NEITHER provider — stays a loud error: the
/// `declares member` half fails before the carrier gate is even consulted. Pins that the
/// `&& spec_mentions_key` refinement narrows wrong-CARRIER acceptance without widening
/// missing-member acceptance (the WI-400 missing-member guard still holds on a multi-param
/// sort, not only the single-param fixture WI-400 tests).
#[test]
fn genuinely_missing_member_still_loud() {
    let bad = format!(
        r#"
namespace test.wi430.missing_member
{TWO_PROVIDER_STATE}
  operation bad(s: State, x: s.provider.Bogus) -> s.provider.Bogus = x
end
"#
    );
    let errs = load_errors(&[&bad]);
    assert!(
        errs.iter().any(|e| e.contains("cannot project 'Bogus'")),
        "Bogus is declared by no provider — must stay a loud error, never slip through the \
         carrier gate; got: {errs:?}",
    );
}
