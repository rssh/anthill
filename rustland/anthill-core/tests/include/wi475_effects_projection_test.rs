//! WI-475 (WI-447 bare-form prereq, Gap F): an `effects s.E` PROJECTION must
//! eliminate to a Node-carried effect ROW (e.g. `{Modify[p]}`) instead of erroring
//! `type projection resolved to a non-term carrier, which is not yet supported`.
//!
//! A bare-form observation op `obsEmpty(s: Strm) -> Bool effects s.E` declares its
//! effect as the receiver's observation row `s.E`. When dispatched on a stream whose
//! `E` is WRITTEN (`Strm[E = {Modify[p]}]`), the `s.E` projection must eliminate to
//! `{Modify[p]}` — a `Value::Node` effect row — so the undeclared-effect check sees
//! `Modify[p]` and REJECTS a pure consumer. Before the fix, the projection grounded
//! to a Node carrier and tripped the term-only guard in `rewrite_term_projections`.
//! The fix lifts a TOP-LEVEL single-ref `ExprCarried` projection into
//! `eliminate_type_projections`, returning the projected `Value` (Term OR Node)
//! directly — representable because the effect IS the whole eliminated value.
//!
//! This is the self-contained bare-`s.E` analogue of `wi375`'s acceptance tests
//! (the stdlib `Stream`/`isEmpty` is still explicit `[Elem, Eff]` pending WI-447).
//! Only the element/effect PROJECTION elimination is in scope here; the deeper
//! value-in-type Modify-row EQUALITY (a correctly-DECLARED `effects {Modify[p]}`
//! being accepted) is the separate, pre-existing WI-481 (reproduces with the
//! explicit form too).

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

/// A bare-form `Strm` spec whose observation op `obsEmpty` declares `effects s.E`
/// (the receiver's observation row, via projection), plus a `Producer` carrier with
/// a PURE stream (`E = {}`) and an EFFECTFUL one (`E = {Modify[p]}`).
const SPEC_AND_CARRIER: &str = r#"
namespace test.wi475.strm
  import anthill.prelude.{Bool, Modify, EffectsRuntime}
  sort Strm
    sort T = ?
    effects E = ?
    operation obsEmpty(s: Strm) -> Bool effects s.E = true
  end
end
namespace test.wi475.carrier
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  import test.wi475.strm.{Strm}
  sort Producer
    operation pure_stream(p: Producer) -> Strm[T = Int64, E = {}]
    operation eff_stream(p: Producer) -> Strm[T = Int64, E = {Modify[p]}]
  end
end
"#;

/// Acceptance (pure): observing the `E = {}` stream incurs no effect, so a pure
/// consumer typechecks — `s.E` eliminates to the empty row `{}` and `obsEmpty`'s
/// `effects s.E` closes to pure.
#[test]
fn pure_written_stream_accepted_bare_form() {
    let consumer = r#"
namespace test.wi475.pure
  import anthill.prelude.{Bool}
  import test.wi475.strm.Strm.{obsEmpty}
  import test.wi475.carrier.{Producer}
  import test.wi475.carrier.Producer.{pure_stream}
  operation good(p: Producer) -> Bool = obsEmpty(pure_stream(p))
end
"#;
    let errs = load_errors(&[SPEC_AND_CARRIER, consumer]);
    assert!(
        errs.is_empty(),
        "a pure consumer observing a written-pure stream (Strm[E = {{}}]) via the bare \
         `effects s.E` op must typecheck — s.E eliminates to {{}}; got: {errs:?}",
    );
}

/// Acceptance (effectful → REJECT): observing the `E = {Modify[p]}` stream incurs
/// `Modify[p]`. A pure consumer must be rejected with an undeclared-effect diagnostic
/// naming `Modify` — the `s.E` projection eliminated to the `{Modify[p]}` Node row
/// and the effect check fired. This is the soundness payoff (the effect is IN the
/// type), and it pins that `s.E` eliminated to a *non-empty* row (not silently `{}`).
#[test]
fn effectful_written_stream_rejected_in_pure_context_bare_form() {
    let consumer = r#"
namespace test.wi475.effectful
  import anthill.prelude.{Bool}
  import test.wi475.strm.Strm.{obsEmpty}
  import test.wi475.carrier.{Producer}
  import test.wi475.carrier.Producer.{eff_stream}
  operation bad(p: Producer) -> Bool = obsEmpty(eff_stream(p))
end
"#;
    let errs = load_errors(&[SPEC_AND_CARRIER, consumer]);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect") && e.contains("Modify")),
        "a pure consumer observing a written-effectful stream (Strm[E = {{Modify[p]}}]) via \
         the bare `effects s.E` op must be rejected with an undeclared-effect diagnostic \
         naming Modify — s.E binds to {{Modify[p]}}; got: {errs:?}",
    );
}

/// The fix must NOT leave the projection un-eliminated: the old `non-term carrier`
/// guard error must be GONE (the effectful case rejects for the right reason — an
/// undeclared effect — not because the projection itself failed to resolve).
#[test]
fn effects_projection_no_longer_trips_non_term_guard() {
    let consumer = r#"
namespace test.wi475.guard
  import anthill.prelude.{Bool}
  import test.wi475.strm.Strm.{obsEmpty}
  import test.wi475.carrier.{Producer}
  import test.wi475.carrier.Producer.{eff_stream}
  operation bad(p: Producer) -> Bool = obsEmpty(eff_stream(p))
end
"#;
    let errs = load_errors(&[SPEC_AND_CARRIER, consumer]);
    assert!(
        !errs.iter().any(|e| e.contains("non-term carrier")),
        "the `effects s.E` projection must eliminate to the effect row, not trip the \
         non-term-carrier guard; got: {errs:?}",
    );
}
