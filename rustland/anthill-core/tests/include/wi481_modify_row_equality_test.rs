//! WI-481 — a value-in-type (denoted) `Modify[p]` effect row must compare EQUAL
//! across a call so a correctly-DECLARED `effects {Modify[p]}` is ACCEPTED.
//!
//! Repro (pre-existing; reproduces with the explicit `[T, E]` form too, so NOT a
//! projection issue): an op `eff_stream(p: Producer) -> Strm[T = Int64, E = {Modify[p]}]`
//! and a `Strm` observation op that incurs its `E` row; the consumer
//!   `operation okeff(p: Producer) -> Bool effects {Modify[p]} = obsEmpty(eff_stream(p))`
//! errors `undeclared effect: Modify[T = p]` even though the declared and incurred
//! `Modify[T = p]` (Modify parameterized by the VALUE `p`, a denoted/value-in-type
//! effect) are structurally identical. The undeclared-effect check
//! (`check_operation_bodies` → `views_structurally_equal`) treats them as distinct.
//!
//! Acceptance: the `okeff`-style DECLARED-Modify acceptance loads clean, while a
//! WRONG/absent declaration still REJECTS (so the fix is an equality fix, not a
//! blanket accept).

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

// A bare-form `Strm` spec whose observation op `obsEmpty` incurs its `E` row, plus a
// `Producer` carrier whose `eff_stream` writes `E = {Modify[p]}` (Modify by the VALUE
// p — a denoted/value-in-type effect).
const SPEC_AND_CARRIER: &str = r#"
namespace test.wi481.strm
  import anthill.prelude.{Bool, Modify, EffectsRuntime}
  sort Strm
    sort T = ?
    effects E = ?
    operation obsEmpty(s: Strm) -> Bool effects s.E = true
  end
end
namespace test.wi481.carrier
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  import test.wi481.strm.{Strm}
  sort Producer
    operation pure_stream(p: Producer) -> Strm[T = Int64, E = {}]
    operation eff_stream(p: Producer) -> Strm[T = Int64, E = {Modify[p]}]
    operation remix(s: Strm, p: Producer) -> Strm[T = s.T, E = {Modify[p]}]
  end
end
"#;

/// THE BUG: a consumer DECLARING `effects {Modify[p]}` and incurring exactly
/// `Modify[p]` (by observing the effectful stream) must LOAD CLEAN — the declared and
/// incurred denoted `Modify[p]` are the same effect.
#[test]
fn declared_modify_row_accepted() {
    let consumer = r#"
namespace test.wi481.okeff
  import anthill.prelude.{Bool, Modify}
  import test.wi481.strm.Strm.{obsEmpty}
  import test.wi481.carrier.{Producer}
  import test.wi481.carrier.Producer.{eff_stream}
  operation okeff(p: Producer) -> Bool effects {Modify[p]} = obsEmpty(eff_stream(p))
end
"#;
    let errs = load_errors(&[SPEC_AND_CARRIER, consumer]);
    assert!(
        errs.is_empty(),
        "a consumer declaring `effects {{Modify[p]}}` and incurring exactly Modify[p] must \
         load clean (WI-481); got: {errs:?}",
    );
}

/// MUST STILL REJECT — a pure consumer (no `effects` declaration) incurring Modify[p]
/// is still an undeclared effect. Pins that the fix is an equality fix, not a blanket
/// accept (mirrors wi475's effectful-rejected control).
#[test]
fn absent_declaration_still_rejected() {
    let consumer = r#"
namespace test.wi481.bad
  import anthill.prelude.{Bool}
  import test.wi481.strm.Strm.{obsEmpty}
  import test.wi481.carrier.{Producer}
  import test.wi481.carrier.Producer.{eff_stream}
  operation bad(p: Producer) -> Bool = obsEmpty(eff_stream(p))
end
"#;
    let errs = load_errors(&[SPEC_AND_CARRIER, consumer]);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect") && e.contains("Modify")),
        "a pure consumer incurring Modify[p] with no declaration must still be rejected; got: {errs:?}",
    );
}

/// THE BUG, MIXED with a projection: `remix(s, p) -> Strm[T = s.T, E = {Modify[p]}]`
/// has BOTH a projection (`s.T`) and a value-in-type denoted (`Modify[p]`) in its
/// return. Because the op has a projection, the return is re-keyed inside
/// `eliminate_type_projections` (NOT the projection-free call-site path), so the
/// denoted `Modify[p]` must be re-keyed in the elimination's `Denoted` arm. Observing
/// it and declaring `effects {Modify[p]}` must load clean.
#[test]
fn declared_modify_row_accepted_with_projection() {
    let consumer = r#"
namespace test.wi481.mix
  import anthill.prelude.{Bool, Modify}
  import test.wi481.strm.{Strm}
  import test.wi481.strm.Strm.{obsEmpty}
  import test.wi481.carrier.{Producer}
  import test.wi481.carrier.Producer.{remix}
  operation usemix(s: Strm, p: Producer) -> Bool effects {Modify[p]} = obsEmpty(remix(s, p))
end
"#;
    let errs = load_errors(&[SPEC_AND_CARRIER, consumer]);
    assert!(
        errs.is_empty(),
        "a consumer declaring `effects {{Modify[p]}}` over a mixed projection+denoted return \
         must load clean (WI-481 elimination Denoted-arm re-key); got: {errs:?}",
    );
}

/// MUST NOT REGRESS — declaring `effects {Modify[p]}` but incurring NOTHING (observing
/// the pure stream) loads clean: an over-declaration is allowed (the declared row is an
/// upper bound; nothing incurred is a subset).
#[test]
fn over_declaration_accepted() {
    let consumer = r#"
namespace test.wi481.over
  import anthill.prelude.{Bool, Modify}
  import test.wi481.strm.Strm.{obsEmpty}
  import test.wi481.carrier.{Producer}
  import test.wi481.carrier.Producer.{pure_stream}
  operation over(p: Producer) -> Bool effects {Modify[p]} = obsEmpty(pure_stream(p))
end
"#;
    let errs = load_errors(&[SPEC_AND_CARRIER, consumer]);
    assert!(
        errs.is_empty(),
        "declaring Modify[p] but incurring nothing (pure stream) must load clean; got: {errs:?}",
    );
}
