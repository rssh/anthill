//! WI-463 — an UNqualified spec-op call dispatches to a WITNESS sort: the
//! witness completion of WI-476's name-resolution model.
//!
//! WI-450 made witness dispatch work for the QUALIFIED direct form
//! (`Combiner.combine(tag, tag)`), the generic `requires` form, and the
//! dot-call form, but left the UNqualified direct form `combine(tag, tag)`
//! to a name-resolution concern: the (now deleted) `resolve_by_short_name`
//! global fallback returned `None` on the spec-op / witness-member short-name
//! collision (`Combiner.combine` and `TagCombiner.combine` both matched short
//! `combine`), so the call was silently left unresolved and died
//! `UnknownOperation` at eval. A `fact`-based instance had no such collision
//! (its impl is a distinct name like `tagCombine`), which is why the
//! fact-instance form already worked unqualified (wi431.eval).
//!
//! WI-476 dissolved that at the root by deleting `resolve_by_short_name`: an
//! unqualified spec-op short name resolves to the SPEC op through the LOCAL
//! scope (here a self-namespace `import …Combiner.{combine}`, exactly as
//! wi431.eval brings its spec op into scope), and a witness member
//! (`TagCombiner.combine`) is NEVER an unqualified-namespace candidate — it is
//! reachable only by dispatch or qualification. So there is no collision: the
//! unqualified name resolves unambiguously to `Combiner.combine` and then
//! value-directs to the witness impl, identically to the fact-instance form.
//!
//! This pins that completion — the unqualified witness call both LOADS clean
//! and DISPATCHES to the witness member at eval (result `99`).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// The witness scenario with the spec op brought into scope by a self-namespace
/// import, so the unqualified `combine(tag, tag)` call resolves to the SPEC op
/// `Combiner.combine` (and dispatches to the witness member at eval).
const SRC: &str = r#"namespace test.wi463.eval
  import anthill.prelude.Int64
  import test.wi463.eval.Combiner.{combine}

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end

  sort TagCombiner
    provides Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  end

  -- UNqualified value-directed call (the WI-463 form). `combine` resolves to the
  -- SPEC op `Combiner.combine` via the self-namespace import above; the witness
  -- member `TagCombiner.combine` is not an unqualified-namespace candidate, so
  -- there is no collision. At runtime the args pin `T := Tag` and the spec op
  -- value-directs to the witness impl.
  operation runUnqualified() -> Int64 =
    match combine(tag(n: 1), tag(n: 2))
      case tag(v) -> v
end
"#;

fn load_errors(src: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let s = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&s).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(src).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// LOAD — the unqualified witness scenario loads clean: `combine` resolves to
/// the spec op through the self-namespace import (no `UnknownOperation`, no
/// ambiguity from the witness member sharing the short name).
#[test]
fn unqualified_witness_call_loads_clean() {
    let errs = load_errors(SRC);
    assert!(
        errs.is_empty(),
        "an unqualified spec-op call with the spec op imported and a witness \
         member sharing the short name must load clean: {errs:?}"
    );
}

/// EVAL — the unqualified `combine(tag, tag)` dispatches to the WITNESS member
/// `TagCombiner.combine`, exactly as the qualified `Combiner.combine(tag, tag)`
/// does (wi450 `witness_dispatches_direct_value_call`) and as the fact-instance
/// form does (wi431 `instance_fact_op_dispatches_at_eval`). Result `99` ⇒ the
/// witness ran via the spec op the unqualified name resolved to.
#[test]
fn unqualified_call_dispatches_to_witness() {
    let mut interp = crate::common::interp_for(SRC);
    match interp.call("test.wi463.eval.runUnqualified", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 99,
            "unqualified combine(tag, tag) must dispatch to the witness \
             TagCombiner.combine (n = 99); got {n}"
        ),
        other => panic!(
            "unqualified combine(tag, tag) should resolve to the spec op and \
             value-direct to the witness TagCombiner.combine; got {other:?}"
        ),
    }
}
