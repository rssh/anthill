//! WI-450 — WITNESS SORTS dispatch param-agnostically, exactly as instance FACTS do.
//!
//! A witness sort retroactively satisfies a spec for a carrier WITHOUT modifying
//! the carrier or the spec — the dual of an instance fact, but the impl ops are
//! MEMBERS of the witness sort rather than op-valued bindings:
//!
//! ```anthill
//! sort TagCombiner
//!   provides Combiner[T = Tag]
//!   operation combine(x: Tag, y: Tag) -> Tag = tag(n: 99)
//! end
//! ```
//!
//! The witness's `SortProvidesInfo` carries `sort_ref = TagCombiner` (the provider
//! sort) but the DISPATCH carrier — what a `combine(tag, tag)` call's args are — is
//! `Tag`. Pre-WI-450 value-directed dispatch keyed on `sort_ref == carrier_sym`
//! (`Tag`), so it never found the witness (whose `sort_ref` is `TagCombiner`),
//! while a `fact Combiner[T = Tag, combine = …]` worked because its derived carrier
//! IS `Tag`. WI-450 makes value-directed dispatch UNIFY the spec application
//! (`Combiner[T = Tag]`) against provisions — param-agnostic, like the requires
//! path — so the witness resolves identically, with the op found as a member of the
//! provider sort (`TagCombiner.combine`).

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

const WITNESS_SRC: &str = r#"namespace test.wi450.eval
  import anthill.prelude.Int64

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

  -- Generic typeclass-polymorphic consumer: `combine` resolves to the SPEC op
  -- `Combiner.combine` via Box's `requires Combiner[T]` (no name collision — the
  -- witness member `TagCombiner.combine` is not in this scope). At runtime
  -- `combineBox(box(tag))` pins `T := Tag` and dispatches `combine` to the witness.
  sort Box
    sort T = ?
    requires Combiner[T]
    entity box(content: T)
    operation combineBox(b: Box) -> T =
      match b
        case box(c) -> combine(c, c)
  end

  -- Direct value-directed call, QUALIFIED `Combiner.combine`. The UNqualified form
  -- `combine(tag, tag)` (the spec op imported into scope, no collision with the
  -- witness member `TagCombiner.combine`) was a name-resolution concern dissolved by
  -- WI-476 and verified for the witness in WI-463 (wi463_unqualified_witness_dispatch_test).
  operation runDirect() -> Int64 =
    match Combiner.combine(tag(n: 1), tag(n: 2))
      case tag(v) -> v

  operation runGeneric() -> Int64 =
    match box(content: tag(n: 5)).combineBox()
      case tag(v) -> v

  -- Dot-call sugar `tag.combine(tag)` resolves `combine` to the spec op via the
  -- witness provision (the dot path, not the ambiguous unqualified name) and
  -- value-directs to the witness impl.
  operation runDot() -> Int64 =
    match tag(n: 1).combine(tag(n: 2))
      case tag(v) -> v
end
"#;

/// The witness sort `TagCombiner provides Combiner[T = Tag]` with its own `combine`
/// member op covers `Combiner.combine` (the provider owns a real impl) — it must
/// load clean (no `UnbackedProviderOperation`).
#[test]
fn witness_sort_loads_clean() {
    let errs = load_errors(&[WITNESS_SRC]);
    assert!(
        errs.is_empty(),
        "a witness sort providing Combiner with its own combine member must load clean: {errs:?}"
    );
}

/// EVAL — the realistic typeclass usage: a generic `combineBox` over `requires
/// Combiner[T]` calls `combine` on its abstract `T`; at `combineBox(box(tag))` the
/// receiver pins `T := Tag` and the spec op dispatches to the WITNESS member
/// `TagCombiner.combine` — the carrier-keyed lookup (`instance_fact_op_binding`)
/// misses it (provision `sort_ref` is `TagCombiner`, ≠ carrier `Tag`), so the
/// param-agnostic witness resolution is the only route. Result `99` ⇒ the witness ran.
#[test]
fn witness_dispatches_in_generic_context() {
    let mut interp = crate::common::interp_for(WITNESS_SRC);
    match interp.call("test.wi450.eval.runGeneric", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 99,
            "combineBox must dispatch combine to the witness TagCombiner.combine (n = 99); got {n}"
        ),
        other => panic!(
            "combineBox should dispatch combine via the witness provision to TagCombiner.combine; got {other:?}"
        ),
    }
}

/// EVAL — a direct value-directed call on the carrier value: `Combiner.combine(tag,
/// tag)` dispatches to `TagCombiner.combine` even though `Tag` owns no `combine` and
/// the provision's `sort_ref` is `TagCombiner` (≠ the dispatch carrier `Tag`). The
/// param-agnostic unification of `Combiner[T = Tag]` against the witness provision
/// is the only route. Result `99` ⇒ the witness ran.
#[test]
fn witness_dispatches_direct_value_call() {
    let mut interp = crate::common::interp_for(WITNESS_SRC);
    match interp.call("test.wi450.eval.runDirect", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 99,
            "Combiner.combine(tag, tag) must dispatch to the witness TagCombiner.combine (n = 99); got {n}"
        ),
        other => panic!(
            "Combiner.combine(tag, tag) should dispatch via the witness provision; got {other:?}"
        ),
    }
}

/// EVAL — dot-call sugar on the carrier value: `tag.combine(tag)` resolves `combine`
/// to `Combiner.combine` through the witness provision (the typer's dot-apply
/// fallback, `find_spec_op_for_provided_sort`, now param-agnostic) and dispatches to
/// `TagCombiner.combine`. Result `99`.
#[test]
fn witness_dispatches_dot_call() {
    let mut interp = crate::common::interp_for(WITNESS_SRC);
    match interp.call("test.wi450.eval.runDot", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 99,
            "tag.combine(tag) must dispatch to the witness TagCombiner.combine (n = 99); got {n}"
        ),
        other => panic!(
            "tag.combine(tag) should resolve combine via the witness provision and dispatch; got {other:?}"
        ),
    }
}

/// COHERENCE (rule 2, witness flavor) — RELOCATED BY WI-843 (058 §4.1 tier 3).
///
/// Two witnesses providing the same `Combiner[T = Tag]` with different `combine`
/// impls were a loud ambiguity AT LOAD, exactly as two instance facts are (WI-431
/// rule 2 extended to witness provisions). They now COEXIST: a witness sort has a
/// name, so the choice can be written, and the refusal moved to a dispatch that
/// writes none. The two instance facts stay refused at load — they have no name —
/// so what looked like one rule is now visibly two, keyed on nameability (§4.3).
///
/// Both halves are asserted here rather than only the flip, because "no error"
/// alone would also be satisfied by the coherence walk never seeing this shape:
/// the same pair with an unselected CALL added must still be loud, at that call.
#[test]
fn duplicate_witnesses_coexist_and_only_an_unselected_call_is_loud() {
    let program = |caller: &str| {
        format!(
            r#"namespace test.wi450.coherence
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end

  sort TagCombinerA
    provides Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 1)
  end
  sort TagCombinerB
    provides Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 2)
  end
{caller}end
"#
        )
    };
    let declarations_only = program("");
    let errs = load_errors(&[&declarations_only]);
    assert!(
        errs.is_empty(),
        "two NAMEABLE witnesses for (Combiner, Tag) coexist under 058 tier 3: {errs:?}"
    );

    // The same declarations plus a call that names neither: loud, at that call.
    let with_unselected_call = program(
        "  sort Use\n    operation go(a: Tag, b: Tag) -> Tag = Combiner.combine(a, b)\n  end\n",
    );
    let errs = load_errors(&[&with_unselected_call]);
    assert!(
        errs.iter().any(|e| e.contains("ambiguous dispatch of")
            && e.contains("test.wi450.coherence.TagCombinerA")
            && e.contains("test.wi450.coherence.TagCombinerB")),
        "an unselected dispatch against the coexisting pair must be loud AT THE \
         CALL, naming both witnesses: {errs:?}"
    );
}
