//! WI-20260823-GMG6N — a loader-emitted reflect fact whose slot set disagrees with its
//! entity declaration is UNREACHABLE from anthill, and nothing said so.
//!
//! ## The mechanism, which is not "loader facts are second-class"
//!
//! The facts are ordinary facts in the ordinary KB — `rules_by_functor` lists all 398
//! `OperationInfo` clauses, and `anthill query --mode functor` prints them. What fails is
//! that no GOAL can be built that unifies with one. `convert_term_inner`'s named-arg
//! completion (load.rs, *"fill missing entity fields so every fact/pattern of a functor
//! presents the same named slots"*) rewrites every term written in source — fact head,
//! rule head, rule-body goal, CLI pattern — to exactly the fields the entity DECLARES. A
//! loader-emitted head skips that path: it is assembled from a hand-written field list at
//! the emitter. Disagree, and the completed goal and the stored head have different slot
//! sets forever.
//!
//! BOTH SPELLINGS FAIL AND NEITHER SAYS WHY. A goal that omits the extra field matches
//! nothing, in silence. A goal that names it is refused by WI-851 as an unknown field.
//! That pincer is why this survived: every way of asking looks like "there is nothing
//! there".
//!
//! ## Two instances, and they drift in opposite directions
//!
//! | functor | declared | emitted | who could not see it |
//! |---|---|---|---|
//! | `anthill.reflect.OperationInfo` | 7 | **8** (`type_params`) | every anthill reader, incl. `docs/proposals/typing_pass_spec.anthill`'s own rule bodies |
//! | `anthill.realization.Implementation` | 8 | **7** (no `binding`) | a query trying to see BOTH a source-written `fact Implementation(…)` and a `provides … language rust` block |
//!
//! The second is the one that shows the invariant is EQUALITY and not "emitted ⊇
//! declared": a head SHORT of a declared slot is just as unreachable, because the goal is
//! completed to the declared set either way. `examples/webots-modelling/lf1` writes nine
//! `fact Implementation(…)` by hand — those are complete — so the two shapes coexisted in
//! one KB and no single goal could reach both.
//!
//! ## What fails when this is backed out
//!
//! [`an_operations_effect_row_is_readable_from_anthill`] and
//! [`a_provides_block_is_readable_from_anthill`] return zero solutions — they are the
//! DRIVEN half, one per instance.
//! [`a_metadata_head_that_disagrees_with_its_declaration_is_refused`] stops panicking if
//! `check_metadata_slots` is removed.
//!
//! [`a_sorts_operation_list_is_readable_either_way`] passes with or WITHOUT the fix, by
//! design: `SortInfo` never drifted, so it fixes the BOUNDARY of the claim — the fact
//! layer was fine, one schema was not — rather than measuring the change.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use anthill_core::kb::{ClauseKind, KnowledgeBase};
use smallvec::SmallVec;

/// A sort with one operation carrying a two-label row, plus a `provides … language rust`
/// block, plus the anthill-side readers for both.
///
/// The readers reach the subject WITHOUT naming it in a goal argument: a bare nominal type
/// in that position is refused today (proposal 055 §3's "logic: rule-body goals, goal
/// arguments — admit" is the plan that changes it), so the sort is pinned by a `fact`
/// ARGUMENT — the surface `anthill.reflect.typing`'s `DefaultProvider(spec, provider)`
/// already rides — and joined to `SortInfo` from there.
const SUBJECT: &str = r#"
sort probe.Thing
  import anthill.prelude.{Error, External}
  entity mk

  operation act(self: Thing) -> Thing
    effects {External, Error}
end

namespace probe
  import anthill.prelude.{String}
  import anthill.reflect.{Symbol, SortInfo, OperationInfo}
  import anthill.reflect.typing.{list_contains}
  import anthill.realization.{Implementation}
  import probe.{Thing}

  -- The subject, as data. A sort reference in a fact argument shares `SortInfo.name`'s
  -- shape, which is what makes the join below possible at all.
  entity Subject(sort: Symbol)
  fact Subject(sort: Thing)

  -- THE CAPABILITY: read a declared operation's effect row, from anthill.
  rule subject_row(?e)
    :- Subject(sort: ?s),
       SortInfo(name: ?s, operations: ?ops),
       list_contains(?op, ?ops),
       OperationInfo(name: ?op, effects: ?e)

  -- The boundary control: the operation LIST needs no `OperationInfo` at all.
  rule subject_ops(?ops)
    :- Subject(sort: ?s), SortInfo(name: ?s, operations: ?ops)

  -- THE CAPABILITY: read a `provides … language rust` block, from anthill. Pinned by a
  -- string literal, which is an ordinary value and needs no nominal-type occurrence.
  rule subject_artifact(?a)
    :- Implementation(target: "probe.Thing", artifact: ?a)

  provides Thing language rust
    artifact "rustland/anthill-core/tests/include/wi_gmg6n_metadata_slot_drift_test.rs"
  end
end
"#;

fn subject_kb() -> KnowledgeBase {
    crate::common::expect_loaded(crate::common::try_load_kb_with_files(&[SUBJECT]))
}

/// The `TermId` a solution carries.
///
/// A loader-emitted reflect field rides as a HASH-CONSED `Value::Term`, not as the
/// entity carrier `common::list_heads` / `Value::Str` expect — so these assertions walk
/// term-side. LOUD on any other carrier: a lenient fallback would turn a carrier change
/// into a mysteriously-failing (or worse, vacuously passing) assertion.
fn term_of(v: &Value) -> anthill_core::kb::term::TermId {
    match v {
        Value::Term { id, .. } => *id,
        other => panic!("expected a hash-consed reflect field, got {other:?}"),
    }
}

/// The qualified names a cons-list of name terms carries.
fn names_in(kb: &KnowledgeBase, v: &Value) -> Vec<String> {
    anthill_core::kb::typing::list_to_vec(kb, term_of(v))
        .into_iter()
        .map(|id| match kb.get_term(id) {
            Term::Ref(s) => kb.qualified_name_of(*s).to_string(),
            Term::Fn { functor, .. } => kb.qualified_name_of(*functor).to_string(),
            other => panic!("expected a name term, got {other:?}"),
        })
        .collect()
}

/// The `String` literal a term-carried field holds.
fn string_in(kb: &KnowledgeBase, v: &Value) -> String {
    match kb.get_term(term_of(v)) {
        Term::Const(anthill_core::kb::term::Literal::String(s)) => s.clone(),
        other => panic!("expected a String literal term, got {other:?}"),
    }
}

#[test]
fn an_operations_effect_row_is_readable_from_anthill() {
    // THE DRIVEN CLAIM, and the one an anthill-side checker needs: "what may this
    // operation do" is a question about `OperationInfo.effects`, and until the
    // declaration grew `type_params` no goal could ask it. Zero solutions before the fix.
    let mut kb = subject_kb();
    let rows = crate::common::definite_unary(&mut kb, "probe.subject_row");
    assert_eq!(
        rows.len(),
        1,
        "probe.Thing declares exactly one operation, so exactly one row is expected; got {rows:?}"
    );
    let labels = names_in(&kb, &rows[0]);
    assert_eq!(
        labels,
        vec![
            "anthill.prelude.External".to_string(),
            "anthill.prelude.Error".to_string()
        ],
        "the declared row {{External, Error}} must come back, in declaration order"
    );
}

#[test]
fn a_provides_block_is_readable_from_anthill() {
    // The second instance, and it drifts the OTHER way — the emitter was SHORT of a
    // declared slot. Zero solutions before `emit_implementation_fact` learned to write
    // `binding: none()`.
    let mut kb = subject_kb();
    let arts = crate::common::definite_unary(&mut kb, "probe.subject_artifact");
    assert_eq!(
        arts.len(),
        1,
        "one `provides Thing language rust` block was declared; got {arts:?}"
    );
    let artifact = string_in(&kb, &arts[0]);
    assert!(
        artifact.contains("wi_gmg6n_metadata_slot_drift_test.rs"),
        "the block's artifact must come back; got {artifact:?}"
    );
}

#[test]
fn a_sorts_operation_list_is_readable_either_way() {
    // THE BOUNDARY, not a measurement: `SortInfo` never drifted, so this passes with the
    // fix backed out. It is here to keep the diagnosis honest — the fact layer was never
    // broken, one schema was.
    let mut kb = subject_kb();
    let ops = crate::common::definite_unary(&mut kb, "probe.subject_ops");
    assert_eq!(ops.len(), 1, "one sort, one operations list; got {ops:?}");
    let names = names_in(&kb, &ops[0]);
    assert!(
        names.iter().any(|n| n.ends_with(".act")),
        "SortInfo.operations must list `act`; got {names:?}"
    );
}

#[test]
#[should_panic(expected = "metadata fact schema drift")]
fn a_metadata_head_that_disagrees_with_its_declaration_is_refused() {
    // THE GUARD, driven directly, because no source program can provoke it:
    // `assert_metadata_fact` is the loader's own door (a user-written fact goes through
    // `convert_term_inner` to `assert_fact`), so the drift can only be introduced by
    // editing an emitter — which is exactly when this must fire.
    //
    // Simulated by widening the DECLARATION instead of narrowing an emitter: the check
    // compares the two lists and does not care which side moved.
    let mut kb = crate::common::load_stdlib_kb();
    let functor = kb
        .try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("SortProvidesInfo is a reflect functor the loader emits");
    let sort_ref = kb.intern("sort_ref");
    let spec = kb.intern("spec");
    let bogus = kb.intern("bogus");
    kb.register_entity_fields(functor, vec![sort_ref, spec, bogus]);

    let unit = kb.intern("Unit");
    let leaf = kb.alloc(Term::Ref(unit));
    let head = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(sort_ref, leaf), (spec, leaf)]),
    });
    let domain = kb.intern("probe");
    kb.assert_metadata_fact(head, ClauseKind::Fact, domain, None);
}
