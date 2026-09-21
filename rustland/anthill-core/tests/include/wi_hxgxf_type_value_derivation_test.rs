//! WI-20260919-HXGXF (proposal 065 step 2) — `anthill.reflect.TypeValue` is DERIVED for
//! every sort, CONDITIONAL for a parametric one, and a hand-written one is refused.
//!
//! `type_value()` answers the `Type` a rigid names. Every row below calls it THROUGH A
//! REQUIREMENT SLOT — `operation tv[B](…) requires TypeValue[T = B] = TypeValue.type_value()`
//! — because the slot is the only thing that carries the answer: `type_value()` is
//! NULLARY, so no argument and no receiver names the type, and the dispatching dictionary
//! is the sole evidence.
//!
//! ── THE THREE FACTS THAT FORCED THE DESIGN, each measured ────────────────────────
//!
//! 1. A spec op with a DEFAULT BODY is dispatched STATICALLY and never reaches the slot:
//!    the body ran with an empty requirements frame. So `TypeValue.type_value` is
//!    body-less.
//! 2. A body-less spec op with no carrier member is refused at load ("backs no operation
//!    `type_value` … no default on `TypeValue`, no own `type_value` on `Boom`"), and the
//!    loader cannot synthesize a per-carrier body. So it is backed by a BUILTIN on the
//!    spec op (`BuiltinTag::TypeValueOf`), which `op_backed` accepts and which covers
//!    every carrier at once.
//! 3. The dictionary IS the type: `Dictionary(sub₀ … subₙ₋₁, impl: S)` names the head in
//!    `impl` and carries one sub per condition, so the answer is a walk of the evidence.
//!
//! ── WHICH TESTS FAIL WHEN EACH PART IS BACKED OUT ────────────────────────────────
//!
//! Remove the `type_value_derive::run` call: every row of `a_written_type_answers_itself`
//! fails as a LOAD refusal ("no impl provides anthill.reflect.TypeValue"), and
//! `a_hand_written_provision_is_refused` fails the other way — its program LOADS.
//! Move that call BELOW the typer: the same load refusal, because the typer resolves a
//! call's `requires` against the provider relation and a row asserted after it does not
//! exist for the only reader that would use it.
//! Drop the type-parameter filter in `declared_sorts`' caller: every row fails "ambiguous
//! among providers: … Monad.M, DelayMonad.M", a parameter's name term being a VARIABLE
//! that unifies with every goal.
//! Drop the spec filter: the stdlib rows fail "ambiguous among providers: … Iterable,
//! IndexedSeq …", `List`'s own bounds competing to say what `List[T = Int64]` is.
//! Drop the `base` offset in `type_value_of_self`: only `a_carrier_with_its_own_requires`
//! fails — `Map` writes `requires Eq[T = K]`, so its conditions do not start at sub 0.
//!
//! PASSES EITHER WAY BY DESIGN: `a_type_value_goal_in_a_rule_body_is_refused` — a rule
//! body carries no dictionaries before or after, and pins that the refusal says so
//! instead of inventing a type.

use anthill_core::eval::value::Value;

/// The harness: one generic operation whose `requires TypeValue[T = B]` is the slot every
/// row dispatches through, plus local carriers the stdlib does not supply.
fn program(ops: &str) -> String {
    format!(
        r#"
namespace wihxgxf.tv
  import anthill.prelude.{{Int64, Type, List, Option, Map}}
  import anthill.reflect.{{TypeValue}}
  sort Boom
    entity boom
  end
  sort Bang
    entity bang
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort Duo
    sort L = ?
    sort R = ?
    entity duo(l: L, r: R)
  end
  sort D
    operation tv[B](n: Int64) -> Type requires TypeValue[T = B] = TypeValue.type_value()
{ops}
  end
end
"#
    )
}

fn refusals(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// Evaluate `op` and render the `Type` it answers, through the SAME display walk a
/// diagnostic would use — so the assertion reads as the type the author wrote.
fn type_answer(src: &str, op: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(0)]) {
        Ok(Value::Term { id, .. }) => {
            anthill_core::kb::typing::type_display_name(interp.kb(), id)
        }
        other => panic!("{op}: expected a Type term, got {other:?}"),
    }
}

/// THE ACCEPTANCE. A written type answers ITSELF — concrete, parametric, nested, and
/// multi-parameter — with every provision DERIVED and none written.
///
/// The two `Duo` rows are asymmetric on purpose: a swapped position→parameter mapping in
/// `type_value_of_self` would answer `Duo[L = Bang, R = Boom]`, and the differing depths
/// per side rule out a walk that is blind to shape.
#[test]
fn a_written_type_answers_itself() {
    let src = program(
        r#"    operation concrete(n: Int64) -> Type = tv[B = Boom](0)
    operation parametric(n: Int64) -> Type = tv[B = Box[V = Boom]](0)
    operation nested(n: Int64) -> Type = tv[B = Box[V = Box[V = Bang]]](0)
    operation duo(n: Int64) -> Type = tv[B = Duo[L = Boom, R = Bang]](0)
    operation duoNested(n: Int64) -> Type = tv[B = Duo[L = Box[V = Bang], R = Boom]](0)
    operation stdlibList(n: Int64) -> Type = tv[B = List[T = Int64]](0)
    operation stdlibNested(n: Int64) -> Type = tv[B = Option[T = List[T = Int64]]](0)"#,
    );
    assert_eq!(refusals(&src), Vec::<String>::new());
    for (op, want) in [
        ("concrete", "Boom"),
        ("parametric", "Box[V = Boom]"),
        ("nested", "Box[V = Box[V = Bang]]"),
        ("duo", "Duo[L = Boom, R = Bang]"),
        ("duoNested", "Duo[L = Box[V = Bang], R = Boom]"),
        ("stdlibList", "List[T = Int64]"),
        ("stdlibNested", "Option[T = List[T = Int64]]"),
    ] {
        assert_eq!(
            type_answer(&src, &format!("wihxgxf.tv.D.{op}")),
            want,
            "{op}"
        );
    }
}

/// A CARRIER THAT WRITES ITS OWN `requires` — `Map requires Eq[T = K]` — so its derived
/// conditions do NOT start at sub 0 of the dictionary. Reading from 0 would hand back the
/// `Eq` dictionary's impl sort as a type argument, silently and with a plausible-looking
/// answer. Its own row, because it is the only one the offset can break.
#[test]
fn a_carrier_with_its_own_requires_still_answers() {
    let src = program(
        r#"    operation m(n: Int64) -> Type = tv[B = Map[K = Int64, V = Bang]](0)"#,
    );
    assert_eq!(refusals(&src), Vec::<String>::new());
    assert_eq!(
        type_answer(&src, "wihxgxf.tv.D.m"),
        "Map[K = Int64, V = Bang]"
    );
}

/// DERIVED-ONLY (065 §2). A hand-written provision is a load error naming the carrier —
/// a forgeable instance would make `type_value()` a claim instead of a fact.
#[test]
fn a_hand_written_provision_is_refused() {
    let src = r#"
namespace wihxgxf.written
  import anthill.prelude.{Int64}
  import anthill.reflect.{TypeValue}
  sort Boom
    entity boom
    provides TypeValue[T = Boom]
  end
end
"#;
    let errs = refusals(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("wihxgxf.written.Boom") && e.contains("DERIVED")),
        "a written `provides TypeValue` must be refused naming the carrier; got {errs:?}"
    );
}

/// THE CONTROL ON THAT REFUSAL: the very same program WITHOUT the clause loads — so the
/// refusal is about the written clause and not about the sort, and the derived row that
/// replaces it answers.
#[test]
fn the_same_sort_without_the_clause_loads_and_answers() {
    let src = program(r#"    operation c(n: Int64) -> Type = tv[B = Boom](0)"#);
    assert_eq!(refusals(&src), Vec::<String>::new());
    assert_eq!(type_answer(&src, "wihxgxf.tv.D.c"), "Boom");
}

/// THE GATE'S OTHER HALF. `type_value_derive` derives nothing unless something REQUIRES
/// `TypeValue`, and a requirement can be written at the SORT level as well as on an
/// operation. Every other row here uses the operation-level spelling, so this is the only
/// one that drives `any_requirement_names_spec`'s `SortRequiresInfo` branch — and it is
/// the spelling 065 §6 says step 3's migration needs (a sort parameter read as a value,
/// so "the sort gains `requires TypeValue[T = T]`").
///
/// Asserted on the DERIVED ROWS rather than on a call, because the question is whether
/// the gate opened, not whether dispatch works — the rows appearing at all is the answer,
/// and `a_written_type_answers_itself` already drives the dispatch.
///
/// BACK-OUT: delete the `SortRequiresInfo` scan from `any_requirement_names_spec` and
/// this row fails with zero derived rows, while every other row in the file still passes.
#[test]
fn a_sort_level_requires_opens_the_gate() {
    let src = r#"
namespace wihxgxf.sortreq
  import anthill.prelude.{Int64}
  import anthill.reflect.{TypeValue}
  sort Holder
    sort V = ?
    requires TypeValue[T = V]
    entity holder(v: V)
  end
end
"#;
    assert_eq!(refusals(src), Vec::<String>::new());
    let kb = crate::common::load_kb_with(src);
    let rows: Vec<(String, String)> = crate::common::sort_provisions_all(&kb)
        .into_iter()
        .filter(|(_, spec)| spec == "anthill.reflect.TypeValue")
        .collect();
    assert!(
        rows.iter().any(|(c, _)| c == "wihxgxf.sortreq.Holder"),
        "a SORT-level `requires TypeValue` must open the gate and derive `Holder`'s row;          got {rows:?}"
    );
}

/// THE GATE HAS OPENED, AND THE TRANSITION IS THE POINT OF THIS ROW NOW.
///
/// It used to assert the CONTROL — that a program requiring `TypeValue` nowhere derives
/// NOTHING — and that was the cost argument (~113ms/load unconditionally, 0 gated). The
/// gate's own comment predicted the end of it: "step 3 is what makes the clause appear at
/// every rigid value read, and at that point the gate opens BY ITSELF: it keys on the
/// REQUIREMENT existing, so step 3 removes nothing and there is no flag left behind."
///
/// WI-20260921-28TAT IS WHEN THAT ARRIVED, one step earlier than expected and from the
/// prelude rather than from a user's rigid read: `Error.reify requires ErrorTag[T = T1]`
/// with `Error provides ErrorTag[T = T] :- TypeValue[T = T]`. Every program that loads
/// the prelude — which is every program — now carries a standing demand for `TypeValue`,
/// so the derivation runs and the gate is permanently open.
///
/// WHAT THIS ROW STILL GUARANTEES, and it is why it was kept rather than deleted: the
/// gate is not DEAD. It is still the predicate that decides, and the assertion now names
/// the clause that opens it — so a change removing `reify`'s requirement, or one breaking
/// `any_requirement_names_spec`' provision-condition leg (WI-20260921-28TAT: conditions
/// are `SortView`-shaped, and reading them with the bare-application decoder matched
/// NOTHING while looking like it worked), takes this row red instead of silently
/// returning the workspace to deriving nothing.
///
/// BACKED OUT: drop the `requires ErrorTag[T = T1]` line in `prelude/effects.anthill`, or
/// the `condition_names_spec` leg of the gate, and this goes red.
#[test]
fn the_preludes_reify_clause_holds_the_derivation_gate_open() {
    let src = r#"
namespace wihxgxf.nogate
  import anthill.prelude.{Int64}
  sort Holder
    sort V = ?
    entity holder(v: V)
  end
end
"#;
    let kb = crate::common::load_kb_with(src);
    let rows: Vec<(String, String)> = crate::common::sort_provisions_all(&kb)
        .into_iter()
        .filter(|(_, spec)| spec == "anthill.reflect.TypeValue")
        .collect();
    assert!(
        !rows.is_empty(),
        "the prelude's `Error.reify requires ErrorTag[T = T1]` — whose provision is \
         conditioned on `TypeValue` — is a standing demand, so the gate is open and \
         every sort carries a derived row; got none"
    );
    // The demand reaches a sort of the USER's program, not merely the prelude's own:
    // the gate is program-wide, and a row only for `anthill.*` would mean the
    // derivation had been narrowed to the asker rather than opened.
    assert!(
        rows.iter().any(|(c, _)| c == "wihxgxf.nogate.Holder"),
        "the open gate derives for every sort, this program's included; got {rows:?}"
    );
}

/// PASSES EITHER WAY BY DESIGN — a rule body carries no requirement dictionaries, so a
/// `type_value()` GOAL has no evidence to read. Pinned so the refusal keeps SAYING that
/// rather than failing silently into a `not(…)` that would then read as true.
#[test]
fn a_type_value_goal_in_a_rule_body_is_refused() {
    let src = r#"
namespace wihxgxf.rule
  import anthill.prelude.{Int64, Type, Bool}
  import anthill.reflect.{TypeValue}
  sort D
    entity d
    rule bad(?t) :- TypeValue.type_value(?t)
  end
end
"#;
    // Either a load refusal or a resolve-time fault is acceptable; what must NOT happen
    // is a clean load that then answers a type out of nowhere.
    let errs = refusals(src);
    if errs.is_empty() {
        let kb = crate::common::load_kb_with(src);
        assert!(
            kb.try_resolve_symbol("wihxgxf.rule.D.bad").is_some(),
            "the fixture must at least have loaded the rule it pins"
        );
    }
}
