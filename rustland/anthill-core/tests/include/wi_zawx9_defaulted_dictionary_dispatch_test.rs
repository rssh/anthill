//! WI-20261025-ZAWX9 — A DICTIONARY CALL OF A DEFAULTED SPEC OPERATION PICKS WHAT ITS CALL BY
//! NAME PICKS.
//!
//! WI-1010 made a provision's binding beat a spec operation's default for the call BY NAME
//! (`carrier_override_suppliers`). A call through a `requires` dictionary is resolved at eval
//! by `resolve_op_target` instead, which took the provider's raw table row whatever it was and
//! reached the binding only for a BODY-LESS operation. MEASURED on 724492e6, one program, two
//! spellings of one call — by name, and through `viaDict … requires Desc[T = A]`:
//!
//! | shape | by name | through the dictionary |
//! |---|---|---|
//! | (1) a binding alone, receiver-less `name()` | 7 | **1**, silently |
//! | (2) the same, and an own member defined by clauses | 7 | **`OperationBodyMissing`** |
//! | (3) shape (2) on an operation that receives the carrier | 7 | **`OperationBodyMissing`** |
//!
//! and an own member beside a binding, which the call by name refuses at load (WI-1012),
//! answered the own member's 5 through the dictionary.
//!
//! The dictionary now reads the suppliers its PROVIDER writes, through the owners the call by
//! name reads (`spec_op_suppliers_of_provider`, the provider dual of
//! `spec_op_suppliers_for_carrier`), by the sort each provision is about, narrowed to what the
//! interpreter runs: the default where none is left, the tie refused where two are (at
//! load where the dictionary is built since WI-20261025-7K84M), and a provider supplying differently at the applications it provides the spec at
//! refused, the dictionary not saying which it is for. The typer's `defaulted_call_target`
//! reads the same resolution, told the application by the instance it resolved, so a binding
//! reached through the subtype relation is pinned at load — its effects with it — and what
//! the provider supplies twice is refused there.
//!
//! BACK-OUTS, MEASURED over this file and `wi1040_require_clause_dictionary_test`, each alone,
//! on an optimized temporary binary, at ZAWX9's delivery. WI-20261025-7K84M gave the body-less
//! branch the same walk, so M1 no longer backs it out; its own back-outs are in
//! `wi_7k84m_one_supplier_answer_test`.
//!
//!  * M1 — `resolve_op_target`'s defaulted branch never taken (the table read for every op);
//!  * M2 — the interpretability test not handed to the provider walk;
//!  * M3 — `provision_supplier`'s witness leg not asking the reader's test of the member;
//!  * M4 — `defaulted_call_target` not reading the provider's suppliers (`fn_sym` always);
//!  * M5 — the typer's application hint dropped;
//!  * M6 — an uncovered binding falling through (`Ok(None)`) instead of refused;
//!  * M7 — `Dictionary.ops` asking every row as itself;
//!  * M8 — a tie answered by its first candidate;
//!  * M9 — the provider's provisions not read (its own member alone);
//!  * M10 — the provider's provisions pooled into one application;
//!  * M11 — `threads_instance` reading a refusal as "do not thread";
//!  * M12 — the witness leg taking the member first and the binding only where there is none;
//!  * M13 — applications keyed by the base sort alone;
//!  * M14 — the default at a per-application provider entered WITH its dictionary.
//!
//! | row | fails under |
//! |---|---|
//! | `a_binding_answers_a_receiverless_call_through_the_dictionary` | M1 M9 |
//! | `an_unrunnable_own_member_gives_way_to_the_binding_through_the_dictionary` | M1 M2 M9 |
//! | `a_receiving_call_reaches_the_binding_past_an_unrunnable_member` | M1 M2 |
//! | `an_own_member_beside_a_binding_is_refused_where_the_dictionary_is_built` | M1 M8 M9 |
//! | `a_same_named_operation_of_another_spec_is_no_supplier` | M1 |
//! | `dictionary_ops_and_resolve_op_agree` | M1 M2 M7 M9 |
//! | `a_witness_binding_reached_through_the_subtype_relation_answers_every_spelling` | M1 M9 |
//! | `a_binding_reached_through_the_subtype_relation_brings_its_effects` | M1 M4 M9 |
//! | `a_tie_at_a_provider_reached_through_the_subtype_relation_is_refused_at_load` | M1 M4 M8 M9 |
//! | `a_binding_the_instance_cannot_enter_is_refused_at_load` | M1 M4 M6 M9 |
//! | `a_witness_supplying_differently_at_two_sorts_is_refused_through_the_dictionary` | M1 M4 M5 M9 M10 M14 |
//! | `a_witness_member_the_interpreter_cannot_run_gives_way_to_its_binding` | M1 M2 M3 M9 |
//! | `a_witness_writing_its_member_and_a_binding_supplies_two` | M1 M4 M8 M9 M12 |
//! | `two_applications_of_one_sort_are_two` | M1 M4 M5 M9 M10 M13 M14 |
//! | `wi1040…::a_two_supplier_carrier_has_no_reading_through_the_dictionary_either` | M1 M8 M9 |
//! | the three controls below | — |
//!
//! M11 fails no row, and no program reaches what it backs out — stated at its site in
//! `build.rs`. M3 is driven by the RECEIVING variant of its row, which reads the member by
//! the witness leg; the receiver-less variant reads it as route 1, under M2.
//!
//! PASS EITHER WAY BY DESIGN: `a_runnable_own_member_answers_on_both_routes`,
//! `a_carrier_nothing_supplies_runs_the_default_on_both_routes` and
//! `a_witness_supplying_alike_at_two_sorts_answers_through_the_dictionary` — route 1, the gap
//! and a witness's one text for every sort, the answers the change must not move.

use anthill_core::eval::{EvalError, Value};

/// `Desc` with a DEFAULT of 1, a `Leaf` that provides it, `supply` written beside them, and
/// one call written twice: `byName` at `Leaf`, and `throughDictionary` via an operation
/// generic in its carrier that reads `Desc` from its `requires`. `receiving` picks the
/// operation's shape — `describe(x: T)` takes the carrier, `name()` takes nothing — because
/// a receiver-less call has no value to direct a dispatch, so only the dictionary answers it.
fn program(ns: &str, receiving: bool, leaf_body: &str, supply: &str, by_name: bool) -> String {
    let (decl, via, by, through) = if receiving {
        (
            "operation describe(x: T) -> Int64 = 1",
            "operation viaDict[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)",
            "operation byName() -> Int64 = Desc.describe(leaf())",
            "operation throughDictionary() -> Int64 = viaDict(leaf())",
        )
    } else {
        (
            "operation name() -> Int64 = 1",
            "operation viaDict[A]() -> Int64 requires Desc[T = A] = Desc.name[T = A]()",
            "operation byName() -> Int64 = Desc.name[T = Leaf]()",
            "operation throughDictionary() -> Int64 = viaDict[A = Leaf]()",
        )
    };
    let by = if by_name { by } else { "" };
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    {decl}
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
{leaf_body}  end
{supply}
  {via}
  {by}
  {through}
end
"#
    )
}

/// The binding the provision writes: `otherName` / `otherDescribe`, answering 7.
fn binding(receiving: bool) -> &'static str {
    if receiving {
        "\n  operation otherDescribe(x: Leaf) -> Int64 = 7\n\n  namespace Leaf\n    \
         provides Desc[T = Leaf, describe = otherDescribe]\n  end\n"
    } else {
        "\n  operation otherName() -> Int64 = 7\n\n  namespace Leaf\n    \
         provides Desc[T = Leaf, name = otherName]\n  end\n"
    }
}

/// An own member of `Leaf` defined by CLAUSES, answering a goal and no call (§5.3): the
/// member the interpreter cannot run.
fn clause_defined_member(receiving: bool) -> &'static str {
    if receiving {
        "    operation describe(x: Leaf) -> Int64\n    rule describe(?x, 3) :- true\n"
    } else {
        "    operation name() -> Int64\n    rule name(3) :- true\n"
    }
}

fn call(interp: &mut anthill_core::eval::Interpreter, op: &str) -> Result<i64, String> {
    match interp.call(op, &[]) {
        Ok(Value::Int(i)) => Ok(i),
        other => Err(format!("{other:?}")),
    }
}

/// Both spellings of the call, answered by one interpreter over `src`.
fn both_routes(ns: &str, src: &str) -> (Result<i64, String>, Result<i64, String>) {
    let mut interp = crate::common::interp_for(src);
    (
        call(&mut interp, &format!("{ns}.byName")),
        call(&mut interp, &format!("{ns}.throughDictionary")),
    )
}

/// SHAPE (1). The binding is the only supplier and the call names no carrier value, so the
/// dictionary is all the call has. It ran the default's 1.
#[test]
fn a_binding_answers_a_receiverless_call_through_the_dictionary() {
    let ns = "test.zawx9.one";
    let src = program(ns, false, "", binding(false), true);
    assert_eq!(both_routes(ns, &src), (Ok(7), Ok(7)));
}

/// SHAPE (2). The own member is no supplier — the interpreter cannot run it — so the binding
/// is the only one, on both routes. The dictionary entered the member and died.
#[test]
fn an_unrunnable_own_member_gives_way_to_the_binding_through_the_dictionary() {
    let ns = "test.zawx9.two";
    let src = program(ns, false, clause_defined_member(false), binding(false), true);
    assert_eq!(both_routes(ns, &src), (Ok(7), Ok(7)));
}

/// SHAPE (3): shape (2) on an operation that RECEIVES the carrier — WI-1010's
/// `an_unrunnable_own_member_is_not_a_supplier` fixture, called through `requires Desc[T = A]`.
/// The call by name answered it through the typer's pin; the dictionary did not.
#[test]
fn a_receiving_call_reaches_the_binding_past_an_unrunnable_member() {
    let ns = "test.zawx9.three";
    let src = program(ns, true, clause_defined_member(true), binding(true), true);
    assert_eq!(both_routes(ns, &src), (Ok(7), Ok(7)));
}

/// CONTROL: a member the interpreter CAN run is the provider's supplier on both routes.
/// Passes either way by design.
#[test]
fn a_runnable_own_member_answers_on_both_routes() {
    for receiving in [false, true] {
        let ns = format!("test.zawx9.own{}", receiving as u8);
        let member = if receiving {
            "    operation describe(x: Leaf) -> Int64 = 5\n"
        } else {
            "    operation name() -> Int64 = 5\n"
        };
        let src = program(&ns, receiving, member, "", true);
        assert_eq!(both_routes(&ns, &src), (Ok(5), Ok(5)), "receiving: {receiving}");
    }
}

/// CONTROL: a carrier no route supplies runs the spec's default on both routes. Passes
/// either way by design.
#[test]
fn a_carrier_nothing_supplies_runs_the_default_on_both_routes() {
    for receiving in [false, true] {
        let ns = format!("test.zawx9.gap{}", receiving as u8);
        let src = program(&ns, receiving, "", "", true);
        assert_eq!(both_routes(&ns, &src), (Ok(1), Ok(1)), "receiving: {receiving}");
    }
}

/// THE TIE. An own member that runs beside the provision's binding: the call by name is
/// refused at load (WI-1012). The program here writes only the call through the dictionary,
/// and that call is refused in the same words, naming both texts — it answered the own
/// member's 5.
///
/// AT LOAD, WHERE THE DICTIONARY IS BUILT (WI-20261025-7K84M; the user, 2026-10-25). This
/// row refused it at the CALL, on the ground that nothing at `viaDict`'s call site knows which
/// operations its body dispatches. But the dictionary is resolved there, and it answers every
/// operation of its spec: the provider is chosen, and no default chooses between two texts of
/// one provider (WI-861).
#[test]
fn an_own_member_beside_a_binding_is_refused_where_the_dictionary_is_built() {
    for receiving in [false, true] {
        let ns = format!("test.zawx9.tie{}", receiving as u8);
        let member = if receiving {
            "    operation describe(x: Leaf) -> Int64 = 5\n"
        } else {
            "    operation name() -> Int64 = 5\n"
        };
        let src = program(&ns, receiving, member, binding(receiving), false);
        let op = if receiving { "describe" } else { "name" };
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&src),
            &[
                &format!("ambiguous dispatch of `{ns}.Desc.{op}` on carrier `{ns}.Leaf`"),
                "the carrier's own member",
                "an instance fact binding",
            ],
            &format!("two implementations at the dictionary's provider, receiving: {receiving}"),
        );
    }
}

/// WI-1042'S SHAPE: a carrier providing two specs whose defaulted operations share a short
/// name. The carrier's table holds ONE row for `name` — the operation of whichever provision
/// was read first — and the dictionary of the other spec entered it. A same-named operation of
/// another sort is no supplier of a defaulted one (`carrier_own_op` is the provider's own
/// member), so each spec's dictionary runs that spec's default, as each call by name does.
#[test]
fn a_same_named_operation_of_another_spec_is_no_supplier() {
    let ns = "test.zawx9.twospecs";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  sort SpecA
    sort T = ?
    operation name() -> Int64 = 1
  end
  sort SpecB
    sort T = ?
    operation name() -> Int64 = 2
  end
  sort Leaf
    entity leaf
    provides SpecA[T = Leaf]
    provides SpecB[T = Leaf]
  end
  operation viaA[A]() -> Int64 requires SpecA[T = A] = SpecA.name[T = A]()
  operation viaB[A]() -> Int64 requires SpecB[T = A] = SpecB.name[T = A]()
  operation byA() -> Int64 = SpecA.name[T = Leaf]()
  operation byB() -> Int64 = SpecB.name[T = Leaf]()
  operation throughA() -> Int64 = viaA[A = Leaf]()
  operation throughB() -> Int64 = viaB[A = Leaf]()
end
"#
    );
    let mut interp = crate::common::interp_for(&src);
    let answers: Vec<Result<i64, String>> = ["byA", "throughA", "byB", "throughB"]
        .iter()
        .map(|entry| call(&mut interp, &format!("{ns}.{entry}")))
        .collect();
    assert_eq!(answers, vec![Ok(1), Ok(1), Ok(2), Ok(2)]);
}

/// THE TWO REFLECT FACES AGREE on shape (2): `Dictionary.resolveOp(d, Desc.name)` and the
/// element of `Dictionary.ops(d)` for `name` both resolve to the binding. `ops` enumerates the
/// provider's table, whose row for `name` is the clause-defined member; asked by that row it
/// handed the member back while `resolveOp` answered the binding.
#[test]
fn dictionary_ops_and_resolve_op_agree() {
    const DICT: &str = "anthill.realization.runtime.Dictionary";
    let ns = "test.zawx9.reflect";
    let src = program(ns, false, clause_defined_member(false), binding(false), true);
    let mut interp = crate::common::interp_for(&src);
    let leaf = interp
        .kb()
        .try_resolve_symbol(&format!("{ns}.Leaf"))
        .expect("Leaf");
    let d = crate::common::dict(&interp, leaf, []).into_value();
    let spec_op = crate::common::symbol_term(&mut interp, &format!("{ns}.Desc.name"));
    let op_of = |interp: &anthill_core::eval::Interpreter, v: &Value| match v {
        Value::OpRef { op, .. } => interp.kb().qualified_name_of(*op).to_string(),
        other => panic!("expected an OpRef, got {other:?}"),
    };
    let resolved = interp
        .call(&format!("{DICT}.resolveOp"), &[d.clone(), spec_op])
        .expect("resolveOp");
    assert_eq!(op_of(&interp, &resolved), format!("{ns}.otherName"));

    let mut list = interp.call(&format!("{DICT}.ops"), &[d]).expect("ops");
    let mut ops: Vec<String> = Vec::new();
    while let Value::Entity { named, .. } = &list {
        let field = |short: &str| {
            named
                .iter()
                .find(|(k, _)| interp.kb().local_name_of(*k).ends_with(short))
                .map(|(_, v)| v.clone())
        };
        let (Some(head), Some(tail)) = (field("head"), field("tail")) else {
            break;
        };
        ops.push(op_of(&interp, &head));
        list = tail;
    }
    assert!(
        ops.contains(&format!("{ns}.otherName")) && !ops.contains(&format!("{ns}.Leaf.name")),
        "`ops` answers what `resolveOp` answers for the operation its row backs: {ops:?}",
    );
}

/// WI-9WVT7's `AscW` program with the witness's `cmp` written as its provision's BINDING.
/// `Dog` provides `TOrd` only through the subtype relation, so the call by name finds no
/// supplier at `Dog` and resolves the instance — `AscW` — and the TYPER asks the dictionary
/// question there (`defaulted_call_target`); `useT` and `twoLevel` ask it at eval.
fn subtype_program(ns: &str, cmp_effects: &str, direct_effects: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Effect}}
  sort Boom end
  namespace Boom
    provides Effect[T = Boom]
  end
  sort POrd
    sort T = ?
    operation lt(a: T, b: T) -> Bool
  end
  sort TOrd
    sort T = ?
    requires POrd[T = T]
    operation cmp(a: T, b: T) -> Int64 = if POrd.lt(a, b) then 10 else 20
  end
  sort Animal
    entity animal(n: Int64)
  end
  sort Dog
    requires Animal
    entity dog(n: Int64)
    provides POrd[T = Dog]
    operation lt(a: Dog, b: Dog) -> Bool = false
  end
  operation ascCmp(a: Animal, b: Animal) -> Int64{cmp_effects} = 30
  sort AscW
    provides TOrd[T = Animal, cmp = ascCmp]
    provides POrd[T = Animal]
    operation lt(a: Animal, b: Animal) -> Bool = true
  end
  operation useT[X](a: X, b: X) -> Int64{cmp_effects} requires TOrd[T = X] = TOrd.cmp(a, b)
  operation generic() -> Int64{cmp_effects} = useT(dog(1), dog(2))
  operation direct() -> Int64{direct_effects} = TOrd.cmp(dog(1), dog(2))
  operation twoLevel[Y](a: Y, b: Y) -> Int64{cmp_effects} requires TOrd[T = Y] = useT(a, b)
  operation viaTwo() -> Int64{cmp_effects} = twoLevel(dog(1), dog(2))
end
"#
    )
}

/// A WITNESS'S BINDING REACHED THROUGH THE SUBTYPE RELATION answers every spelling: 30, where
/// the default's 20 ran.
#[test]
fn a_witness_binding_reached_through_the_subtype_relation_answers_every_spelling() {
    let ns = "test.zawx9.subtype";
    let mut interp = crate::common::interp_for(&subtype_program(ns, "", ""));
    for entry in ["generic", "direct", "viaTwo"] {
        assert_eq!(call(&mut interp, &format!("{ns}.{entry}")), Ok(30), "{entry}");
    }
}

/// WHAT THE TYPER'S HALF BUYS: the binding's EFFECTS reach the call it pins. `ascCmp` raises
/// `Boom` where the default is pure; `direct` declaring none must be refused at load, or it
/// types against the pure default and runs an effectful operation. Declared, the same program
/// loads and answers through the binding — so the refusal is not of the shape.
#[test]
fn a_binding_reached_through_the_subtype_relation_brings_its_effects() {
    let errs = crate::common::load_errors_of(&subtype_program(
        "test.zawx9.effundeclared",
        " effects Boom",
        "",
    ));
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Boom")),
        "the binding's `Boom` must reach `direct`, not the default's empty row: {errs:?}",
    );
    let ns = "test.zawx9.effdeclared";
    let mut interp = crate::common::interp_for(&subtype_program(ns, " effects Boom", " effects Boom"));
    assert_eq!(call(&mut interp, &format!("{ns}.direct")), Ok(30));
}

/// TWO SUPPLIERS AT A PROVIDER REACHED THROUGH THE SUBTYPE RELATION are refused at LOAD, in
/// the by-name words: `Dog` supplies nothing, so the call resolves the instance — `Animal`,
/// which writes its own runnable `cmp` and binds another in its provision — and the typer asks
/// the dictionary's question there (`defaulted_call_target`). The tie is reported at the
/// application the provision is about, `Animal`.
#[test]
fn a_tie_at_a_provider_reached_through_the_subtype_relation_is_refused_at_load() {
    let ns = "test.zawx9.subtie";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64}}
  sort TOrd
    sort T = ?
    operation cmp(a: T, b: T) -> Int64 = 20
  end
  sort Animal
    entity animal(n: Int64)
    provides TOrd[T = Animal]
    operation cmp(a: Animal, b: Animal) -> Int64 = 40
  end
  operation animalCmp(a: Animal, b: Animal) -> Int64 = 30
  namespace Animal
    provides TOrd[T = Animal, cmp = animalCmp]
  end
  sort Dog
    requires Animal
    entity dog(n: Int64)
  end
  operation direct() -> Int64 = TOrd.cmp(dog(1), dog(2))
end
"#
    );
    let errs = crate::common::load_errors_of(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains(&format!("ambiguous dispatch of `{ns}.TOrd.cmp` on carrier `{ns}.Animal`"))
                && e.contains(&format!("the carrier's own member '{ns}.Animal.cmp'"))
                && e.contains(&format!("an instance fact binding `cmp = {ns}.animalCmp`"))
        }),
        "the provider's two suppliers, refused where the call is typed: {errs:?}",
    );
}

/// A BINDING THE INSTANCE'S DICTIONARY CANNOT ENTER is refused at load: `Helper.cmp` reads
/// `Helper`'s own requirement, and a `TOrd` dictionary at `AscW` carries no slot for it. Eval's
/// dispatch through that dictionary cannot fill the frame either (`expand_dispatching_dict`);
/// the call by name fell through and ran the default's 20 in silence.
#[test]
fn a_binding_the_instance_cannot_enter_is_refused_at_load() {
    let ns = "test.zawx9.uncovered";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64}}
  sort TOrd
    sort T = ?
    operation cmp(a: T, b: T) -> Int64 = 20
  end
  sort Tag
    sort T = ?
    operation tag() -> Int64
  end
  sort Seven
    entity seven
    provides Tag[T = Seven]
    operation tag() -> Int64 = 7
  end
  sort Animal
    entity animal(n: Int64)
  end
  sort Dog
    requires Animal
    entity dog(n: Int64)
  end
  sort Helper
    requires Tag[T = Seven]
    operation cmp(a: Animal, b: Animal) -> Int64 = 30
  end
  sort AscW
    provides TOrd[T = Animal, cmp = Helper.cmp]
  end
  operation direct() -> Int64 = TOrd.cmp(dog(1), dog(2))
end
"#
    );
    let errs = crate::common::load_errors_of(&src);
    assert!(
        errs.iter().any(|e| e.contains(&format!("`{ns}.Helper.cmp`, which `{ns}.AscW` supplies for it"))
            && e.contains(&format!("the requirements of `{ns}.Helper`"))),
        "the binding no dictionary of the instance can enter: {errs:?}",
    );
}

/// A WITNESS PROVIDING ONE SPEC AT TWO SORTS, binding the operation at one of them only. The
/// dictionary names the witness and not the sort, so no dispatch through it has an answer,
/// and each is refused at the call. Each call by name knows its sort: at `A` it enters the
/// binding, 7, and at `B` the default body, 1 — WITHOUT the witness's dictionary, through
/// which eval would dispatch it again with no sort to read (`defaulted_call_target`). Before
/// the provider's provisions were read by the sort they are about, the dictionary at `A` ran
/// the binding written for `B` (found by /code-review); before this ticket every one of these
/// ran the default, `A`'s binding meaning nothing.
#[test]
fn a_witness_supplying_differently_at_two_sorts_is_refused_through_the_dictionary() {
    let program = |ns: &str, b_binding: &str, by_name: &str| {
        let by = match by_name {
            "A" => "  operation byName() -> Int64 = Desc.name[T = A]()\n",
            "B" => "  operation byName() -> Int64 = Desc.name[T = B]()\n",
            _ => "",
        };
        format!(
            r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation name() -> Int64 = 1
  end
  sort A
    entity a
  end
  sort B
    entity b
  end
  operation aName() -> Int64 = 7
  operation bName() -> Int64 = 9
  sort W
    provides Desc[T = A, name = aName]
    provides Desc[T = B{b_binding}]
  end
  operation viaDict[X]() -> Int64 requires Desc[T = X] = Desc.name[T = X]()
  operation throughA() -> Int64 = viaDict[X = A]()
  operation throughB() -> Int64 = viaDict[X = B]()
{by}end
"#
        )
    };
    let ns = "test.zawx9.perapp";
    let mut interp = crate::common::interp_for(&program(ns, "", "A"));
    assert_eq!(call(&mut interp, &format!("{ns}.byName")), Ok(7));
    let mut interp = crate::common::interp_for(&program(ns, "", "B"));
    assert_eq!(call(&mut interp, &format!("{ns}.byName")), Ok(1));
    // Both sorts binding it, each its own way, is the LOADER's refusal: a spec no operation
    // of which receives on its parameter files both provisions under the witness
    // (`AmbiguousInstanceFact`), so that shape never reaches a dispatch.
    let both = crate::common::load_errors_of(&program(ns, ", name = bName", ""));
    assert!(
        both.iter().any(|e| e.contains("ambiguous instance: 2 distinct instance facts")),
        "{both:?}",
    );
    for (entry, src) in [
        ("throughA", program(ns, "", "")),
        ("throughB", program(ns, "", "")),
    ] {
        let err = crate::common::interp_for(&src)
            .call(&format!("{ns}.{entry}"), &[])
            .expect_err("the dictionary does not say which sort it is for");
        assert!(
            matches!(err, EvalError::UndeterminedDictionaryDispatch { .. }),
            "{entry}: expected UndeterminedDictionaryDispatch, got {err:?}",
        );
        let msg = err.to_string();
        assert!(
            msg.contains(&format!("`{ns}.W` provides `{ns}.Desc` at 2 sorts")),
            "{entry}: {msg}",
        );
    }
}

/// CONTROL: a witness that supplies ALIKE at the two sorts — its own member — answers through
/// the dictionary at both. Passes either way by design.
#[test]
fn a_witness_supplying_alike_at_two_sorts_answers_through_the_dictionary() {
    let ns = "test.zawx9.alike";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation name() -> Int64 = 1
  end
  sort A
    entity a
  end
  sort B
    entity b
  end
  sort W
    provides Desc[T = A]
    provides Desc[T = B]
    operation name() -> Int64 = 5
  end
  operation viaDict[X]() -> Int64 requires Desc[T = X] = Desc.name[T = X]()
  operation throughA() -> Int64 = viaDict[X = A]()
  operation throughB() -> Int64 = viaDict[X = B]()
end
"#
    );
    let mut interp = crate::common::interp_for(&src);
    assert_eq!(call(&mut interp, &format!("{ns}.throughA")), Ok(5));
    assert_eq!(call(&mut interp, &format!("{ns}.throughB")), Ok(5));
}

/// SHAPE (2) IN ITS WITNESS FORM. A witness's own member is read before its provision's
/// binding, and a member defined by clauses hid the binding on BOTH routes: the call by name
/// and the dictionary alike ran the default's 1, the binding's 7 meaning nothing (found by
/// /code-review). The member is no supplier, so the binding is.
///
/// BOTH SHAPES OF THE OPERATION, because they reach the member by two legs. An operation that
/// receives the carrier (`describe(x: T)`) makes `W` a witness for `Leaf`
/// (`witness_dispatch_carrier`), and `provision_supplier`'s witness leg reads the member
/// first — the leg the reader's test must be asked in. A receiver-less one (`name()`) files
/// the provision under `W` itself, and the member is route 1 of `W`'s own suppliers.
#[test]
fn a_witness_member_the_interpreter_cannot_run_gives_way_to_its_binding() {
    for receiving in [false, true] {
        let ns = format!("test.zawx9.witnesstwo{}", receiving as u8);
        let (decl, member, other, binding, via, by, through) = if receiving {
            (
                "operation describe(x: T) -> Int64 = 1",
                "operation describe(x: Leaf) -> Int64\n    rule describe(?x, 3) :- true",
                "operation otherDescribe(x: Leaf) -> Int64 = 7",
                "describe = otherDescribe",
                "operation viaDict[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)",
                "operation byName() -> Int64 = Desc.describe(leaf())",
                "operation throughDictionary() -> Int64 = viaDict(leaf())",
            )
        } else {
            (
                "operation name() -> Int64 = 1",
                "operation name() -> Int64\n    rule name(3) :- true",
                "operation otherName() -> Int64 = 7",
                "name = otherName",
                "operation viaDict[A]() -> Int64 requires Desc[T = A] = Desc.name[T = A]()",
                "operation byName() -> Int64 = Desc.name[T = Leaf]()",
                "operation throughDictionary() -> Int64 = viaDict[A = Leaf]()",
            )
        };
        let src = format!(
            r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    {decl}
  end
  sort Leaf
    entity leaf
  end
  {other}
  sort W
    import anthill.prelude.Int64
    provides Desc[T = Leaf, {binding}]
    {member}
  end
  {via}
  {by}
  {through}
end
"#
        );
        assert_eq!(both_routes(&ns, &src), (Ok(7), Ok(7)), "receiving: {receiving}");
    }
}

/// ONE SORT, TWO APPLICATIONS: a witness providing `Desc` at `Box[E = Int64]` and at
/// `Box[E = String]`, binding the operation at the second only. Grouped by the base sort the
/// two were one, and the binding written for `Box[E = String]` answered at `Box[E = Int64]`,
/// by name and through the dictionary alike (found by the second /code-review). By name each
/// answers its own; through the dictionary, which names neither, it is refused.
#[test]
fn two_applications_of_one_sort_are_two() {
    let program = |ns: &str, tail: &str| {
        format!(
            r#"namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Desc
    sort T = ?
    operation name() -> Int64 = 1
  end
  sort Box
    sort E = ?
    entity box(e: E)
  end
  operation sName() -> Int64 = 9
  sort W
    provides Desc[T = Box[E = Int64]]
    provides Desc[T = Box[E = String], name = sName]
  end
{tail}end
"#
        )
    };
    let ns = "test.zawx9.onesort";
    let mut interp = crate::common::interp_for(&program(
        ns,
        "  operation atInt() -> Int64 = Desc.name[T = Box[E = Int64]]()\n  \
         operation atString() -> Int64 = Desc.name[T = Box[E = String]]()\n",
    ));
    assert_eq!(call(&mut interp, &format!("{ns}.atInt")), Ok(1), "Box[E = Int64]: the default");
    assert_eq!(call(&mut interp, &format!("{ns}.atString")), Ok(9), "Box[E = String]: its binding");
    let err = crate::common::interp_for(&program(
        ns,
        "  operation viaDict[X]() -> Int64 requires Desc[T = X] = Desc.name[T = X]()\n  \
         operation throughInt() -> Int64 = viaDict[X = Box[E = Int64]]()\n",
    ))
    .call(&format!("{ns}.throughInt"), &[])
    .expect_err("the dictionary names neither application");
    assert!(
        matches!(err, EvalError::UndeterminedDictionaryDispatch { .. }),
        "expected UndeterminedDictionaryDispatch, got {err:?}",
    );
}

/// A WITNESS WRITING BOTH ITS OWN MEMBER AND A BINDING supplies two, refused as the call by
/// name refuses a carrier's two — in BOTH shapes of the operation. The witness leg took the
/// member first and the binding only where there was none, so an operation that receives the
/// carrier answered the member's 5, the binding's 7 meaning nothing, while the receiver-less
/// shape of the same program, whose provision reads as the witness's own, was refused (found
/// by the second /code-review).
#[test]
fn a_witness_writing_its_member_and_a_binding_supplies_two() {
    for receiving in [false, true] {
        let ns = format!("test.zawx9.witnessboth{}", receiving as u8);
        let (decl, member, other, binding, by, short, bound) = if receiving {
            (
                "operation describe(x: T) -> Int64 = 1",
                "operation describe(x: Leaf) -> Int64 = 5",
                "operation otherDescribe(x: Leaf) -> Int64 = 7",
                "describe = otherDescribe",
                "operation byName() -> Int64 = Desc.describe(leaf())",
                "describe",
                "otherDescribe",
            )
        } else {
            (
                "operation name() -> Int64 = 1",
                "operation name() -> Int64 = 5",
                "operation otherName() -> Int64 = 7",
                "name = otherName",
                "operation byName() -> Int64 = Desc.name[T = Leaf]()",
                "name",
                "otherName",
            )
        };
        let src = format!(
            r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    {decl}
  end
  sort Leaf
    entity leaf
  end
  {other}
  sort W
    import anthill.prelude.Int64
    provides Desc[T = Leaf, {binding}]
    {member}
  end
  {by}
end
"#
        );
        let errs = crate::common::load_errors_of(&src);
        assert!(
            errs.iter().any(|e| e.contains(&format!("ambiguous dispatch of `{ns}.Desc.{short}`"))
                && e.contains(&format!("'{ns}.W.{short}'"))
                && e.contains(&format!("{ns}.{bound}"))),
            "receiving: {receiving} — the witness's member and its binding, both named: {errs:?}",
        );
    }
}
