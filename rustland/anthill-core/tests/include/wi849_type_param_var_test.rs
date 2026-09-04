//! WI-849 — the operation type-param table holds VARIABLES, and its type says so.
//!
//! `OpInfoRecord` / `OpSignature` / `OperationInfoFull`'s `type_params` used to be
//! `Vec<(Symbol, TermId)>` where every entry was, by construction, the `TermId` of a
//! `Term::Var(Global)`: the loader mints one `fresh_var` per declared parameter
//! (`kb/load.rs` `load_operation`) and `build_list`s them into a ground cons-list. The
//! term spelling bought nothing and cost a destructure at every reader — three of which
//! SILENTLY DROPPED whatever failed to match (`extract_type_params`' `filter_map`,
//! `rigidify_op_type_params`, `op_tp_pinning_params`).
//!
//! This file pins what the type change has to preserve, plus the one thing it newly
//! guarantees.

use crate::common::{load_kb_with, try_load_kb_with};

/// The invariant the new `Vec<(Symbol, Var)>` encodes: every declared op type parameter
/// arrives as a `Var::Global` named after the parameter, in DECLARATION order. Before
/// WI-849 a reader had to `kb.get_term(tid)` and hope; a param that failed that test was
/// dropped with no diagnostic anywhere.
#[test]
fn declared_type_params_decode_as_named_global_vars() {
    let kb = load_kb_with(
        r#"
namespace test.wi849.decode
  import anthill.prelude.{Int64}
  sort Driver
    operation pair[A, B](a: A, b: B) -> Int64 = 0
  end
end
"#,
    );
    let op = kb
        .try_resolve_symbol("test.wi849.decode.Driver.pair")
        .expect("the operation must be defined");
    let rec = anthill_core::kb::op_info::lookup_operation_info(&kb, op)
        .expect("a declared operation has an OperationInfo record");

    let names: Vec<String> = rec
        .type_params
        .iter()
        .map(|(n, _)| kb.local_name_of(*n).to_string())
        .collect();
    assert_eq!(
        names,
        vec!["A".to_string(), "B".to_string()],
        "declaration order, by name"
    );

    // Every entry is a flex variable — the property `rigidify_op_type_params` (WI-392)
    // and `seed_op_type_args` both rely on, and which the TermId spelling only implied.
    for (name, var) in rec.type_params.iter() {
        assert!(
            var.is_global(),
            "type param '{}' must be a flex Global var, got {var:?}",
            kb.local_name_of(*name),
        );
    }

    // The two params are DISTINCT variables — the WI-343 "distinct type params get
    // distinct vars" property, now readable without decoding a term.
    assert_ne!(
        format!("{:?}", rec.type_params[0].1),
        format!("{:?}", rec.type_params[1].1),
        "distinct declared params must not share one variable",
    );
}

/// A monomorphic operation has an EMPTY table — the case `seed_op_type_args` used to
/// short-circuit on (WI-839 deleted that guard) and the case
/// `check_unconstrained_type_params` returns early for.
#[test]
fn a_monomorphic_operation_has_no_type_params() {
    let kb = load_kb_with(
        r#"
namespace test.wi849.mono
  import anthill.prelude.{Int64}
  sort Driver
    operation plain(n: Int64) -> Int64 = n
  end
end
"#,
    );
    let op = kb
        .try_resolve_symbol("test.wi849.mono.Driver.plain")
        .expect("the operation must be defined");
    let rec = anthill_core::kb::op_info::lookup_operation_info(&kb, op)
        .expect("a declared operation has an OperationInfo record");
    assert!(rec.type_params.is_empty(), "got {:?}", rec.type_params);
}

/// A `type_params` entry that is not a variable is REPORTED, not dropped.
///
/// This is the case `extract_type_params`' `filter_map` used to swallow. It is reached
/// from ordinary user source — MEASURED, not assumed, and the measurement is the reason
/// the report is a typer diagnostic rather than the panic WI-849 originally specified:
/// a panic here would be a panic on user input.
///
/// WI-851 BRIEFLY CLOSED THE SOURCE PATH, and it was closing it for the wrong reason.
/// `type_params` was not a declared field of the stdlib `OperationInfo` entity while the
/// loader emitted it anyway, so an undeclared-label refusal fired here and this program
/// was refused TWICE. That was not defence in depth — it was
/// WI-20260823-GMG6N's schema drift, and the same gap made every `OperationInfo` fact
/// unreachable from anthill. `type_params` is declared now, so the label refusal
/// correctly does NOT fire and the WI-849 report is the whole diagnosis, which is what
/// this report exists for: a value in the slot that is not a variable.
///
/// `name: Driver` deliberately targets a symbol the loader emits NO `OperationInfo`
/// fact for. Naming a real operation would put this fact SECOND for that name, and
/// `build_op_signatures` / `lookup_operation_info` both consult only the FIRST fact per
/// name — so the malformed one would never be decoded and the test would pass vacuously.
#[test]
fn a_type_param_entry_that_is_not_a_variable_is_reported() {
    let errs = try_load_kb_with(
        r#"
namespace test.wi849.handwritten
  import anthill.prelude.{Int64}
  import anthill.reflect.{OperationInfo}
  import anthill.prelude.List.{cons, nil}
  sort Driver
    operation victim(n: Int64) -> Int64 = n
  end
  fact OperationInfo(name: Driver, params: nil(), return_type: Int64,
                     effects: nil(), requires: nil(), ensures: nil(),
                     type_params: cons(head: 42, tail: nil()), meta: meta())
end
"#,
    )
    .err()
    .expect("a non-variable type_params entry must be refused, not silently dropped");
    // Asserts the SYMBOL and the RENDERED ENTRY, not just the shared phrase. A
    // substring-only assertion passed while the message called a SORT an "operation"
    // and printed the entry as `Fn { functor: Symbol(16), … TermId(3060) }`
    // (/code-review) — both invisible to a test that only looks for the sentence.
    let report = errs
        .iter()
        .find(|e| e.contains("type parameter that is not a variable"))
        .unwrap_or_else(|| panic!("the WI-849 report must fire; got: {errs:?}"));
    assert!(
        report.contains("`OperationInfo` fact naming 'test.wi849.handwritten.Driver'"),
        "the report must name the symbol the FACT claims, and must not call a sort an \
         operation: {report:?}",
    );
    assert!(
        report.contains("(42)"),
        "the offending entry must render as source text, not internal ids: {report:?}",
    );
    // WI-20260823-GMG6N: `type_params` IS a declared field now, so WI-851's
    // unknown-label refusal correctly no longer fires and this report stands alone.
    //
    // That is the improvement, not a loss. The label was undeclared by MISTAKE — the
    // loader emitted an eighth slot against a seven-field declaration, which made every
    // `OperationInfo` fact unreachable from anthill and made a hand-written one refused
    // for the wrong reason (a spelling complaint) instead of the right one (the entry is
    // not a variable). The assertion this replaces pinned that accident.
    assert!(
        !errs
            .iter()
            .any(|e| e.contains("'OperationInfo' has no field 'type_params'")),
        "`type_params` is declared, so the unknown-label refusal must NOT fire — the \
         WI-849 report is the whole diagnosis; got: {errs:?}",
    );
}

/// A `type_params` field that is not a LIST at all is reported too — the same
/// silent-drop class one layer out. `type_params: 42` used to decode to zero entries and
/// zero reports (`list_to_vec` breaks out of the walk and returns what it has), so the
/// operation simply appeared to declare no type parameters. Found by /code-review; the
/// WI-849 delivery notes had MEASURED this spelling and used it only to argue the arm's
/// reachability, never closing it.
#[test]
fn a_type_params_field_that_is_not_a_list_is_reported() {
    let errs = try_load_kb_with(
        r#"
namespace test.wi849.notalist
  import anthill.prelude.{Int64}
  import anthill.reflect.{OperationInfo}
  import anthill.prelude.List.{nil}
  sort Driver
    operation victim(n: Int64) -> Int64 = n
  end
  fact OperationInfo(name: Driver, params: nil(), return_type: Int64,
                     effects: nil(), requires: nil(), ensures: nil(),
                     type_params: 42, meta: meta())
end
"#,
    )
    .err()
    .expect("a non-list type_params field must be refused");
    assert!(
        errs.iter()
            .any(|e| e.contains("type parameter that is not a variable")),
        "a field that is not a list must report, not decode to zero entries: {errs:?}",
    );
}

/// The CONTROL for the above: a hand-written `OperationInfo` fact still loads. Without
/// this, the test above would pass on an implementation that rejected hand-written
/// `OperationInfo` facts wholesale — a different behaviour that happens to produce an
/// error too.
///
/// It OMITS `type_params`, which since WI-20260823-GMG6N is a declared REQUIRED field —
/// so the loader's named-arg completion fills it with a fresh variable rather than
/// leaving it absent, and this control is also what pins
/// `op_info::type_param_entries`' reading of a variable in that slot as "unspecified"
/// rather than as a malformed entry. Back that reading out and this fails with
/// `type parameter that is not a variable (?type_params)`.
#[test]
fn a_hand_written_operation_info_with_only_declared_fields_still_loads() {
    try_load_kb_with(
        r#"
namespace test.wi849.handwritten_ok
  import anthill.prelude.{Int64}
  import anthill.reflect.{OperationInfo}
  import anthill.prelude.List.{nil}
  sort Driver
    operation victim(n: Int64) -> Int64 = n
  end
  fact OperationInfo(name: Driver, params: nil(), return_type: Int64,
                     effects: nil(), requires: nil(), ensures: nil(), meta: meta())
end
"#,
    )
    .unwrap_or_else(|errs| panic!("only-declared-fields must still load: {errs:?}"));
}
