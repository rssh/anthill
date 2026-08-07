//! WI-886 — a `language cpp` `operation_map` entry is a real implementation of an
//! operation, and it is NOT one this interpreter can run.
//!
//! WI-876 built ONE index over the `operation_map` facts and asked it two questions:
//! the LOAD CHECK's ("does an implementation exist anywhere?", `op_is_executable`) and
//! EVAL's ("can I call it?", `op_is_interpretable`, which decides whether a carrier's
//! own member SHADOWS the spec's default body). The two agreed while every binding
//! block in the tree said `language rust`. WI-886 adds `provides Float language cpp` /
//! `provides Int64 language cpp` blocks for the C++ backend, and there the merged index
//! answers "yes, the interpreter has this" for an operation whose implementation is
//! C++ source — `register_operation_mappings` registers `lang == "rust"` and skips the
//! rest, so nothing is in eval's builtin map for it.
//!
//! `set_host_op_mappings`' own doc already stated the invariant this would break:
//! "this predicate promises the INTERPRETER has an implementation, and the
//! interpreter's builtin map is a RAW `Symbol` lookup. Answering `true` for a spelling
//! that map does not hold would select a carrier override the evaluator then cannot
//! find, skipping a spec default that would have worked." The language is the second
//! axis of the same argument, and this file drives it.
//!
//! Reference: `kb/mod.rs` (`is_host_mapped_op` / `is_interpreter_mapped_op`),
//! `kb/typing.rs` (`op_is_executable` / `op_is_interpretable`),
//! `eval/builtins.rs` (`register_operation_mappings`).

use anthill_core::eval::Value;

/// A carrier that provides `Ord` through a hand-written `compare`, and whose own
/// `max` is realized ONLY in C++. The spec's default `max` (derived from `gte`, and
/// therefore from `compare`) is the one that must run here.
///
/// `language cpp` is not decoration: with the merged index,
/// `op_is_interpretable(Box.max)` answers true off the cpp mapping,
/// `carrier_override_op` selects `Box.max` as the carrier's own implementation, and
/// eval looks it up in a builtin map that has nothing.
///
/// WHY IT LOADS CLEAN is worth stating exactly, because the obvious answer is wrong:
/// it is NOT that `op_is_executable`'s language-agnostic leg counts the cpp mapping as
/// backing. `check_provider_operations` (`kb/typing.rs`) skips a HOST-realized carrier
/// WHOLESALE, and it builds that set from `Implementation` facts with NO language
/// filter — so the `provides Box language cpp` block alone exempts `Box`'s provisions
/// from the backing check, for the rust build too. That is the coarse exemption WI-880
/// is to retire; until then, attaching a cpp binding block to a carrier silently
/// disables its rust-side `UnbackedProviderOperation` check, and this program is the
/// first thing in the tree shaped to notice.
const CPP_ONLY_MEMBER: &str = r#"
namespace wi886.cpponly
  import anthill.prelude.{Int64, Bool, Ord, PartialOrd, PartialEq, Eq}

  sort Box
    import anthill.prelude.{Int64, Bool, Ord, PartialOrd, PartialEq, Eq}
    entity box(v: Int64)

    provides PartialEq[Box]
    provides Eq[Box]
    provides PartialOrd[Box]
    provides Ord[Box]

    operation eq(a: Box, b: Box) -> Bool =
      match a
        case box(av) ->
          match b
            case box(bv) -> PartialEq.eq(av, bv)

    operation compare(a: Box, b: Box) -> Int64 =
      match a
        case box(av) ->
          match b
            case box(bv) -> Ord.compare(av, bv)

    -- Declared and body-less: its implementation is the C++ one named below.
    operation max(a: Box, b: Box) -> Box
  end

  provides Box language cpp
    operation_map { max: "box_max($1, $2)" }
  end

  sort Driver
    import anthill.prelude.{Int64, Ord}
    import wi886.cpponly.Box.{box}
    operation maxV(n: Int64) -> Int64 =
      match Ord.max(box(2), box(9))
        case box(v) -> v
  end
end
"#;

/// The two predicates DISAGREE for a cpp-only mapping, which is the whole point: the
/// program has an implementation of `Box.max` and this process does not.
///
/// The RUST half is asserted on the same KB — `Int64.compare` is WI-876's first
/// mapping and is present in every stdlib load — because "filter by language" could
/// just as easily have been written the wrong way round, and every existing carrier
/// would then lose its host implementation at once. Same KB, because a second
/// `load_kb_with` is a second full stdlib parse-and-load for two symbol lookups.
#[test]
fn the_two_predicates_split_by_language() {
    let kb = crate::common::load_kb_with(CPP_ONLY_MEMBER);
    let sym = |qn: &str| kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("{qn} resolves"));

    let max = sym("wi886.cpponly.Box.max");
    assert!(
        kb.is_host_mapped_op(max),
        "a `language cpp` operation_map entry IS an implementation of the operation"
    );
    assert!(
        !kb.is_interpreter_mapped_op(max),
        "...and NOT one the rust interpreter registered — \
         `register_operation_mappings` keeps only `INTERPRETER_LANG`"
    );

    let compare = sym("anthill.prelude.Int64.compare");
    assert!(kb.is_host_mapped_op(compare), "a rust mapping is a host mapping");
    assert!(
        kb.is_interpreter_mapped_op(compare),
        "...and is what the interpreter registers"
    );
}

/// The behavioural consequence, which is what makes the split worth having: eval falls
/// through to `Ord`'s DEFAULT `max` instead of selecting a member it cannot call.
/// Before the split this died `OperationBodyMissing { wi886.cpponly.Box.max }` on a
/// program that loads clean — the exact shape WI-876 removed one axis over.
#[test]
fn eval_runs_the_spec_default_when_the_only_implementation_is_cpp() {
    let mut interp = crate::common::interp_for(CPP_ONLY_MEMBER);
    match interp.call("wi886.cpponly.Driver.maxV", &[Value::Int(0)]) {
        Ok(Value::Int(9)) => {}
        other => panic!(
            "Ord.max must fall back to the spec default body and pick the \
             greater box; got {other:?}"
        ),
    }
}
