//! WI-850 — a declared operation type-param DEFAULT (`operation foo[T = Int64](…)`)
//! is REFUSED, not silently dropped.
//!
//! MEASURED on the parent commit: the grammar parsed the `= Type` form, the converter
//! stored it in `TypeParam.default`, and NOBODY read it. `load_operation` mints one
//! `fresh_var` per parameter from the NAME alone, so `[T = Int64]` loaded EXACTLY as
//! `[T]`. Worse than inert: a call that left `T` otherwise unconstrained then raised
//! `UnconstrainedTypeParam`, whose message tells the author to pin `T` with
//! `foo[T = …]` — which is what they had written, on the DECLARATION.
//!
//! WHY REFUSAL AND NOT SEMANTICS. The kernel spec's production is `TypeParam ::= Name`
//! (§5.4) — the default form is not in the language. Proposal 042 §"Declaration form"
//! admitted it grammatically and OQ3 left the semantics unadopted: "the use case is
//! thin … revisit if a concrete driver appears". None has: no `.anthill` file in
//! stdlib, examples or `anthill-todo` writes one, and the only occurrences anywhere
//! were two fixtures asserting that it PARSES (this file's parent commit had them in
//! `parse_test.rs` and the tree-sitter corpus). Honouring it (fill
//! `T` from the default at exactly the point `check_unconstrained_type_params` raises)
//! stays available and is a strictly larger design — it needs the default carried
//! beside the minted var through `OperationInfo`, and a verdict on whether a default
//! may mention an earlier parameter (`[T, U = List[T]]`).
//!
//! WHERE THE REFUSAL LIVES, and why it is not the loader. `convert_operation_type_params`
//! — the CONVERTER. The verdict is decidable from the surface form alone (no scope, no
//! types, no KB), and that one function is the single producer both declaration
//! spellings share: `operation_declaration` and an `operation { … }` block's
//! `operation_entry`. A load-time check would have left the parse-only consumer open:
//! `generate_rust` takes a `&ParsedFile` and never loads a KB (`run_codegen_rust` in
//! anthill-cli parses and emits), so `anthill codegen rust` would have gone on dropping
//! the default exactly as before. Same reasoning as WI-809's duplicate-named-argument
//! rule, which is syntax for the same reason.
//!
//! The GRAMMAR deliberately still accepts the form (`operation_type_param`'s optional
//! `default` field): that is what lets the diagnostic name the operation, the
//! parameter and the type written, instead of an unexpected-`=` syntax error pointing
//! at a token.

use crate::common::{interp_for, parse_errs, parses_clean};
use anthill_core::codegen::generate_rust;
use anthill_core::parse;

fn assert_default_refused(src: &str, needle: &str, what: &str) {
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{what} must refuse the default; expected a diagnostic containing {needle:?}, \
         got: {errs:?}",
    );
}

/// THE ACCEPTANCE CASE, verbatim from the ticket: `operation foo[T = Int64](x: T) -> T`.
/// Asserted on the MESSAGE, not on a count — a count-only assertion would pass on an
/// implementation that rejected this program for an unrelated reason (an unresolved
/// `Int64`, say), which is exactly the failure mode a refusal test must exclude.
#[test]
fn a_declared_type_param_default_is_refused_naming_op_and_param() {
    let errs = parse_errs(
        r#"
namespace test.wi850.decl
  import anthill.prelude.{Int64}
  sort Driver
    operation foo[T = Int64](x: T) -> T = x
  end
end
"#,
    );
    let hit = errs
        .iter()
        .find(|e| e.contains("carries a default"))
        .unwrap_or_else(|| panic!("the defaulted declaration must be refused; got: {errs:?}"));
    assert!(
        hit.contains("`foo`"),
        "the diagnostic must name the OPERATION; got: {hit}"
    );
    assert!(
        hit.contains("`T`"),
        "the diagnostic must name the PARAMETER; got: {hit}"
    );
    assert!(
        hit.contains("`T = Int64`"),
        "the diagnostic must quote what was WRITTEN, so the author can see the dropped \
         default; got: {hit}",
    );
}

/// The SECOND declaration spelling — an `operation { … }` block entry. It reaches the
/// same converter (`convert_operation_block` → `convert_operation`), which is the whole
/// reason the check sits there rather than at each declaration site; this pins that the
/// shared producer really is shared.
#[test]
fn the_operation_block_entry_form_is_refused_too() {
    assert_default_refused(
        r#"
namespace test.wi850.block
  import anthill.prelude.{Int64}
  sort Driver
    operation {
      foo[T = Int64](x: T) -> T = x
    }
  end
end
"#,
        "type parameter `T` carries a default",
        "an `operation { … }` block entry",
    );
}

/// EVERY defaulted parameter in one bracket is reported, and only those: the check is
/// per parameter, not "the bracket has a default somewhere". A first-offender-only
/// implementation would hide `C` behind `B`.
#[test]
fn each_defaulted_param_is_named_and_the_bare_one_is_not() {
    let errs = parse_errs(
        r#"
namespace test.wi850.several
  import anthill.prelude.{Int64, String}
  sort Driver
    operation foo[A, B = Int64, C = String](a: A, b: B, c: C) -> A = a
  end
end
"#,
    );
    let defaults: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("carries a default"))
        .collect();
    assert_eq!(
        defaults.len(),
        2,
        "one diagnostic per defaulted param; got: {errs:?}"
    );
    assert!(
        defaults.iter().any(|e| e.contains("`B`")) && defaults.iter().any(|e| e.contains("`C`")),
        "both defaulted params must be named; got: {defaults:?}",
    );
    assert!(
        !defaults.iter().any(|e| e.contains("parameter `A`")),
        "the BARE param must not be flagged; got: {defaults:?}",
    );
}

/// THE CONTROL the refusal must not break, driven end to end: a bare `[T]` operation
/// still loads AND runs, with `T` inferred from the argument. Without this, a check
/// that refused every bracketed type param would pass every test above.
#[test]
fn a_bare_type_param_still_loads_and_runs() {
    let src = r#"
namespace test.wi850.bare
  import anthill.prelude.{Int64}
  sort Driver
    operation identity[T](x: T) -> T = x
    operation drive() -> Int64 = identity(7)
  end
end
"#;
    parses_clean(src);
    let mut interp = interp_for(src);
    match interp
        .call("test.wi850.bare.Driver.drive", &[])
        .expect("drive")
    {
        anthill_core::eval::Value::Int(7) => {}
        other => panic!("a bare `[T]` op must still evaluate; got {other:?}"),
    }
}

/// The MOVE the diagnostic recommends has to work, or the advice is empty: pin the
/// parameter at the CALL, which is the position the bracket is actually read in
/// (WI-839). A fresh `Interpreter` per call — a trapped call poisons later ones.
#[test]
fn pinning_the_param_at_the_call_is_the_working_alternative() {
    let src = r#"
namespace test.wi850.pinned
  import anthill.prelude.{Int64}
  sort Driver
    operation identity[T](x: T) -> T = x
    operation drive() -> Int64 = identity[T = Int64](7)
  end
end
"#;
    let mut interp = interp_for(src);
    match interp
        .call("test.wi850.pinned.Driver.drive", &[])
        .expect("drive")
    {
        anthill_core::eval::Value::Int(7) => {}
        other => panic!("a call-site pin is the advertised alternative; got {other:?}"),
    }
}

/// THE REASON THE CHECK IS AT THE CONVERTER. `generate_rust` consumes a `&ParsedFile`
/// and never loads a KB, and it reads `op.type_params` for the method generics — so a
/// loader-only refusal would have left this path emitting `fn foo<T>(…)` from a
/// defaulted declaration, dropping the default in silence through a second door. The
/// bare form still generates; the defaulted one cannot reach codegen at all, because
/// its file no longer parses.
#[test]
fn the_parse_only_codegen_path_is_covered_by_the_same_refusal() {
    let bare = parse::parse(
        "namespace test.wi850.gen\n  sort Driver\n    operation identity[T](x: T) -> T\n  end\nend\n",
    )
    .expect("the bare form must parse");
    let code = generate_rust(&bare).expect("the bare form must generate");
    assert!(
        code.contains("identity"),
        "control: the bare form still reaches Rust codegen; got:\n{code}",
    );

    assert!(
        parse::parse(
            "namespace test.wi850.gen\n  sort Driver\n    operation identity[T = Int64](x: T) -> T\n  end\nend\n",
        )
        .is_err(),
        "the defaulted form must fail at PARSE, so the parse-only codegen consumer \
         never sees it",
    );
}
