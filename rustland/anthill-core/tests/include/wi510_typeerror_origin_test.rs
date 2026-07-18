//! WI-510: the `TypeError -> LoadError` remapping used to flatten the structured
//! `TypeErrorContext` (`EntityField{entity,field}` / `OperationArgument{op,param}`
//! / …) and the `Value`-typed expected/actual into plain display strings, dropping
//! the variant identity and the construction site. Two structurally-different
//! checks could then render IDENTICALLY (WI-509 hit this: an `EntityField`
//! field-arg check and an `OperationArgument` arg check both surfacing as
//! `field_access.field`), and a backtrace at the bulk conversion revealed nothing
//! about where the error was built.
//!
//! These tests pin the fix: `LoadError::TypeMismatch` now carries a
//! `TypeMismatchOrigin` that (a) tags the rendered message with the originating
//! context variant — so `EntityField` and `OperationArgument` mismatches are
//! distinguishable — and (b) records the `TypeError::…{ … }` construction site so
//! a mismatch can be traced to its origin without hand-instrumenting each
//! candidate.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, LoadError, NullResolver};
use anthill_core::parse;

fn try_load(extra: &str) -> Vec<load::LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap();
            parse::parse(&src).unwrap()
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .err()
        .unwrap_or_default()
}

/// The first `TypeMismatch` carrying a typer origin.
fn first_origin_mismatch(errs: &[LoadError]) -> &LoadError {
    errs.iter()
        // WI-745: whole-KB typer errors are now file-stamped (`Located`); peel to match the variant.
        .find(|e| matches!(e.peel(), LoadError::TypeMismatch { origin: Some(_), .. }))
        .unwrap_or_else(|| panic!("expected a TypeMismatch with a typer origin, got: {errs:?}"))
}

#[test]
fn op_argument_mismatch_tagged_op_arg_and_traceable() {
    let src = r#"
namespace test.wi510.arg
  import anthill.prelude.{Int64, String}
  operation f(x: Int64) -> Int64 = x
  operation use_f() -> Int64 = f("hello")
end
"#;
    let errs = try_load(src);
    let err = first_origin_mismatch(&errs);
    let LoadError::TypeMismatch { origin: Some(o), .. } = err.peel() else { unreachable!() };

    // (2) the diagnostic distinguishes the originating context variant.
    assert_eq!(
        o.context_kind, "op-arg",
        "an operation-argument mismatch must carry the op-arg context tag: {o:?}"
    );
    // (1) it is traceable to the construction site inside the typer.
    assert!(
        o.site.file().contains("typing.rs"),
        "the origin site must point into the typer source, got {}:{}",
        o.site.file(),
        o.site.line(),
    );
    assert!(o.site.line() > 0, "the origin site must record a real line");

    // The rendered message carries the tag, and still names the op.param so the
    // existing WI-385 / WI-469 assertions on `{op}.{param}` keep matching.
    let text = format!("{err}");
    assert!(
        text.contains("(op-arg)") && text.contains("f.x"),
        "rendered op-arg mismatch should tag the origin and name op.param: {text}"
    );
}

#[test]
fn entity_field_mismatch_tagged_entity_field() {
    let src = r#"
namespace test.wi510.field
  import anthill.prelude.{Int64, String}
  entity Counter(n: Int64)
  operation make() -> Counter = Counter(n: "hello")
end
"#;
    let errs = try_load(src);
    let err = first_origin_mismatch(&errs);
    let LoadError::TypeMismatch { origin: Some(o), .. } = err.peel() else { unreachable!() };

    assert_eq!(
        o.context_kind, "entity-field",
        "an entity-field mismatch must carry the entity-field context tag: {o:?}"
    );
    assert!(
        o.site.file().contains("typing.rs"),
        "the origin site must point into the typer source, got {}:{}",
        o.site.file(),
        o.site.line(),
    );

    let text = format!("{err}");
    assert!(
        text.contains("(entity-field)"),
        "rendered entity-field mismatch should tag the origin: {text}"
    );
}

/// The regression WI-509 hit: an `EntityField` check and an `OperationArgument`
/// check that flatten to the same `entity.field` strings must now render
/// distinguishably via their context tags.
#[test]
fn entity_field_and_op_arg_render_distinguishably() {
    let field_src = r#"
namespace test.wi510.f2
  import anthill.prelude.{Int64, String}
  entity Counter(n: Int64)
  operation make() -> Counter = Counter(n: "hello")
end
"#;
    let arg_src = r#"
namespace test.wi510.a2
  import anthill.prelude.{Int64, String}
  operation f(x: Int64) -> Int64 = x
  operation use_f() -> Int64 = f("hello")
end
"#;
    let field_err = format!("{}", first_origin_mismatch(&try_load(field_src)));
    let arg_err = format!("{}", first_origin_mismatch(&try_load(arg_src)));

    assert!(field_err.contains("(entity-field)"), "field: {field_err}");
    assert!(arg_err.contains("(op-arg)"), "arg: {arg_err}");
    assert_ne!(
        field_err.contains("(entity-field)"),
        arg_err.contains("(entity-field)"),
        "the two mismatches must carry distinct context tags"
    );
}
