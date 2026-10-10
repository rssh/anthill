//! WHAT A CALL SITE'S BRACKET AND RECEIVER BIND IS READ BEFORE ITS ARGUMENTS ARE TYPED —
//! found while probing WI-20261009-B6QYA, and fixed with it.
//!
//! THE RULE. An argument is typed from a hint: its parameter's declared type, read as the
//! call reads it. The call binds its own bracket and its receiver before it reads any
//! argument, so the hint does too. Over `keep(f: V)` in `sort Hold[V]`,
//! `Hold.keep[V = (x: Int64) -> Int64](inc)` and `Hold[V = (x: Int64) -> Int64].keep(inc)`
//! say that `f` is an arrow, and the bare operation name `inc` is lifted against it; a
//! constructor's field is hinted the same way, at the instance its own bracket and
//! receiver name.
//!
//! BEFORE. The hint was the declared `V`, which is no arrow, and the name was refused,
//! "expected a slot declaring the arrow to lift this operation against" — in both
//! spellings, on an operation and on a constructor. A field typed by a parameter the
//! receiver pinned to a variant classified its argument at the parent sort and was refused
//! at the field: `Box[V = Colour.red].mk(red(v: 1))`, "expected red, got Colour".
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   an operation call's hints not reading its site (`call_site_bindings_for_hint`
//!   answering `None`) — FAIL:
//!     a_bracket_that_pins_an_arrow_lifts_an_operation_name (its operation rows)
//!   a construction's hints not reading its site (`constructor_instance_for_hint`
//!   answering the expectation alone) — FAIL:
//!     a_bracket_that_pins_an_arrow_lifts_an_operation_name (its let-bound constructor
//!     rows; a construction passed straight to `run` is hinted by that parameter)
//!     a_field_is_hinted_at_the_instance_the_construction_names
//!
//!   PASS UNDER EVERY BACK-OUT, by design — the fence:
//!     a_name_nothing_pins_to_an_arrow_is_still_refused

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The declarations the rows are about, indented for a namespace body.
const DECLS: &str = r#"
  sort Hold[V]
    entity holdf(f: V)
    operation keep(f: V) -> Self = holdf(f)
    operation both[W](g: W, f: V) -> Self = holdf(f)
  end
  sort Box[V]
    entity mk(v: V)
  end
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  operation inc(x: Int64) -> Int64 = add(x, 1)
  operation shout(s: String) -> String = s
  operation wrap[W](f: W) -> Hold[V = W] = holdf(f)
  operation run(h: Hold[V = (x: Int64) -> Int64], x: Int64) -> Int64 = match h
    case holdf(f) -> f(x)
  operation redOf(b: Box[V = Colour.red]) -> Int64 = b.v.v
"#;

fn source(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Type, Bool}}\n  import anthill.prelude.Numeric.{{add}}\n{DECLS}\n{body}\nend\n"
    )
}

/// The integer `go() -> Int64 = <expr>` answers, as text.
fn run(ns: &str, expr: &str) -> String {
    let mut interp = interp_for(&source(ns, &format!("  operation go() -> Int64 = {expr}")));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n.to_string(),
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The refusals of `go() -> Int64 = <expr>`, rendered.
fn refusal(ns: &str, expr: &str) -> String {
    let errs = try_load_kb_with(&source(ns, &format!("  operation go() -> Int64 = {expr}")))
        .err()
        .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
    format!("{errs:?}")
}

const ARROW: &str = "(x: Int64) -> Int64";

/// A parameter the call's bracket or receiver pins to an arrow lifts a bare operation
/// name: on an operation of the sort, on a free operation, by key and by position, and on
/// a constructor — and the name is held to that arrow.
#[test]
fn a_bracket_that_pins_an_arrow_lifts_an_operation_name() {
    for (ns, held) in [
        ("bhopkey", format!("Hold.keep[V = {ARROW}](inc)")),
        ("bhoprecv", format!("Hold[V = {ARROW}].keep(inc)")),
        ("bhopboth", format!("Hold[V = {ARROW}].both[W = (s: String) -> String](shout, inc)")),
        ("bhfreekey", format!("wrap[W = {ARROW}](inc)")),
        ("bhfreepos", format!("wrap[{ARROW}](inc)")),
        ("bhctorkey", format!("Hold.holdf[V = {ARROW}](inc)")),
        ("bhctorpos", format!("Hold.holdf[{ARROW}](inc)")),
        ("bhctorrecv", format!("Hold[V = {ARROW}].holdf(inc)")),
    ] {
        assert_eq!(run(ns, &format!("run({held}, 41)")), "42", "{ns}");
    }
    // With no expectation above it — bound to a name first — the construction's own
    // bracket or receiver is all its field is hinted from.
    for (ns, held) in [
        ("bhletctorkey", format!("Hold.holdf[V = {ARROW}](inc)")),
        ("bhletctorrecv", format!("Hold[V = {ARROW}].holdf(inc)")),
        ("bhletopkey", format!("Hold.keep[V = {ARROW}](inc)")),
    ] {
        let body = format!("  operation go() -> Int64 =\n    let h = {held}\n    run(h, 41)");
        let mut interp = interp_for(&source(ns, &body));
        match interp.call(&format!("test.{ns}.go"), &[]) {
            Ok(Value::Int(42)) => {}
            other => panic!("{ns}: expected 42, got {other:?}"),
        }
    }
    for (ns, held, site) in [
        (
            "bhopbad",
            format!("Hold.keep[V = {ARROW}](shout)"),
            "keep.f (op-arg): expected Int64 -> Int64, got String -> String",
        ),
        (
            "bhctorbad",
            format!("Hold.holdf[V = {ARROW}](shout)"),
            "holdf.f (entity-field): expected Int64 -> Int64, got String -> String",
        ),
    ] {
        let rendered = refusal(ns, &format!("run({held}, 41)"));
        assert!(rendered.contains(site), "{ns}: {rendered}");
    }
}

/// A field typed by a parameter is hinted at the instance the construction's own bracket
/// or receiver names: the argument of a variant-typed field is classified at the variant,
/// and a sibling variant is refused at the field.
#[test]
fn a_field_is_hinted_at_the_instance_the_construction_names() {
    for (ns, built) in [
        ("bhvarkey", "Box.mk[V = Colour.red](red(v: 3))"),
        ("bhvarrecv", "Box[V = Colour.red].mk(red(v: 3))"),
    ] {
        assert_eq!(run(ns, &format!("redOf({built})")), "3", "{ns}");
    }
    let rendered = refusal("bhvarbad", "redOf(Box.mk[V = Colour.red](blue(v: 3)))");
    assert!(
        rendered.contains("mk.v (entity-field): expected red, got blue"),
        "{rendered}"
    );
}

/// The fence: with nothing pinning the parameter to an arrow — no bracket, or a bracket
/// that pins another type — a bare operation name has nothing to lift against.
#[test]
fn a_name_nothing_pins_to_an_arrow_is_still_refused() {
    for (ns, expr) in [
        ("bhnone", "run(Hold.keep(inc), 41)"),
        ("bhother", "run(Hold.keep[V = Int64](inc), 41)"),
    ] {
        let rendered = refusal(ns, expr);
        assert!(
            rendered.contains("expected a slot declaring the arrow to lift this operation against"),
            "{ns}: {rendered}"
        );
    }
}
