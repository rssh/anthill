//! WI-385: operation ARGUMENT and constructor FIELD values are type-checked
//! against their declared parameter / field types — the arg/field direction,
//! peer to the RETURN direction WI-379 made authoritative. Before WI-385 the
//! arg/field unify booleans were DISCARDED (they drove type-param inference
//! only), so `f(x: Int64)` called `f("hello")` and `entity Counter(n: Int64)` with
//! `fact Counter(n: "hello")` BOTH loaded clean. These tests pin the validation,
//! and the two boundary CONVERSIONS it accepts rather than flags:
//!   1. value→Term reflection — TOTAL (`as_term[E]`, WI-406), so any value
//!      conforms to a declared reflect `Term`.
//!   2. bare-`T`-vs-`Option[T]` in a FIELD position — an explicit INTERIM
//!      (on-disk facts persist optionals UNWRAPPED, e.g. `depends_on: []`); the
//!      sound `some`-coercion-insertion pass is a follow-on ticket.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
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

fn errors_text(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

// ── The two proven holes are now diagnosed ──────────────────────────────────

#[test]
fn operation_arg_int_param_rejects_string() {
    let src = r#"
namespace test.wi385.argint
  import anthill.prelude.{Int64, String}
  operation f(x: Int64) -> Int64 = x
  operation use_f() -> Int64 = f("hello")
end
"#;
    let errs = try_load(src);
    let text = errors_text(&errs);
    eprintln!("=== operation_arg_int_param_rejects_string ===\n{text}");
    assert!(
        !errs.is_empty(),
        "f(\"hello\") with f(x: Int64) must be rejected (was a silent hole)"
    );
    assert!(
        text.contains("Int64") && text.contains("String"),
        "error should name the Int64/String mismatch: {text}"
    );
}

// Field validation is reached through the op-body constructor path that
// `load_all` type-checks — the same path the anthill-todo blast radius exercised
// (`do_add` / `with_status` build `WorkItem(...)` in op bodies). The field check
// runs BEFORE the constructor's type is built, so a bad field bails the op body.

#[test]
fn entity_field_int_rejects_string() {
    let src = r#"
namespace test.wi385.fieldint
  import anthill.prelude.{Int64, String}
  entity Counter(n: Int64)
  operation make() -> Counter = Counter(n: "hello")
end
"#;
    let errs = try_load(src);
    let text = errors_text(&errs);
    eprintln!("=== entity_field_int_rejects_string ===\n{text}");
    assert!(
        !errs.is_empty(),
        "Counter(n: \"hello\") with entity Counter(n: Int64) must be rejected"
    );
    assert!(
        text.contains("Int64") && text.contains("String"),
        "error should name the Int64/String mismatch: {text}"
    );
}

// ── No false positive on a CORRECT call/constructor ─────────────────────────

#[test]
fn correct_arg_and_field_load_clean() {
    let src = r#"
namespace test.wi385.ok
  import anthill.prelude.{Int64}
  operation f(x: Int64) -> Int64 = x
  operation use_f() -> Int64 = f(42)
  entity Counter(n: Int64)
  operation make() -> Counter = Counter(n: 7)
end
"#;
    let errs = try_load(src);
    eprintln!("=== correct_arg_and_field_load_clean ===\n{}", errors_text(&errs));
    assert!(
        errs.is_empty(),
        "correct Int64 arg/field must load clean: {}",
        errors_text(&errs)
    );
}

// ── Accepted CONVERSION 1: value→Term reflection (total, both positions) ─────

#[test]
fn term_field_accepts_any_value_reflection() {
    let src = r#"
namespace test.wi385.termfield
  import anthill.prelude.{String}
  import anthill.reflect.{Term}
  entity Note(content: Term)
  operation note() -> Note = Note(content: "hi")
end
"#;
    let errs = try_load(src);
    eprintln!(
        "=== term_field_accepts_any_value_reflection ===\n{}",
        errors_text(&errs)
    );
    assert!(
        errs.is_empty(),
        "a String in a reflect Term field is reflection (total), not a mismatch: {}",
        errors_text(&errs)
    );
}

// ── Accepted CONVERSION 2: bare T vs Option[T] in a FIELD (interim) ──────────

#[test]
fn option_field_accepts_bare_value_interim() {
    let src = r#"
namespace test.wi385.optfield
  import anthill.prelude.{Int64, Option}
  entity Box(v: Option[T = Int64])
  operation box() -> Box = Box(v: 5)
end
"#;
    let errs = try_load(src);
    eprintln!(
        "=== option_field_accepts_bare_value_interim ===\n{}",
        errors_text(&errs)
    );
    assert!(
        errs.is_empty(),
        "bare Int64 in an Option[Int64] field is accepted (Option-wrapping interim): {}",
        errors_text(&errs)
    );
}

// ── Provider admissibility: a concrete carrier conforms to a BARE spec it ────
// provides. `types_compatible` confines provider-admissibility to its bare↔bare
// arm, so a parameterized carrier (List[Int64]) against a bare spec (Stream) it
// PROVIDES reached validate_arg_against_param unaccepted — the validation adds
// the explicit provider check. Without it WI-385 false-rejects valid code.

#[test]
fn bare_spec_param_accepts_concrete_provider() {
    let src = r#"
namespace test.wi385.provider
  import anthill.prelude.{List, Int64, Stream}
  import anthill.prelude.Stream.{iterator}
  operation feed(xs: List[T = Int64]) -> Stream[T = Int64, E = {}] = iterator(xs)
end
"#;
    let errs = try_load(src);
    eprintln!(
        "=== bare_spec_param_accepts_concrete_provider ===\n{}",
        errors_text(&errs)
    );
    assert!(
        errs.is_empty(),
        "List[Int64] (provides Stream) passed to a bare Stream param must be accepted: {}",
        errors_text(&errs)
    );
}

#[test]
fn bare_spec_field_accepts_concrete_provider() {
    let src = r#"
namespace test.wi385.providerfield
  import anthill.prelude.{List, Int64, Stream}
  import anthill.prelude.List.{cons, nil}
  entity Holder(s: Stream)
  operation mk() -> Holder = Holder(s: cons(head: 1, tail: nil()))
end
"#;
    let errs = try_load(src);
    eprintln!(
        "=== bare_spec_field_accepts_concrete_provider ===\n{}",
        errors_text(&errs)
    );
    assert!(
        errs.is_empty(),
        "a List[Int64] (provides Stream) in a bare Stream field must be accepted: {}",
        errors_text(&errs)
    );
}

#[test]
fn bare_option_field_accepts_value() {
    // A bare `Option` (no `[T = …]`) has no element to re-check; the interim
    // accepts any value as its implicit `some` payload.
    let src = r#"
namespace test.wi385.bareopt
  import anthill.prelude.{Int64, Option}
  entity Box2(v: Option)
  operation box2() -> Box2 = Box2(v: 5)
end
"#;
    let errs = try_load(src);
    eprintln!("=== bare_option_field_accepts_value ===\n{}", errors_text(&errs));
    assert!(
        errs.is_empty(),
        "bare Option field accepts any value under the interim: {}",
        errors_text(&errs)
    );
}
