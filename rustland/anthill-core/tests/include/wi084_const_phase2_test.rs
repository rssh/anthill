//! WI-084 / proposal 039 — term-level named constants, **Phase 2** (resolution
//! + typing).
//!
//! Phase 2 scope: a BARE reference to a const resolves (it joins the §8.6
//! candidate set like any defined symbol) and TYPES as the const's declared
//! type `T`, read fold-free off the symbol — no evaluation of the body. The
//! single typer hook is the `Const` branch in `check_bare_ref` (typing.rs).
//!
//! Still NOT in scope (later phases): folding the body to a value, the value
//! cache / cycle sentinel / purity gate (Phase 3), eval/codegen, and
//! type-checking a const's own BODY against its declared type (the body stays
//! inert — the typer's free-op-body pass scans `op_bodies`, not `const_bodies`).
//!
//! The proposal's two named Phase-2 checks are covered:
//!   * `set_channel(em, BROADCAST_CHANNEL)` type-checks against `Int64`
//!     (`const_ref_types_against_param` / `const_ref_as_return_value`).
//!   * an ambiguous same-name tie is a load error (`ambiguous_const_name_*`).

use crate::common::try_load_kb_with;

#[test]
fn const_ref_as_return_value_types_as_declared_type() {
    // The simplest reference site: a body that IS the const. It must type as the
    // declared `Int64` and satisfy the `-> Int64` return.
    let src = r#"
namespace test.wi084p2.ret
  import anthill.prelude.{Int64}
  const BROADCAST_CHANNEL: Int64 = -1
  operation go() -> Int64 = BROADCAST_CHANNEL
end
"#;
    let r = try_load_kb_with(src);
    assert!(r.is_ok(), "bare const should type as its declared type:\n{}", errs(r));
}

#[test]
fn const_ref_types_against_param() {
    // The load-bearing driver from proposal 039: a const passed in ARGUMENT
    // position checks against the parameter type (`channel: Int64`).
    let src = r#"
namespace test.wi084p2.arg
  import anthill.prelude.{Int64}
  const BROADCAST_CHANNEL: Int64 = -1
  operation set_channel(channel: Int64) -> Int64 = channel
  operation go() -> Int64 = set_channel(BROADCAST_CHANNEL)
end
"#;
    let r = try_load_kb_with(src);
    assert!(r.is_ok(), "const in arg position should check against the param type:\n{}", errs(r));
}

#[test]
fn const_ref_type_mismatch_is_rejected() {
    // Soundness: an `Int64` const passed where a `String` is expected is a loud
    // type error — the declared type is enforced at the use site, not ignored.
    let src = r#"
namespace test.wi084p2.mismatch
  import anthill.prelude.{Int64, String}
  const BROADCAST_CHANNEL: Int64 = -1
  operation needs_str(s: String) -> String = s
  operation go() -> String = needs_str(BROADCAST_CHANNEL)
end
"#;
    let r = try_load_kb_with(src);
    assert!(
        r.is_err(),
        "an Int64 const passed to a String parameter must be a type error"
    );
}

#[test]
fn const_used_as_a_local_is_shadowed_by_a_let() {
    // §8.6 precedence: a `let`-local named like a const shadows it. Here the
    // local `x` is bound to a String, so the body's `needs_str(x)` resolves to
    // the LOCAL (String), not the `Int64` const — and type-checks.
    let src = r#"
namespace test.wi084p2.shadow
  import anthill.prelude.{Int64, String}
  const x: Int64 = -1
  operation needs_str(s: String) -> String = s
  operation go() -> String =
    let x = "hello"
    needs_str(x)
end
"#;
    let r = try_load_kb_with(src);
    assert!(r.is_ok(), "a let-local must shadow a same-named const:\n{}", errs(r));
}

#[test]
fn ambiguous_const_name_is_a_load_error() {
    // Two namespaces each export a `SHARED` const; a third wildcard-imports both
    // and references bare `SHARED`. Per §8.6 the two distinct symbols make the
    // bare name ambiguous — a load error. (Consts participate in the existing
    // candidate-set arbitration like any defined symbol; the Phase-2 typer hook
    // never sees an ambiguous ref because resolution rejects it first.)
    let src = r#"
namespace test.wi084p2.a
  import anthill.prelude.{Int64}
  const SHARED: Int64 = 1
end

namespace test.wi084p2.b
  import anthill.prelude.{Int64}
  const SHARED: Int64 = 2
end

namespace test.wi084p2.user
  import anthill.prelude.{Int64}
  import test.wi084p2.a.*
  import test.wi084p2.b.*
  operation go() -> Int64 = SHARED
end
"#;
    let joined = errs(try_load_kb_with(src));
    assert!(
        joined.to_lowercase().contains("ambig"),
        "a bare const name resolving to two distinct const symbols must be reported as \
         AMBIGUOUS (not merely unresolved); got:\n{joined}"
    );
}

fn errs(r: Result<anthill_core::kb::KnowledgeBase, Vec<String>>) -> String {
    match r {
        Ok(_) => String::new(),
        Err(es) => es.join("\n"),
    }
}
