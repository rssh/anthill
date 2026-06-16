//! WI-280 — bare-identifier value-receiver FIELD access: `p.x` where `p` is a
//! local binding (op param / let / lambda / match binder), without the `?`
//! sigil the WI-279 value-receiver form required. The no-call sibling of the
//! WI-443 method-call re-route.
//!
//! The scope-blind converter lowers `p.x` (a NAME-rooted receiver — the
//! `?x.field` VALUE form already became `dot_apply`) to
//! `field_access(p, Ident(x))`. The loader — which knows the scope — re-routes
//! it to the same zero-arg `Expr::DotApply` the `?x.field` form produces
//! (`load.rs try_identifier_dot_field`), dispatched by the typer's field
//! fallback on the receiver's sort. A head naming a sort/namespace keeps the
//! `field_access` path.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// THE acceptance shape: `b.value` on a bare `Box` PARAM types and EVALs the
/// field — for both a POSITIONAL `box(42)` and a NAMED `box(value: 42)`
/// construction (the runtime entity keeps positional fields positional).
#[test]
fn dot_field_param_positional_and_named() {
    let src = r#"
namespace wi280.field
  import anthill.prelude.{Int64}
  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
  end
  operation read(b: Box) -> Int64 = b.value
  operation t_pos() -> Int64 = read(box(42))
  operation t_named() -> Int64 = read(box(value: 7))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "p.x field access must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.field.t_pos"), 42);
    assert_eq!(run_int(&mut interp, "wi280.field.t_named"), 7);
}

/// `p.x` (bare) dispatches identically to `?p.x` (sigil, WI-279) — same
/// synthesized `field_access`, same result.
#[test]
fn dot_field_bare_matches_sigil() {
    let src = r#"
namespace wi280.parity
  import anthill.prelude.{Int64}
  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
  end
  operation read_bare(b: Box) -> Int64 = b.value
  operation read_sigil(b: Box) -> Int64 = ?b.value
  operation t_bare() -> Int64 = read_bare(box(42))
  operation t_sigil() -> Int64 = read_sigil(box(42))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.parity.t_bare"), 42);
    assert_eq!(run_int(&mut interp, "wi280.parity.t_sigil"), 42);
}

/// A LET-bound local receiver (the `lookup_local_name` arm of the binder check,
/// vs the op-param arm).
#[test]
fn dot_field_let_bound_receiver() {
    let src = r#"
namespace wi280.letrecv
  import anthill.prelude.{Int64}
  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
  end
  operation t() -> Int64 =
    let b = box(42)
    b.value
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "let-bound p.x must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.letrecv.t"), 42);
}

/// A MATCH-bound local receiver.
#[test]
fn dot_field_match_bound_receiver() {
    let src = r#"
namespace wi280.matchrecv
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}
  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
  end
  operation t(o: Option[T = Box]) -> Int64 =
    match o
      case some(bx) -> bx.value
      case none() -> 0 - 1
  operation hit() -> Int64 = t(some(box(42)))
  operation miss() -> Int64 = t(none())
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "match-bound p.x must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.matchrecv.hit"), 42);
    assert_eq!(run_int(&mut interp, "wi280.matchrecv.miss"), -1);
}

/// Generic field: `o.value` on `o: Option[T = Int64]` resolves the field type
/// with the receiver's type-arg substituted (T = Int64) and reads the payload —
/// the `resolve_field_type` substitution path, exercised through the bare form.
#[test]
fn dot_field_generic_param_substitutes() {
    let src = r#"
namespace wi280.genfield
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.some
  operation read(o: Option[T = Int64]) -> Int64 = o.value
  operation t() -> Int64 = read(some(value: 42))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "bare generic field access must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.genfield.t"), 42);
}

/// SHADOWING: a param named like an in-scope sort prefers the LOCAL binding in
/// the dot RECEIVER (the value-vs-name discriminator consults locals/params
/// first). A param `Pair: Box` → `Pair.value` reads the Box field, NOT a
/// `anthill.prelude.Pair` companion (mirrors the WI-443 method-call shadow pin).
#[test]
fn dot_field_param_shadows_sort() {
    let src = r#"
namespace wi280.shadow
  import anthill.prelude.{Int64, Pair}
  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
  end
  operation use_it(Pair: Box) -> Int64 = Pair.value
  operation t() -> Int64 = use_it(box(9))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "param-named-like-sort field access must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.shadow.t"), 9);
}

/// Positional field read indexes by RANK among not-named fields, so a
/// two-field entity built with mixed / reordered args still reads each field
/// correctly (the `pos` slot ≠ the absolute declared index when a named arg
/// precedes a positional one).
#[test]
fn dot_field_mixed_arg_order() {
    let src = r#"
namespace wi280.mixed
  import anthill.prelude.{Int64}
  sort Pair2
    import anthill.prelude.{Int64}
    entity pair2(a: Int64, b: Int64)
  end
  operation get_a(p: Pair2) -> Int64 = p.a
  operation get_b(p: Pair2) -> Int64 = p.b
  -- named arg `a` precedes positional `20` (positional fills `b`)
  operation t_a() -> Int64 = get_a(pair2(a: 10, 20))
  operation t_b() -> Int64 = get_b(pair2(a: 10, 20))
  -- positional `1` precedes named `b`
  operation t_a2() -> Int64 = get_a(pair2(1, b: 2))
  operation t_b2() -> Int64 = get_b(pair2(1, b: 2))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "mixed-arg-order field access must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.mixed.t_a"), 10);
    assert_eq!(run_int(&mut interp, "wi280.mixed.t_b"), 20);
    assert_eq!(run_int(&mut interp, "wi280.mixed.t_a2"), 1);
    assert_eq!(run_int(&mut interp, "wi280.mixed.t_b2"), 2);
}

/// A CHAINED receiver `p.x.y` re-routes level by level (each inner
/// `field_access` revisits the loader arm), nesting DotApply field accesses.
#[test]
fn dot_field_chained_receiver() {
    let src = r#"
namespace wi280.chain
  import anthill.prelude.{Int64}
  sort Inner
    import anthill.prelude.{Int64}
    entity inner(value: Int64)
  end
  sort Outer
    import wi280.chain.Inner
    entity outer(in: Inner)
  end
  operation read(o: Outer) -> Int64 = o.in.value
  operation t() -> Int64 = read(outer(inner(42)))
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "chained p.x.y must load; got: {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi280.chain.t"), 42);
}

/// An unknown member on a known value receiver is a clean no-match at the dot
/// span (not a silent flatten to a bogus qualified name).
#[test]
fn dot_field_unknown_member_reports_no_match() {
    let src = r#"
namespace wi280.nofield
  import anthill.prelude.{Int64}
  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
  end
  operation read(b: Box) -> Int64 = b.nope
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "an unknown field on a value receiver must be a loud no-match",
    );
}
