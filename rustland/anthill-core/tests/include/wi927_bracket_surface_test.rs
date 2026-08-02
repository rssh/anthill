//! WI-927 — the BRACKETED surface is a type application, whatever the functor is.
//!
//! `Box[T = Int64]` and `Box(value: 1)` lower to `Term::Fn` with the SAME functor
//! symbol; only the written surface tells them apart, which is why parse records
//! it (`mark_type_application`). The loader used to substitute the functor's KIND
//! for that surface, which worked only while a sort and an entity were always
//! different symbols. WI-926 (§6.3) made an eponymous `sort Box { entity Box(…) }`
//! ONE symbol that is both, and the substitute stopped working — a bracket was
//! read as a construction and its type arguments as fields:
//!
//! ```text
//! Box[T = Int64]   ->  unknown field 'T' on entity 'Box' (declared: value)
//! Box[Int64]       ->  `Box` has no type parameter named 'value'   <- a label
//!                      nobody wrote: the positional->named desugar renamed the
//!                      type argument INTO the field before the type-arg gate saw it
//! ```
//!
//! Each test pairs the eponymous sort with a NON-eponymous control of the same
//! shape (`sort Holder { sort T = ?; entity mk(value: T) }`), which was unaffected
//! throughout — so a green run says the two surfaces agree, not that the check
//! stopped running.

use crate::common::try_load_kb_with;

/// Load and return the error strings (empty when the load is clean).
fn errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

fn eponymous(body: &str) -> String {
    format!(
        r#"
namespace test.wi927
  import anthill.prelude.{{Int64, Bool}}
  sort Box
    sort T = ?
    entity Box(value: T)
  end
{body}
end
"#
    )
}

fn control(body: &str) -> String {
    format!(
        r#"
namespace test.wi927ctl
  import anthill.prelude.{{Int64, Bool}}
  sort Holder
    sort T = ?
    entity mk(value: T)
  end
{body}
end
"#
    )
}

#[test]
fn a_named_bracket_on_an_eponymous_sort_is_a_type_application() {
    let ctl = errors(&control("  rule ok(?x) :- eq(?x, Holder[T = Int64])"));
    assert!(ctl.is_empty(), "the non-eponymous control must load clean; got {ctl:?}");

    let errs = errors(&eponymous("  rule ok(?x) :- eq(?x, Box[T = Int64])"));
    assert!(
        errs.is_empty(),
        "a bracketed type application over an eponymous sort must load — its \
         arguments are TYPE arguments, not fields; got {errs:?}"
    );
}

#[test]
fn a_positional_bracket_is_not_desugared_into_a_field() {
    // The nastier half: the positional->named desugar filled the entity's `value`
    // field with the type argument, so the type-arg check downstream complained
    // about a label the author never wrote.
    let ctl = errors(&control("  rule ok(?x) :- eq(?x, Holder[Int64])"));
    assert!(ctl.is_empty(), "the non-eponymous control must load clean; got {ctl:?}");

    let errs = errors(&eponymous("  rule ok(?x) :- eq(?x, Box[Int64])"));
    assert!(
        errs.is_empty(),
        "a POSITIONAL bracket binds the sort's declared type param, not the \
         entity's first field; got {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("'value'")),
        "the diagnostic must never name the FIELD for a bracketed argument: {errs:?}"
    );
}

/// The checking is not what was removed — only the second, wrong reading of it.
#[test]
fn a_stray_type_argument_stays_loud_and_names_a_type_parameter() {
    let errs = errors(&eponymous("  rule bad(?x) :- eq(?x, Box[W = Int64])"));
    assert!(
        errs.iter().any(|e| e.contains("no type parameter named 'W'")),
        "a stray bracket argument must still be refused by the shared \
         type-argument gate; got {errs:?}"
    );
    // The rendered form is `'Box' has no field 'W' (declares: value)` — matched on
    // the phrase the formatter actually emits, so this cannot pass vacuously.
    assert!(
        !errs.iter().any(|e| e.contains("has no field")),
        "and must NOT also be reported as an unknown field — one written node, \
         one reading; got {errs:?}"
    );
}

/// The other surface keeps its own reading, and its own error.
#[test]
fn the_parenthesized_surface_still_constructs_and_still_checks_fields() {
    let errs = errors(&eponymous("  fact Box(value: 1)"));
    assert!(errs.is_empty(), "parens over an eponymous sort construct; got {errs:?}");

    let bad = errors(&eponymous("  fact Box(valu: 1)"));
    assert!(
        bad.iter().any(|e| e.contains("has no field") && e.contains("valu")),
        "a misspelled FIELD through parens must still be refused; got {bad:?}"
    );
}

/// A bracket in TYPE position was never affected (it lowers through
/// `TypeExpr::Parameterized`) — pinned so the two positions stay agreed.
#[test]
fn a_bracket_in_type_position_is_unaffected() {
    let errs = errors(&eponymous(
        "  sort Use\n    entity use(b: Box[T = Int64])\n  end",
    ));
    assert!(errs.is_empty(), "an annotation over an eponymous sort loads; got {errs:?}");
}
