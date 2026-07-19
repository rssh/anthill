//! WI-766 — a general one-component NAMED tuple type `(a: A)` is writable.
//!
//! WI-763 admitted the one-component form only for the DENOTED shape (`(who: "name")`, a
//! one-entry keep spec), leaving the surface asymmetric: `(a: "x")` was a 1-tuple type but
//! `(a: A)` was not a type at all. The denoted form needed no disambiguation because a
//! literal cannot begin a `_type`, so `field_decl` was already dead by the token after `:`;
//! the general form has no such tell.
//!
//! `(a: A)` was exactly the arrow parameter list's single form, and the two readings differ
//! only by whether `->` follows the `)` — beyond LR(1) while they were two productions.
//! Rather than pay a GLR conflict for that lookahead, WI-766 removed the ambiguity: the
//! parameter list and the tuple type are now ONE production (`tuple_type`), so `( … )` reduces
//! unconditionally and a following `->` is an ordinary shift. See the `arrow_type` comment in
//! tree-sitter-anthill/grammar.js for the measurement against the conflict-based alternative.
//!
//! What stays out is the BARE `(A)`: parenthesizing a single type is neither grouping nor a
//! 1-tuple. The name is what carries the field label, so the named form is the only one saying
//! something a bare `A` does not. Unification moves WHERE that is enforced — `(A)` is a valid
//! parameter list, so it parses, and `convert_tuple_type` rejects the TYPE reading with a
//! located message. Same verdict, better diagnostic.

//! NOTE on what the tests below can and cannot say: a tuple LITERAL has no one-element form
//! (`TupleLiteral` in docs/kernel-language.md), so no term spells an ARITY-MATCHING value of
//! type `(a: Int64)` — `(a: 1)` is grouping applied to a named argument, a syntax error here.
//! The type is still inhabited, by width subtyping from a wider tuple. The signatures below
//! are bodyless because that is what the type-level acceptance needs; the width-subtyping
//! route is pinned separately so the gap is recorded as behavior rather than folklore.

use anthill_core::parse;

use crate::common::try_load_kb_with;

fn load_errs(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// THE TICKET'S ACCEPTANCE: `(a: A)` parses as a type and loads.
///
/// Written in return position, the one place a bare `(a: Int64)` cannot be mistaken for
/// anything else the grammar already had.
#[test]
fn wi766_one_component_named_tuple_type_is_writable() {
    let src = r#"
namespace test.wi766write
  import anthill.prelude.{Int64}

  operation one() -> (a: Int64)
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "`(a: Int64)` must parse and load as a one-component named tuple type; got: {:?}",
        load_errs(src),
    );
}

/// The one-component type is a genuine 1-TUPLE, not a synonym for its component.
///
/// A bare `is_ok()` on the test above cannot tell "parsed as a 1-tuple" from "parsed as
/// grouping and collapsed to `Int64`" — both load clean. This distinguishes them: if `(a:
/// Int64)` were grouping, the declared `Int64` would conform and this would pass silently.
/// The message is asserted on, not just the failure, so the test cannot be satisfied by a
/// load that broke for some unrelated reason.
#[test]
fn wi766_one_component_tuple_is_not_its_component_type() {
    let src = r#"
namespace test.wi766distinct
  import anthill.prelude.{Int64}

  operation one() -> (a: Int64)
  operation collapsed() -> Int64 = one()
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("(a: Int64)")),
        "`(a: Int64)` must be a 1-tuple distinct from `Int64`, and the mismatch must NAME it \
         — a clean load, or one failing without naming the tuple, would mean the parens were \
         read as grouping and the component collapsed away; got: {errs:?}",
    );
}

/// The type is INHABITED, despite having no arity-matching literal.
///
/// Pins the gap named in the module note as behavior: a two-component literal conforms to the
/// one-component type by width subtyping, so `(a: A)` is a type you can actually return —
/// it is only the one-element *literal* that the term grammar lacks. Without this, "no
/// one-element literal exists" would read as "the type is uninhabitable", which is false.
#[test]
fn wi766_one_component_tuple_is_inhabited_by_width_subtyping() {
    let src = r#"
namespace test.wi766inhabit
  import anthill.prelude.{Int64}

  operation one() -> (a: Int64) = (a: 1, b: 2)
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "a wider tuple must conform to `(a: Int64)` by width subtyping; got: {:?}",
        load_errs(src),
    );
}

/// REGRESSION GUARD for the reading the unification has to keep separate.
///
/// `(acc: Int64) -> String` must still be an ARROW. Under one shared production the `(acc:
/// Int64)` prefix now reduces to a `tuple_type` either way, so this no longer tests which
/// production won — it tests that a `tuple_type` followed by `->` is still assembled into an
/// arrow and still behaves like one. Calling `cb(1)` is what makes it an assertion about the
/// arrow's SHAPE (one `Int64` parameter) rather than merely about its parse: a `tuple_type`
/// that failed to become an arrow, or became a one-parameter arrow over the TUPLE rather than
/// over `Int64`, fails here.
#[test]
fn wi766_single_named_param_arrow_type_still_parses_as_an_arrow() {
    let src = r#"
namespace test.wi766arrow
  import anthill.prelude.{Int64, String}

  operation apply_cb(cb: (acc: Int64) -> String) -> String = cb(1)
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "`(acc: Int64) -> String` must still read as an arrow, not a one-component tuple; \
         got: {:?}",
        load_errs(src),
    );
}

/// The bare `(A)` stays OUT — but is now rejected by the CONVERTER, not the grammar.
///
/// Unifying the arrow parameter list and the tuple type into one production means `(Int64)`
/// necessarily parses: it is a legitimate parameter list the moment a `->` follows it. Only
/// the TYPE reading is invalid, so `convert_tuple_type` refuses it, and `convert_arrow_type`
/// — which walks the same node for a parameter list — does not. That is the same
/// parse-permissive / convert-strict split WI-763 chose for a literal in an arrow parameter.
///
/// Asserting the MESSAGE and not merely `is_err()` is the point: after the move, `is_err()`
/// no longer distinguishes "rejected as a non-type" from "failed to parse for some unrelated
/// reason", and the located message is the user-visible improvement over a bare syntax error.
#[test]
fn wi766_bare_parenthesized_type_is_still_rejected() {
    let src = r#"
namespace test.wi766bare
  import anthill.prelude.{Int64}

  operation grouped() -> (Int64)
end
"#;
    let errs = parse::parse(src).expect_err("a bare `(Int64)` must not be accepted as a type");
    assert!(
        errs.iter().any(|e| e.message.contains("single parenthesized type is not a type")),
        "the rejection must be the located non-type diagnostic, not an incidental failure; \
         got: {errs:?}",
    );

    // CONTROL 1: the same shape with its component NAMED is what this ticket added, so it
    // must parse. Without this, the test would pass if every parenthesized type were rejected.
    let named = src.replace("(Int64)", "(a: Int64)");
    assert!(
        parse::parse(&named).is_ok(),
        "control: `(a: Int64)` must parse, else the rejection above proves nothing",
    );

    // CONTROL 2: the SAME `(Int64)` as an arrow PARAMETER list must stay legal. This is what
    // scopes the rule to type position — a guard written on the shared production instead of
    // on the type-reading walk would break every `(A) -> B` in the stdlib.
    let as_params = src.replace("-> (Int64)", "-> (Int64) -> Int64");
    assert!(
        parse::parse(&as_params).is_ok(),
        "control: `(Int64) -> Int64` is a parameter list, not a type, and must stay legal",
    );
}

/// Malformed one-component tuple types are all LOUD — the property, not the mechanism.
///
/// Tree-sitter can recover a missing token as a ZERO-WIDTH node that is neither `ERROR` nor
/// `MISSING`, which makes `has_error()` false and prunes the whole tree from the syntax-error
/// collector. Under the two-production grammar this repo previously ran, that is exactly what
/// happened: `(Int64,)` and `(a: Int64,)` parsed CLEAN into a tuple carrying a phantom
/// zero-width component, and `(: Int64)` loaded with an empty-string field label. Sharing one
/// production between the tuple type and the arrow parameter list removed those recoveries.
///
/// Asserted as behavior rather than as a specific message precisely because the mechanism is
/// tree-sitter's recovery heuristic: this must keep holding however that is spelled, and a
/// grammar edit that reintroduces a phantom component has to fail here.
#[test]
fn wi766_malformed_one_component_tuple_types_are_loud() {
    for bad in ["(: Int64)", "(a: )", "(a: Int64,)", "(Int64,)"] {
        let src = format!(
            r#"
namespace test.wi766bad
  import anthill.prelude.{{Int64}}

  operation bad() -> {bad}
end
"#
        );
        assert!(
            parse::parse(&src).is_err(),
            "`{bad}` must be rejected; silently recovering it yields a tuple whose arity or \
             field label does not match the source",
        );
    }

    // CONTROL: a trailing comma on a 2+ tuple IS legal (`optional(',')` on the multi arm), so
    // the rejections above are about the malformed shapes and not about commas in general.
    let ok = r#"
namespace test.wi766goodcomma
  import anthill.prelude.{Int64, String}

  operation good() -> (a: Int64, b: String,)
end
"#;
    assert!(
        parse::parse(ok).is_ok(),
        "control: a trailing comma on a two-component tuple must stay legal",
    );
}
