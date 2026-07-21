//! WI-763 — a literal is admissible as a named-tuple TYPE component, so a keep spec is
//! WRITABLE.
//!
//! WI-732 gave `project_run` a self-correcting signature by putting the projection map in
//! TYPE position — `Keep`, a named-tuple type whose field name is each RESULT key and whose
//! component is a `denoted` carrying the SOURCE column's name. The typer SYNTHESIZED that
//! `Keep` and it reduced, but nobody could WRITE one: type-ARGUMENT position admits a literal
//! (`_common_type_expr`, the channel `FieldOf[Name = "age"]` uses) while a named-tuple type
//! COMPONENT did not (`_tuple_type_arg` was `choice($._type, $.field_decl)`). So `Project`
//! was reducible-when-synthesized and writable-only-abstractly, unlike the `Concat` /
//! `Without` / `FieldOf` peers it shares a reduction boundary with.
//!
//! The grammar now has `denoted_field_decl` — `person: "name"` — its own production rather
//! than a widened `field_decl` RHS, because `field_decl` is also what ENTITY constructors
//! declare their fields with, where a component is a type and never a value.
//!
//! What that buys beyond ergonomics is TESTABILITY: `keep_spec_projections`' and
//! `projection_columns`' diagnostics had exactly one producer — the typer itself — which
//! builds a well-formed keep spec by construction and shares `projection_columns` with the
//! forward gate, so a bad keep spec could not be constructed to test them. The malformation
//! tests below are that coverage, and they are the reason this ticket is not cosmetic.

use anthill_core::parse;

use crate::common::{parse_errs, try_load_kb_with};

/// The relation the projections below keep from: schema `(name: String, age: Int64)`.
const REL: &str = r#"
  import anthill.prelude.{String, Int64, Relation, Project}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
"#;

fn load_errs(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

// ── The writability half ───────────────────────────────────────────────────────────

/// THE TICKET'S ACCEPTANCE: a CONCRETE keep spec parses in a signature and REDUCES.
///
/// `Project[T = (name: String, age: Int64), Keep = (person: "name", years: "age")]` must
/// reduce to `(person: String, years: Int64)` — the schema restricted to the kept columns and
/// re-keyed to the result names. The caller's declared type is what makes it an assertion:
/// conformance fails if the constructor reduced to anything else, and fails if it did not
/// reduce at all (an unreduced `Project[..]` head conforms to no named tuple).
///
/// Written with two DIFFERENT component types and BOTH keys renamed, so it cannot pass by a
/// reduction that dropped the rename (`(name: String, age: Int64)` would not conform) or one
/// that widened to the source schema.
#[test]
fn wi763_written_keep_spec_reduces_to_the_projected_schema() {
    let src = format!(
        r#"
namespace test.wi763write
{REL}
  operation kept(r: Relation[T = (name: String, age: Int64)])
    -> Project[T = (name: String, age: Int64), Keep = (person: "name", years: "age")]
  operation use_kept(r: Relation[T = (name: String, age: Int64)]) -> (person: String, years: Int64) =
    kept(r)
end
"#
    );
    assert!(
        load_errs(&src).is_empty(),
        "a written `Keep = (person: \"name\", years: \"age\")` must reduce to \
         `(person: String, years: Int64)`; got: {:?}",
        load_errs(&src),
    );
}

/// NEGATIVE CONTROL for the above — and the test that actually READS the reduced schema
/// rather than inferring it from a clean load.
///
/// The keep spec keeps `name` (a `String`) under the result key `person`, so a caller claiming
/// `Int64` for it is rejected — and the mismatch REPORTS what `Project` reduced to. Asserting
/// on that text is what distinguishes the three worlds a bare `is_err()` cannot: a reduction
/// that dropped the rename would say `got (name: …, age: …)`, one that widened to the source
/// schema would name both columns, and one that never fired would say `got Project[…]`.
#[test]
fn wi763_written_keep_spec_rejects_the_wrong_component_type() {
    let src = format!(
        r#"
namespace test.wi763writeneg
{REL}
  operation kept(r: Relation[T = (name: String, age: Int64)])
    -> Project[T = (name: String, age: Int64), Keep = (person: "name", years: "age")]
  operation wrong(r: Relation[T = (name: String, age: Int64)]) -> (person: Int64, years: Int64) =
    kept(r)
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("got (person: String, years: Int64)")),
        "keeping the `String` column `name` as `person` must not conform to `person: Int64`, \
         and the mismatch must name the REDUCED schema; got: {errs:?}",
    );
}

/// The ONE-component keep spec — `Keep = (who: "name")` — the ticket's verbatim acceptance
/// shape, and the form the grammar admits as its own `tuple_type` alternative. (At the time
/// this was written the general one-component `(a: A)` stayed unwritable, being
/// the arrow parameter list's single form; WI-766 later admitted that too, by merging the
/// parameter list and the tuple type into one production so the ambiguity disappeared.)
///
/// A single kept column 1-COLLAPSES to its element type, exactly as any relation schema does,
/// so this reduces to `String` and not to a one-field tuple. That collapse is why the declared
/// `-> String` is a real assertion here.
#[test]
fn wi763_single_component_keep_spec_reduces_and_collapses() {
    let src = format!(
        r#"
namespace test.wi763one
{REL}
  operation kept_one(r: Relation[T = (name: String, age: Int64)])
    -> Project[T = (name: String, age: Int64), Keep = (who: "name")]
  operation use_one(r: Relation[T = (name: String, age: Int64)]) -> String = kept_one(r)
end
"#
    );
    assert!(
        load_errs(&src).is_empty(),
        "a one-entry keep spec must parse and 1-collapse to the kept column's type; got: {:?}",
        load_errs(&src),
    );
}

// ── The diagnostics the synthesized-only producer could not reach ──────────────────

/// `projection_columns`' missing-column diagnostic, reached from a WRITTEN keep spec for the
/// first time. Until now its only producer was the typer, which shares this very lookup with
/// the forward gate that decides "this IS a projection" — so a keep spec naming no column
/// could not be constructed, and the error path was unreachable and untested.
#[test]
fn wi763_written_keep_spec_naming_no_column_is_loud() {
    let src = format!(
        r#"
namespace test.wi763nocol
{REL}
  operation kept(r: Relation[T = (name: String, age: Int64)])
    -> Project[T = (name: String, age: Int64), Keep = (person: "nosuchcolumn")]
  operation use_kept(r: Relation[T = (name: String, age: Int64)]) -> String = kept(r)
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("nosuchcolumn")),
        "a keep spec selecting a column the schema does not have must be loud and NAME it; \
         got: {errs:?}",
    );
}

/// `keep_spec_projections`' per-component diagnostic: a component that is not a `denoted` is
/// not a source column NAME. `(person: String)` is a perfectly good named-tuple type — it is
/// the SCHEMA shape — but as a keep spec it says nothing about which column to keep, and a
/// projection needs the name because a rename has a source AND a result.
///
/// This one was writable before the grammar change (a non-denoted component is an ordinary
/// `field_decl`); what it pins now is that admitting the denoted component did not turn the
/// non-denoted one into a silently accepted alias for it.
#[test]
fn wi763_non_denoted_keep_component_is_loud() {
    let src = format!(
        r#"
namespace test.wi763nondenoted
{REL}
  operation kept(r: Relation[T = (name: String, age: Int64)])
    -> Project[T = (name: String, age: Int64), Keep = (person: String, years: "age")]
  operation use_kept(r: Relation[T = (name: String, age: Int64)]) -> (person: String, years: Int64) =
    kept(r)
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("keep-spec entry `person`") && e.contains("denoted")),
        "a keep-spec component that is not a denoted source name must be loud and name the \
         offending ENTRY; got: {errs:?}",
    );
}

/// `keep_spec_projections`' outer diagnostic: a `Keep` that is not a named tuple at all. A
/// keep spec IS a map from result key to source name, so a non-tuple cannot be one.
#[test]
fn wi763_non_tuple_keep_is_loud() {
    let src = format!(
        r#"
namespace test.wi763nontuple
{REL}
  operation kept(r: Relation[T = (name: String, age: Int64)])
    -> Project[T = (name: String, age: Int64), Keep = String]
  operation use_kept(r: Relation[T = (name: String, age: Int64)]) -> String = kept(r)
end
"#
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("`Keep` must be a named-tuple type")),
        "a `Keep` that is not a named-tuple type must be loud; got: {errs:?}",
    );
}

/// A duplicate RESULT key — the malformation that only became reachable by making `Keep`
/// writable, and the one the family's own documentation already promised was rejected.
///
/// The dot surface rejects `r.(a: f1, a: f2)` at parse (`validate_projection_labels`), but a
/// WRITTEN `Keep` never passed through that check — so before WI-763 the two keys reached
/// `collapse_schema` and built a schema with two `a` columns, which no field lookup can answer
/// unambiguously. Measured, not assumed: it loaded to `(a: String, a: Int64)` and failed only
/// later, as a confusing conformance mismatch against a duplicate-keyed type.
///
/// WI-805 MOVED WHERE THIS IS CAUGHT, without changing whether it is. A written `Keep` IS a
/// tuple type — `(a: "name", a: "age")`, its components denoted — so it now meets the §4.5
/// distinctness rule at the mint, one stage earlier than `keep_spec_projections`' own check
/// and with the offending component located. This test follows the diagnostic rather than
/// asserting the old one, because the requirement it encodes is "loud, and NAMES the key",
/// which both spellings satisfy.
///
/// KEPT rather than folded into `wi805_duplicate_tuple_label_test`, unlike the wi800/wi803
/// duplicate tests that WI-805 subsumed. This fixture reaches `convert_tuple_type` through
/// `denoted_field_decl` — a DIFFERENT grammar production from every wi805 fixture, all of
/// which are `field_decl`. It is the only test that says the distinctness rule covers a keep
/// spec's surface too, which is precisely the production WI-763 added.
///
/// `keep_spec_projections`' check is deliberately KEPT, and this is the honest statement of
/// its coverage: it is now a backstop for a `Keep` this code DERIVES rather than one the
/// author writes, and no fixture in this corpus reaches it — INSTRUMENTED, not assumed: a
/// `panic!` on that branch was run against the full workspace suite and never fired, because
/// every derived schema arrives from `concat_named_tuple_types` (which refuses colliding names
/// itself) or from `Project` (which runs this very check). Recorded rather than deleted: the
/// two guards answer for different producers, and the parse one cannot see a spec that was
/// never written.
#[test]
fn wi763_duplicate_result_key_in_a_written_keep_spec_is_loud() {
    let src = format!(
        r#"
namespace test.wi763dup
{REL}
  operation kept(r: Relation[T = (name: String, age: Int64)])
    -> Project[T = (name: String, age: Int64), Keep = (a: "name", a: "age")]
  operation use_kept(r: Relation[T = (name: String, age: Int64)]) -> String = kept(r)
end
"#
    );
    let errs = parse_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate tuple type component label `a`")),
        "a keep spec naming one result key twice must be loud and NAME the key, not build a \
         duplicate-keyed schema; got: {errs:?}",
    );
}

// ── What the new component production must NOT reach ───────────────────────────────

/// The reason `denoted_field_decl` is its own production instead of a widened `field_decl`
/// RHS: `field_decl` is also how an ENTITY constructor declares its fields, where a component
/// is a TYPE and a literal is never one. Widening it would have made `entity person(name:
/// "foo")` parse — a singleton type the language does not have (WI-759) — so this is the
/// naive fix's regression test.
#[test]
fn wi763_entity_field_declared_with_a_literal_stays_a_parse_error() {
    let src = r#"
namespace test.wi763entity
  sort S
    import anthill.prelude.String
    entity person(name: "foo")
  end
end
"#;
    assert!(
        parse::parse(src).is_err(),
        "a literal must not be admissible as an ENTITY field's declared type",
    );
}

/// The other context that shares the component symbol. The arrow parameter list and `tuple_type` have a
/// common prefix and are told apart only by the `->` after the `)`, so they must share ONE
/// component symbol or every named param list becomes a GLR fork. The denoted component
/// therefore rides into arrow params syntactically, and is refused at CONVERSION — with a
/// located diagnostic that says what is wrong, which is strictly better than the syntax error
/// a scoped-by-grammar production would have produced.
#[test]
fn wi763_arrow_parameter_declared_with_a_literal_is_refused() {
    let src = r#"
namespace test.wi763arrow
  import anthill.prelude.Int64
  operation takes_fn(f: (a: "x", b: Int64) -> Int64) -> Int64
end
"#;
    let errs = parse::parse(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.message.contains("parameter `a` is declared with a constant")),
        "a literal in an arrow PARAMETER's type slot must be refused, naming the parameter; \
         got: {errs:?}",
    );
}

// ── Fallout from making the component walk exhaustive ─────────────────────────────

/// Admitting a new component kind meant replacing `convert_tuple_type`'s silent `_ => {}`
/// with a loud arm — which immediately exposed what that silence had been hiding, and what it
/// would newly break.
///
/// HIDING: `arrow_type` was not among the positional component kinds, so a tuple type with a
/// function component dropped it — `((A) -> B, C)` silently became the 1-tuple `(C)`. Pinned
/// here by ARITY: the operation returns a 2-component tuple, and a caller declaring the same
/// two components conforms only if both survived.
///
/// BREAKING: comments are `extras`, so they appear among the named children of ANY node,
/// including between tuple components. A loud arm that did not skip them would reject every
/// commented tuple type — found by probing the parse tree rather than by the suite, which has
/// no such case.
#[test]
fn wi763_tuple_type_components_survive_comments_and_arrows() {
    let src = r#"
namespace test.wi763walk
  import anthill.prelude.{Int64, String}
  operation pair() -> (Int64, -- a comment between components
                       String)
  operation use_pair() -> (Int64, String) = pair()
  operation with_fn() -> ((Int64) -> String, Int64)
  operation use_with_fn() -> ((Int64) -> String, Int64) = with_fn()
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "a comment between tuple components must be skipped, and an arrow component must be \
         KEPT (it was silently dropped); got: {:?}",
        load_errs(src),
    );
}

/// The same comment hazard in the sibling walk: the arrow parameter list. Its fallback converts any
/// unlisted child as a positional parameter type, so a comment inside a parameter list becomes
/// a bogus parameter.
#[test]
fn wi763_arrow_parameters_survive_comments() {
    let src = r#"
namespace test.wi763arrowcomment
  import anthill.prelude.{Int64, String}
  operation takes_fn(f: (Int64, -- a comment between parameters
                          String) -> Int64) -> Int64
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "a comment inside an arrow parameter list must not become a parameter; got: {:?}",
        load_errs(src),
    );
}

/// …and the one-parameter form of the same mistake. WI-763 settled this in the GRAMMAR, with
/// a `prec` that picked `tuple_type` for `( ident : <literal> )` and so left `(a: "x") -> Int64`
/// with no arrow-params reading at all. WI-766 unified the parameter list and the tuple type
/// into one production, which dissolved the overlap that precedence existed to resolve — so it
/// is gone, and this now takes the SAME route as the multi-parameter case above: a located
/// diagnostic from `convert_arrow_type`.
///
/// That is the outcome WI-763 wanted here and could not get; its own note called a located
/// "not a type" better than a bare syntax error, and the one-parameter case was the exception.
/// Asserting the message rather than `is_err()` is what pins the improvement — both mechanisms
/// reject, only one of them explains.
#[test]
fn wi763_one_parameter_arrow_with_a_literal_is_rejected_with_a_located_message() {
    let src = r#"
namespace test.wi763arrowone
  import anthill.prelude.Int64
  operation takes_fn(f: (a: "x") -> Int64) -> Int64
end
"#;
    let errs = parse::parse(src)
        .expect_err("`(a: \"x\") -> Int64` has no valid reading — a param's type is never a literal");
    assert!(
        errs.iter().any(|e| e.message.contains("declared with a constant for its type")),
        "the one-parameter case must get the same explanatory diagnostic as the multi-parameter \
         one, not a bare syntax error; got: {errs:?}",
    );
}
