//! WI-732 — `Project[T, Keep]`: a projection states its own schema.
//!
//! `Relation.project_run` used to declare the NOMINAL `-> Relation[T = r.T]` — the
//! UNPROJECTED schema — and the typer stamped the real, restricted schema over it at
//! synthesis. That stamp forced an idempotency hatch in `check_apply_iter` keyed on
//! `project_run`'s own identity (`if fn_sym != project_run { return None }`), so that a
//! re-type would re-derive the projection instead of widening back to the full schema. It was
//! the LAST such hatch in the typer, and the `join` → `Concat` discipline forbids them:
//! nothing in the typer may be keyed on a domain operation's identity.
//!
//! The signature now states the projection —
//!
//!   project_run[Keep](r: Relation, spec: Term)
//!     -> Relation[T = Project[T = r.T, Keep = Keep], E = r.E]
//!
//! — and `Project` joins `Concat` (join's merge) / `Without` (fix's drop) / `FieldOf`
//! (WI-759's field selection) in the binary-type-constructor family, reducing at the SAME
//! return-type normalization boundary and keyed on its own SORT. So the forward direction
//! ("this tuple IS a projection, here is its schema") and a later re-type of the stored node
//! are ONE decision procedure over ONE lookup (`projection_columns`) rather than two that can
//! drift — the drift WI-758 recorded for `field_access` is what that discipline prevents.
//!
//! `Keep` is the projection MAP in type position: a named-tuple TYPE whose field name is each
//! RESULT key and whose component is a `denoted` carrying the SOURCE column's name. There are
//! no singleton types, so a name in value position types as plain `String` and loses the name
//! (WI-759); the denoted type-argument channel is the only route that carries it. `Without`
//! needs no denoted for the same job because it reads only its `Drop` record's FIELD NAMES —
//! a projection cannot, because a rename has a source AND a result.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::typing::{TypeExtractor, extract_type, type_check_sorts};

use crate::common::{load_stdlib_kb_with_source, try_load_kb_with};

/// Type-check `source`'s own sorts, then RE-type-check with no sort owning the ops — the
/// free-op sweep re-visits the already-rewritten bodies, the same path an incremental load
/// takes. Then read the SCHEMA (`T`) off the re-typed body node.
///
/// This is what makes the self-correcting claim testable rather than asserted: the body node
/// stored after the first pass is the synthesized `project_run(r, <spec>)` call, and NOTHING
/// stamps its type any more. A re-type that widened to the receiver's full schema reads back
/// `(name: String, age: Int64)`; one that left the constructor unreduced reads back a
/// `Project[..]`.
fn retyped_body_schema(source: &str, op_qn: &str) -> String {
    let (mut kb, result) = load_stdlib_kb_with_source(source);
    let first = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(first.is_empty(), "first type-check must be clean, got: {first:?}");
    let second = type_check_sorts(&mut kb, &[]);
    assert!(second.is_empty(), "re-type-check must be clean, got: {second:?}");
    let op = kb.try_resolve_symbol(op_qn).unwrap_or_else(|| panic!("no symbol for {op_qn}"));
    let body = kb
        .op_body_node(op)
        .cloned()
        .unwrap_or_else(|| panic!("{op_qn} has no stored body node"));
    let ty = body
        .inferred_type()
        .unwrap_or_else(|| panic!("{op_qn}'s body carries no inferred type after the re-type"));
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(&kb, &ty) else {
        panic!("{op_qn}'s re-typed body type is not a parameterized `Relation[..]`");
    };
    let schema = bindings
        .iter()
        .find(|(n, _)| short_of(kb.qualified_name_of(*n)) == "T")
        .map(|(_, v)| v.clone())
        .unwrap_or_else(|| panic!("{op_qn}'s re-typed body type has no `T` binding"));
    render_schema(&kb, &schema)
}

fn short_of(qn: &str) -> String {
    qn.rsplit('.').next().unwrap_or(qn).to_string()
}

/// Render a relation SCHEMA for assertion: a named tuple as `(k: T, …)` in field order, and
/// a 1-collapsed scalar as its own sort name. Deliberately hand-rolled rather than reusing
/// the typer's own display helper — an assertion that shared the renderer with the code under
/// test could agree with it about a wrong answer. An UNREDUCED `Project[..]` renders with its
/// constructor head, which is exactly the failure this must be able to report.
fn render_schema(kb: &KnowledgeBase, ty: &anthill_core::eval::Value) -> String {
    match extract_type(kb, ty) {
        TypeExtractor::NamedTuple(fields) => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(n, t)| format!("{}: {}", short_of(kb.qualified_name_of(*n)), render_schema(kb, t)))
                .collect();
            format!("({})", inner.join(", "))
        }
        TypeExtractor::SortRef(s) => short_of(kb.qualified_name_of(s)),
        TypeExtractor::Parameterized { base, bindings } => {
            let inner: Vec<String> = bindings
                .iter()
                .map(|(n, t)| format!("{} = {}", short_of(kb.qualified_name_of(*n)), render_schema(kb, t)))
                .collect();
            format!("{}[{}]", short_of(kb.qualified_name_of(base)), inner.join(", "))
        }
        other => format!("<{other:?}>"),
    }
}

const REL: &str = r#"
  import anthill.prelude.{String, Int64, Bool, List, Relation}
  import anthill.prelude.Relation.{Project}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
"#;

// ── The self-correcting signature ─────────────────────────────────────────────────

/// THE TICKET'S CENTRAL CLAIM. A stored projection node survives a re-type with its
/// RESTRICTED schema intact — read directly off the re-typed node, not inferred from the
/// absence of errors.
///
/// `person_row` has schema `(name, age)`; the body projects ONE column and renames it, so the
/// three possible answers are all distinguishable: `String` is the projection (a single kept
/// column 1-collapses to its element), `(name: String, age: Int64)` would be the widening the
/// retired stamp existed to prevent, and a `Project[..]` head would be a constructor that
/// never reduced.
#[test]
fn wi732_retype_keeps_the_projected_schema() {
    let src = format!(
        r#"
namespace test.wi732retype
{REL}
  operation justNames() -> List[String] effects Error =
    let rel = person_row
    let cols = rel.(who: name)
    cols.takeN(9)
end
"#
    );
    assert_eq!(
        retyped_body_schema(&src, "test.wi732retype.justNames"),
        "String",
        "a re-typed projection must keep its RESTRICTED schema"
    );
}

/// The multi-column peer: a re-type keeps BOTH the restriction and the RENAME. Two different
/// component types plus renamed keys, so it cannot pass by every projection collapsing to one
/// answer, and a widening back to `r.T` would read back the source keys `name` / `age`.
#[test]
fn wi732_retype_keeps_the_renamed_multi_column_schema() {
    let src = format!(
        r#"
namespace test.wi732retypemulti
{REL}
  operation renamedRows() -> List[(person: String, years: Int64)] effects Error =
    let rel = person_row
    let cols = rel.(person: name, years: age)
    cols.takeN(9)
end
"#
    );
    assert_eq!(
        retyped_body_schema(&src, "test.wi732retypemulti.renamedRows"),
        "(person: String, years: Int64)",
        "a re-typed projection must keep BOTH the kept columns and their result keys"
    );
}

// ── `Project` is a general type constructor, not project-specific machinery ────────

/// `Project` is WRITABLE in a user's own signature, over its own type parameters — the
/// property that makes it a member of the `Concat` / `Without` / `FieldOf` family rather than
/// a private encoding for `project_run`. `join`'s own signature does exactly this with
/// `Concat[A = L, B = R]`.
///
/// It also pins WI-734's ABSTRACT-OPERAND rule, which `Project` inherits by joining the
/// family: neither operand is known here, so the constructor stays SYMBOLIC to reduce once
/// they ground, instead of raising the concrete-malformation diagnostic ("must be a
/// named-tuple type … a 1-collapse / membership schema is not supported") against a shape the
/// user never wrote. Before that rule, both operands went straight to the reducer.
///
/// Honest about its own reach: this passes with `Project` unregistered too (an unregistered
/// constructor also never reduces, so it also never raises). What it genuinely pins is that
/// the SORT is declared and `Project[..]` PARSES and LOADS in a signature over type
/// parameters — the writability half — not that the abstract-operand path is what spared it.
///
/// The ABSTRACT half of writability. WI-763 added the concrete half — a keep spec
/// (`Keep = (who: "name")`) needs a literal per component, which a named-tuple type component
/// did not admit when this test was written, so `Project` was then reducible-when-synthesized
/// and writable-only-abstractly. `wi763_written_keep_spec_test` covers the concrete form and
/// the malformation diagnostics that only a written keep spec can reach.
#[test]
fn wi732_project_is_writable_and_stays_symbolic_while_abstract() {
    let src = format!(
        r#"
namespace test.wi732sym
{REL}
  operation wrap[S, K](r: Relation[T = S])
    -> Relation[T = Project[T = S, Keep = K], E = r.E]
end
"#
    );
    if let Err(e) = try_load_kb_with(&src) {
        panic!(
            "a `Project` over abstract operands must be writable and stay symbolic, not raise \
             the concrete-malformation error, got: {}",
            e.join("\n")
        );
    }
}

/// A projection restricted to one renamed column must NOT conform to the receiver's FULL
/// schema — the widening that `project_run`'s old nominal `-> Relation[T = r.T]` would have
/// produced had the typer not stamped over it.
///
/// Scope of what this pins, measured rather than assumed: it rejects whether or not `Project`
/// is registered in `BINARY_TYPE_CTORS` — unregistered, the return stays an UNREDUCED
/// constructor, which does not conform either. So this is a guard against widening, NOT
/// evidence that the reduction fires. The tests that distinguish those two worlds are the
/// re-type pair above: A/B-verified, both FAIL with `Project` unregistered, because reading
/// the schema back off the re-typed node is what an unreduced constructor cannot satisfy.
#[test]
fn wi732_projection_against_a_wrong_declared_schema_is_rejected() {
    let src = format!(
        r#"
namespace test.wi732wrong
{REL}
  operation wrong() -> List[(name: String, age: Int64)] effects Error =
    let rel = person_row
    let cols = rel.(who: name)
    cols.takeN(9)
end
"#
    );
    assert!(
        try_load_kb_with(&src).is_err(),
        "a projection restricted to one renamed column must not conform to the FULL schema"
    );
}

/// A source column the schema does not have stays a loud LOAD error — the gate and the
/// reduction share [`projection_columns`], so "this is not a projection" and "this projection
/// has no such column" are one answer, and neither degrades into a silent empty projection.
#[test]
fn wi732_projecting_an_unknown_column_is_loud() {
    let src = format!(
        r#"
namespace test.wi732nocol
{REL}
  operation bad() -> List[String] effects Error =
    let rel = person_row
    let cols = rel.(name, nosuchcolumn)
    cols.takeN(9)
end
"#
    );
    let joined = match try_load_kb_with(&src) {
        Ok(_) => panic!("projecting a column that does not exist must not load"),
        Err(e) => e.join("\n"),
    };
    assert!(
        joined.contains("nosuchcolumn"),
        "expected a loud error naming the missing column, got: {joined}"
    );
}
