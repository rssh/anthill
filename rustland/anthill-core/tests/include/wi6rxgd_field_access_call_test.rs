//! WI-20260824-6RXGD — `anthill.reflect.field_access` is CALLABLE by hand.
//!
//! kernel-language.md §8.6 tells reflection code to import what it names — "a meta-rule
//! matching an occurrence writes `import anthill.reflect.{occurrence_term}` … before it
//! can use them" — and `field_access`'s own declaration states the calling convention the
//! import is supposed to unlock:
//!
//! ```text
//! operation field_access[R, Name](object: R, field: String) -> FieldOf[T = R, Name = Name]
//! ```
//!
//! The selector name travels TWICE, once per channel, because there are no singleton
//! types: the value argument `field` types as plain `String` and has lost the name by the
//! time the return type is assembled, so `Name` carries it into type position. That is the
//! declaration's own doc, and until this ticket NO spelling of it worked — `[Name = "x"]`
//! and the positional `[P, "x"]` both came back `FieldOf[T = P, Name = ?Name]`, an
//! irreducible residual, so the operation had no usable type from any hand-written call.
//!
//! THE CAUSE WAS A CARRIER, not the signature. A denoted written in a bracket rides as a
//! `Value::Node` (`Loader::type_expr_to_value`, because a denoted may carry poison —
//! `Modify[c]`), and the `TermId` deep σ-walk that resolves a term-backed return type
//! STOPS at a non-`Term` binding (WI-394). `typing::synthesize_field_access` — what `q.x`
//! rewrites to — already builds its `Name` argument GROUND for exactly that reason and
//! says so at the site; the channel a person writes had no route to it.
//! [`typing::ground_literal_denoted`] gives it one, for a CLOSED LITERAL only.
//!
//! THE CONTROL. Backing the change out is making `ground_literal_denoted` return `None`.
//! Then `a_written_name_bracket_binds_and_the_call_evaluates` and
//! `the_positional_bracket_binds_the_same_way` fail — the calls stop type-checking, with
//! `expected Int64, got FieldOf[T = P, Name = ?Name]` — and
//! `a_name_the_receiver_does_not_have_is_refused` fails too, because its refusal changes
//! from "no such member" (the name was READ) to the same `?Name` residual (the name was
//! never read at all). That third row is what separates "the binding is resolved" from
//! "the binding was made to disappear"; the first two alone cannot.
//!
//! `the_dot_form_is_unaffected` passes either way BY DESIGN — it is the representation
//! control, and it is what says the ground/Node split reaches the written bracket and
//! nothing else.
//!
//! THE FIFTH ROW HAS ITS OWN CONTROL, because it measures a SECOND change:
//! `a_written_literal_bracket_renders_its_literal` fails when `type_display_name`'s
//! `Term::Const` arm is removed. It needs BOTH halves — grounding the binding is what puts
//! a `Term::Const` denoted where a diagnostic can reach it, and the arm is what renders
//! it. This ticket introduced the first and therefore owed the second.
//!
//! NOT CLOSED BY THIS TICKET, and pinned below rather than left as prose:
//! `an_annotation_written_by_hand_still_does_not_reduce`. A `FieldOf[…]` a user writes in
//! their OWN return-type annotation is not a reduction site, so it stays unreduced even
//! with both operands concrete. A caller does not need it — declaring the field's concrete
//! type is what these tests do — but a reader who tries it deserves to find the boundary
//! recorded. See the ticket.

use crate::common::{interp_for, scalar_int, try_load_kb_with};

/// A receiver with one `Int64` field, plus the imports §8.6 prescribes.
const PRELUDE: &str = r#"
  import anthill.prelude.{Int64, String}
  import anthill.reflect.{field_access}
  sort P
    entity p(x: Int64)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace probe.{ns}\n{PRELUDE}\n{body}\nend\n")
}

/// Load errors, or the empty vec.
fn errors_of(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// Call `probe.<ns>.go()` and read its `Int64`.
fn go(src: &str, ns: &str) -> i64 {
    let mut interp = interp_for(src);
    let v = interp
        .call(&format!("probe.{ns}.go"), &[])
        .unwrap_or_else(|e| panic!("probe.{ns}.go: {e}"));
    let kb = interp.kb();
    scalar_int(kb, &v).unwrap_or_else(|| panic!("probe.{ns}.go did not answer an Int64: {v:?}"))
}

/// The convention the declaration documents — the name in the bracket AND in the value
/// argument — type-checks, and the call ANSWERS THE FIELD. Loading clean is not the
/// claim: the value 7 is, because a `FieldOf` that reduced to the wrong thing (or to
/// `Term`) would still load.
#[test]
fn a_written_name_bracket_binds_and_the_call_evaluates() {
    let src = program(
        "named",
        "  operation get(q: P) -> Int64 = field_access[Name = \"x\"](q, \"x\")\n\
         \x20 operation go() -> Int64 = get(p(x: 7))",
    );
    assert_eq!(errors_of(&src), Vec::<String>::new());
    assert_eq!(go(&src, "named"), 7);
}

/// The positional bracket binds the same two parameters in declaration order
/// (`[R, Name]`), so `[P, "x"]` is the same call. Included because the two spellings reach
/// `seed_op_type_args` through different arms of `resolve_call_type_arg_targets`, and only
/// the labelled one is written in the declaration's doc.
#[test]
fn the_positional_bracket_binds_the_same_way() {
    let src = program(
        "positional",
        "  operation get(q: P) -> Int64 = field_access[P, \"x\"](q, \"x\")\n\
         \x20 operation go() -> Int64 = get(p(x: 7))",
    );
    assert_eq!(errors_of(&src), Vec::<String>::new());
    assert_eq!(go(&src, "positional"), 7);
}

/// THE ROW THAT SAYS THE NAME IS READ. `P` has no field `zz`, and the refusal quotes that
/// name — so the `"zz"` in the bracket reached the projection. Not the `?Name` residual,
/// which is what an unbound `Name` produces and which would look like a refusal while
/// measuring nothing: back the change out and this row's message becomes
/// `expected Int64, got FieldOf[T = P, Name = ?Name]`, which names no field at all.
#[test]
fn a_name_the_receiver_does_not_have_is_refused() {
    let src = program(
        "missing",
        "  operation get(q: P) -> Int64 = field_access[Name = \"zz\"](q, \"zz\")",
    );
    let errs = errors_of(&src);
    assert!(
        errs.iter().any(|e| e.contains("`P` has no field `zz`")),
        "a projected name the receiver does not declare must be refused by NAME; got {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("?Name")),
        "an unbound `Name` residual is not a refusal of the name — it is the defect this \
         ticket fixed, wearing a refusal's clothes; got {errs:?}"
    );
}

/// The representation control: the dot form goes through `synthesize_field_access`, which
/// grounded its own argument before this ticket and still does. Green with the change
/// backed out, and that is the point — it bounds the change to the written bracket.
#[test]
fn the_dot_form_is_unaffected() {
    let src = program(
        "dot",
        "  operation get(q: P) -> Int64 = q.x\n\
         \x20 operation go() -> Int64 = get(p(x: 7))",
    );
    assert_eq!(errors_of(&src), Vec::<String>::new());
    assert_eq!(go(&src, "dot"), 7);
}

/// THE BOUNDARY, pinned. Writing `FieldOf[…]` yourself in a return-type annotation does
/// not reduce it — an operation's declared return type is not a `CtorReduceSite` — so the
/// annotation stays `FieldOf[T = P, Name = "x"]` and clashes with the `Int64` the body
/// produces. Not a regression and not fixed here; recorded so the next reader finds the
/// edge rather than rediscovering it.
///
/// IT DOES NOT PIN THE RENDERING, and an earlier draft of this doc claimed it did —
/// `/code-review` caught that. This fixture's denoted comes from a written ANNOTATION, so
/// it rides the Node carrier and never reaches `seed_op_type_args`; the row is green with
/// the change backed out. The rendering is measured by
/// `a_written_literal_bracket_renders_its_literal` instead, on the carrier this ticket
/// actually moves.
#[test]
fn an_annotation_written_by_hand_still_does_not_reduce() {
    let src = format!(
        "namespace probe.annot\n  import anthill.prelude.{{Int64, String, FieldOf}}\n  \
         import anthill.reflect.{{field_access}}\n  sort P\n    entity p(x: Int64)\n  end\n  \
         operation get(q: P) -> FieldOf[T = P, Name = \"x\"] = q.x\nend\n"
    );
    let errs = errors_of(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("FieldOf[T = P, Name = \"x\"]")),
        "the unreduced annotation must render its literal operand legibly; got {errs:?}"
    );
}

/// THE RENDERING THIS TICKET OWES, and it is not about `field_access` at all — which is
/// why it is the row that matters. Grounding a written bracket's literal (the change
/// above) puts a `Term::Const` denoted into σ for EVERY operation with a value-in-type
/// parameter, so a mismatch renders one; `type_display_name` had no `Term::Const` arm and
/// printed `Vec[T = Int64, N = TermId(8960)]` — the allocation index, not the value.
///
/// That is exactly the illegibility WI-404 exists to prevent ("must name the actual
/// literals, `N = 3` vs `N = 4`"), and every WI-404 row stays green either way because
/// none of them writes a CALL bracket. Found by `/code-review`, against a comment of mine
/// asserting no path could drive it; the fixture below is that disproof, re-run here.
#[test]
fn a_written_literal_bracket_renders_its_literal() {
    let src = "namespace probe.vec\n  import anthill.prelude.{Int64}\n  sort Vec[T, N]\n\
               \x20   entity vec(t: T)\n  end\n  operation mk[T, N]() -> Vec[T = T, N = N]\
               \x20= vec(t: 0)\n  operation use2() -> Vec[T = Int64, N = 4] = \
               mk[Int64, 3]()\nend\n";
    let errs = errors_of(src);
    let mismatch = errs
        .iter()
        .find(|e| e.contains("use2.return"))
        .unwrap_or_else(|| panic!("the N = 4 vs N = 3 mismatch must be reported; got {errs:?}"));
    assert!(
        mismatch.contains("N = 3"),
        "the bound literal must render as its value; got {mismatch:?}"
    );
    assert!(
        !mismatch.contains("TermId"),
        "a raw allocation index in a user-facing type is the defect this row measures; \
         got {mismatch:?}"
    );
}
