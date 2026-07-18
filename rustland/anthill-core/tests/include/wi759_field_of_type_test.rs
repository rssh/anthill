//! WI-759 — `FieldOf[T, Name]`: field access states its own type.
//!
//! `anthill.reflect.field_access` used to be typed by TWO early returns in
//! `check_apply_iter`, both keyed on its own operation identity — which the repo forbids
//! ("nothing in the typer keyed on a domain operation's identity"). They existed because
//! the node the typer synthesizes for `x.f` was ill-typed against `field_access`'s OWN
//! declared signature `(object: Term, field: Symbol) -> Term` in all three positions: the
//! receiver is an entity or a named tuple and `Term` is not a top type; the selector is a
//! `String` constant, not a `Symbol`; the result is the FIELD's type, not `Term`.
//!
//! The signature is now `field_access[R, Name](object: R, field: String) -> FieldOf[T = R,
//! Name = Name]`, and `FieldOf` joins the `Concat` / `Without` binary-type-constructor
//! family — reduced at the same return-type normalization boundary, keyed on its own SORT.
//! So the rewrite is idempotent BY CONSTRUCTION: the forward direction (`x.f` ⟹ the
//! member's type) and a later re-type of the stored node are one decision procedure,
//! sharing one lookup. They used to be two, and had already drifted — WI-758 is exactly
//! that drift, a named-tuple arm the forward direction grew and the reverse never did.
//!
//! The enabling primitive is a compile-time NAME in TYPE-ARGUMENT position. There are no
//! singleton types, so a field name in VALUE position types as plain `String` and loses the
//! name; the `denoted` value-in-type channel is the only route that carries it. These are
//! the repo's first STRING-valued type arguments (the channel was previously exercised only
//! by integers, `Vec[T = Int64, N = 3]`).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, LoadResult, NullResolver};
use anthill_core::kb::typing::{sort_functor_of_view, type_check_sorts};
use anthill_core::parse;

use crate::common::try_load_kb_with;

fn load_stdlib_kb() -> KnowledgeBase {
    let files = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
    assert!(!files.is_empty(), "no stdlib files found");
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {p:?}: {e:?}"))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_stdlib(&mut kb, &refs, &NullResolver).expect("stdlib load");
    kb
}

fn load_with_result(source: &str) -> (KnowledgeBase, LoadResult) {
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    let result = load::load(&mut kb, &parsed, &NullResolver).expect("load failed");
    (kb, result)
}

/// Type-check `source`'s own sorts, then RE-type-check with no sort owning the ops — the
/// free-op sweep re-visits the already-rewritten bodies, the same path an incremental load
/// takes. Returns the second pass's errors.
fn retype_errors(source: &str) -> Vec<String> {
    let (mut kb, result) = load_with_result(source);
    let first = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(first.is_empty(), "first type-check must be clean, got: {first:?}");
    type_check_sorts(&mut kb, &[]).iter().map(|e| e.to_string()).collect()
}

/// Re-type as above, then read the SHORT sort name the re-typed body node actually carries.
/// WI-758's acceptance asks for the field's TYPE, not merely the absence of errors — this
/// reads the `inferred_type` the `Stamp` frame pushed onto the stored (already-rewritten)
/// `field_access` node during the SECOND pass, so a re-type that widened to the reflect
/// signature would read back `Term`, and one that left the constructor unreduced `FieldOf`.
fn retyped_body_sort(source: &str, op_qn: &str) -> String {
    let (mut kb, result) = load_with_result(source);
    let first = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(first.is_empty(), "first type-check must be clean, got: {first:?}");
    let second = type_check_sorts(&mut kb, &[]);
    assert!(second.is_empty(), "re-type-check must be clean, got: {second:?}");
    let op = kb
        .try_resolve_symbol(op_qn)
        .unwrap_or_else(|| panic!("no symbol for {op_qn}"));
    let body = kb
        .op_body_node(op)
        .cloned()
        .unwrap_or_else(|| panic!("{op_qn} has no stored body node"));
    let ty = body
        .inferred_type()
        .unwrap_or_else(|| panic!("{op_qn}'s body carries no inferred type after the re-type"));
    let head = sort_functor_of_view(&kb, &ty)
        .unwrap_or_else(|| panic!("{op_qn}'s re-typed body type has no sort head"));
    short_of(kb.qualified_name_of(head))
}

fn short_of(qn: &str) -> String {
    qn.rsplit('.').next().unwrap_or(qn).to_string()
}

// ── WI-758's acceptance: the drift the shared lookup makes impossible ──────────────

/// THE WI-758 shape: a NAMED-TUPLE projection survives a re-type round-trip.
///
/// The forward direction has handled a named-tuple receiver since WI-638 (its THIRD
/// dot-dispatch mode, which rewrites `t.x` to a `field_access` node and stamped the
/// component's type on it). The reverse — re-typing that stored node — resolved the field
/// only through the receiver's SORT, and a named tuple's functor is `named_tuple`, not a
/// sort. So the re-type fell through to the declared reflect signature and failed with
/// `expected Symbol, got String`: a diagnostic naming an internal desugaring rather than
/// anything the user wrote.
///
/// It is satisfied here STRUCTURALLY rather than by adding a second arm — one lookup now
/// serves both directions, so there is no second place for the named-tuple case to be
/// missing from.
#[test]
fn wi759_named_tuple_projection_survives_retype() {
    const SRC: &str = r#"
namespace test.wi759nt
  import anthill.prelude.{Int64, String}
  operation pick_name(t: (name: String, age: Int64)) -> String = t.name
  operation pick_age(t: (name: String, age: Int64)) -> Int64 = t.age
  operation pick_pos(t: (Int64, Int64)) -> Int64 = t._2
end
"#;
    let errs = retype_errors(SRC);
    assert!(
        errs.is_empty(),
        "re-typing a named-tuple projection must resolve the component, not check the \
         rewritten node against `field_access`'s reflect signature; got: {errs:?}",
    );
    // WI-758's acceptance names the TYPE, not just the absence of errors. Read what the
    // re-typed node actually carries: `Term` would mean the reflect signature won, `FieldOf`
    // that the constructor never reduced. Two DIFFERENT component types (and a positional
    // `_2`) so this cannot pass by every projection collapsing to one type.
    assert_eq!(
        retyped_body_sort(SRC, "test.wi759nt.pick_name"),
        "String",
        "`t.name` must re-type to the component's type",
    );
    assert_eq!(
        retyped_body_sort(SRC, "test.wi759nt.pick_age"),
        "Int64",
        "`t.age` must re-type to the component's type",
    );
    assert_eq!(
        retyped_body_sort(SRC, "test.wi759nt.pick_pos"),
        "Int64",
        "a positional `t._2` must re-type to the component's type",
    );
}

/// PRESERVATION control for the above, not a second regression test: the ENTITY twin
/// (WI-509's shape) already round-tripped before WI-759 — that is precisely the asymmetry
/// WI-758 reported, the entity case handled on both sides and the named-tuple case on only
/// one. A/B-verified: this test passes against the pre-WI-759 code and the one above fails
/// there, with the ticket's verbatim `expected Symbol, got String`.
///
/// What it pins now is that the case still works for the GENERAL reason rather than via the
/// retired hatch: `FieldOf[T = Box, Name = "n"]` reduces to `Int64`. The declared `-> Int64`
/// return is what makes it an assertion — a re-type that widened to `field_access`'s nominal
/// `-> Term` would fail the body/return conformance check.
#[test]
fn wi759_entity_projection_retypes_to_the_field_type() {
    let errs = retype_errors(
        r#"
namespace test.wi759ent
  import anthill.prelude.{Int64}
  sort Box
    import anthill.prelude.{Int64}
    entity box(n: Int64)
  end
  operation get_n(b: Box) -> Int64 = b.n
end
"#,
    );
    assert!(
        errs.is_empty(),
        "re-typing an entity projection must yield the FIELD's type, got: {errs:?}",
    );
}

// ── The enabling primitive: a compile-time NAME in TYPE-ARGUMENT position ──────────

/// A signature may WRITE `FieldOf[T = …, Name = "…"]` — the repo's first string-valued type
/// argument. The reduction fires at the call site (as `Concat` / `Without` do), so
/// `name_of(r)` types as `String` and the caller's declared `-> String` conforms.
///
/// This is the primitive WI-732's `Project[T, keep]` needs: a keep-spec in type position.
#[test]
fn wi759_field_name_in_type_argument_position_reduces() {
    let src = r#"
namespace test.wi759prim
  import anthill.prelude.{Int64, String, FieldOf}
  sort Rec
    import anthill.prelude.{Int64, String}
    entity rec(name: String, age: Int64)
  end
  operation name_of(r: Rec) -> FieldOf[T = Rec, Name = "name"]
  operation age_of(r: Rec) -> FieldOf[T = Rec, Name = "age"]
  operation use_name(r: Rec) -> String = name_of(r)
  operation use_age(r: Rec) -> Int64 = age_of(r)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "a written `FieldOf[T, Name = \"…\"]` must reduce to the named field's type; got: {:?}",
        try_load_kb_with(src).err(),
    );
}

/// NEGATIVE CONTROL for the above: the reduction is not a rubber stamp. `name_of` returns
/// the `String` field, so a caller claiming `-> Int64` must be REJECTED — otherwise the
/// previous test would pass just as well against a `FieldOf` that reduced to anything.
#[test]
fn wi759_field_name_in_type_position_rejects_the_wrong_type() {
    let src = r#"
namespace test.wi759primneg
  import anthill.prelude.{Int64, String, FieldOf}
  sort Rec
    import anthill.prelude.{Int64, String}
    entity rec(name: String, age: Int64)
  end
  operation name_of(r: Rec) -> FieldOf[T = Rec, Name = "name"]
  operation wrong(r: Rec) -> Int64 = name_of(r)
end
"#;
    assert!(
        try_load_kb_with(src).is_err(),
        "`FieldOf[T = Rec, Name = \"name\"]` reduces to String — a `-> Int64` caller must be \
         a loud mismatch",
    );
}

/// A name that names NO field of a concrete receiver is LOUD — never a silent widening to
/// `Term`, which is what the old declared return would have given.
#[test]
fn wi759_unknown_field_name_is_loud() {
    let src = r#"
namespace test.wi759miss
  import anthill.prelude.{Int64, String, FieldOf}
  sort Rec
    import anthill.prelude.{Int64, String}
    entity rec(name: String, age: Int64)
  end
  operation bogus(r: Rec) -> FieldOf[T = Rec, Name = "nosuch"]
  operation use_bogus(r: Rec) -> String = bogus(r)
end
"#;
    let errs = match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(
        errs.iter().any(|e| e.contains("nosuch")),
        "projecting a field the receiver does not declare must name it; got: {errs:?}",
    );
}

// ── The family's abstract-operand rule (WI-734) applies to FieldOf ─────────────────

/// A receiver that is NOT YET KNOWN leaves `FieldOf` SYMBOLIC, exactly as `Concat` /
/// `Without` do. This is what lets a reducible constructor sit in a signature checked
/// before the receiver's type is known — and `field_access` forces it harder than `Concat`
/// does, because a rule body's `field_access(?t, f)` has no static receiver at all.
///
/// The residual must CONFORM in a generic wrapper, and REDUCE once the receiver grounds.
#[test]
fn wi759_abstract_receiver_stays_symbolic_then_reduces() {
    let src = r#"
namespace test.wi759abs
  import anthill.prelude.{Int64, String, FieldOf}
  sort Rec
    import anthill.prelude.{Int64, String}
    entity rec(name: String, age: Int64)
  end
  operation field_of_any[S](r: S) -> FieldOf[T = S, Name = "name"]
  operation wrap[S2](r: S2) -> FieldOf[T = S2, Name = "name"] = field_of_any(r)
  operation grounded(r: Rec) -> String = wrap(r)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "a FieldOf over an abstract receiver must stay symbolic and reduce once grounded; \
         got: {:?}",
        try_load_kb_with(src).err(),
    );
}

// ── WI-369 rides the SAME resolution ──────────────────────────────────────────────

/// `internal` visibility is enforced by the REDUCTION, off the same lookup that produced
/// the type — so it also covers the hand-written desugared form, which never passes through
/// dot dispatch. Here the projection is written in TYPE position from another sort's scope:
/// the field `v` belongs to `Box`'s `internal` constructor `mk`, so reducing
/// `FieldOf[T = Box, Name = "v"]` there must be refused.
#[test]
fn wi759_internal_field_hidden_from_the_reduction() {
    const BOX_SRC: &str = r#"
sort test.wi759int.Box
  import anthill.prelude.Int64
  internal entity mk(v: Int64)
end
"#;
    const PEEK_SRC: &str = r#"
sort test.wi759int.Peeker
  import anthill.prelude.{Int64, FieldOf}
  import test.wi759int.Box
  operation raw(b: Box) -> FieldOf[T = Box, Name = "v"]
  operation peek(b: Box) -> Int64 = raw(b)
end
"#;
    let errs = match crate::common::try_load_kb_with_files(&[BOX_SRC, PEEK_SRC]) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(
        errs.iter().any(|e| e.contains("internal") && e.contains("v")),
        "reducing a FieldOf onto an internal entity's field from another scope must be \
         refused, naming the field; got: {errs:?}",
    );
}

/// Control for the above: the SAME projection inside the declaring sort's own scope is
/// visible. Without this, the previous test would pass against a rule that simply refused
/// every `internal`-owned field everywhere.
#[test]
fn wi759_internal_field_visible_in_its_own_scope() {
    let src = r#"
sort test.wi759intok.Box
  import anthill.prelude.{Int64, FieldOf}
  internal entity mk(v: Int64)
  operation raw(b: Box) -> FieldOf[T = Box, Name = "v"]
  operation peek(b: Box) -> Int64 = raw(b)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "an internal field stays projectable inside its declaring scope; got: {:?}",
        try_load_kb_with(src).err(),
    );
}

// ── The third receiver: the genuine reflect metaprogramming call ───────────────────

/// A `Term` receiver projects to `Term` for ANY name — its "fields" are a runtime term's
/// named arguments, not a declared schema. This is the one case `field_access`'s old
/// nominal `-> Term` return described correctly, and it must survive the generalization.
#[test]
fn wi759_term_receiver_projects_to_term() {
    let src = r#"
namespace test.wi759term
  import anthill.prelude.{FieldOf}
  import anthill.reflect.{Term}
  operation any_field(t: Term) -> FieldOf[T = Term, Name = "whatever"]
  operation use_it(t: Term) -> Term = any_field(t)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "a Term receiver must project to Term for any name; got: {:?}",
        try_load_kb_with(src).err(),
    );
}

/// …but that permissiveness must NOT leak into the forward DOT DISPATCH. `t.typo` on a
/// `Term`-typed receiver has to stay a loud `no such member`: a `Term` declares no members,
/// so a dot on one is a mistake in the user's code, not a metaprogramming call. The
/// "any name projects" answer belongs to the REDUCTION alone, where the node exists only
/// because someone WROTE `field_access` / `FieldOf` explicitly.
///
/// Found by review: the first draft put the `Term` arm in the lookup SHARED by both
/// directions, which silently type-checked every typo on a Term receiver. A/B-probed in
/// both states — clean before the fix, `no such member (dot dispatch)` after.
#[test]
fn wi759_term_receiver_dot_dispatch_stays_loud() {
    let src = r#"
namespace test.wi759termdot
  import anthill.reflect.{Term}
  operation bogus(t: Term) -> Term = t.definitely_not_a_field
end
"#;
    let errs = match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(
        errs.iter().any(|e| e.contains("definitely_not_a_field")),
        "a dot on a Term receiver must stay loud — the reduction's `any name projects` \
         reading must not widen dot dispatch; got: {errs:?}",
    );
}
