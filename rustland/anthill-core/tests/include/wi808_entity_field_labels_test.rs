//! WI-808 — an ENTITY's field names must be DISTINCT.
//!
//! The same family as WI-805 (tuple component labels) reached through a different
//! declaration, and recorded there as out of scope before being fixed here. MEASURED
//! before the guard, with WI-805's tuple guards already in place:
//!
//! ```anthill
//! sort S
//!   entity mk(a: Int64, a: Int64)
//! end
//! operation drive() -> Int64 = mk(1, 2).a     -- loaded clean, returned Int(1)
//! ```
//!
//! THE HARM IS NARROWER THAN THE TUPLE CASE, and the distinction is why this needed
//! its own decision rather than following automatically. A tuple component under a
//! repeated name is unreachable ENTIRELY — by name and by position — so its declared
//! type is never checked against anything. An entity's second `a` is still BUILT and
//! READ positionally: `mk(1, 2)` type-checks both fields against their declarations,
//! and `case mk(p, q) -> q` reads the second (measured: returns the second field's
//! value). What it loses is its ACCESS PATH — `x.f`, a named argument, and a rule
//! pattern all resolve a field name to the FIRST match, so the later field can never
//! be addressed by name.
//!
//! That is still decisive: a field name IS the field's public interface, so a name
//! identifying two fields addresses neither. It is the same reason the spec gives for
//! a projection's result keys and a call's named arguments.
//!
//! NOT extended to an arrow's parameter list or an operation's parameters, for the
//! reason WI-805 settled: those are applied positionally and their names are local
//! binders, not part of a type's interface.

use crate::common::{interp_for, parse_errs, parses_clean, try_load_kb_with};

fn load_errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// The headline: a same-typed duplicate, which nothing else can catch. The
/// differently-typed spelling was already refused incidentally, by a type mismatch
/// against whichever field `.a` resolved to — this one loaded clean and returned the
/// FIRST field with the second permanently unaddressable.
#[test]
fn duplicate_entity_field_is_refused() {
    let src = r#"
namespace test.wi808.dup
  import anthill.prelude.Int64
  sort S
    entity mk(a: Int64, a: Int64)
  end
end
"#;
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate entity field `a`")),
        "a repeated entity field name must be refused, naming it; got: {errs:?}",
    );
}

/// The diagnostic is located at the OFFENDING FIELD's name, not at the entity — the
/// check runs per field with `self.field(f, "name")` for that reason. Pinned by span,
/// since an error reported at the whole declaration would satisfy every `contains`
/// assertion above.
#[test]
fn the_duplicate_is_located_at_the_second_field() {
    let src = "namespace test.wi808.loc\n  import anthill.prelude.Int64\n  \
               sort S\n    entity mk(aa: Int64, aa: Int64)\n  end\nend\n";
    let errs = match anthill_core::parse::parse(src) {
        Ok(_) => panic!("a duplicate entity field must not parse"),
        Err(errs) => errs,
    };
    let dup = errs
        .iter()
        .find(|e| e.message.contains("duplicate entity field"))
        .unwrap_or_else(|| panic!("no duplicate-field error; got: {errs:?}"));
    let second = src.rfind("aa: Int64").expect("fixture spells the second field") as u32;
    assert_eq!(
        (dup.span.start, dup.span.end),
        (second, second + 2),
        "the error must point at the SECOND `aa`; got {:?} — `{}`",
        dup.span,
        &src[dup.span.start as usize..dup.span.end as usize],
    );
}

/// The differently-typed spelling, refused for the same reason now rather than
/// incidentally. Before the guard this DID surface an error — but a misleading one
/// (`expected String, got Int64` on the return), because `.a` read the first field
/// while the author had written the second's type as the result.
#[test]
fn differently_typed_duplicate_is_refused_at_the_declaration() {
    let src = r#"
namespace test.wi808.dup2
  import anthill.prelude.{Int64, String}
  sort S
    entity mk(a: Int64, a: String)
  end
  operation drive() -> String = mk(1, "ess").a
end
"#;
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate entity field `a`")),
        "the fault is the declaration, not the return type; got: {errs:?}",
    );
}

// ── what the rule must NOT catch ───────────────────────────────

/// DISTINCT fields are untouched, and still readable by name end to end. Without this
/// the tests above pass just as well against a guard that refuses every entity.
#[test]
fn distinct_entity_fields_still_load_and_read() {
    let src = r#"
namespace test.wi808.ok
  import anthill.prelude.{Int64, String}
  sort S
    entity mk(a: Int64, b: String)
  end
  operation drive() -> Int64 = mk(1, "ess").a
end
"#;
    assert!(load_errs(src).is_empty(), "a distinct-field entity must load: {:?}", load_errs(src));
    let mut interp = interp_for(src);
    match interp.call("test.wi808.ok.drive", &[]).expect("drive") {
        anthill_core::eval::Value::Int(1) => {}
        other => panic!("`.a` must read the `a` field; got {other:?}"),
    }
}

/// The field-name set is PER ENTITY, not per sort or per file — two entities in one
/// sort may each declare an `a`, which is the ordinary shape of a variant type.
/// A check keyed on the sort rather than the entity would break every such sort.
#[test]
fn sibling_entities_may_share_a_field_name() {
    parses_clean(
        "namespace test.wi808.sib\n  import anthill.prelude.Int64\n  \
         sort S\n    entity mk(a: Int64)\n    entity mk2(a: Int64, b: Int64)\n  end\nend\n",
    );
}

/// A single-field entity, and one whose field name matches its own entity name —
/// neither is a duplicate. Guards against a check that compares the wrong pair.
#[test]
fn a_field_named_like_its_entity_is_not_a_duplicate() {
    parses_clean(
        "namespace test.wi808.self\n  import anthill.prelude.Int64\n  \
         sort S\n    entity mk(mk: Int64)\n  end\nend\n",
    );
}
