//! WI-912 — a PERSISTED name is read by THE SAME LADDER as source text.
//!
//! `term_ser` reads names out of a data file (`meta.entity`, a variant key) — text the
//! KB did not write in any scope, exactly like an extent-owner name (WI-908). It had its
//! own ladder: the absolute lookup, then the name's LAST SEGMENT looked up absolutely
//! (the WI-476 global short-name scan), then a bare `intern` (WI-894's hazard). Each row
//! below persists a name, reloads it, and asserts WHICH symbol it landed on — or that it
//! was refused, and how.
//!
//! BACKED OUT (the pre-WI-912 `resolve_entity_functor` / `resolve_variant_sym`), the
//! four refusal rows fail: `a_missing_member_does_not_fall_back_to_its_last_segment` and
//! `a_variant_outside_the_declared_sort_is_refused` LOAD a fact onto the stranger,
//! `an_unknown_variant_is_refused_not_interned` loads one onto a fresh bare symbol, and
//! `an_ambiguous_entity_name_is_refused_as_ambiguous` reports `UnknownEntity`. The two
//! `…_still_…` rows pass either way by design — they pin the spellings the serializer
//! itself writes.

use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::term_ser::{self, SerError};

/// `Stray` is a TOP-LEVEL entity, so its qualified name IS its short name — the one
/// shape the last-segment fallback could land on from any path ending in `.Stray`.
const SRC: &str = "\
namespace wi912.app
  sort Status
    entity Open
    entity Closed
  end
  sort Job
    entity Job(id: String, status: Status)
  end
end

entity Stray(id: String)
";

fn fixture() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

fn load(kb: &mut KnowledgeBase, toml: &str) -> Result<usize, Vec<SerError>> {
    let domain = kb.intern("wi912_domain");
    term_ser::load_toml(kb, toml, domain)
}

/// The one fact `functor` has after a load, as its `Term`.
fn only_fact_of(kb: &KnowledgeBase, qualified: &str) -> Term {
    let sym = kb.resolve_symbol(qualified);
    let ids: Vec<_> = kb.rules_by_functor(sym);
    assert_eq!(ids.len(), 1, "expected exactly one `{qualified}` fact");
    kb.get_term(kb.rule_head(ids[0])).clone()
}

/// CONTROL — the spelling the serializer writes (the qualified `meta.entity`, a variant by
/// its local name) lands where it always did.
#[test]
fn a_qualified_entity_and_a_local_variant_still_load() {
    let mut kb = fixture();
    let n = load(
        &mut kb,
        r#"
[meta]
entity = "wi912.app.Job"

[data]
id = "j1"
status = "Open"
"#,
    )
    .expect("the serializer's own spelling loads");
    assert_eq!(n, 1);

    let Term::Fn { named_args, .. } = only_fact_of(&kb, "wi912.app.Job") else {
        panic!("a Job fact is an entity term");
    };
    let open = kb.resolve_symbol("wi912.app.Status.Open");
    assert!(
        named_args
            .iter()
            .any(|(_, v)| matches!(kb.get_term(*v), Term::Ref(s) if *s == open)),
        "`status = \"Open\"` must land on the declared sort's `Open`",
    );
}

/// CONTROL — a variant written as a one-key object (the payload form) still resolves
/// within the declared sort.
#[test]
fn a_variant_object_of_the_declared_sort_still_loads() {
    let mut kb = fixture();
    load(
        &mut kb,
        r#"
[meta]
entity = "wi912.app.Job"

[data]
id = "j1"
status = { Closed = {} }
"#,
    )
    .expect("a variant of the declared sort loads");
    let closed = kb.resolve_symbol("wi912.app.Status.Closed");
    let Term::Fn { named_args, .. } = only_fact_of(&kb, "wi912.app.Job") else {
        panic!("a Job fact is an entity term");
    };
    assert!(
        named_args.iter().any(|(_, v)| match kb.get_term(*v) {
            Term::Ref(s) => *s == closed,
            Term::Fn { functor, .. } => *functor == closed,
            _ => false,
        }),
        "`{{ Closed = {{}} }}` must land on the declared sort's `Closed`",
    );
}

/// THE SHORT-NAME FALLBACK. `wi912.app.Stray` declares nothing; the old reader then
/// looked up `Stray` — its last segment — absolutely, and landed the row on the
/// top-level entity the file never named.
#[test]
fn a_missing_member_does_not_fall_back_to_its_last_segment() {
    let mut kb = fixture();
    let errs = load(
        &mut kb,
        r#"
[meta]
entity = "wi912.app.Stray"

[data]
id = "s1"
"#,
    )
    .expect_err("`wi912.app.Stray` names nothing");
    assert!(
        errs.iter()
            .any(|e| matches!(e, SerError::UnknownEntity(n) if n == "wi912.app.Stray")),
        "expected UnknownEntity(wi912.app.Stray), got {errs:?}",
    );
    let stray = kb.resolve_symbol("Stray");
    assert_eq!(
        kb.rules_by_functor(stray).len(),
        0,
        "no row may land on the top-level `Stray`",
    );
}

/// THE VARIANT's ABSOLUTE RUNG. `Stray` is not a constructor of `Status`, the field's
/// declared sort; the old reader missed the sort join and then took the top-level
/// `Stray` — a foreign entity inside a `Status`-typed field.
#[test]
fn a_variant_outside_the_declared_sort_is_refused() {
    let mut kb = fixture();
    let errs = load(
        &mut kb,
        r#"
[meta]
entity = "wi912.app.Job"

[data]
id = "j1"
status = { Stray = { id = "s1" } }
"#,
    )
    .expect_err("`Stray` is not a `Status`");
    assert!(
        errs.iter().any(|e| matches!(
            e,
            SerError::UnknownConstructor { name, sort: Some(sort) }
                if name == "Stray" && sort == "wi912.app.Status"
        )),
        "expected UnknownConstructor(Stray in wi912.app.Status), got {errs:?}",
    );
}

/// THE FINAL `intern` (WI-894's hazard): a variant nobody declares used to become a bare
/// global symbol, so the row loaded clean and matched nothing ever written in source.
#[test]
fn an_unknown_variant_is_refused_not_interned() {
    let mut kb = fixture();
    let errs = load(
        &mut kb,
        r#"
[meta]
entity = "wi912.app.Job"

[data]
id = "j1"
status = { Nowhere = {} }
"#,
    )
    .expect_err("`Nowhere` is declared nowhere");
    assert!(
        errs.iter()
            .any(|e| matches!(e, SerError::UnknownConstructor { name, .. } if name == "Nowhere")),
        "expected UnknownConstructor(Nowhere), got {errs:?}",
    );
}

/// AN AMBIGUITY ENDS THE LADDER (WI-907), here as everywhere: a short `meta.entity` that
/// two imports put in scope at `<global>` is refused AS AMBIGUOUS, naming both, rather
/// than as absent.
#[test]
fn an_ambiguous_entity_name_is_refused_as_ambiguous() {
    let mut kb = crate::common::load_kb_bare(&[
        "namespace wi912.l\n  entity Rec(id: Int64)\nend\n",
        "namespace wi912.r\n  entity Rec(id: Int64)\nend\n",
    ]);
    crate::common::supply_invocation_imports(&mut kb, &["wi912.l.*", "wi912.r.*"]);

    let errs = load(&mut kb, "[meta]\nentity = \"Rec\"\n\n[data]\nid = 1\n")
        .expect_err("`Rec` is contested");
    let Some(SerError::AmbiguousName { name, candidates }) = errs
        .iter()
        .find(|e| matches!(e, SerError::AmbiguousName { .. }))
    else {
        panic!("expected AmbiguousName, got {errs:?}");
    };
    assert_eq!(name, "Rec");
    let mut candidates = candidates.clone();
    candidates.sort();
    assert_eq!(candidates, ["wi912.l.Rec", "wi912.r.Rec"]);
}
