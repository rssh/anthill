//! WI-928 / §6.3 — a free-standing `entity E` emits the same DECLARATION RECORD
//! as `sort E { entity E }`, so the load-time passes reach it.
//!
//! WI-925 made the two spellings agree at run time (an entity's sort is total).
//! They still disagreed at LOAD time, and on the question a declaration exists to
//! answer — whether a write is accepted. MEASURED before this ticket, one fact
//! under each spelling of one declaration:
//!
//! ```text
//! entity Thing(count: Int64)            + fact Thing(count: "hello")  → 0 errors
//! sort Thing { entity Thing(count: …) } + the SAME fact               → type mismatch
//! ```
//!
//! MECHANISM: `type_check_sorts` walks `LoadResult.defined_sorts` and takes each
//! sort's constructors from its `SortInfo`. `load_sort_with_body` pushed and
//! emitted; `load_entity` did neither, so the sugar's facts were not merely
//! unindexed — they were never checked, in stdlib and user code alike.
//!
//! CONTROL DISCIPLINE, measured by disabling the emission: the six SUBJECT tests
//! below fail without it; the three named `control_…` pass either way and say so
//! at each site — they are here to catch an over-broad fix (refusing well-typed
//! facts, promoting sort-body variants, or re-breaking the stdlib load), which is
//! a different failure than the one being fixed.

use crate::common::try_load_kb_with;
use anthill_core::intern::Symbol;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;

/// One declaration, both §6.3 spellings, plus whatever the caller wants after it.
/// Only the spelling differs between the two arms.
fn arms(decl: &str, rest: &str) -> (String, String) {
    let sugar = format!(
        "\nnamespace test.wi928\n  import anthill.prelude.{{Int64, String}}\n\n  entity {decl}\n\n{rest}\nend\n"
    );
    let long = format!(
        "\nnamespace test.wi928\n  import anthill.prelude.{{Int64, String}}\n\n  sort Thing\n    entity {decl}\n  end\n\n{rest}\nend\n"
    );
    (sugar, long)
}

/// The errors this source is responsible for. The stdlib's own load is identical
/// under both arms, so anything not naming the subject is not what is being
/// measured (there is nothing at the time of writing, and `control_the_stdlib_
/// loads_clean` pins that).
fn own_errors(r: Result<KnowledgeBase, Vec<String>>) -> Vec<String> {
    match r {
        Ok(_) => Vec::new(),
        Err(errs) => errs.into_iter().filter(|m| m.contains("Thing")).collect(),
    }
}

/// Strip the `line:col` prefix: the two spellings put the fact on different lines,
/// which is the ONE difference that must not count as disagreement.
fn without_position(msgs: &[String]) -> Vec<String> {
    msgs.iter()
        .map(|m| match m.find(": ") {
            Some(i) if m[..i].contains(':') => m[i + 2..].to_string(),
            _ => m.clone(),
        })
        .collect()
}

// ── The subject: one verdict, both spellings ────────────────────

/// THE TICKET. An ill-typed fact is refused under BOTH spellings, with the same
/// message. Before this, the sugar arm loaded clean.
#[test]
fn an_illtyped_fact_is_refused_under_both_spellings() {
    let (sugar, long) = arms("Thing(count: Int64)", r#"  fact Thing(count: "hello")"#);
    let s = own_errors(try_load_kb_with(&sugar));
    let l = own_errors(try_load_kb_with(&long));

    assert_eq!(
        s.len(),
        1,
        "the sugar must refuse an ill-typed fact — this is the defect (got {s:?})",
    );
    assert!(
        s[0].contains("type mismatch in Thing.count") && s[0].contains("expected Int64"),
        "and refuse it for the declared reason, not incidentally: {s:?}",
    );
    assert_eq!(
        without_position(&s),
        without_position(&l),
        "§6.3 is an equivalence: one declaration, one verdict, one message",
    );
}

/// CONTROL — the agreement is not "both refuse everything". A well-typed fact
/// loads under both. Without this, an implementation that refused every fact of a
/// free-standing entity would pass the test above.
#[test]
fn control_a_welltyped_fact_loads_under_both_spellings() {
    let (sugar, long) = arms("Thing(count: Int64)", "  fact Thing(count: 42)");
    assert_eq!(own_errors(try_load_kb_with(&sugar)), Vec::<String>::new());
    assert_eq!(own_errors(try_load_kb_with(&long)), Vec::<String>::new());
}

/// The check reaches EVERY declared field, not just the first — a fact ill-typed
/// in its second field is refused under both spellings too.
#[test]
fn a_later_field_is_checked_under_both_spellings() {
    let (sugar, long) = arms(
        "Thing(count: Int64, label: String)",
        r#"  fact Thing(count: 1, label: 2)"#,
    );
    let s = own_errors(try_load_kb_with(&sugar));
    assert_eq!(s.len(), 1, "the second field is checked: {s:?}");
    assert!(s[0].contains("Thing.label"), "and named: {s:?}");
    assert_eq!(without_position(&s), without_position(&own_errors(try_load_kb_with(&long))));
}

// ── The record itself ───────────────────────────────────────────

/// What makes the above work: the sugar emits a `SortInfo`, and its constructor
/// list is the entity ITSELF (WI-926 — one symbol, so `sort E { entity E }` has
/// exactly one constructor, `E`). This is the record every load-time pass that
/// walks declared sorts reads.
#[test]
fn both_spellings_emit_one_sort_info_whose_constructor_is_itself() {
    for (label, src) in spellings() {
        let mut kb = try_load_kb_with(&src).expect("declaration alone loads");
        let thing = subject(&kb);
        let records = records_naming(&kb, "anthill.reflect.SortInfo", thing);
        assert_eq!(records.len(), 1, "[{label}] exactly one SortInfo names Thing");

        let ctors: Vec<String> =
            anthill_core::kb::typing::list_to_vec(&kb, field(&kb, &records[0], "constructors"))
                .into_iter()
                .map(|t| kb.resolve_sym(head_sym(&kb, t).expect("a constructor ref")).to_string())
                .collect();
        assert_eq!(ctors, vec!["Thing".to_string()], "[{label}] its sole constructor is itself");
    }
}

/// The one field that differs, and deliberately: `kind` reports the KEYWORD
/// WRITTEN (§6.3, the same rule the category set's head follows). A reader may
/// report it; nothing may branch on it to decide what the declaration is.
#[test]
fn the_records_differ_only_in_the_written_keyword() {
    let kinds: Vec<String> = spellings()
        .into_iter()
        .map(|(_, src)| {
            let mut kb = try_load_kb_with(&src).expect("declaration alone loads");
            let thing = subject(&kb);
            let records = records_naming(&kb, "anthill.reflect.SortInfo", thing);
            let kind = field(&kb, &records[0], "kind");
            kb.resolve_sym(head_sym(&kb, kind).expect("kind is a name")).to_string()
        })
        .collect();
    assert_eq!(kinds, vec!["entity".to_string(), "sort".to_string()]);
}

/// The other straight omission: a single-constructor sort's induction principle is
/// well-defined, and the long form has emitted it since proposal 030.
#[test]
fn both_spellings_emit_the_induction_principle() {
    for (label, src) in spellings() {
        let kb = try_load_kb_with(&src).expect("declaration alone loads");
        assert!(
            kb.try_resolve_symbol("test.wi928.Thing.induction").is_some(),
            "[{label}] a one-constructor sort has an induction principle",
        );
    }
}

/// WI-926 residue: an eponymous constructor is not a MEMBER of itself. The long
/// form used to emit `MemberInfo(name: Thing, kind: Constructor, parent: Thing)` —
/// the containment `register_entity_of` refuses two blocks earlier in the same
/// loader pass. Each spelling now lists the declaration exactly once, under its
/// enclosing namespace.
#[test]
fn neither_spelling_makes_the_name_a_member_of_itself() {
    for (label, src) in spellings() {
        let mut kb = try_load_kb_with(&src).expect("declaration alone loads");
        let thing = subject(&kb);
        let records = records_naming(&kb, "anthill.reflect.MemberInfo", thing);
        assert_eq!(records.len(), 1, "[{label}] the declaration is listed once");
        assert_ne!(
            head_sym(&kb, field(&kb, &records[0], "parent")),
            Some(thing),
            "[{label}] and not as its own member",
        );
    }
}

// ── Controls: what must NOT have changed ────────────────────────

/// NEGATIVE CONTROL — the whole corpus still loads. This is the measurement that
/// scoped the change: turning the load-time passes on for 68 previously-invisible
/// entities surfaced 685 reports over the loader's own DECLARATION RECORDS
/// (`check_entity_facts` skips those — their slots hold reflect handles, and
/// reaching a handle is a conversion, not subsumption) and 12 unbacked-provider
/// findings on four free-standing carriers (staged, WI-931).
#[test]
fn control_the_stdlib_loads_clean() {
    let errs = match try_load_kb_with("\nnamespace test.wi928c\n  fact marker(x: 1)\nend\n") {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(errs.is_empty(), "the stdlib + host bindings must load clean: {errs:#?}");
}

/// NEGATIVE CONTROL — a sort-body variant named DIFFERENTLY from its sort is
/// untouched: it is a constructor of its sort, listed as a member of it, and gets
/// no record of its own. §6.3's rule is keyed on the name matching.
#[test]
fn control_a_differently_named_variant_is_unaffected() {
    let src = "
namespace test.wi928v
  sort Status
    entity Open
    entity Closed
  end
end
";
    let mut kb = try_load_kb_with(src).expect("loads");
    let status = kb.try_resolve_symbol("test.wi928v.Status").expect("Status");
    let open = kb.try_resolve_symbol("test.wi928v.Status.Open").expect("Open");
    assert_eq!(kb.constructor_parent_sort(open), Some(status));

    let si = kb.try_resolve_symbol("anthill.reflect.SortInfo").expect("reflect");
    let own_record = kb
        .rules_by_functor(si)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .filter_map(|rid| kb.fact_head_named_args(rid))
        .any(|named| {
            named.iter().any(|(f, v)| {
                kb.resolve_sym(*f) == "name" && head_sym(&kb, *v) == Some(open)
            })
        });
    assert!(!own_record, "a variant is not a sort; it has no SortInfo of its own");
}

// ── Reading the declaration record ──────────────────────────────

/// The subject declaration in both §6.3 spellings, labelled — the loop header of
/// every test above, since "the same in both spellings" is what is being asserted.
fn spellings() -> Vec<(&'static str, String)> {
    let (sugar, long) = arms("Thing(count: Int64)", "");
    vec![("sugar", sugar), ("long", long)]
}

fn subject(kb: &KnowledgeBase) -> Symbol {
    kb.try_resolve_symbol("test.wi928.Thing").expect("Thing resolves")
}

/// Every fact of `functor` (a reflect record) whose `name:` field denotes
/// `subject`, as its named arguments. Asking through the FACTS rather than an
/// index is the point: it is what the load-time passes read.
fn records_naming(kb: &KnowledgeBase, functor: &str, subject: Symbol) -> Vec<Record> {
    let sym = kb.try_resolve_symbol(functor).expect("reflect is loaded");
    kb.rules_by_functor(sym)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .filter_map(|rid| kb.fact_head_named_args(rid))
        .filter(|named| head_sym(kb, field_of(kb, named, "name").expect("a record names something")) == Some(subject))
        .collect()
}

type Record = smallvec::SmallVec<[(Symbol, TermId); 2]>;

fn field_of(kb: &KnowledgeBase, record: &Record, name: &str) -> Option<TermId> {
    record.iter().find(|(f, _)| kb.resolve_sym(*f) == name).map(|(_, v)| *v)
}

fn field(kb: &KnowledgeBase, record: &Record, name: &str) -> TermId {
    field_of(kb, record, name).unwrap_or_else(|| panic!("the record carries `{name}`"))
}

/// The functor symbol a name term denotes, whatever spelling it carries
/// (`Ref` / `Ident` / nullary `Fn` — the WI-511 canon lets one name appear as
/// more than one of these).
fn head_sym(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    match kb.get_term(t) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}
