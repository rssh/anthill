//! WI-840 (proposal 058 §4.7 / §4.2 / §9 phase 1) — a NAMED requirement slot,
//! `requires <name>: Spec[…]`, on an operation and on a sort.
//!
//! WHY IT IS NOT PLUMBING. A named slot **is a type parameter** (§4.7), and that is
//! what lets a chosen witness enter a TYPE: `SortedSet[T = String, O = ByLength]` and
//! `SortedSet[T = String, O = Alphabetical]` are then two types, refused against each
//! other by the ordinary checker with no new type machinery. An ANONYMOUS slot stays a
//! constraint — solved, not recorded — which is why `List[T = Int64]` is one type no
//! matter which `Eq` satisfied it. The author picks by naming it. Without a name the
//! `SortedSet` merge hazard cannot be STATED, so this is the declaration half the rest
//! of the arc stands on; SELECT (phase 2) needs no further grammar, because §4.2
//! reuses the call bracket 042 already added.
//!
//! MEASURED before the change: `requires d: Desc[E]` did not parse — `syntax error
//! near ': Desc'`. The two existing productions carry no name slot (`requires_declaration`
//! takes a bare `_type`; `requires_clause` takes a `rule_body`), and
//! `design/operation-call-model.md` states the property outright: sub-requirements are
//! "positional and nameless".
//!
//! HOW THE BINDER BECOMES A PARAMETER — one desugar, no new loader concept. The
//! converter rewrites the sort-level `requires O: Ord[T]` into `sort O = ?` + the
//! requirement (`convert_requires_items`), the same fan-out WI-320's `effects E = T`
//! already uses; the op-level `requires plus: Monoid[T]` appends `plus` to the
//! operation's `type_params` and leaves its spec in the clause list as an ordinary goal
//! (`convert_requires_body`). Everything downstream — `add_type_param`,
//! `check_sort_type_args`, `seed_op_type_args` — then treats it as the parameter it is.
//! What the loader adds is only the NAME→slot record (§4.7 wrinkle 3: slots stay
//! POSITIONAL, `requirement_at_sort(node, k)`; phase 1 names one, it does not re-key
//! the projection path).
//!
//! THE GUARD (§4.2), refused AT THE DECLARATION rather than at the call: a bracket key
//! is a bare LABEL with two rungs — a declared type parameter (the operation's or its
//! ENCLOSING SORT's) and a requirement's spec SHORT name — so a parameter whose name is
//! also answered by another rung gives `op[N = …]` two targets. Resolving that at the
//! call by an ordered ladder would be a silent capture: the reader cannot see which `N`
//! the key hit.
//!
//! Binder-vs-parameter collision needs no case of its own, and this file does not test
//! one: a named slot IS a parameter, so two slots of one name — or a slot and a bracket
//! parameter of one name — are the ordinary duplicate-parameter rule's business.

use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;

use crate::common::{parse_errs, try_load_kb_with};

fn loaded(src: &str, why: &str) -> KnowledgeBase {
    try_load_kb_with(src).unwrap_or_else(|errs| panic!("{why}; got: {errs:?}"))
}

fn refused_with(src: &str, needle: &str, why: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: {why}"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{why}; expected a diagnostic containing {needle:?}, got: {errs:?}",
    );
}

/// `owner`'s named requirement slots as `(binder short name, slot position)`.
fn slots_of(kb: &KnowledgeBase, owner_qn: &str) -> Vec<(String, usize)> {
    let sym: Symbol = kb
        .try_resolve_symbol(owner_qn)
        .unwrap_or_else(|| panic!("no symbol {owner_qn}"));
    kb.named_requirement_slots(sym)
        .iter()
        .map(|(b, i)| (kb.resolve_sym(*b).to_owned(), *i))
        .collect()
}

/// The spec vocabulary every program below is written against: one two-slot-able spec,
/// one second spec so the anonymous/named mix is observable, and a carrier.
const SPECS: &str = r#"
  sort Ord
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end
  sort Same
    sort T = ?
    operation same(a: T, b: T) -> Bool
  end
"#;

// ── §9 phase-1 acceptance, the three rows ──────────────────────────────────

/// ACCEPTANCE 1 — "a two-slot op loads". The declaration §4.2 motivates the whole
/// binder with: two slots of the SAME spec, which a short name cannot discriminate
/// (`fold[Ord = …]` would be ambiguous), so each is NAMED.
///
/// The value preconditions on either side of the binders are not decoration — §4.7
/// wrinkle 1 is that the op-scoped `requires` list is OVERLOADED, carrying both spec
/// requirements (WI-448) and value preconditions (WI-539) in one comma list, and a
/// binder must coexist with them AT ANY POSITION of it.
#[test]
fn a_two_slot_operation_loads() {
    let kb = loaded(
        &format!(
            r#"
namespace test.wi840.two_slots
  import anthill.prelude.{{Int64, Bool}}
{SPECS}
  sort Use
    operation biFold(xs: Int64, n: Int64) -> Int64
      requires neq(n, 0), lo: Ord[T = Int64], gt(n, 0), hi: Ord[T = Int64]
  end
end
"#
        ),
        "an operation with two NAMED requirement slots must load",
    );
    // The record, and with it the two facts phase 2 needs: WHICH parameter names WHICH
    // slot. Positions 1 and 3 — the value preconditions at 0 and 2 occupy their own
    // places in the requirement list, so the index is over the whole list, not over the
    // named subset.
    assert_eq!(
        slots_of(&kb, "test.wi840.two_slots.Use.biFold"),
        vec![("lo".to_owned(), 1), ("hi".to_owned(), 3)],
        "both binders must be recorded, at their source-order positions in the \
         operation's requirement list",
    );
}

/// Each binder must also BE a type parameter, or "a named slot is a parameter" is a
/// claim about nothing. Measured through the channel that decides it at a call: an
/// undeclared bracket key is loud, a declared one is not — so `biFold[lo = …]` reaching
/// the parameter is the same event as `biFold[Bogus = …]` being refused.
#[test]
fn a_named_operation_slot_is_a_type_parameter_at_the_bracket() {
    let program = |key: &str| {
        format!(
            r#"
namespace test.wi840.op_bracket
  import anthill.prelude.{{Int64}}
{SPECS}
  sort ByValue
    fact Ord[T = Int64]
    operation cmp(a: Int64, b: Int64) -> Int64 = 0
  end
  sort Use
    operation biFold(n: Int64) -> Int64 requires lo: Ord[T = Int64]
      = n
    operation main(n: Int64) -> Int64 = biFold[{key} = ByValue](n)
  end
end
"#
        )
    };
    loaded(&program("lo"), "the binder must be addressable as a bracket key");
    refused_with(
        &program("Bogus"),
        "unknown type-param 'Bogus'",
        "the CONTROL: an undeclared key on the same call is loud, so the accepted `lo` \
         above measures the binder and not a bracket that swallows everything",
    );
}

/// ACCEPTANCE 2 — "a named sort-level slot is addressable in type position
/// (`Box[E = …, O = …]`)". This is the row that makes §5.3 possible: the witness enters
/// the TYPE, so two differently-ordered `SortedSet`s are two types.
#[test]
fn a_named_sort_slot_is_addressable_in_type_position() {
    let program = |key: &str| {
        format!(
            r#"
namespace test.wi840.sort_slot
  import anthill.prelude.{{Int64}}
{SPECS}
  sort Box
    sort E = ?
    requires Same[T = E]
    requires O: Ord[T = E]
    operation mk(x: E) -> Box[E = E, {key} = O]
  end
end
"#
        )
    };
    let kb = loaded(
        &program("O"),
        "a named sort-level slot must be bindable in a type application",
    );
    assert_eq!(
        kb.type_params_of_sort(kb.try_resolve_symbol("test.wi840.sort_slot.Box").unwrap()),
        vec!["E".to_owned(), "O".to_owned()],
        "the binder must join the sort's DECLARED type parameters, in source order — \
         positional bindings (`Box[Int64, ByValue]`) read that order",
    );
    assert_eq!(
        slots_of(&kb, "test.wi840.sort_slot.Box"),
        vec![("O".to_owned(), 1)],
        "the sort-level binder is recorded at its position among the sort's `requires` \
         items — the ANONYMOUS `Same` slot at 0 counts, or the position would index the \
         named subset rather than the requirement list",
    );
    refused_with(
        &program("Bogus"),
        "has no type parameter named 'Bogus'",
        "the CONTROL: `check_sort_type_args` still refuses an undeclared key on the \
         same application, so the accepted `O` measures the binder",
    );
}

/// ACCEPTANCE 3, rung (2) — a type parameter colliding with one of the operation's own
/// requirement SPEC SHORT NAMES. §4.2's rule (2) resolves a bracket key by exactly that
/// short name, so `fold[Ord = …]` would name both the parameter and the slot.
///
/// The requirement is written QUALIFIED here, deliberately: that is the spelling where
/// the two channels genuinely both answer `Ord`. The bare spelling is a DIFFERENT and
/// more common failure (the parameter captures the goal's head outright) with its own
/// diagnosis, measured in the next test — one guard, two diagnoses, because after the
/// capture there is no spec left to be ambiguous with.
#[test]
fn a_type_param_colliding_with_its_own_requirement_spec_is_refused() {
    refused_with(
        &format!(
            r#"
namespace test.wi840.collide_spec
  import anthill.prelude.{{Int64}}
{SPECS}
  sort Use
    operation fold[Ord](n: Int64) -> Int64
      requires test.wi840.collide_spec.Ord[T = Int64]
  end
end
"#
        ),
        "type parameter `Ord` collides with the SHORT name of its own requirement \
         `test.wi840.collide_spec.Ord`",
        "an op type param named after one of its own requirement specs is refused at \
         the DECLARATION",
    );
}

/// The same guard, the bare spelling — and the reason it needs a diagnosis of its own.
/// `requires Ord[…]` beside `[Ord]` resolves `Ord` in the OPERATION's scope, where
/// `scan_operation_params` has already defined the parameter, so the clause requires
/// the parameter and no spec at all. Reporting that as "two targets for one bracket
/// key" would name a spec (`…fold.Ord`) that is the parameter itself.
#[test]
fn a_type_param_capturing_its_own_requirements_head_is_refused() {
    refused_with(
        &format!(
            r#"
namespace test.wi840.capture_spec
  import anthill.prelude.{{Int64}}
{SPECS}
  sort Use
    operation fold[Ord](n: Int64) -> Int64 requires Ord[T = Int64]
  end
end
"#
        ),
        "collides with the head of its own `requires Ord…` goal, which now resolves to \
         THIS PARAMETER",
        "a type parameter that captures its own requires clause's head is refused, and \
         diagnosed as the capture it is",
    );
}

/// ACCEPTANCE 3, rung (1) — a type parameter colliding with the ENCLOSING SORT's. Rule
/// (1) spans both scopes once phase 2 adds the sort-level seeding leg, so one key would
/// have two targets.
#[test]
fn a_type_param_colliding_with_its_enclosing_sorts_is_refused() {
    refused_with(
        r#"
namespace test.wi840.collide_sort_param
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    operation mk[T](x: Int64) -> Int64 = x
  end
end
"#,
        "collides with the type parameter `T` of its enclosing sort",
        "an op type param named after one of its enclosing sort's is refused at the \
         DECLARATION",
    );
}

/// The same rung, reached through a SORT-LEVEL NAMED SLOT — §4.2 says the guard covers
/// the enclosing sort's parameters "including a sort-level named requirement slot", and
/// that clause is only true because §4.7 made the slot a parameter. Distinct from the
/// row above: nothing here is written `sort O = ?`.
#[test]
fn a_type_param_colliding_with_a_sort_level_named_slot_is_refused() {
    refused_with(
        &format!(
            r#"
namespace test.wi840.collide_named_slot
  import anthill.prelude.{{Int64}}
{SPECS}
  sort Box
    sort E = ?
    requires O: Ord[T = E]
    operation mk[O](x: E) -> E = x
  end
end
"#
        ),
        "collides with the type parameter `O` of its enclosing sort",
        "a sort-level NAMED slot is a type parameter of the sort, so an operation may \
         not redeclare its name",
    );
}

/// The third source, §4.2's spec-op clause: a spec's own operation may not declare a
/// type parameter named after the SPEC, because a direct spec-op call selects the
/// dictionary backing it by that very key (`Desc.describe[Desc = LoudDesc](w)`).
#[test]
fn a_spec_op_type_param_named_after_its_spec_is_refused() {
    refused_with(
        r#"
namespace test.wi840.collide_own_spec
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe[Desc](w: T) -> Int64
  end
end
"#,
        "collides with its own spec",
        "a spec op declaring a type parameter named after its spec would shadow the \
         direct-dispatch key",
    );
}

/// THE CONTROL for all four refusals above, and the one that keeps them from being a
/// blanket ban on operation type parameters inside a spec sort: a non-colliding name in
/// the very same shapes loads. Without this a guard that refused every op type param
/// would pass every test above.
#[test]
fn a_non_colliding_type_param_still_loads_in_all_four_shapes() {
    loaded(
        &format!(
            r#"
namespace test.wi840.no_collision
  import anthill.prelude.{{Int64}}
{SPECS}
  sort Box
    sort E = ?
    requires O: Ord[T = E]
    operation mk[U](x: U) -> U = x
  end
  sort Desc
    sort T = ?
    operation describe[U](w: U) -> Int64
  end
  sort Use
    operation fold[U](n: U) -> U requires Ord[T = U]
      = n
  end
end
"#
        ),
        "a type parameter that collides with nothing must still load — inside a spec \
         sort, beside a sort-level named slot, and beside its own requirement",
    );
}

// ── The refusals and controls the desugar itself needs ─────────────────────

/// A named slot only means something where there is a sort to parameterize. At
/// namespace or file level `scan_items_pass1` would define the binder as an ordinary
/// nested sort (`is_type_param && is_sort_scope`), leaving a name addressable in no
/// bracket and selectable at no call — the silent drop this arc exists to remove.
///
/// Refused at the CONVERTER, so this asserts a PARSE diagnostic: the verdict needs
/// only the surface (is the owner a sort body?), and the load-time twin was not
/// equivalent. Driven: with the refusal at load, `anthill codegen rust` on this exact
/// program reported `0 errors` and emitted `struct O;` — `generate_rust` takes a
/// `&ParsedFile` and never loads a KB, so the spliced type parameter reached codegen
/// and MATERIALIZED a host artifact from a declaration the language rejects. That is
/// WI-850's rationale with a sharper cost than WI-850 had.
#[test]
fn a_named_slot_outside_a_sort_is_refused() {
    let errs = parse_errs(&format!(
        r#"
namespace test.wi840.namespace_slot
  import anthill.prelude.{{Int64}}
{SPECS}
  requires O: Ord[T = Int64]
end
"#
    ));
    assert!(
        errs.iter().any(|e| e.contains("only meaningful on a SORT")),
        "a namespace has no type parameters, so a named slot there would record a name \
         with no channel; got: {errs:?}",
    );
}

/// THE COUPLING THE RECORDED POSITION DEPENDS ON, made a test rather than a comment.
///
/// The sort-level index is produced by `load_items`' walk and is claimed to index
/// `SortInfo.requires`, which `load_sort_with_body` builds in a SECOND walk over the
/// same `s.items`. Nothing in the code makes the two agree — they are two functions
/// apart — so this asserts it.
///
/// It matters because a nearby candidate is measurably WRONG: the `SortRequiresInfo`
/// FACT order is a permutation of the source order. `resolve_requires_bindings`
/// retracts and re-asserts every requirement whose op bindings it completes, moving it
/// to the end of the functor index — so the program below, whose FIRST requirement is
/// completed and whose second is not, comes back `Marker, Ord` as facts while
/// `SortInfo.requires` stays `Ord, Marker`. A reader that took `direct_requires`'
/// enumeration for the referent would resolve `O` to the wrong requirement.
#[test]
fn the_sort_level_slot_position_indexes_sort_info_requires() {
    let kb = loaded(
        r#"
namespace test.wi840.coupling
  import anthill.prelude.{Int64}
  sort Ord
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end
  sort Marker
  end
  sort Box
    sort E = ?
    requires O: Ord[T = E]
    requires Marker
  end
end
"#,
        "a completed and an uncompleted requirement must coexist",
    );
    let slots = slots_of(&kb, "test.wi840.coupling.Box");
    assert_eq!(slots, vec![("O".to_owned(), 0)], "`O` is written first");

    let boxsym = kb.try_resolve_symbol("test.wi840.coupling.Box").unwrap();
    let info = sort_info_requires_bases(&kb, boxsym);
    assert_eq!(
        info.first().map(String::as_str),
        Some("Ord"),
        "`SortInfo.requires[0]` must be the requirement `O` names — this is the list \
         the recorded position indexes; got {info:?}",
    );

    let facts = sort_requires_fact_bases(&kb, boxsym);
    assert_eq!(
        facts,
        vec!["Marker".to_owned(), "Ord".to_owned()],
        "the CONTROL that keeps the coupling above meaningful: the FACT order is NOT \
         source order (retract + re-assert in `resolve_requires_bindings`), so if this \
         ever starts matching, the `named_requirement_slots` doc's warning is stale",
    );
}

/// `sort_sym`'s `SortInfo.requires` spec BASE names, in list order.
fn sort_info_requires_bases(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<String> {
    let info_sym = kb.try_resolve_symbol("anthill.reflect.SortInfo").unwrap();
    for rid in kb.rules_by_functor(info_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let field = |k: &str| {
            named.iter().find(|(s, _)| kb.resolve_sym(*s) == k).map(|(_, t)| *t)
        };
        let (Some(name), Some(reqs)) = (field("name"), field("requires")) else { continue };
        if head_sym(kb, name) != Some(sort_sym) {
            continue;
        }
        return cons_list_bases(kb, reqs);
    }
    Vec::new()
}

/// `sort_sym`'s `SortRequiresInfo` FACT spec bases, in the order the functor index
/// enumerates them — deliberately a different reader from the one above.
fn sort_requires_fact_bases(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<String> {
    let sri = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo").unwrap();
    let mut out = Vec::new();
    for rid in kb.rules_by_functor(sri) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let field = |k: &str| {
            named.iter().find(|(s, _)| kb.resolve_sym(*s) == k).map(|(_, t)| *t)
        };
        let (Some(owner), Some(spec)) = (field("sort_ref"), field("spec")) else { continue };
        if head_sym(kb, owner) != Some(sort_sym) {
            continue;
        }
        out.push(spec_base_name(kb, spec));
    }
    out
}

/// A cons-list of specs → their base names.
fn cons_list_bases(kb: &KnowledgeBase, list: anthill_core::kb::term::TermId) -> Vec<String> {
    use anthill_core::kb::term::Term;
    let mut out = Vec::new();
    let mut cur = list;
    while let Term::Fn { functor, named_args, .. } = kb.get_term(cur) {
        if kb.resolve_sym(*functor) != "cons" {
            break;
        }
        let field = |k: &str| {
            named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == k).map(|(_, t)| *t)
        };
        let (Some(h), Some(t)) = (field("head"), field("tail")) else { break };
        out.push(spec_base_name(kb, h));
        cur = t;
    }
    out
}

/// A requirement's spec base name, through either shape: a `SortView(Ref(Spec), …)`
/// (what a parameterized requirement becomes once its bindings are completed) or the
/// bare spec reference an unparameterized one stays as.
fn spec_base_name(kb: &KnowledgeBase, spec: anthill_core::kb::term::TermId) -> String {
    use anthill_core::kb::term::Term;
    if let Term::Fn { functor, pos_args, .. } = kb.get_term(spec) {
        if kb.resolve_sym(*functor) == "SortView" && !pos_args.is_empty() {
            let inner = pos_args[0];
            return head_sym(kb, inner)
                .map_or_else(|| "?".to_owned(), |f| kb.resolve_sym(f).to_owned());
        }
    }
    head_sym(kb, spec).map_or_else(|| "?".to_owned(), |f| kb.resolve_sym(f).to_owned())
}

/// A term's head functor. `KnowledgeBase::head_functor` is `pub(crate)`, so this local
/// twin keeps the test from widening the crate's API for a test's sake.
fn head_sym(kb: &KnowledgeBase, tid: anthill_core::kb::term::TermId) -> Option<Symbol> {
    use anthill_core::kb::term::Term;
    match kb.get_term(tid) {
        Term::Fn { functor, .. } => Some(*functor),
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// A BARE spec name is a requirement too (`requires Desc`), so the binder must take
/// one — at both levels. Found by driving rather than assumed, and it was broken: the
/// grammar's binder takes a `_type`, which wraps a bare name in `simple_type`, while
/// the anonymous spelling reaches the same name as a rule-body `name` term. Converting
/// the wrapper is what closes the gap; the goal the two spellings build is then the
/// same node.
#[test]
fn a_bare_spec_name_is_a_valid_binder_type_at_both_levels() {
    loaded(
        r#"
namespace test.wi840.bare_binder
  import anthill.prelude.{Int64}
  sort Desc
    operation describe(x: Int64) -> Int64
  end
  sort Box
    sort E = ?
    requires W: Desc
  end
  sort Use
    operation f(n: Int64) -> Int64 requires w: Desc
      = n
  end
end
"#,
        "a bare (unapplied) spec name must be admissible as a named slot's type",
    );
}

/// And the refusal on the other side of it. The binder's grammar takes a full `_type`,
/// but a requirement is a spec — naming a slot names the spec's WITNESS, and an arrow
/// has none. Refused with the shape quoted rather than converted into a goal nothing
/// resolves (repo: loud over silent).
#[test]
fn a_binder_type_that_is_not_a_spec_is_refused() {
    let errs = parse_errs(
        r#"
namespace test.wi840.arrow_binder
  import anthill.prelude.{Int64}
  sort Use
    operation f(n: Int64) -> Int64 requires w: (a: Int64) -> Int64
      = n
  end
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("must name a SPEC")),
        "expected the not-a-spec refusal, got: {errs:?}",
    );
}

/// THE CONTROL that the binder is OPTIONAL and changes nothing when absent: the
/// anonymous forms — sort-level and op-level, in both flavors of the overloaded clause
/// list — keep loading, and record NO slot. `requires_body` is otherwise `rule_body`
/// verbatim precisely so this stays true.
#[test]
fn the_anonymous_forms_are_unchanged_and_record_nothing() {
    let kb = loaded(
        &format!(
            r#"
namespace test.wi840.anonymous
  import anthill.prelude.{{Int64}}
{SPECS}
  sort Box
    sort E = ?
    requires Ord[T = E]
    operation mk(x: E, n: Int64) -> E requires Same[T = E], neq(n, 0)
      = x
  end
end
"#
        ),
        "the anonymous spellings must load exactly as before",
    );
    assert!(
        slots_of(&kb, "test.wi840.anonymous.Box").is_empty(),
        "an anonymous sort-level requirement names no slot",
    );
    assert!(
        slots_of(&kb, "test.wi840.anonymous.Box.mk").is_empty(),
        "an anonymous op-level requirement names no slot",
    );
    assert_eq!(
        kb.type_params_of_sort(kb.try_resolve_symbol("test.wi840.anonymous.Box").unwrap()),
        vec!["E".to_owned()],
        "an anonymous slot is a CONSTRAINT, not a parameter — it must not appear in \
         the sort's type parameters (§4.7: solved, not recorded)",
    );
}

/// A VALUE precondition sharing the clause list is not a requirement slot, so a
/// parameter whose name merely resembles one collides with nothing. The discriminator
/// is `is_value_precondition_clause`'s — a goal head that is not a Sort — and without
/// it the guard would refuse a parameter for standing next to `requires neq(n, 0)`.
///
/// Both halves matter, so both are here. `[U]` beside `requires neq(n, 0)` loads: the
/// predicate contributes no candidate. `[neq]` beside the same clause does NOT — not
/// because a predicate became a slot, but because the parameter CAPTURED the goal's
/// head exactly as a spec name would be captured, leaving a `requires` that proves
/// nothing. Refusing it is the loud-over-silent reading, and the diagnosis says which
/// of the two happened.
#[test]
fn a_value_precondition_contributes_no_candidate_but_its_head_is_still_capturable() {
    loaded(
        r#"
namespace test.wi840.value_precondition
  import anthill.prelude.{Int64}
  sort Use
    operation div[U](a: Int64, b: Int64) -> Int64 requires neq(b, 0)
      = a
  end
end
"#,
        "a value precondition is no requirement slot, so it contributes no bracket key",
    );
    refused_with(
        r#"
namespace test.wi840.value_precondition_captured
  import anthill.prelude.{Int64}
  sort Use
    operation div[neq](a: Int64, b: Int64) -> Int64 requires neq(b, 0)
      = a
  end
end
"#,
        "collides with the head of its own `requires neq…` goal",
        "a parameter that captures a value precondition's predicate is refused too — \
         the clause no longer calls the predicate",
    );
}
