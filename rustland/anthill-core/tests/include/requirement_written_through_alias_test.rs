//! A requirement keeps the alias a binding of it was written through.
//!
//! THE RULE. `requires Show[T = Money]` over `sort Money = Int64` is the requirement `Show[T
//! = Int64]` to everything that reads it — the dispatch that supplies it, the pass that
//! completes its bindings, the index, the scope axiom, a rule over the reflect relation —
//! in a sort's clause and in an operation's. The clause that is stored holds the binding
//! on an occurrence that keeps the name, and a refusal names the requirement as its clause
//! wrote it: `Show[T = Money (Int64)]`. The provision it advises is written at the type
//! alone, `provides Show[T = Int64]`: an alias need not be in scope where a provision goes.
//!
//! HOW. A clause binding written as an alias is lowered to `TypeNode::Aliased`
//! (`Loader::clause_binding_as_written`). A sort's requirement is stored as that value
//! (`Loader::requirement_spec_to_store`); an operation's `requires` goal is converted as a
//! term, and its bindings written through an alias are put back on their occurrences
//! (`Loader::contract_goal_as_written`). Every reader of a requirement takes it through
//! the view.
//!
//! BEFORE. The binding was replaced by the type where it was lowered, and the refusal said
//! `Show[T = Int64]` for a clause that wrote `Money`.
//!
//! A BINDING A CALL FIXES rides the occurrence of the argument's declared type, so a
//! requirement bound at a call is named the same way where that type was declared through
//! an alias: `x: Money` handed to `g[P](x: P) requires Show[T = P]`, or to `Show.show`.
//!
//! CONTROLS — measured, each piece backed out on its own. `the wording row` is
//! `wi_zy11j_alias_typed_value_test::a_requirement_written_at_an_alias_is_asked_at_its_type`,
//! at its refusal.
//!
//!   the node in a clause binding (`Loader::clause_binding_as_written` answering the
//!   type's term for an alias) — FAIL:
//!     an_unsupplied_requirement_is_named_as_its_clause_wrote_it, and the wording row
//!   a sort's requirement stored as the term of its type (`requirement_spec_to_store`
//!   lowering every spec) — FAIL: an_unsupplied_requirement_…, its `sort` rows.
//!   an operation's goal stored as its term (`contract_goal_as_written` answering the
//!   term) — FAIL: an_unsupplied_requirement_…, its `op` rows, and the wording row.
//!   an operation's goal not reading its own bracket (the read in `convert_term`'s
//!   application arm skipped) — FAIL: an_unsupplied_requirement_…, the wording row, and
//!     wi_zy11j_alias_typed_value_test::a_clause_binding_at_an_alias_with_an_open_slot_is_asked_at_its_type
//!     wi_zy11j_alias_typed_value_test::a_clause_binding_naming_its_sorts_parameter_through_an_alias_is_about_that_parameter
//!   the refusal naming a requirement by its type alone (`render_requires_entry` through
//!   `format_goal`) — FAIL: an_unsupplied_requirement_…, the wording row, and
//!     a_requirement_bound_at_a_call_names_the_alias_the_argument_was_declared_by, its
//!     `declared` rows
//!   the same for a spec's operation called at a value (`unprovided_spec_at_carrier`
//!   through `format_goal`) — FAIL: a_requirement_bound_at_a_call_…, its `called` rows.
//!   an alias inside a binding's type not named (`format_binding_for_goal` handing its
//!   children on unasked) — FAIL: an_unsupplied_requirement_…, its `nested` rows.
//!   the advised provision taken from the requirement's own text (the advice printing
//!   `dep_text`) — FAIL: an_unsupplied_requirement_…, and the wording row.
//!   with the stored requirement holding its node, each of these reading a term alone:
//!     the completion of a requirement's bindings (`resolve_requires_bindings` skipping a
//!     fact that is no term) — FAIL:
//!       a_requirement_written_through_an_alias_is_completed_as_its_type_is
//!     the scope axiom's registration (skipping the same) — FAIL:
//!       a_requirement_written_through_an_alias_has_its_scope_axiom, and `anthill-cli`'s
//!       check_scope_axiom_requires_test (no record to check)
//!     `anthill check` reading the relation (refusing a row that is no term) — FAIL:
//!       `anthill-cli`'s check_scope_axiom_requires_test
//!     the written-row check (`all_spec_clause_views` through `sort_clause_fields`) —
//!     FAIL: a_row_beside_a_binding_written_through_an_alias_is_judged
//!   a reader that keeps a term taking only a spec that is one already
//!   (`plain_spec_term` answering for `Value::Term` alone) — FAIL:
//!     a_sorts_record_lists_a_requirement_written_through_an_alias_at_its_type
//!     a_provides_block_with_a_binding_written_through_an_alias_loads
//!   …and taking a spec that holds a value (`plain_spec_term` without
//!   `type_holds_a_value`) — FAIL:
//!     wi366_value_in_type_facts_test::provides_block_value_in_type_spec_loads_without_panic
//!
//!   DRIVEN BY THE NODE-CARRIER CONTROL (`ANTHILL_TEST_NODE_CARRIER=1`, where a plain
//!   sort rides a node too) and by no row without it: the occurrence built only for a
//!   sort applied to arguments (`term_read_through_aliases` without
//!   `is_a_type_application`) — a PANIC, "base must be a sort reference", in four rows of
//!   `wi_pyns2_written_row_type_argument_test` and four of `wi_v25n3_written_row_label_test`,
//!   whose `requires Spec[E = {B}]` holds the sort under a row's constructors. A row in a
//!   bracket reads its own aliases where it is lowered, so no alias reaches that walk
//!   under one without the switch.
//!
//!   two clauses of one requirement told apart by their carrier (`collect_sort_requires`
//!   pushing every fact) — FAIL:
//!     one_requirement_written_in_two_spellings_is_one_slot, its `both` and `reversed` rows
//!
//!   PASS EITHER WAY, by design:
//!     a_requirement_written_through_an_alias_is_supplied_as_its_type_is — the fence: what
//!       a requirement asks for is the same before and after, and in both spellings;
//!     one_requirement_written_in_two_spellings_is_supplied_once — the same, for a sort
//!       or an operation that writes both;
//!     the `written` half of every row — a type written out names no alias.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;
use smallvec::SmallVec;

use crate::common::{interp_for, load_errors_of, load_kb_with};

fn source(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Int64, String, Bool, List, Error}}
  sort Money = Int64
  sort Oops = String
  sort Box
    sort V = ?
    entity mk(v: V)
  end
  sort IntBox = Box[V = Int64]
  sort Show[T]
    operation show(x: T) -> Int64
  end
{body}
end
"#
    )
}

/// A witness that provides `Show` at `Int64`.
const INT_SHOW: &str = "  sort IntShow\n    entity intshow\n    provides Show[T = Int64]\n    \
                        operation show(x: Int64) -> Int64 = x + 1\n  end\n";

/// A spec with a type parameter and a row parameter, and a sort that is no effect kind.
const CHAN: &str = "  sort Chan\n    sort T = ?\n    effects E = ?\n    \
                    operation send(x: T) -> Int64 effects {E, Error} = 1\n  end\n  \
                    sort Beep\n    entity beep\n  end\n";

/// The two places a requirement is written: `Show` required at `at` by an operation `ask`
/// whose parameter is typed `param`, called from `go` with `arg`.
fn levels(at: &str, param: &str, arg: &str) -> [(&'static str, String); 2] {
    [
        (
            "sort",
            format!(
                "  sort Use\n    entity use_\n    requires Show[T = {at}]\n    \
                 operation ask(x: {param}) -> Int64 = Show.show(x)\n  end\n  \
                 operation go() -> Int64 = Use.ask({arg})"
            ),
        ),
        (
            "op",
            format!(
                "  operation ask(x: {param}) -> Int64 requires Show[T = {at}] = Show.show(x)\n  \
                 operation go() -> Int64 = ask({arg})"
            ),
        ),
    ]
}

/// Load, call `test.<ns>.go()`, and hand back the integer it answers.
fn run(ns: &str, body: &str) -> i64 {
    let mut interp = interp_for(&source(ns, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The one refusal of a source that must not load.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
    errs.into_iter().next().unwrap()
}

// ── what a requirement asks for ─────────────────────────────────────────────

/// A requirement written through an alias is supplied by the provision at its type, as
/// the requirement written out is — in a sort's clause and in an operation's.
#[test]
fn a_requirement_written_through_an_alias_is_supplied_as_its_type_is() {
    for (spelling, at) in [("alias", "Money"), ("written", "Int64")] {
        for (level, body) in levels(at, "Int64", "5") {
            let ns = format!("rwasup{level}{spelling}");
            assert_eq!(run(&ns, &format!("{INT_SHOW}{body}")), 6, "{ns}");
        }
    }
}

/// One requirement written twice, in either spelling or in both, is one requirement: the
/// call is supplied once and runs.
#[test]
fn one_requirement_written_in_two_spellings_is_supplied_once() {
    for (spelling, first, second) in [
        ("both", "Money", "Int64"),
        ("written", "Int64", "Int64"),
        ("aliases", "Money", "Money"),
    ] {
        let ns = format!("rwatwicesort{spelling}");
        let body = format!(
            "{INT_SHOW}  sort Use\n    entity use_\n    requires Show[T = {first}]\n    \
             requires Show[T = {second}]\n    \
             operation ask(x: Int64) -> Int64 = Show.show(x)\n  end\n  \
             operation go() -> Int64 = Use.ask(5)"
        );
        assert_eq!(run(&ns, &body), 6, "{ns}");

        let ns = format!("rwatwiceop{spelling}");
        let body = format!(
            "{INT_SHOW}  operation ask(x: Int64) -> Int64\n    \
             requires Show[T = {first}], Show[T = {second}] = Show.show(x)\n  \
             operation go() -> Int64 = ask(5)"
        );
        assert_eq!(run(&ns, &body), 6, "{ns}");
    }
}

/// …and one slot of the sort's requirements, whichever spelling comes first: the clause
/// written through the alias is held on another carrier than its written-out twin, and
/// the two are compared as the requirement they state.
#[test]
fn one_requirement_written_in_two_spellings_is_one_slot() {
    for (spelling, first, second) in [
        ("both", "Money", "Int64"),
        ("reversed", "Int64", "Money"),
        ("written", "Int64", "Int64"),
        ("aliases", "Money", "Money"),
    ] {
        let ns = format!("rwaslots{spelling}");
        let body = format!(
            "{INT_SHOW}  sort Use\n    entity use_\n    requires Show[T = {first}]\n    \
             requires Show[T = {second}]\n    \
             operation ask(x: Int64) -> Int64 = Show.show(x)\n  end"
        );
        let mut kb = load_kb_with(&source(&ns, &body));
        let sort = kb.resolve_symbol(&format!("test.{ns}.Use"));
        let slots = anthill_core::kb::typing::direct_requires_chain(&mut kb, sort);
        assert_eq!(slots.len(), 1, "{ns}");
    }
}

// ── the name in a refusal ───────────────────────────────────────────────────

/// A requirement nothing supplies is named as its clause wrote it — the alias first, the
/// type it stands for beside it, at any depth — and the provision the refusal advises is
/// written at the type alone.
#[test]
fn an_unsupplied_requirement_is_named_as_its_clause_wrote_it() {
    // (row, the binding, the parameter's type, the argument, how the refusal names the
    // binding, the binding in the advised provision); `NS` is the row's namespace.
    let rows = [
        ("alias", "Money", "Int64", "5", "NS.Money (anthill.prelude.Int64)", "anthill.prelude.Int64"),
        ("written", "Int64", "Int64", "5", "anthill.prelude.Int64", "anthill.prelude.Int64"),
        (
            "nested",
            "Box[V = Money]",
            "Box[V = Int64]",
            "Box.mk(5)",
            "NS.Box[V = NS.Money (anthill.prelude.Int64)]",
            "NS.Box[V = anthill.prelude.Int64]",
        ),
        (
            "nestedwritten",
            "Box[V = Int64]",
            "Box[V = Int64]",
            "Box.mk(5)",
            "NS.Box[V = anthill.prelude.Int64]",
            "NS.Box[V = anthill.prelude.Int64]",
        ),
        (
            "applied",
            "IntBox",
            "Box[V = Int64]",
            "Box.mk(5)",
            "NS.IntBox (NS.Box[V = anthill.prelude.Int64])",
            "NS.Box[V = anthill.prelude.Int64]",
        ),
    ];
    for (row, at, param, arg, named, provided) in rows {
        for (level, body) in levels(at, param, arg) {
            let ns = format!("rwauns{level}{row}");
            let qualified = |text: &str| text.replace("NS", &format!("test.{ns}"));
            let rendered = refusal(&ns, &body);
            let requirement = format!("requirement `test.{ns}.Show[T = {}]`", qualified(named));
            assert!(rendered.contains(&requirement), "{ns}: wants {requirement}: {rendered}");
            let advice = format!("declare `provides test.{ns}.Show[T = {}]`", qualified(provided));
            assert!(rendered.contains(&advice), "{ns}: wants {advice}: {rendered}");
        }
    }
}

/// A requirement's binding that a CALL fixes is named the same way: where the argument's
/// type was declared through an alias, the refusal leads with that alias — for a
/// requirement an operation declares of its own parameter, and for a spec's operation
/// called at the value.
#[test]
fn a_requirement_bound_at_a_call_names_the_alias_the_argument_was_declared_by() {
    for (spelling, ty, named) in [
        ("alias", "Money", "NS.Money (anthill.prelude.Int64)"),
        ("written", "Int64", "anthill.prelude.Int64"),
    ] {
        let rows = [
            (
                "declared",
                format!(
                    "  operation g[P](x: P) -> Int64 requires Show[T = P] = Show.show(x)\n  \
                     operation via(x: {ty}) -> Int64 = g(x)"
                ),
            ),
            ("called", format!("  operation via(x: {ty}) -> Int64 = Show.show(x)")),
        ];
        for (row, body) in rows {
            let ns = format!("rwacall{row}{spelling}");
            let rendered = refusal(&ns, &body);
            let requirement = format!(
                "requirement `test.{ns}.Show[T = {}]`",
                named.replace("NS", &format!("test.{ns}"))
            );
            assert!(rendered.contains(&requirement), "{ns}: wants {requirement}: {rendered}");
            let advice = format!("declare `provides test.{ns}.Show[T = anthill.prelude.Int64]`");
            assert!(rendered.contains(&advice), "{ns}: wants {advice}: {rendered}");
        }
    }
}

// ── the readers of a stored requirement ─────────────────────────────────────

fn make_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

/// The specs of the `requires` clauses written on `sort_qn`, as the resolver answers the
/// reflect relation — each on whichever carrier it rides.
fn required_specs(kb: &mut KnowledgeBase, sort_qn: &str) -> Vec<Value> {
    let sort_term = kb.resolve_qualified_name_term(sort_qn);
    let var_inst = make_var(kb, "inst");
    let requires_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
    let sort_ref_sym = kb.intern("sort_ref");
    let spec_sym = kb.intern("spec");
    let goal = kb.alloc(Term::Fn {
        functor: requires_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(sort_ref_sym, sort_term), (spec_sym, var_inst)]),
    });
    let config = ResolveConfig {
        max_solutions: 10,
        ..ResolveConfig::default()
    };
    let solutions = kb.resolve(&[goal], &config);
    solutions
        .iter()
        .map(|s| kb.reify(var_inst, &s.subst))
        .collect()
}

/// The qualified name a type or an operation reference is headed by.
fn head_name<V: TermView>(kb: &KnowledgeBase, v: &V) -> String {
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(name),
            ..
        }
        | ViewHead::Ident(name) => kb.qualified_name_of(name).to_owned(),
        other => format!("{other:?}"),
    }
}

const MONOID_USE: &str = "  sort Monoid[T]\n    operation combine(a: T, b: T) -> T\n    \
                          operation identity() -> T\n  end\n  \
                          sort Use\n    entity use_\n    requires Monoid[T = AT]\n    \
                          operation combine(a: Int64, b: Int64) -> Int64 = a + b\n    \
                          operation identity() -> Int64 = 0\n  end";

/// A requirement written through an alias is completed as the one written out is: the
/// spec's operations the requiring sort declares by name are bound to them, and the type
/// binding is the type.
#[test]
fn a_requirement_written_through_an_alias_is_completed_as_its_type_is() {
    for (spelling, at) in [("alias", "Money"), ("written", "Int64")] {
        let ns = format!("rwacomp{spelling}");
        let mut kb = load_kb_with(&source(&ns, &MONOID_USE.replace("AT", at)));
        let specs = required_specs(&mut kb, &format!("test.{ns}.Use"));
        assert_eq!(specs.len(), 1, "{ns}: one requirement");
        let mut bindings: Vec<String> = specs[0]
            .named_keys(&kb)
            .into_iter()
            .map(|key| {
                let value = specs[0].named_arg(&kb, key).expect("a listed key");
                format!("{} = {}", kb.local_name_of(key), head_name(&kb, &value))
            })
            .collect();
        bindings.sort();
        assert_eq!(
            bindings,
            [
                "T = anthill.prelude.Int64".to_owned(),
                format!("combine = test.{ns}.Use.combine"),
                format!("identity = test.{ns}.Use.identity"),
            ],
            "{ns}"
        );
    }
}

/// The scope-axiom records of namespace `test.<ns>`, printed.
fn scope_axiom_records(kb: &KnowledgeBase, ns: &str) -> Vec<String> {
    let record_sym = kb.resolve_symbol("anthill.realization.ProofRecord");
    let printer = TermPrinter::new(kb);
    kb.rules_by_functor(record_sym)
        .into_iter()
        .map(|rid| printer.print_term(kb.rule_head(rid)))
        .filter(|record| record.contains(&format!("test.{ns}.")))
        .collect()
}

/// …and has the scope axiom the one written out has, named by the type — beside a
/// binding that holds a value too, which the name says by the value.
#[test]
fn a_requirement_written_through_an_alias_has_its_scope_axiom() {
    for (spelling, at) in [("alias", "Money"), ("written", "Int64")] {
        let ns = format!("rwaaxiom{spelling}");
        let kb = load_kb_with(&source(&ns, &MONOID_USE.replace("AT", at)));
        let wanted = format!("rule: \"test.{ns}.Use.requires.Monoid_Int64\"");
        let records = scope_axiom_records(&kb, &ns);
        assert!(
            records.iter().any(|record| record.contains(&wanted)),
            "{ns}: wants {wanted}: {records:#?}"
        );

        let ns = format!("rwaaxiomvalue{spelling}");
        let body = format!(
            "  sort Tagged\n    sort T = ?\n    sort N = ?\n  end\n  \
             sort Holds\n    entity holds\n    requires Tagged[T = {at}, N = 3]\n  end"
        );
        let kb = load_kb_with(&source(&ns, &body));
        let wanted = format!("rule: \"test.{ns}.Holds.requires.Tagged_den_i3_Int64\"");
        let records = scope_axiom_records(&kb, &ns);
        assert!(
            records.iter().any(|record| record.contains(&wanted)),
            "{ns}: wants {wanted}: {records:#?}"
        );
    }
}

/// The requirement a sort's own record lists (`SortInfo.requires`) is the type's in both
/// spellings: a binding written through an alias is the type it stands for there.
#[test]
fn a_sorts_record_lists_a_requirement_written_through_an_alias_at_its_type() {
    use anthill_core::kb::op_info::head_field_term;
    let listed = |spelling: &str, at: &str| {
        let ns = format!("rwainfo{spelling}");
        let kb = load_kb_with(&source(&ns, &MONOID_USE.replace("AT", at)));
        let sort_info = kb.resolve_symbol("anthill.reflect.SortInfo");
        let wanted = format!("test.{ns}.Use");
        let requires = kb
            .rules_by_functor(sort_info)
            .into_iter()
            .find_map(|rid| {
                let head = kb.rule_head_value(rid);
                let name = head_field_term(&kb, head, "name")?;
                (anthill_core::kb::load::qn_of_sort_ref(&kb, name)? == wanted)
                    .then(|| head_field_term(&kb, head, "requires"))?
            })
            .unwrap_or_else(|| panic!("{ns}: `Use` has a record with a `requires` list"));
        TermPrinter::new(&kb).print_term(requires).replace(&ns, "NS")
    };
    let written = listed("written", "Int64");
    assert!(written.contains("Monoid") && written.contains("Int64"), "{written}");
    assert_eq!(listed("alias", "Money"), written);
}

/// A standalone `provides` block whose spec has a binding written through an alias is the
/// block at the type: it loads as the one written out does.
#[test]
fn a_provides_block_with_a_binding_written_through_an_alias_loads() {
    for (spelling, at) in [("alias", "Money"), ("written", "Int64")] {
        let ns = format!("rwablock{spelling}");
        let body = format!(
            "  sort Stack\n    sort T = ?\n    entity push(x: Int64)\n  end\n  \
             provides Stack[T = {at}]\n    language rust\n    artifact \"src/stack.rs\"\n  end"
        );
        assert_eq!(load_errors_of(&source(&ns, &body)), Vec::<String>::new(), "{ns}");
    }
}

/// A row binding beside a binding written through an alias is judged as it is beside one
/// written out: a label that is no effect kind is refused, once, in a sort's clause and in
/// an operation's.
#[test]
fn a_row_beside_a_binding_written_through_an_alias_is_judged() {
    for (spelling, at) in [("alias", "Money"), ("written", "Int64")] {
        let clause = format!("requires Chan[T = {at}, E = {{Beep}}]");
        let levels = [
            ("sort", format!("  sort Needs\n    entity needs\n    {clause}\n  end")),
            ("op", format!("  operation ask(x: Int64) -> Int64 {clause} = 1")),
        ];
        for (level, body) in levels {
            let ns = format!("rwarow{level}{spelling}");
            let rendered = refusal(&ns, &format!("{CHAN}{body}"));
            assert!(
                rendered.contains("is not a REGISTERED effect kind") && rendered.contains("`Beep`"),
                "{ns}: {rendered}"
            );
        }
    }
}
