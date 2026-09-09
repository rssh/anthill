//! WI-20260909-51W18 — a `require[X]` / `requires(X)` keeps the spec's TYPE ARGUMENTS.
//!
//! `requirement-channel.md` §10 item 1, whose answer is written at
//! `docs/design/060-implementation.md` §8.6. Both producers used to call
//! `strip_spec_type_args`, which rebuilt the spec instance as a bare nullary `Fn`, so
//! `require[Desc]` and `require[Desc[T = Leaf]]` were BYTE-IDENTICAL after convert — the
//! reason two `requires` on one spec base are refused as unattributable, and the reason
//! writing `require[FiniteCollection[C = List[T = String]]]` said nothing the witness did
//! not.
//!
//! ## What this file drives, and what it deliberately does NOT claim
//!
//! It drives RETENTION: the written binding survives convert, both loader walks, and the
//! typer's rewrite, and is READABLE on the stored goal. **Nothing consumes it yet** — the
//! anchor that reads it is WI-20260909-QMFC5 (S2). So this file asserts a SHAPE, and says
//! so; a green suite here is not evidence that any program dispatches differently, and no
//! test here claims one does.
//!
//! ## The three rungs, and which rows fail when each is backed out
//!
//! MEASURED by mutating each site on the delivered code and re-running this file; the
//! counts below are that run's, not a prediction.
//!
//!  * **RETENTION** — `build_require_spec_occurrence` emits a bare base (the observable
//!    the old convert-time strip produced). **3 fail**:
//!    [`a_written_binding_survives_onto_the_stored_goal`],
//!    [`the_check_tier_keeps_its_binding_too`] and
//!    [`the_positional_spelling_binds_the_same_way`]. The last is on this axis only
//!    because `stored_bindings` reports POSITIONALS too — listing named args alone made
//!    it read `[]`, identical to the bare row, and it measured nothing. Caught by running
//!    this back-out, which is why the reader is shaped the way it is.
//!  * **THE DROP** — `require_spec_binding_occurrence` falls back to the ordinary value
//!    walk when the name denotes no sort, instead of dropping the binding. **3 fail
//!    here**: [`a_free_type_parameter_is_dropped`],
//!    [`a_name_that_denotes_nothing_is_dropped_too`] and
//!    [`the_free_parameter_spelling_answers_as_the_bare_one_does`] — and **33 fail
//!    ELSEWHERE in this binary**, which is the population this rung actually protects:
//!    `wi1040_require_clause_dictionary_test` 9, `wi625_sld_eval_bridge_test` 7,
//!    `wi_x9pb4_require_dictionary_element_test` 6,
//!    `wi1045_one_dictionary_representation_test` 5, `kernel_mint_address_test` 3,
//!    `wi1098_derive_eq_total_test` 2, `wi642_rule_body_requires_test` 1. They are NOT
//!    duplicated here: the point of the rung is that they keep passing UNCHANGED, and a
//!    copy would measure this file instead of them.
//!  * **THE WHOLE ARM** — the `spec_instance_slot` gate in
//!    `build_body_atom_occurrence_inner`. **4 fail**: the DROP's three PLUS
//!    [`a_head_introduced_type_variable_resolves_inside_the_bracket`]. Note which rows do
//!    NOT move: the three RETENTION rows still pass, because once the converter stops
//!    stripping, the ordinary walk lowers a CONCRETE binding correctly on its own —
//!    `Leaf` resolves as a value too. So this arm's job is precisely the names that do
//!    NOT resolve as values: the drop, and the head-introduced type variable.
//!
//! ## One walk, not two — measured, and the term-side twin was deleted
//!
//! A first cut also wrote the TERM-side lowering (`convert_term_inner`'s `Term::Fn` arm),
//! on WI-742 §2.1's precedent that a rule's head rides one walk and its body the other.
//! **Nothing drives it**: the whole binary passed with that arm disabled, because a rule
//! BODY is stored as occurrences (WI-246 — "the term body is gone") and `require[…]` is
//! legal only as a body goal. It was deleted rather than kept as an undrivable branch;
//! `build_require_spec_occurrence`'s own doc records what a future term-path user would
//! get instead.
//!
//! [`the_bare_spelling_is_unchanged`] passes under ALL THREE back-outs BY DESIGN — it
//! writes no bracket at all. It is the yardstick, not a duplicate.

use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

/// A spec `Desc` whose default answers `1` and a carrier `Leaf` supplying `7`, so a
/// dispatch assertion cannot be satisfied by accident. `tail` is the clause under test.
fn program(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact seed(leaf())
{tail}end
"#
    )
}

/// The clause shape every retention row shares: a grounded requirement (the witness call
/// is `Desc.describe`, which is what keeps the rule loadable while the anchor does not
/// exist yet) whose spec instance is `spec`.
fn with_spec(ns: &str, spec: &str) -> String {
    program(
        ns,
        &format!("  rule answer(?r) :- ?d = require[{spec}], seed(?x), Desc.describe(?x, ?r)\n"),
    )
}

/// The BINDINGS on the stored `find_dictionary` goal's spec-instance slot, as
/// `(param, value)` local names — the shape the typer's rewrite leaves behind.
///
/// POSITIONALS ARE REPORTED TOO, keyed `#0`, `#1`, …, and that is not cosmetic: a reader
/// that listed only named args would report `[]` for `Desc[Leaf]` — indistinguishable
/// from the bare `Desc` and from the stripped reading this ticket removes — so the
/// positional row would have measured nothing. Caught by running the back-out.
///
/// Reads slot 0 of the REWRITTEN goal (`find_dictionary(spec_instance, op, args…)`).
/// `None` when no such goal is stored at all, which is distinct from `Some(vec![])` (the
/// goal is there and carries no binding) — a test that conflated the two would pass on a
/// program whose requirement vanished.
fn stored_bindings(kb: &KnowledgeBase, rule_qn: &str) -> Option<Vec<(String, String)>> {
    let head_sym = kb.try_resolve_symbol(rule_qn)?;
    for rid in kb.live_rule_ids() {
        let anthill_core::eval::Value::Term { id: head, .. } = *kb.rule_head_value(rid) else {
            continue;
        };
        if !matches!(kb.get_term(head), Term::Fn { functor, .. } if *functor == head_sym) {
            continue;
        }
        for node in kb.rule_body_nodes(rid) {
            let Some(Expr::Apply {
                functor, pos_args, ..
            }) = node.as_expr()
            else {
                continue;
            };
            if !kb.qualified_name_of(*functor).ends_with("find_dictionary") {
                continue;
            }
            let slot = pos_args.first()?;
            let name_of = |v: &Rc<NodeOccurrence>| match v.as_expr() {
                Some(Expr::Ref(s)) | Some(Expr::Ident(s)) => kb.local_name_of(*s).to_owned(),
                other => format!("{other:?}"),
            };
            return Some(match slot.as_expr() {
                Some(Expr::Apply {
                    pos_args: bp,
                    named_args: bn,
                    ..
                }) => bp
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (format!("#{i}"), name_of(v)))
                    .chain(
                        bn.iter()
                            .map(|(k, v)| (kb.local_name_of(*k).to_owned(), name_of(v))),
                    )
                    .collect(),
                // A bare `Ref(Desc)` — no bracket was written, or every binding dropped.
                _ => Vec::new(),
            });
        }
    }
    None
}

/// The single Int answer of `{ns}.answer`, driven as an SLD goal. Panics on any other
/// shape including `[]` — "returned nothing" must never read as a pass.
fn answer(ns: &str, src: &str) -> i64 {
    let mut kb = crate::common::load_kb_with(src);
    match crate::common::query_unary(&mut kb, &format!("{ns}.answer")).as_slice() {
        [(anthill_core::eval::Value::Int(i), true)] => *i,
        other => panic!("`{ns}.answer` must answer one definite Int, got {other:?}\n{src}"),
    }
}

// ── retention ────────────────────────────────────────────────────────────────

#[test]
fn a_written_binding_survives_onto_the_stored_goal() {
    // THE ROW THIS TICKET EXISTS FOR. Before the un-strip this asserted `[]`, identically
    // to `the_bare_spelling_is_unchanged` below — the two spellings were one term.
    let ns = "test.w51w18.named";
    let kb = crate::common::load_kb_with(&with_spec(ns, "Desc[T = Leaf]"));
    assert_eq!(
        stored_bindings(&kb, &format!("{ns}.answer")),
        Some(vec![("T".into(), "Leaf".into())]),
        "the written `T = Leaf` must reach the stored goal",
    );
}

#[test]
fn the_positional_spelling_binds_the_same_way() {
    // `Desc[Leaf]` is the positional surface of the row above, and it lands on the SAME
    // named slot — positionals are paired with the spec's declared params by index, the
    // language's own rule (`canonicalize_fact_binding_value`,
    // `op_requires_entry_carrier_map`). Two spellings, one internal form.
    //
    // A FIRST CUT KEPT POSITIONALS POSITIONAL, and that was a defect `/code-review`
    // found and [`a_dropped_positional_does_not_re_index_the_others`] now pins: a DROPPED
    // positional silently shifted the ones after it. This row asserted `#0` then, so it
    // moved when the fix landed — which is what the assertion was for.
    let ns = "test.w51w18.pos";
    let kb = crate::common::load_kb_with(&with_spec(ns, "Desc[Leaf]"));
    assert_eq!(
        stored_bindings(&kb, &format!("{ns}.answer")),
        Some(vec![("T".into(), "Leaf".into())]),
        "a positional binding is paired with the spec's first declared type parameter",
    );
}

/// A two-parameter spec, so a positional binding has a slot it can be shifted OUT of.
fn two_param_program(ns: &str, spec: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    sort U = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact seed(leaf())
  rule answer(?r) :- requires({spec}), seed(?x), Desc.describe(?x, ?r)
end
"#
    )
}

#[test]
fn a_dropped_positional_does_not_re_index_the_others() {
    // FOUND BY `/code-review`, DRIVEN, AND FIXED. With positionals kept positional, the
    // drop rebuilt the list without the dropped entry, so `Desc[Zork, Leaf]` stored
    // `Leaf` — written SECOND — at slot `#0`, attributing it to `T`. A clean load, a
    // definite binding, the WRONG type parameter, and S2 is specified to read exactly
    // this slot.
    //
    // The CONTROL is the row below it: both arguments denoting sorts, which is what says
    // the SHIFT moved and not merely the count.
    // THE DROPPED ARGUMENT IS NOW THE WILDCARD, which is the only spelling that still
    // drops: `T` is `Desc`'s own declared parameter, so `Desc[T, Leaf]` leaves `T` open
    // and binds `Leaf` — written SECOND — to `U`. (`Desc[Zork, Leaf]` used to be this
    // row's fixture; it is REPORTED now, by
    // [`a_name_that_denotes_nothing_is_reported`], so the shift has to be measured on a
    // spelling that still loads.)
    let ns = "test.w51w18.shift";
    let kb = crate::common::load_kb_with(&two_param_program(ns, "Desc[T, Leaf]"));
    assert_eq!(
        stored_bindings(&kb, &format!("{ns}.answer")),
        Some(vec![("U".into(), "Leaf".into())]),
        "`Leaf` was written SECOND, so it binds `U` — a dropped first argument must not \
         promote it to `T`",
    );

    // THE SAME DEFECT FROM THE OTHER SIDE (`/code-review`): the NAMED loop dropped
    // silently and without recording its claim, so the positional skip loop read `T` as
    // free and `Desc[T = T, Leaf]` re-indexed `Leaf` onto `T`. A rule written twice is an
    // asymmetry waiting.
    let ns = "test.w51w18.nshift";
    let kb = crate::common::load_kb_with(&two_param_program(ns, "Desc[T = T, Leaf]"));
    assert_eq!(
        stored_bindings(&kb, &format!("{ns}.answer")),
        Some(vec![("U".into(), "Leaf".into())]),
        "a NAMED binding that drops still claims its slot",
    );

    let ns = "test.w51w18.noshift";
    let kb = crate::common::load_kb_with(&two_param_program(ns, "Desc[Leaf, Leaf]"));
    assert_eq!(
        stored_bindings(&kb, &format!("{ns}.answer")),
        Some(vec![
            ("T".into(), "Leaf".into()),
            ("U".into(), "Leaf".into())
        ]),
    );
}

#[test]
fn a_bogus_parameter_name_and_an_over_application_are_refused() {
    // THE SAME `check_sort_type_args` THE SIBLING WALK RUNS on a nested sort application.
    // This slot bypassed it, so both of these loaded clean and stored the bogus binding —
    // invisible only while nothing read the bracket, which is what this ticket ends. Not
    // a new rule; the shared one, applied at a site that was missing it.
    for (spec, expect) in [
        ("Desc[Bogus = Leaf]", "no type parameter named 'Bogus'"),
        ("Desc[Leaf, Leaf, Leaf]", "over-applied"),
    ] {
        let src = two_param_program("test.w51w18.argck", spec);
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| panic!("`{spec}` must be refused; it loaded clean:\n{src}"))
            .join("\n");
        assert!(
            errs.contains(expect) && errs.contains("invalid type argument"),
            "`{spec}` must be refused as an invalid type argument naming {expect}; got:\n{errs}",
        );
    }
}

#[test]
fn a_dotted_spec_base_names_the_spec_and_not_field_access() {
    // PRE-EXISTING and confirmed so by control, but this function is now where the shape
    // is decided. A dotted base is the converter's minted `field_access` chain, so
    // reading it as an APPLICATION made the grounding scan report "a body call to one of
    // `field_access`'s operations". `parse_arg_type_is_applied` asks
    // `dotted_citation_name` first, which is exactly the discriminator that was missing.
    let ns = "test.w51w18.dotted";
    let src = program(
        ns,
        &format!("  rule answer(?r) :- requires({ns}.Desc), seed(?x), Desc.describe(?x, ?r)\n"),
    );
    let kb = crate::common::load_kb_with(&src);
    assert_eq!(stored_bindings(&kb, &format!("{ns}.answer")), Some(vec![]));
    assert_eq!(answer(ns, &src), 7);
}

#[test]
fn a_written_effect_row_survives_the_bracket() {
    // A `ParseAux` carrier, NOT a name — so the drop rule ("a name that denotes no sort")
    // never covered it, and it vanished with no diagnostic. `lower_effect_row_aux_occ` is
    // the same lowering the ordinary named-arg loop applies (WI-366 B1). Asserted by the
    // KEY's presence: the row's own value shape belongs to that lowering, not to this
    // ticket.
    let ns = "test.w51w18.row";
    let kb = crate::common::load_kb_with(&two_param_program(ns, "Desc[T = Leaf, U = {}]"));
    let got = stored_bindings(&kb, &format!("{ns}.answer")).expect("a stored goal");
    assert_eq!(
        got.iter().map(|(k, _)| k.as_str()).collect::<Vec<_>>(),
        vec!["T", "U"],
        "the written row must keep its slot; got {got:?}",
    );
}

#[test]
fn the_check_tier_keeps_its_binding_too() {
    // ONE RELATION, ONE SPELLING OF THE BRACKET: `requires(X)` is the no-`out` reading of
    // the same goal (WI-1040's "one form, one owner"), so the two producers must retain
    // identically. They are separate call sites, so this is a second back-out and not a
    // restatement of the row above.
    let ns = "test.w51w18.check";
    let kb = crate::common::load_kb_with(&program(
        ns,
        "  rule answer(?r) :- requires(Desc[T = Leaf]), seed(?x), Desc.describe(?x, ?r)\n",
    ));
    assert_eq!(
        stored_bindings(&kb, &format!("{ns}.answer")),
        Some(vec![("T".into(), "Leaf".into())]),
    );
}

#[test]
fn the_bare_spelling_is_unchanged() {
    // THE YARDSTICK: no bracket, so no rung of this ticket can move it. Passes under
    // every back-out BY DESIGN — it is here to say that `Some(vec![])` in the rows above
    // means "the goal is present and carries nothing", not "no goal".
    let ns = "test.w51w18.bare";
    let kb = crate::common::load_kb_with(&with_spec(ns, "Desc"));
    assert_eq!(stored_bindings(&kb, &format!("{ns}.answer")), Some(vec![]));
}

// ── the drop: a name that denotes no sort ────────────────────────────────────

#[test]
fn a_free_type_parameter_is_dropped() {
    // `requires(Eq[T])` in a free rule is the canonical typeclass spelling and its whole
    // point is that `T` is UNCONSTRAINED. Dropping the binding leaves the goal exactly as
    // the old convert-time strip left it, which is what makes this change additive.
    let ns = "test.w51w18.free";
    let kb = crate::common::load_kb_with(&with_spec(ns, "Desc[T]"));
    assert_eq!(stored_bindings(&kb, &format!("{ns}.answer")), Some(vec![]));
}

#[test]
fn a_name_that_denotes_nothing_is_reported() {
    // A TYPO USED TO BE SILENT HERE, recorded as a stated boundary: telling
    // `Desc[T = Zork]` from `Desc[T]` "needs a rule about which names an author may leave
    // open, and inventing one at this site would refuse the stdlib idiom". The rule was
    // not hard to state once `/code-review` showed what the silence cost — the drop was
    // applied to EVERY carrier, so a literal, an entity constructor, a rule name, a
    // logical variable and a tuple all vanished with no diagnostic.
    //
    // THE RULE IS ABOUT NAMES: a value that spells one of the spec's OWN declared
    // parameters is the wildcard (`Desc[T]`, X9PB4); anything else that denotes no sort
    // is a mistake and now says so. A corpus census says the narrow rule costs nothing —
    // every free-name binding that ships spells the spec's own parameter.
    let ns = "test.w51w18.typo";
    let errs = crate::common::try_load_kb_with(&with_spec(ns, "Desc[T = Zork]"))
        .err()
        .unwrap_or_else(|| panic!("expected a refusal"))
        .join("\n");
    assert!(
        errs.contains("`Zork` in it names neither a sort nor one of `Desc`'s own type parameters"),
        "got:\n{errs}"
    );
}

#[test]
fn a_binding_that_is_not_a_name_at_all_is_reported() {
    // THE DRIVEN HALF of the same finding, and the reason the rule had to be stated about
    // NAMES rather than about "a name that denotes no sort": none of these is a name.
    // Each silently vanished, and before the pairing fix each also re-indexed the
    // argument written after it.
    for spelling in [
        "Desc[T = 3]",            // a literal
        "Desc[T = leaf]",         // an entity constructor
        "Desc[T = seed]",         // a rule name
        "Desc[T = ?v]",           // a logical variable in type position
        "Desc[T = (Leaf, Leaf)]", // a tuple type
    ] {
        let ns = "test.w51w18.nn";
        let r = crate::common::try_load_kb_with(&with_spec(ns, spelling));
        assert!(
            r.is_err(),
            "`{spelling}` must be reported, not dropped; it loaded clean",
        );
    }
    // THE CONTROL, and it is the one that keeps the rule narrow: the spec's own declared
    // parameter name is still OPEN, and a real sort is still a binding.
    let ns = "test.w51w18.nnc";
    assert!(crate::common::try_load_kb_with(&with_spec(ns, "Desc[T]")).is_ok());
    assert!(crate::common::try_load_kb_with(&with_spec(ns, "Desc[T = Leaf]")).is_ok());
}

#[test]
fn the_free_parameter_spelling_answers_as_the_bare_one_does() {
    // The BEHAVIOURAL half of the drop, by VALUE and not by shape: `7` is the carrier's
    // own `describe` and `1` is the spec default, so a requirement that stopped being
    // grounded would show as `1` rather than as a failure.
    assert_eq!(
        answer("test.w51w18.b1", &with_spec("test.w51w18.b1", "Desc[T]")),
        7
    );
    assert_eq!(
        answer("test.w51w18.b2", &with_spec("test.w51w18.b2", "Desc")),
        7
    );
    assert_eq!(
        answer(
            "test.w51w18.b3",
            &with_spec("test.w51w18.b3", "Desc[T = Leaf]")
        ),
        7,
        "retaining the binding must not change what the clause answers — nothing reads \
         it yet (the anchor is S2), so a different answer here would be a regression, \
         not a feature",
    );
}

// ── the introducer rung ──────────────────────────────────────────────────────

#[test]
fn a_head_introduced_type_variable_resolves_inside_the_bracket() {
    // `A` is not in scope as a value anywhere; before this ticket the bracket reported
    // `unresolved name 'A'` about a variable the same head introduced. It resolves
    // through `parse_arg_sort_symbol` — the SAME owner the §2.1 parameter form's bound
    // reads — so `A` denotes the sort its `:- Desc[A]` guard bounds it with.
    //
    // THIS ROW MOVED WHEN WI-20260909-QMFC5 LANDED, and that is what it was for. As S1
    // delivered it, the clause still did NOT load: the name resolved but the requirement
    // had no anchor, so it asserted the ABSENCE of the name error beside the PRESENCE of
    // the anchor refusal — honest about which half S1 owned. S2 lifted the second half,
    // so the clause now loads and THREADS, and the row asserts that instead. What it
    // still measures for S1 is the same thing: the introducer resolves inside the
    // bracket, and the binding it resolves to is retained on the stored goal.
    let src = program(
        "test.w51w18.tv",
        "  rule answer(?r) :- anchored(?x, ?d), Desc.describe(?x, ?r)\n  \
         rule anchored[A](?x: A, ?d) :- Desc[A], ?d = require[Desc[T = A]], seed(?x)\n",
    );
    let kb = crate::common::load_kb_with(&src);
    // `A` denotes `Desc` — its guard-given bound — so that is what the retained binding
    // holds. Asserting the VALUE, not merely that something is there: an `A` that failed
    // to resolve would have been dropped by the same rule that drops a free `T`, and this
    // row would then read `[]` and pass for the wrong reason.
    assert_eq!(
        stored_bindings(&kb, "test.w51w18.tv.anchored"),
        Some(vec![("T".into(), "Desc".into())]),
        "the introducer must resolve to its guard-given bound and be retained",
    );
    // AND IT THREADS, asserted BY VALUE. The header said "loads and THREADS" while the
    // only assertion was a stored SHAPE — so if threading stopped and `Desc.describe`
    // fell back to the spec default, the row stayed green. `7` is the carrier's own
    // answer and `1` is that default (`/code-review`).
    assert_eq!(answer("test.w51w18.tv", &src), 7);
}

#[test]
fn a_positional_binds_the_next_param_not_already_named() {
    // FOUND BY `/code-review` ON S2's DIFF, but the defect is this ticket's: positionals
    // were paired with the spec's declared params by RAW INDEX, while the language's rule
    // — `type_expr_to_child_inner`'s `positional_index` loop, and `check_sort_type_args`'s
    // `free` count — is that a positional binds the next param NOT ALREADY BOUND BY NAME.
    //
    // The consequence was not a silent misattribution but a REFUSAL of a valid program:
    // the positional was paired with `T`, which the named arg already claims, and the load
    // failed with "binds the type parameter 'T' more than once". The CONTROL is that the
    // identical spelling in an ordinary type position loads — same surface, same rule, and
    // this site was the only one reading it differently.
    let ns = "test.w51w18.mixed";
    let kb = crate::common::load_kb_with(&two_param_program(ns, "Desc[T = Leaf, Leaf]"));
    assert_eq!(
        stored_bindings(&kb, &format!("{ns}.answer")),
        Some(vec![
            ("T".into(), "Leaf".into()),
            ("U".into(), "Leaf".into())
        ]),
        "the positional must bind `U` — the first param the named arg did not claim",
    );
}

#[test]
fn both_spellings_of_one_slot_key_alike() {
    // WI-1016's rule, one carrier over: `Desc[Leaf]` and `Desc[T = Leaf]` name ONE slot,
    // so they must key it under one `Symbol`. The named loop interns the written short
    // name; the positional loop used to key by the SPEC-QUALIFIED symbol.
    //
    // READ THROUGH THE QUALIFIED NAME, and that is the whole point of this row. An
    // earlier version compared `local_name_of`, which renders BOTH keys as `"T"` — so it
    // passed with the fix backed out and measured nothing. (`Symbol` identity cannot be
    // compared either: the two loads build separate `KnowledgeBase`s.) Backing out the
    // `intern(&n)` at the positional slot makes the first key `test.…Desc.T` and the
    // second `T`, and this row goes red.
    let a = crate::common::load_kb_with(&with_spec("test.w51w18.k1", "Desc[Leaf]"));
    let b = crate::common::load_kb_with(&with_spec("test.w51w18.k2", "Desc[T = Leaf]"));
    let key_qn = |kb: &KnowledgeBase, qn: &str| -> String {
        let head_sym = kb.try_resolve_symbol(qn).expect("the rule");
        for rid in kb.live_rule_ids() {
            let anthill_core::eval::Value::Term { id: head, .. } = *kb.rule_head_value(rid) else {
                continue;
            };
            if !matches!(kb.get_term(head), Term::Fn { functor, .. } if *functor == head_sym) {
                continue;
            }
            for node in kb.rule_body_nodes(rid) {
                let Some(Expr::Apply {
                    functor, pos_args, ..
                }) = node.as_expr()
                else {
                    continue;
                };
                if !kb.qualified_name_of(*functor).ends_with("find_dictionary") {
                    continue;
                }
                if let Some(Expr::Apply { named_args, .. }) =
                    pos_args.first().and_then(|s| s.as_expr())
                {
                    return kb
                        .qualified_name_of(named_args.first().expect("one binding").0)
                        .to_owned();
                }
            }
        }
        panic!("no stored goal for {qn}");
    };
    assert_eq!(
        key_qn(&a, "test.w51w18.k1.answer"),
        key_qn(&b, "test.w51w18.k2.answer"),
    );
}

// ── what `/code-review` found on the second pass, driven and pinned ──────────────────

#[test]
fn a_dropped_argument_is_still_counted_by_the_arity_check() {
    // `check_sort_type_args` was fed the SURVIVING arguments, so the very drop rule it
    // was added to police made over-application invisible. Two spellings of one mistake
    // got two verdicts, decided by an unrelated property of the value:
    //
    //     Desc[Leaf, Leaf]  on a one-parameter spec  → refused ✅
    //     Desc[T, Leaf]     on a one-parameter spec  → loaded clean ❌
    //
    // It now counts what the AUTHOR WROTE. Backing the change out (passing the survivors
    // again) fails the first assert and leaves the control passing.
    let ns = "test.w51w18.arity";
    let errs = crate::common::try_load_kb_with(&with_spec(ns, "Desc[T, Leaf]"))
        .err()
        .unwrap_or_else(|| {
            panic!("a two-argument application of a one-parameter spec must be refused")
        })
        .join("\n");
    assert!(errs.contains("over-applied"), "got:\n{errs}");

    // THE CONTROL: one argument for one parameter, and the wildcard spelling on its own
    // still loads — the count is what moved, not the drop.
    assert!(crate::common::try_load_kb_with(&with_spec(ns, "Desc[T]")).is_ok());
}

#[test]
fn a_positional_effect_row_does_not_parse_at_all() {
    // `/code-review` predicted an asymmetry here: the effect-row arm was on the NAMED
    // loop only, so `Walk[C = Src, E = {}]` would keep the row while `Walk[Src, {}]`
    // dropped it. MEASURED, the positional spelling never reaches the loop — the GRAMMAR
    // refuses it (`unexpected term node: effect_row`), so there is no second surface to
    // disagree with the first.
    //
    // The arm was added to the positional loop anyway, for symmetry with the sibling
    // occurrence walk which has it on both. It is a BACKSTOP and cannot be driven from
    // source; this row is what says so, and what will start failing if the grammar ever
    // admits the spelling.
    let ns = "test.w51w18.erpos";
    let src = two_param_program(ns, "Desc[Leaf, {}]");
    let panicked = std::panic::catch_unwind(|| {
        let _ = crate::common::try_load_kb_with(&src);
    })
    .is_err();
    assert!(
        panicked,
        "a positional effect row is expected to be refused by the PARSER; if this now \
         loads, the backstop arm in the positional loop has become drivable and needs a \
         real assertion",
    );
}

#[test]
fn a_bracketed_requires_loads_in_every_term_surface() {
    // THE REGRESSION THE UN-STRIP INTRODUCED, and it shipped green because the corpus
    // could not reach it. Constraint bodies, operation `ensures` bodies and
    // aggregation-constraint conditions are stored as TERMS, not occurrences, and only
    // the occurrence walk got the spec-instance arm. Every one of these reported
    // `unresolved name 'T'` where it loaded before the change.
    //
    // The deleted term-side lowering was justified by "the whole test binary passes with
    // it disabled" — but the corpus has zero BRACKETED `requires(` outside a rule body,
    // so the binary could not have measured it. These five rows are the measurement.
    for (name, tail) in [
        (
            "constraint",
            "  constraint c :- requires(Desc[T]), seed(?x)\n",
        ),
        (
            "constraint-bind",
            "  constraint c :- ?d = require[Desc[T]], seed(?x)\n",
        ),
        (
            "ensures",
            "  operation we(x: Int64) -> Int64 ensures requires(Desc[T]) = x\n",
        ),
        (
            "aggregation",
            "  constraint a :- count(?x, seed(?x), ?n), requires(Desc[T])\n",
        ),
        // THE CONTROL: the bare spelling, which never travelled the bracket path and so
        // loaded either way. It is here so a reader can see which rows the change moves.
        (
            "control-bare",
            "  constraint c :- requires(Desc), seed(?x)\n",
        ),
    ] {
        let src = term_surface_program("test.w51w18.term", tail);
        assert!(
            crate::common::try_load_kb_with(&src).is_ok(),
            "`requires(Desc[T])` in a {name} body must load",
        );
    }
}

/// A file whose `requires(…)` sits in a body stored as a TERM rather than as
/// occurrences — a constraint, an `ensures`, an aggregation condition.
fn term_surface_program(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  fact seed(leaf())
{tail}end
"#
    )
}

#[test]
fn a_nested_base_resolves_through_the_ladder_too() {
    // THE LADDER AT A **NESTED** HEAD, which had no driving row. The base of a bracket
    // binding is resolved through `parse_arg_sort_symbol` before falling back to
    // `remap_symbol_strict`, and the comment at that site says the ladder is what answers
    // for a head-introduced type variable at a nested head — `remap_symbol_strict` cannot,
    // because its `rule_head_bound_alias` is gated on `in_rule_head_bound`, false in a
    // body.
    //
    // THE ONLY NESTED-BRACKET FIXTURE IN THE CORPUS COULD NOT MEASURE IT: its nested head
    // is `List`, an ordinary sort that `remap_symbol_strict` resolves too, so it passed
    // before the ladder was consulted. `A` below is head-introduced and resolvable ONLY
    // through the ladder — backing the ladder out reports `unresolved name 'A'`.
    let src = program(
        "test.w51w18.nest",
        "  rule answer(?r) :- anchored(?x, ?d), Desc.describe(?x, ?r)\n  \
         rule anchored[A](?x: A, ?d) :- Desc[A], ?d = require[Desc[T = A[T = Leaf]]], seed(?x)\n",
    );
    assert!(
        crate::common::try_load_kb_with(&src).is_ok(),
        "a head-introduced type variable at a NESTED bracket head must resolve",
    );
    assert_eq!(answer("test.w51w18.nest", &src), 7);
}
