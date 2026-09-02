//! `#[cfg(test)]` modules extracted from `kb/typing.rs` (WI-20260830-009H2).
//!
//! The typer's own unit tests: 26 modules, 5171 lines of them under a 21-line header.
//! The moved span carries 179 lines of OUTER doc comment belonging to 14 of the modules —
//! lifting a module without its doc comment orphans the comment and the crate stops parsing,
//! so the extraction asserted that a blank line precedes every block it moved.
//!
//! TWO things changed in the moved text and nothing else. First, one extra hop on each
//! `super::` path (`super::super::`), because these modules are now children of
//! `typing::tests` rather than of `typing` directly; nothing had to be made public, since a
//! descendant module may name its ancestors' private items. Second, `cargo fmt` then ran over
//! this file and re-wrapped some of it (visibly in four modules). So diffing this file
//! against the pre-split `typing.rs` will NOT come back clean — expect reflow as well as the
//! hop. Neither touches what the tests assert.
//!
//! WHAT THIS DID NOT DO, so the file's existence is not read as more than it is. `typing.rs`
//! is still ONE module of 67402 lines — the tests were 6.8% of it, so navigability is barely
//! improved. The rest does not come apart: 903 of its 1001 free functions fall in a single
//! call-graph community (3.3% of call edges cross), and the six boundaries WI-009H2 proposed
//! overlap 79-100% in transitive reach, with 273 functions reachable from every one of them.
//! There is no semantic seam here to cut along; a further split would be arbitrary layering.

/// WI-20260829-K0E8T — the witness leg's GATE must not allocate before it refuses.
#[cfg(test)]
mod k0e8t_witness_gate_test {
    //! [`super::super::bare_sort_compatible`] ran `kb.make_sort_ref(a)` UNCONDITIONALLY, ahead
    //! of the gate that answers `false` for 1263 of the 1267 entries a full `stdlib/`
    //! load makes (the census is in [`super::super::witness_provides_admissibly`]'s doc). That
    //! is not primarily a speed defect — 41 ns per compare, 50 µs of a 168 ms load — but
    //! a HYGIENE one: `make_sort_ref` is `TermStore::alloc`, and on a hash-cons HIT
    //! `alloc` still bumps a refcount that nothing on this path decrements, so every
    //! refused compare left the actual sort's term one reference heavier, permanently.
    //!
    //! THE REFCOUNT IS THE OBSERVABLE, NOT `TermStore::len`. `Ref(Int64)` is interned
    //! long before any of these compares run, so the eager mint added no SLOT — which is
    //! exactly why the defect was invisible until it was counted.
    //!
    //! TWO BACK-OUTS, AND THE ROWS SEPARATE THEM — which is why row 3 exists at all:
    //!
    //!   * THE HOIST (`WitnessActual::Term(kb.make_sort_ref(a))` restored at the bare
    //!     arm): rows 1 and 2 fail by exactly +1 per compare (MEASURED, 458 → 459), and
    //!     so does row 3.
    //!   * `find_sort_ref` ONLY (`Self::Bare(s) => kb.make_sort_ref(s)` in
    //!     [`super::super::WitnessActual::term`]): row 3 alone fails, by exactly +10 for its 10
    //!     compares (MEASURED, 8 → 18). Rows 1 and 2 pass — they refuse before the mint
    //!     either way, which is the residual /code-review found in the first cut.
    //!
    //! WHAT PASSES EITHER WAY BY DESIGN: every `types_compatible` verdict the rows assert
    //! — neither change answers a question differently, and a test that only checked the
    //! verdict would measure nothing at all.
    use super::super::{types_compatible, TermIdView};
    use crate::intern::Symbol;
    use crate::kb::subst::Substitution;
    use crate::kb::test_support::load_stdlib;
    use crate::kb::KnowledgeBase;

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// `reps` bare↔bare compares of `actual_qn` against `expected_qn`, each asserted to
    /// answer `expect`, with the refcount of the ACTUAL's `Ref` term either side. The
    /// fixture's own `make_sort_ref` is included in `before`, so the pair differs only by
    /// what the compares themselves minted.
    fn refcount_across_compares(
        kb: &mut KnowledgeBase,
        actual_qn: &str,
        expected_qn: &str,
        expect: bool,
        reps: usize,
    ) -> (u32, u32) {
        let (a, e) = (sym(kb, actual_qn), sym(kb, expected_qn));
        let at = kb.make_sort_ref(a);
        let et = kb.make_sort_ref(e);
        let before = kb.terms.refcount(at);
        for _ in 0..reps {
            let mut subst = Substitution::new();
            assert_eq!(
                types_compatible(kb, &mut subst, &TermIdView(at), &TermIdView(et)),
                expect,
                "{actual_qn} <: {expected_qn} must answer {expect} for this row to \
                 measure the path it names"
            );
        }
        (before, kb.terms.refcount(at))
    }

    /// ROW 1 — THE COMMON SHAPE: the expected side is a sort nothing provides, so the
    /// `by_spec_base` bucket is empty and the gate refuses off a single lookup, never
    /// entering the decoder. 1263 of the 1267 stdlib-load entries are this row.
    #[test]
    fn a_gate_refusing_on_an_empty_bucket_mints_nothing() {
        let mut kb = load_stdlib(None);
        let (before, after) = refcount_across_compares(
            &mut kb,
            "anthill.prelude.Int64",
            "anthill.prelude.String",
            false,
            1,
        );
        assert_eq!(
            after, before,
            "a refused compare re-minted `Ref(Int64)`: the mint is back ahead of the gate"
        );
    }

    /// ROW 2 — THE GATE DOES REAL WORK AND STILL REFUSES. `FiniteCollection` is the very
    /// spec WI-20260829-N01PY's leg exists for and carries 6 provisions in `stdlib/`,
    /// none of them witnessed on `Int64`. Distinct from row 1 because the hoist has to
    /// clear the WHOLE gate, not merely the bucket lookup: a repair that minted after the
    /// emptiness check but before the provision walk would pass row 1 and fail here.
    #[test]
    fn a_gate_that_walks_provisions_and_refuses_mints_nothing() {
        let mut kb = load_stdlib(None);
        let (before, after) = refcount_across_compares(
            &mut kb,
            "anthill.prelude.Int64",
            "anthill.prelude.FiniteCollection",
            false,
            1,
        );
        assert_eq!(
            after, before,
            "the provision walk found no witness row yet still minted `Ref(Int64)`"
        );
    }

    /// A BARE WITNESSED CARRIER — the WI-20260829-N01PY shape, and the only one that
    /// reaches [`super::super::WitnessActual::term`] at all. `Plain` has no type parameters, so
    /// it compares at `(sort_ref, sort_ref)`; `PlainWitness` files the provision under
    /// ITSELF, which is what makes the carrier-keyed `sort_provides_admissibly` miss and
    /// the witness leg answer.
    const WITNESSED: &str = r#"
namespace k0e8t
  sort Cap
    sort C = ?
    sort Element = ?
    operation get(c: C) -> Element
  end

  sort Plain
    import anthill.prelude.Int64
    entity plain(v: Int64)
  end

  sort PlainWitness
    import anthill.prelude.Int64
    import k0e8t.{Cap, Plain}
    import k0e8t.Plain.plain
    provides Cap[C = Plain, Element = Int64]
    operation get(p: Plain) -> Int64 = match p case plain(x) -> x
  end
end
"#;

    /// ROW 3 — AN ACCEPTED COMPARE, WHICH THE HOIST ALONE DOES NOT COVER. Rows 1 and 2
    /// both refuse, so they are satisfied by a repair that merely moves the mint past the
    /// gate; a compare that gets THROUGH the gate still calls
    /// [`super::super::WitnessActual::term`], and `alloc` increfs on a hash-cons hit. Ten
    /// compares of one pair, so the assertion is about GROWTH rather than a single
    /// reference: with `make_sort_ref` alone the refcount rises by exactly 10.
    ///
    /// Found by /code-review, which named this as the uncovered residual of the first cut.
    #[test]
    fn an_accepted_witness_compare_does_not_grow_the_refcount() {
        let mut kb = load_stdlib(Some(WITNESSED));
        let (before, after) =
            refcount_across_compares(&mut kb, "k0e8t.Plain", "k0e8t.Cap", true, 10);
        assert_eq!(
            after, before,
            "an ACCEPTED witness compare increfs `Ref(Plain)` once per call — \
             `find_sort_ref` is back to `make_sort_ref`"
        );
    }
}

#[cfg(test)]
mod wi_1ssxm_surviving_dot_backstop_tests {
    //! WI-20260829-1SSXM — THE BACKSTOP'S ONLY COVERAGE, and it is a unit test because
    //! nothing else can reach it any more.
    //!
    //! [`surviving_dot_apply`] was driven from anthill source by
    //! `wi_n2fhm_find_callback_dot_test::an_unresolvable_dot_never_reaches_the_evaluator`
    //! while `MatchAfterScrutinee` still swallowed its scrutinee's `Err`. Repairing that
    //! swallow took the last producer away: measured on this tree, neutralizing the
    //! error push in `check_operation_bodies` leaves `wi_tests` at 3773/3773, because the
    //! frame now reports the refusal before any stored body is walked. That is the
    //! invariant holding — and it left a live, unexercised guard behind, which
    //! /code-review named.
    //!
    //! So the WALK is driven here directly, over synthetic occurrences, since no PROGRAM
    //! can produce one. These cases pin what the function's doc claims and what its
    //! caller reads: that it finds a surviving dot at depth, that it returns the dot's
    //! RECEIVER (so the refusal can name the sort the member was looked for on, rather
    //! than reporting it unresolved), that it reports the FIRST dot in SOURCE ORDER, and
    //! that it stays silent on a dot-free tree — the last being what makes it a backstop
    //! rather than a refusal of every body.

    use super::super::surviving_dot_apply;
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use crate::kb::KnowledgeBase;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn span_at(start: u32) -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), start, start + 1)
    }

    /// A leaf to hang dots off: `?recv`.
    fn var_ref(kb: &mut KnowledgeBase, name: &str, at: u32) -> Rc<NodeOccurrence> {
        let name = kb.intern(name);
        NodeOccurrence::new_expr(Expr::VarRef { name }, span_at(at), None)
    }

    /// `<recv>.<member>` — a field-access `DotApply`, the form that survives when dot
    /// dispatch produced `DotDispatchNoMatch` and the refusal was then lost.
    fn dot(kb: &mut KnowledgeBase, recv: &str, member: &str, at: u32) -> Rc<NodeOccurrence> {
        let receiver = var_ref(kb, recv, at);
        let name = kb.intern(member);
        NodeOccurrence::new_expr(
            Expr::DotApply {
                receiver,
                name,
                pos_args: Vec::new(),
                named_args: Vec::new(),
            },
            span_at(at),
            None,
        )
    }

    fn list(elems: Vec<Rc<NodeOccurrence>>, at: u32) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_expr(Expr::ListLit(elems), span_at(at), None)
    }

    /// DRIVES the backstop: a dot nested under a list literal is found, and the result
    /// carries the member AND the receiver. The receiver is the half the caller needs —
    /// it reads the WI-732 type stamp off it to name the sort; without it the refusal
    /// renders as "the receiver's type is unresolved", which is false whenever the
    /// receiver typed fine and the author simply mistyped the member.
    #[test]
    fn a_surviving_dot_is_found_at_depth_with_its_member_and_receiver() {
        let mut kb = KnowledgeBase::new();
        let body = list(vec![list(vec![dot(&mut kb, "r", "nosuchfield", 10)], 5)], 0);
        let (member, span, receiver) =
            surviving_dot_apply(&body).expect("a surviving DotApply must be found");
        assert_eq!(kb.local_name_of(member), "nosuchfield");
        assert_eq!(
            span.map(|s| s.start),
            Some(10),
            "the dot's own span is reported"
        );
        match receiver.as_expr() {
            Some(Expr::VarRef { name }) => assert_eq!(kb.local_name_of(*name), "r"),
            other => panic!("the dot's own receiver must come back, got {other:?}"),
        }
    }

    /// DRIVES the SOURCE-ORDER claim, which is the reason the walk pushes children in
    /// REVERSE and pops. `and(r.typo1, r.typo2)` must name `typo1`: reporting the LAST
    /// dot would have the author fix it, reload, and only then be told about the first.
    /// RED if the `.rev()` on the child push is dropped — that is the whole content of
    /// this case, and it is invisible to any test with one dot in it.
    #[test]
    fn the_first_dot_in_source_order_is_the_one_reported() {
        let mut kb = KnowledgeBase::new();
        let body = list(
            vec![
                dot(&mut kb, "r", "typo1", 10),
                dot(&mut kb, "r", "typo2", 20),
            ],
            0,
        );
        let (member, _, _) =
            surviving_dot_apply(&body).expect("a surviving DotApply must be found");
        assert_eq!(
            kb.local_name_of(member),
            "typo1",
            "the FIRST dot in source order is reported, not the last",
        );
    }

    /// CONTROL — a tree with no `DotApply` answers `None`. Green with the walk's
    /// `.rev()` removed and with the caller's error push removed; it is what says the
    /// backstop refuses a surviving dot rather than refusing bodies. Every well-typed
    /// body in the corpus takes this path, which is why the guard is silent there.
    #[test]
    fn control_a_dot_free_tree_is_not_refused() {
        let mut kb = KnowledgeBase::new();
        let body = list(vec![list(vec![var_ref(&mut kb, "r", 10)], 5)], 0);
        assert!(
            surviving_dot_apply(&body).is_none(),
            "a body with no DotApply must not be refused",
        );
    }
}

#[cfg(test)]
mod wi323_pattern_type_ann_walker_tests {
    //! WI-323: the two typing.rs pattern-fragment walkers
    //! (`check_ho_apply_pattern_occ` and `occurrence_contains_functor`)
    //! early-returned on a Pattern-kind occurrence via `as_expr()`, so an
    //! `ho_apply` smuggled into a `Pattern.Var.type_ann` Expr child evaded the
    //! hereditary-Harrop pattern-fragment rules (1/2/3/3b). WI-319 lifted
    //! Lambda.param / Let.pattern / MatchBranch.pattern to Pattern-kind
    //! occurrences and WI-298 taught six OTHER walkers to descend into pattern
    //! children, but these two were left on the `as_expr()` early-return. The
    //! load path never populates `Pattern.Var.type_ann` today (load.rs
    //! `load_pattern_var` → None), so the defect is latent — these tests build
    //! the occurrence DIRECTLY (the level at which the gap is reproducible) and
    //! assert both walkers now descend into a pattern's type-annotation child.
    use super::super::{
        check_ho_apply_pattern_occ, occurrence_contains_functor, Expr, NodeOccurrence, Pattern,
    };
    use crate::intern::Symbol;
    use crate::kb::term::{Literal, Var};
    use crate::kb::KnowledgeBase;
    use crate::parse::desugar_target as dt;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn make_span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 10)
    }

    /// `ho_apply(?P, ?x, ?x)` as an Expr-kind occurrence — a rule-3
    /// (duplicate-variable in predicate args) violation, with `ho_apply_sym` as
    /// the functor.
    fn dup_var_ho_apply(ho_apply_sym: Symbol, span: SourceSpan) -> Rc<NodeOccurrence> {
        let pred = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(0)), span, None);
        let x1 = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(1)), span, None);
        let x2 = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(1)), span, None);
        NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: ho_apply_sym,
                pos_args: vec![pred, x1, x2],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        )
    }

    /// A rule body `let p: <ho_apply(?P,?x,?x)> = 0 in 1` — the ho_apply lives in
    /// the Pattern.Var.type_ann slot. Before WI-323 the walker reached the
    /// pattern child, `as_expr()` returned None, and it early-returned, silently
    /// missing the rule-3 violation. ACCEPTANCE (WI-323).
    #[test]
    fn ho_apply_in_let_pattern_type_ann_triggers_violation() {
        let mut kb = KnowledgeBase::new();
        let ho_apply_sym = kb.intern(dt::qualified(dt::HO_APPLY));
        let rule_sym = kb.intern("test_rule");
        let pat_name = kb.intern("p");
        let span = make_span();

        let ho = dup_var_ho_apply(ho_apply_sym, span);
        let pattern = NodeOccurrence::new_pattern_annotated(
            Pattern::Var { name: pat_name },
            Some(ho),
            span,
            None,
        );
        let value = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span, None);
        let body = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let let_occ = NodeOccurrence::new_expr(
            Expr::Let {
                pattern,
                value,
                body,
            },
            span,
            None,
        );

        let mut errors = Vec::new();
        check_ho_apply_pattern_occ(
            &kb,
            &let_occ,
            ho_apply_sym,
            rule_sym,
            Some(span.span),
            &mut errors,
        );
        assert!(
            !errors.is_empty(),
            "ho_apply in a pattern's type_ann must trigger the rule-fragment violation (WI-323)"
        );
    }

    /// The head-vs-body co-occurrence helper (rules 1/3b) must find a functor
    /// nested in a Pattern's type-annotation Expr child.
    #[test]
    fn occurrence_contains_functor_descends_into_pattern_type_ann() {
        let mut kb = KnowledgeBase::new();
        let ho_apply_sym = kb.intern(dt::qualified(dt::HO_APPLY));
        let pat_name = kb.intern("p");
        let span = make_span();

        let ho = dup_var_ho_apply(ho_apply_sym, span);
        let pattern = NodeOccurrence::new_pattern_annotated(
            Pattern::Var { name: pat_name },
            Some(ho),
            span,
            None,
        );
        assert!(
            occurrence_contains_functor(&pattern, ho_apply_sym),
            "occurrence_contains_functor must find a functor nested in a pattern's type_ann (WI-323)"
        );

        // A pattern with no type_ann must still report false (no spurious match).
        let plain = NodeOccurrence::new_pattern(Pattern::Var { name: pat_name }, span, None);
        assert!(
            !occurrence_contains_functor(&plain, ho_apply_sym),
            "a pattern with no nested functor must not spuriously match"
        );
    }

    /// WITNESS A: root is an EXPR whose pattern carries the annotation — the
    /// PRODUCTION shape (`check_pattern_fragment` runs over a rule body, not
    /// over a bare pattern). The existing test above passes the PATTERN itself
    /// as root, where the popped item and the root coincide.
    #[test]
    fn witness_a_expr_root_finds_functor_in_pattern_annotation() {
        let mut kb = KnowledgeBase::new();
        let ho_apply_sym = kb.intern(dt::qualified(dt::HO_APPLY));
        let pat_name = kb.intern("p");
        let span = make_span();

        let ho = dup_var_ho_apply(ho_apply_sym, span);
        let pattern = NodeOccurrence::new_pattern_annotated(
            Pattern::Var { name: pat_name },
            Some(ho),
            span,
            None,
        );
        let value = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span, None);
        let body = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let let_occ = NodeOccurrence::new_expr(
            Expr::Let {
                pattern,
                value,
                body,
            },
            span,
            None,
        );

        assert!(
            occurrence_contains_functor(&let_occ, ho_apply_sym),
            "an ho_apply inside the let's PATTERN annotation must be found from an Expr root"
        );
    }

    /// WITNESS B: a nested pattern. If the walk pushes the ROOT's children
    /// instead of the popped node's, this never terminates.
    #[test]
    fn witness_b_nested_pattern_terminates() {
        let mut kb = KnowledgeBase::new();
        let ho_apply_sym = kb.intern(dt::qualified(dt::HO_APPLY));
        let c = kb.intern("C");
        let span = make_span();

        let leaf = NodeOccurrence::new_pattern(Pattern::Wildcard, span, None);
        let inner = NodeOccurrence::new_pattern(
            Pattern::Constructor {
                name: c,
                pos_args: vec![leaf],
                named_args: Vec::new(),
            },
            span,
            None,
        );
        let outer = NodeOccurrence::new_pattern(
            Pattern::Constructor {
                name: c,
                pos_args: vec![inner],
                named_args: Vec::new(),
            },
            span,
            None,
        );
        assert!(
            !occurrence_contains_functor(&outer, ho_apply_sym),
            "must terminate and report false"
        );
    }
}

#[cfg(test)]
mod wi417_cycle_tests {
    //! WI-417: the typer's substitution-chain walkers must not overflow the
    //! host stack on a CYCLIC substitution. Normal unification does not mint a
    //! pure value-var cycle (WI-416's cycle closed through a sort-alias hop, now
    //! handled by the `walk_type` guard), so these tests build the cycle
    //! DIRECTLY in the `Substitution` — the level at which the defect is
    //! reproducible — and assert each walker terminates with a representative
    //! rather than recursing to a crash. Before WI-417 these recursed forever
    //! and aborted the test binary (an uncatchable stack overflow), so a
    //! regression here is a loud failure.
    use super::super::{
        walk_pattern_field_type_deep, walk_type, walk_type_value, walk_value_to_resolved,
    };
    use crate::eval::value::Value;
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Term, TermId, Var, VarId};
    use crate::kb::KnowledgeBase;

    fn fresh(kb: &mut KnowledgeBase, name: &str) -> VarId {
        let sym = kb.intern(name);
        kb.fresh_var(sym)
    }

    /// Two vars cross-bound through `Value::Term(Var(_))`: `a → b → a`.
    fn term_var_cycle(kb: &mut KnowledgeBase) -> (Substitution, TermId, VarId, VarId) {
        let a = fresh(kb, "A");
        let b = fresh(kb, "B");
        let ta = kb.alloc(Term::Var(Var::Global(a)));
        let tb = kb.alloc(Term::Var(Var::Global(b)));
        let mut subst = Substitution::new();
        subst.bind_value(kb, a, Value::term(tb));
        subst.bind_value(kb, b, Value::term(ta));
        (subst, ta, a, b)
    }

    #[test]
    fn walk_type_terminates_on_term_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let (subst, ta, a, b) = term_var_cycle(&mut kb);
        match kb.get_term(walk_type(&kb, &subst, ta)) {
            Term::Var(Var::Global(v)) => assert!(*v == a || *v == b, "a cycle representative"),
            other => panic!("expected a cycle-representative var, got {other:?}"),
        }
    }

    #[test]
    fn walk_type_value_terminates_on_term_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let (subst, ta, a, b) = term_var_cycle(&mut kb);
        match walk_type_value(&kb, &subst, &Value::term(ta)) {
            Value::Term { id: t, .. } => match kb.get_term(t) {
                Term::Var(Var::Global(v)) => assert!(*v == a || *v == b),
                other => panic!("expected a cycle-representative var, got {other:?}"),
            },
            other => panic!("expected Value::Term(var), got {other:?}"),
        }
    }

    #[test]
    fn walk_pattern_field_type_deep_terminates_on_term_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let (subst, ta, _a, _b) = term_var_cycle(&mut kb);
        // Termination is the property under test (returns instead of crashing).
        let _ = walk_pattern_field_type_deep(&mut kb, &subst, &Value::term(ta));
    }

    #[test]
    fn walk_value_to_resolved_terminates_on_value_var_cycle() {
        let mut kb = KnowledgeBase::new();
        let a = fresh(&mut kb, "A");
        let b = fresh(&mut kb, "B");
        let mut subst = Substitution::new();
        subst.bind_value(&kb, a, Value::Var(Var::Global(b)));
        subst.bind_value(&kb, b, Value::Var(Var::Global(a)));
        match walk_value_to_resolved(&kb, &subst, Value::Var(Var::Global(a))) {
            Value::Var(Var::Global(v)) => assert!(v == a || v == b, "a cycle representative"),
            other => panic!("expected a cycle-representative var, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod wi394_surface_node_binding_tests {
    //! WI-394: a `TermId`-consuming caller (op type-arg write-back at the apply
    //! occurrence, the provider-binding "did it resolve?" probe) that walked a
    //! var resolving to a NON-`Term` carrier — a `Value::Node` denoted / written
    //! effect-row binding — must NOT misread the bare var as unresolved, since
    //! `walk_type` / `walk_type_deep` deliberately STOP at a non-`Term` binding.
    //! `surface_node_binding_to_term` lowers such a binding faithfully to a
    //! `TermId`; a `Term` binding / unbound var / un-lowerable carrier passes
    //! through unchanged (the pre-WI-394 behavior, so all existing term-world
    //! paths are inert).
    use super::super::surface_node_binding_to_term;
    use crate::eval::value::Value;
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Literal, Term, Var};
    use crate::kb::KnowledgeBase;

    fn fresh_var_term(kb: &mut KnowledgeBase, name: &str) -> (Var, Term) {
        let sym = kb.intern(name);
        let vid = kb.fresh_var(sym);
        (Var::Global(vid), Term::Var(Var::Global(vid)))
    }

    #[test]
    fn surfaces_non_term_binding_as_lowered_term() {
        // A var bound to a NON-`Term` value (here `Value::Int`, standing in for
        // any non-`Term` carrier — a `Value::Node`/entity lowers through the
        // same `value_to_term`). The term-only walk would stop at the var; the
        // surface lowers the binding so a TermId consumer sees the real value.
        let mut kb = KnowledgeBase::new();
        let (var, var_t) = fresh_var_term(&mut kb, "V");
        let var_term = kb.alloc(var_t);
        let Var::Global(vid) = var else {
            unreachable!()
        };
        let mut subst = Substitution::new();
        subst.bind_value(&kb, vid, Value::Int(42));
        let out = surface_node_binding_to_term(&mut kb, &subst, var_term);
        assert_ne!(out, var_term, "must not keep the bare var");
        assert!(
            matches!(kb.get_term(out), Term::Const(Literal::Int(42))),
            "expected the lowered Const(Int(42)), got {:?}",
            kb.get_term(out)
        );
    }

    #[test]
    fn passes_through_non_var_term_unchanged() {
        // For a `Value::Term` binding the deep walk already produced a concrete
        // term; the surface sees no var and returns it untouched.
        let mut kb = KnowledgeBase::new();
        let concrete = kb.alloc(Term::Const(Literal::Int(7)));
        let subst = Substitution::new();
        let out = surface_node_binding_to_term(&mut kb, &subst, concrete);
        assert_eq!(out, concrete, "a non-var term passes through");
    }

    #[test]
    fn passes_through_unbound_var_unchanged() {
        let mut kb = KnowledgeBase::new();
        let (_, var_t) = fresh_var_term(&mut kb, "V");
        let var_term = kb.alloc(var_t);
        let subst = Substitution::new();
        let out = surface_node_binding_to_term(&mut kb, &subst, var_term);
        assert_eq!(out, var_term, "an unbound var passes through");
    }

    #[test]
    fn passes_through_term_bound_var_via_walked_input() {
        // A `Value::Term` binding is term-world: even if the surface is handed
        // the raw var, it must NOT treat the `Value::Term` binding as a
        // surface-able non-`Term` carrier (the `matches!(v, Value::Term(_))`
        // guard) — it returns the var, letting the term-world walk handle it.
        let mut kb = KnowledgeBase::new();
        let (var, var_t) = fresh_var_term(&mut kb, "V");
        let var_term = kb.alloc(var_t);
        let Var::Global(vid) = var else {
            unreachable!()
        };
        let concrete = kb.alloc(Term::Const(Literal::Int(7)));
        let mut subst = Substitution::new();
        subst.bind_value(&kb, vid, Value::term(concrete));
        let out = surface_node_binding_to_term(&mut kb, &subst, var_term);
        assert_eq!(out, var_term, "a Term binding is not surfaced here");
    }
}

#[cfg(test)]
mod p3_tests {
    //! WI-342 P3 — carrier-agnostic `unify_types` over `TermView`.
    use super::super::unify_types;
    use crate::eval::value::Value;
    use crate::kb::load::register_prelude;
    use crate::kb::node_occurrence::TypeNode;
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Term, Var};
    use crate::kb::term_view::TermIdView;
    use crate::kb::KnowledgeBase;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 1)
    }

    fn fresh_vid(kb: &mut KnowledgeBase, name: &str) -> crate::kb::term::VarId {
        let sym = kb.intern(name);
        kb.fresh_var(sym)
    }

    /// A fresh inference var `?T` binds to a `Value`-carried `denoted` and
    /// resolves back to it (identity preserved) — the var↔Value-carried path.
    #[test]
    fn unify_var_with_value_carried_denoted() {
        let mut kb = kb_with_prelude();
        let c = kb.intern("c");
        let denoted_occ = kb.make_denoted_occ_ref(c, span(), None);
        let tname = kb.intern("T");
        let vid = kb.fresh_var(tname);
        let var_t = kb.alloc(Term::Var(Var::Global(vid)));

        let mut subst = Substitution::new();
        assert!(unify_types(
            &mut kb,
            &mut subst,
            &TermIdView(var_t),
            &denoted_occ
        ));

        match subst.resolve_as_value(vid) {
            Some(Value::Node(occ)) => {
                assert!(
                    Rc::ptr_eq(occ, &denoted_occ),
                    "binding preserves occurrence identity"
                );
                assert!(matches!(occ.as_type(), Some(TypeNode::Denoted { .. })));
            }
            other => panic!("expected ?T → Value::Node(denoted), got {other:?}"),
        }
    }

    // WI-366: `cross_carrier_denoted_unify` / `ground_denoted_unchanged` deleted
    // with `make_denoted` — they built a GROUND `denoted` term, a carrier no
    // production path produces (every value-in-type mints a `Value::Node` via
    // `make_denoted_occ`). The live Node-denoted unify is covered by
    // `value_value_parameterized_denoted_unify`; mixed TermId-vs-Node dispatch by
    // `occurs_check_var_in_node_tuple_field`.

    /// `bind_value` contradiction via the carrier-aware `views_structurally_equal`
    /// (WI-486): binding a var twice to structurally-equal (distinct `Rc`)
    /// Value-carried types must NOT contradict; to a different one must.
    #[test]
    fn bind_value_structural_eq_no_false_contradiction() {
        let mut kb = kb_with_prelude();
        let vid = fresh_vid(&mut kb, "T");
        let c = kb.intern("c");
        let d = kb.intern("d");
        let occ_c1 = kb.make_denoted_occ_ref(c, span(), None);
        let occ_c2 = kb.make_denoted_occ_ref(c, span(), None); // equal, distinct Rc
        let occ_d = kb.make_denoted_occ_ref(d, span(), None);

        let mut s = Substitution::new();
        s.bind_value(&kb, vid, Value::Node(occ_c1));
        s.bind_value(&kb, vid, Value::Node(occ_c2));
        assert!(
            !s.is_contradiction(),
            "equal Value-carried types must not contradict"
        );
        s.bind_value(&kb, vid, Value::Node(occ_d));
        assert!(
            s.is_contradiction(),
            "a distinct Value-carried type contradicts"
        );
    }
}

#[cfg(test)]
mod wi361_reader_tests {
    //! WI-361 stage 2: the dispatch-key reader `sort_functor_of` classifies via
    //! `type_head`, so it reads the TERM-BACKED form (`Ref(S)` bare sort,
    //! `Fn{S, named}` parameterized — base sort IS the functor) identically to
    //! the deep `sort_ref`/`parameterized` form. Producers still build the deep
    //! form today, so the test manually constructs the term backing to exercise
    //! the migrated path. (The deep-form path stays covered by the wider suite;
    //! the carrier-agnostic classifier itself by `type_extract_test`.)
    use super::super::{extract_sort_ref_sym, sort_functor_of};
    use crate::intern::Symbol;
    use crate::kb::load::register_prelude;
    use crate::kb::term::{Term, TermId};
    use crate::kb::term_view::TermIdView;
    use crate::kb::KnowledgeBase;
    use smallvec::SmallVec;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    /// Term backing `Fn{base, named:[(param, Ref(arg))]}` — a parameterized type
    /// whose base sort IS the functor (no deep `parameterized` wrapper).
    fn term_backed_param(
        kb: &mut KnowledgeBase,
        base: Symbol,
        param: Symbol,
        arg: Symbol,
    ) -> TermId {
        let arg_ref = kb.alloc(Term::Ref(arg));
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named.push((param, arg_ref));
        kb.alloc(Term::Fn {
            functor: base,
            pos_args: SmallVec::new(),
            named_args: named,
        })
    }

    #[test]
    fn sort_functor_of_reads_term_backed_parameterized() {
        let mut kb = kb_with_prelude();
        let list = kb.intern("List");
        let int = kb.intern("Int64");
        let t = kb.intern("T");

        // Term-backed `List[T = Int]` == `Fn{List, named:[(T, Ref(Int))]}` — the
        // functor IS the base sort; pre-migration this returned None.
        let tb = term_backed_param(&mut kb, list, t, int);
        assert_eq!(
            sort_functor_of(&kb, tb),
            Some(list),
            "term-backed Fn{{List,..}} -> List"
        );

        // The same via the real builder `make_parameterized_type` (also term-backed).
        let int_ref = kb.make_sort_ref(int);
        let base = kb.make_sort_ref(list);
        let built = kb.make_parameterized_type(base, &[(t, int_ref)]);
        assert_eq!(
            sort_functor_of(&kb, built),
            Some(list),
            "make_parameterized_type -> List"
        );

        // Term-backed bare sort `Ref(Int)`.
        let bare = kb.alloc(Term::Ref(int));
        assert_eq!(
            sort_functor_of(&kb, bare),
            Some(int),
            "bare Ref(Int64) -> Int64"
        );

        // A structural variant (arrow) has no sort head.
        let unit = kb.intern("Unit");
        let unit_ref = kb.make_sort_ref(unit);
        let arrow = kb.make_arrow_type(unit_ref, unit_ref, &[], 1);
        assert_eq!(sort_functor_of(&kb, arrow), None, "arrow has no sort head");
    }

    #[test]
    fn extract_sort_ref_sym_reads_term_backed_bare_ref() {
        let mut kb = kb_with_prelude();
        let int = kb.intern("Int64");
        let list = kb.intern("List");
        let t = kb.intern("T");

        // Term-backed bare sort `Ref(Int)` — pre-migration this returned None.
        let bare = kb.alloc(Term::Ref(int));
        assert_eq!(
            extract_sort_ref_sym(&kb, &TermIdView(bare)),
            Some(int),
            "bare Ref(Int64) -> Int64"
        );

        // The same via the real builder `make_sort_ref` (also `Ref(Int)`).
        let built = kb.make_sort_ref(int);
        assert_eq!(
            extract_sort_ref_sym(&kb, &TermIdView(built)),
            Some(int),
            "make_sort_ref(Int64) -> Int64"
        );

        // A parameterized type is NOT a bare sort ref.
        let tb = term_backed_param(&mut kb, list, t, int);
        assert_eq!(
            extract_sort_ref_sym(&kb, &TermIdView(tb)),
            None,
            "Fn{{List,..}} is not a bare sort ref"
        );
    }

    /// The unify/subtype STRUCTURAL dispatch reads a term-backed `Fn{S, named}` as
    /// a parameterized type (via `type_dispatch_name`/`extract_type`): the same
    /// instantiation unifies and subtypes, a differing binding is rejected.
    #[test]
    fn parameterized_unify_subtype_term_backed() {
        use super::super::{types_compatible, unify_types};
        use crate::kb::subst::Substitution;
        use crate::kb::term_view::TermIdView;

        let mut kb = kb_with_prelude();
        let list = kb.intern("List");
        let int = kb.intern("Int64");
        let string = kb.intern("String");
        let t = kb.intern("T");

        let tb_int = term_backed_param(&mut kb, list, t, int);
        let tb_int2 = term_backed_param(&mut kb, list, t, int);
        let tb_str = term_backed_param(&mut kb, list, t, string);

        // Same instantiation unifies; a differing binding is rejected.
        let mut s = Substitution::new();
        assert!(
            unify_types(&mut kb, &mut s, &TermIdView(tb_int), &TermIdView(tb_int2)),
            "List[T=Int] unifies with itself"
        );
        let mut s2 = Substitution::new();
        assert!(
            !unify_types(&mut kb, &mut s2, &TermIdView(tb_int), &TermIdView(tb_str)),
            "List[T=Int] vs List[T=String] rejected at the binding"
        );

        // Subtype: same accept; differing reject.
        let mut s4 = Substitution::new();
        assert!(
            types_compatible(&mut kb, &mut s4, &TermIdView(tb_int), &TermIdView(tb_int2)),
            "List[T=Int] <: List[T=Int]"
        );
        let mut s5 = Substitution::new();
        assert!(
            !types_compatible(&mut kb, &mut s5, &TermIdView(tb_int), &TermIdView(tb_str)),
            "List[T=Int] is not <: List[T=String]"
        );
    }

    /// WI-361 PRODUCER FLIP: `make_sort_ref` emits the bare term `Ref(S)` and
    /// `make_parameterized_type` the term backing `Fn{S, named}` (base sort IS the
    /// functor, no `sort_ref`/`parameterized` wrapper); the readers classify the
    /// flipped producers' output, and empty bindings collapse to the bare `Ref(S)`.
    #[test]
    fn producer_flip_emits_term_backing() {
        use super::super::{extract_type, sort_functor_of, TypeExtractor};
        use crate::kb::term_view::TermIdView;
        let mut kb = kb_with_prelude();
        let int = kb.intern("Int64");
        let list = kb.intern("List");
        let t = kb.intern("T");

        // make_sort_ref(Int) -> the bare term `Ref(Int)`, NOT `sort_ref(name: …)`.
        let sr = kb.make_sort_ref(int);
        assert!(
            matches!(kb.get_term(sr), Term::Ref(s) if *s == int),
            "make_sort_ref flips to Ref(S); got {:?}",
            kb.get_term(sr)
        );

        // make_parameterized_type(make_sort_ref(List), [T = Ref(Int)]) ->
        // `Fn{List, named:[(T, Ref(Int))]}` — the base sort IS the functor.
        let base = kb.make_sort_ref(list);
        let int_ref = kb.make_sort_ref(int);
        let p = kb.make_parameterized_type(base, &[(t, int_ref)]);
        match kb.get_term(p).clone() {
            Term::Fn {
                functor,
                named_args,
                pos_args,
            } => {
                assert_eq!(functor, list, "functor IS the base sort (List)");
                assert!(pos_args.is_empty());
                assert_eq!(named_args.len(), 1);
                assert_eq!(named_args[0].0, t, "the binding is the `T` named arg");
            }
            other => panic!("make_parameterized_type flips to Fn{{S, named}}; got {other:?}"),
        }

        // make_parameterized_type with NO bindings collapses to the bare sort
        // `Ref(S)` — a no-binding parameterized IS the bare sort, never a
        // degenerate no-arg `Fn{S}` (which would classify as `Error`).
        let empty_base = kb.make_sort_ref(list);
        let empty_param = kb.make_parameterized_type(empty_base, &[]);
        assert!(
            matches!(kb.get_term(empty_param), Term::Ref(s) if *s == list),
            "empty-bindings parameterized collapses to bare Ref(S); got {:?}",
            kb.get_term(empty_param)
        );

        // Readers classify the flipped producers' output.
        assert!(
            matches!(extract_type(&kb, &TermIdView(sr)), TypeExtractor::SortRef(s) if s == int)
        );
        assert!(
            matches!(extract_type(&kb, &TermIdView(p)), TypeExtractor::Parameterized { base, .. } if base == list)
        );
        assert_eq!(
            sort_functor_of(&kb, p),
            Some(list),
            "term-backed Fn{{List,..}} -> List"
        );
    }
}

#[cfg(test)]
mod p4_tests {
    //! WI-342 P4-A — carrier-agnostic structural unification of a
    //! `Value`-carried `parameterized` (the denoted-bearing effect label),
    //! standalone (not yet inside a row — that's P4-B).
    use super::super::unify_types;
    use crate::kb::load::register_prelude;
    use crate::kb::node_occurrence::{NodeOccurrence, TypeChild};
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Term, TermId};
    use crate::kb::term_view::TermIdView;
    use crate::kb::ClauseKind;
    use crate::kb::KnowledgeBase;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 1)
    }

    /// `Value`-carried `parameterized(sort_ref(Modify), [p = denoted(Ref sym)])`
    /// — a ground `sort_ref` base, a poisoned (denoted-bearing) binding value.
    fn occ_param(
        kb: &mut KnowledgeBase,
        modify: crate::intern::Symbol,
        p: crate::intern::Symbol,
        sym: crate::intern::Symbol,
    ) -> Rc<NodeOccurrence> {
        let base = kb.make_sort_ref(modify);
        let denoted_occ = kb.make_denoted_occ_ref(sym, span(), None);
        kb.make_parameterized_occ(
            TypeChild::Ground(base),
            vec![(p, TypeChild::Node(denoted_occ))],
            span(),
            None,
        )
    }

    /// WI-470 regression: the occurrence-primary `make_arrow_value` must fold a
    /// row-tail `Var` (a row-polymorphic body's open tail) as `open(tail)`, NOT
    /// `present(var)`. The retired ground path got this from
    /// `build_canonical_effects_rows`; the always-Node path re-derives it. Without
    /// the fix the tail var is present-wrapped, so `decompose_effect_row` reads it
    /// as a present LABEL (the WI-441 bug class) — a closed row with a spurious var
    /// label instead of an open row.
    #[test]
    fn wi470_inferred_arrow_folds_row_tail_var_as_open_not_present() {
        use super::super::{arrow_parts, decompose_effect_row, make_arrow_value};
        use crate::eval::value::Value;
        use crate::kb::term::Var;
        let mut kb = kb_with_prelude();
        let int = Value::term(kb.make_sort_ref_by_name("anthill.prelude.Int64"));
        let label_t = kb.make_sort_ref_by_name("anthill.prelude.Bool");
        // A bare Global logic var is a row tail (a row-polymorphic open tail).
        let rho = kb.intern("rho");
        let vid = kb.fresh_var(rho);
        let tail_t = kb.alloc(Term::Var(Var::Global(vid)));
        assert!(
            kb.row_tail_var_of(tail_t).is_some(),
            "sanity: bare Global is a row tail"
        );

        // Inferred arrow `Int64 -> Int64 @ {Bool, ?rho}` — one present label + an
        // open tail. WI-470: occurrence-primary (`Value::Node`).
        let arrow = make_arrow_value(
            &mut kb,
            &int,
            &int,
            &[Value::term(label_t), Value::term(tail_t)],
            1,
            span(),
            None,
        );
        assert!(
            matches!(arrow, Value::Node(_)),
            "WI-470: inferred arrow is occurrence-primary"
        );

        let (_, _, effects) = arrow_parts(&mut kb, &arrow).expect("arrow has effects parts");
        let effects = effects.expect("arrow synthesizes an effects child");
        let subst = Substitution::new();
        let (present, tails, _absent) =
            decompose_effect_row(&mut kb, &subst, &effects).expect("effects row decomposes");
        assert!(
            tails.contains(&tail_t),
            "row-tail var folds as open(tail); tails={tails:?}"
        );
        assert_eq!(
            present.len(),
            1,
            "exactly the real label is present (NOT the tail); present={present:?}"
        );
        assert!(
            present
                .iter()
                .any(|p| matches!(p, Value::Term { id: t, .. } if *t == label_t)),
            "the present label is Bool; present={present:?}",
        );
    }

    /// WI-470: `denoted_value_is_closed` distinguishes the three value-in-type shapes
    /// so the WI-385 groundness gate routes each to the validator that can DECIDE it —
    /// a closed value is conformance-checked here; a free var defers to inference; a
    /// binder-local param ref defers to the alignment-aware `validate_callback_effect_row`.
    /// None is silently skipped.
    #[test]
    fn wi470_denoted_value_is_closed_distinguishes_binder_relative() {
        use super::super::denoted_value_is_closed;
        use crate::intern::SymbolKind;
        use crate::kb::node_occurrence::Expr;
        use crate::kb::term::{Literal, Var};
        let mut kb = kb_with_prelude();

        // Closed: a literal value-in-type (the `3` of `Vector[Int64, 3]`).
        let lit = NodeOccurrence::new_expr(Expr::Const(Literal::Int(3)), span(), None);
        assert!(
            denoted_value_is_closed(&kb, &lit),
            "a literal value is closed"
        );

        // Not closed: a free logical var (the `?n` of `Vector[Int64, ?n]`) — inference.
        let n = kb.intern("n");
        let vid = kb.fresh_var(n);
        let var = NodeOccurrence::new_expr(Expr::Var(Var::Global(vid)), span(), None);
        assert!(
            !denoted_value_is_closed(&kb, &var),
            "a free var is not closed"
        );

        // Not closed: each value-PLACE kind is binder-relative (deferred to the
        // alignment-aware checker). Crucially `CallbackParam` — the `a` of a declared
        // `(a) -> Unit @ Modify[a]` — is the production own-param case the gate MUST
        // defer (testing `Param` alone masked the original miss; see WI-470 review).
        for (i, kind) in [
            SymbolKind::Param,
            SymbolKind::CallbackParam,
            SymbolKind::CallbackResult,
            SymbolKind::OpResult,
            SymbolKind::Field,
            SymbolKind::LocalLet,
        ]
        .into_iter()
        .enumerate()
        {
            let scope = kb.global_scope();
            let s = kb
                .symbols
                .define(&format!("p{i}"), &format!("wi470.test.p{i}"), kind, scope);
            let r = NodeOccurrence::new_expr(Expr::Ref(s), span(), None);
            assert!(
                !denoted_value_is_closed(&kb, &r),
                "a value-place ref ({kind:?}) is binder-relative, not closed",
            );
        }

        // Closed: a ref to a GLOBAL identity (Sort/Entity/Operation) — the `store` of
        // `Modify[store]` (a global resource), compared by symbol identity, not alignment.
        let scope = kb.global_scope();
        let store = kb
            .symbols
            .define("store", "wi470.test.store", SymbolKind::Entity, scope);
        let global_ref = NodeOccurrence::new_expr(Expr::Ref(store), span(), None);
        assert!(
            denoted_value_is_closed(&kb, &global_ref),
            "a global (non-place) ref is closed"
        );
    }

    /// WI-470/WI-600: a parameterized type's binding is READ identically whether the
    /// type is a hash-consed `TermId` (`Fn{List,[T=Int64]}`) or a `Value::Node`
    /// occurrence (the poisoned-receiver shape) — the carrier never erases the
    /// binding. This is the invariant `bind_spec_params_from_carrier` relies on after
    /// switching from `.as_term()` (which dropped the binding of a Node carrier) to
    /// the carrier-agnostic reader. WI-600: the reader (`parameterized_vid_bindings`)
    /// now keys each binding by the owner sort's canonical `Var::Global` param VarId
    /// (identity), not the short name.
    #[test]
    fn wi470_parameterized_vid_bindings_reads_both_carriers() {
        use super::super::{parameterized_vid_bindings, type_param_vid_in_sort};
        use crate::eval::value::Value;
        use crate::intern::SymbolKind;
        use crate::kb::term::{Term, Var};
        use crate::kb::term_view::TermIdView;
        let mut kb = kb_with_prelude();

        // Minimal owner sort `Box` with one type param `Box.T` aliased to a canonical
        // `Var::Global` — the shape the loader emits for `sort T = ?`. Built directly
        // because `register_prelude` loads no parametric stdlib sort, so
        // `type_param_vid_in_sort` has nothing to resolve.
        //
        // WI-954: "the shape the loader emits" is now THREE things, and this test used
        // to build one of them — the `SortAlias` fact. `T` is declared IN `Box`'s own
        // scope and registered as its type parameter (`add_type_param`), and its
        // canonical variable is PUBLISHED (`record_type_param_var`); a hand-built KB
        // that asserts only the fact describes a parameter no reader can find from its
        // sort. `assert_sort_alias` does all three for a loaded program.
        let global_scope = kb.global_scope();
        let global_domain = global_scope.owner();
        kb.symbols
            .define_qualified_only("Box", "Box", SymbolKind::Sort, global_scope);
        let box_sym = kb.resolve_symbol("Box");
        let box_scope = kb.symbols.scope_id(box_sym);
        kb.symbols
            .define_qualified_only("T", "Box.T", SymbolKind::Sort, box_scope);
        let box_t = kb.resolve_symbol("Box.T");
        kb.symbols.add_type_param(box_scope, "T", box_t);
        // SortAlias(Fn{Box.T}, Var::Global(vid)) — pos[0] is the nullary `Fn` head
        // `resolve_sort_alias` extracts the param functor from.
        let vid_seed = kb.fresh_var(box_t);
        let var_term = kb.alloc(Term::Var(Var::Global(vid_seed)));
        kb.record_type_param_var(box_t, vid_seed);
        let alias_sym = kb.resolve_symbol("SortAlias");
        let box_t_head = kb.make_name_term_from_sym(box_t);
        let sort_sort = ClauseKind::Sort;
        kb.assert_fact_carrier(
            alias_sym,
            vec![Value::term(box_t_head), Value::term(var_term)],
            Vec::new(),
            sort_sort,
            global_domain,
            None,
        );
        let vid = type_param_vid_in_sort(&kb, box_sym, box_t)
            .expect("Box.T resolves to its canonical param VarId");

        let int = kb.resolve_symbol("anthill.prelude.Int64");
        let int_ref = kb.make_sort_ref(int);
        let box_ref = kb.make_sort_ref(box_sym);

        // Hash-consed (closed) carrier `Box[T = Int64]` = `Fn{Box, [T = Int64]}`.
        let term_ty = kb.make_parameterized_type(box_ref, &[(box_t, int_ref)]);
        let from_term = parameterized_vid_bindings(&kb, &TermIdView(term_ty), box_sym);

        // Occurrence carrier (the poisoned-receiver shape) `parameterized{Box, [T = Int64]}`.
        let node = kb.make_parameterized_occ(
            TypeChild::Ground(box_ref),
            vec![(box_t, TypeChild::Ground(int_ref))],
            span(),
            None,
        );
        let from_node = parameterized_vid_bindings(&kb, &Value::Node(node), box_sym);

        assert_eq!(
            from_term,
            vec![(vid, int_ref)],
            "binding read from the TermId carrier, keyed by Box.T's canonical VarId"
        );
        assert_eq!(
            from_node, from_term,
            "Node carrier yields the SAME binding (never erased)"
        );
    }

    /// WI-361 regression: `more_general_type`'s bare-vs-parameterized join
    /// normalization must classify a `Value::Node` parameterized via the canonical
    /// `type_head` tag, not its raw functor. After the carrier flip the Node's raw
    /// functor is the base sort (`Modify`), not `parameterized`; a raw-functor read
    /// tags it `None` and the join returns the OVER-SPECIFIC parameterized side
    /// instead of the more-general bare sort. Both orderings must yield the bare.
    #[test]
    fn more_general_type_prefers_bare_over_value_node_parameterized() {
        use crate::eval::value::Value;
        let mut kb = kb_with_prelude();
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");

        // `Value::Node` `Modify[resource = denoted(c)]` (head functor = base sort
        // `Modify` post-flip) vs the bare sort `Modify` (`Ref(Modify)`).
        let node_param = Value::Node(occ_param(&mut kb, modify, p, c));
        let bare_tid = kb.make_sort_ref(modify);
        let bare = Value::term(bare_tid);

        let node_first = super::super::more_general_type(&kb, &node_param, &bare);
        let bare_first = super::super::more_general_type(&kb, &bare, &node_param);
        assert!(
            matches!(node_first, Value::Term { id: t, .. } if t == bare_tid),
            "join should pick the more-general bare sort, got {node_first:?}",
        );
        assert!(
            matches!(bare_first, Value::Term { id: t, .. } if t == bare_tid),
            "join must be commutative (bare sort either way), got {bare_first:?}",
        );
    }

    /// Value-vs-Value: two distinct-`Rc` `Value`-carried `Modify[c]` unify;
    /// `Modify[c]` vs `Modify[d]` is rejected.
    #[test]
    fn value_value_parameterized_denoted_unify() {
        let mut kb = kb_with_prelude();
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");
        let d = kb.intern("d");

        let occ_c1 = occ_param(&mut kb, modify, p, c);
        let occ_c2 = occ_param(&mut kb, modify, p, c);
        let mut s = Substitution::new();
        assert!(
            unify_types(&mut kb, &mut s, &occ_c1, &occ_c2),
            "Value Modify[c] vs Value Modify[c]"
        );

        let occ_d = occ_param(&mut kb, modify, p, d);
        let mut s2 = Substitution::new();
        assert!(
            !unify_types(&mut kb, &mut s2, &occ_c1, &occ_d),
            "Value Modify[c] vs Value Modify[d]"
        );
    }

    /// `Value`-carried arrow `Unit -> Unit` with a single present effect label
    /// `Modify[sym]`: arrow → effects_rows → present → parameterized(Modify,
    /// denoted(Ref sym)). Param/result are ground; the effect label is poisoned.
    fn value_modify_arrow(
        kb: &mut KnowledgeBase,
        modify: crate::intern::Symbol,
        p: crate::intern::Symbol,
        unit_ref: TermId,
        sym: crate::intern::Symbol,
    ) -> Rc<NodeOccurrence> {
        let label = occ_param(kb, modify, p, sym);
        let present = kb.make_present_occ(TypeChild::Node(label), span(), None);
        let rows = kb.make_effects_rows_occ(TypeChild::Node(present), span(), None);
        kb.make_arrow_occ(
            TypeChild::Ground(unit_ref),
            TypeChild::Ground(unit_ref),
            TypeChild::Node(rows),
            1,
            span(),
            None,
        )
    }

    /// WI-361: a `Value::Node` named tuple now exposes the SAME single `fields`
    /// child as its term twin, so `TermView` reads both alike — and
    /// `named_tuple_fields` returns its fields (previously EMPTY for a `Value::Node`
    /// tuple: the closed gap). A ground field reads as `Value::Term`, the poisoned
    /// one as `Value::Node`.
    #[test]
    fn node_named_tuple_reads_fields_through_termview() {
        use crate::eval::value::Value;
        use crate::kb::term_view::{TermView, ViewHead};
        let mut kb = kb_with_prelude();
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");
        let unit = kb.intern("Unit");
        let unit_ref = kb.make_sort_ref(unit);
        let int = kb.intern("Int64");
        let int_ref = kb.make_sort_ref(int);
        let f = kb.intern("f");
        let n = kb.intern("n");
        let fields_key = kb.intern("fields");

        // `(f: Unit -> Unit {Modify[c]}, n: Int)` as a `Value::Node` (poisoned `f`).
        let value_arrow_c = value_modify_arrow(&mut kb, modify, p, unit_ref, c);
        let tuple = Value::Node(kb.make_named_tuple_occ(
            vec![
                (f, TypeChild::Node(value_arrow_c)),
                (n, TypeChild::Ground(int_ref)),
            ],
            span(),
            None,
        ));

        // View surface mirrors the term form: one `fields` named child.
        assert!(
            matches!(tuple.head(&kb), ViewHead::Functor { named_arity: 1, .. }),
            "Node named tuple exposes one `fields` child, got {:?}",
            tuple.head(&kb),
        );
        assert!(
            tuple.named_arg(&kb, fields_key).is_some(),
            "the `fields` child is exposed"
        );

        // The closed gap: `named_tuple_fields` decodes BOTH fields for a Node tuple.
        let by: std::collections::HashMap<_, _> = super::super::named_tuple_fields(&kb, &tuple)
            .into_iter()
            .collect();
        assert_eq!(by.len(), 2, "two fields decoded, got {by:?}");
        assert!(
            matches!(by.get(&n), Some(Value::Term { .. })),
            "`n: Int64` rides as Value::Term"
        );
        assert!(
            matches!(by.get(&f), Some(Value::Node(_))),
            "poisoned `f` rides as Value::Node"
        );
    }

    /// WI-342 occurs-check over a `Value::Node` Rep-A type: binding `?v` to a Node
    /// `named_tuple` whose field mentions `?v` must be REJECTED (the view hides
    /// fields, so `occurs_in_view` walks the occurrence spine via
    /// `occ_contains_var`). Without the complete walk this would create a cyclic
    /// binding `?v = (f: ?v -> …)`.
    #[test]
    fn occurs_check_var_in_node_tuple_field() {
        use crate::kb::term::Var;
        let mut kb = kb_with_prelude();
        let unit = kb.intern("Unit");
        let unit_ref = kb.make_sort_ref(unit);
        let modify = kb.intern("Modify");
        let p = kb.intern("resource");
        let c = kb.intern("c");
        let f = kb.intern("f");
        let vsym = kb.intern("v");
        let vid = kb.fresh_var(vsym);
        let v_term = kb.alloc(Term::Var(Var::Global(vid)));

        // Node arrow `?v -> Unit {Modify[c]}` (Node because of the effect label),
        // with `?v` as its param; wrapped as the single field of a Node tuple.
        let label = occ_param(&mut kb, modify, p, c);
        let present = kb.make_present_occ(TypeChild::Node(label), span(), None);
        let rows = kb.make_effects_rows_occ(TypeChild::Node(present), span(), None);
        let arrow = kb.make_arrow_occ(
            TypeChild::Ground(v_term),
            TypeChild::Ground(unit_ref),
            TypeChild::Node(rows),
            1,
            span(),
            None,
        );
        let tuple = kb.make_named_tuple_occ(vec![(f, TypeChild::Node(arrow))], span(), None);

        let mut s = Substitution::new();
        assert!(
            !unify_types(&mut kb, &mut s, &TermIdView(v_term), &tuple),
            "occurs-check must reject binding ?v to a Node tuple whose field mentions ?v"
        );
    }
}

/// WI-341 Stage B — alpha-equivalence of callback-arrow binders. A callback's
/// own param (`Modify[a]`) is a binder whose alpha-canonical identity is its
/// POSITION; two callbacks' i-th params are the same up to renaming.
#[cfg(test)]
mod wi341_alpha_tests {
    use crate::kb::subst::Substitution;
    use crate::kb::test_support::load_stdlib;
    use crate::kb::KnowledgeBase;

    /// The (`Value`) type of an op's first parameter — a callback arrow.
    fn first_param_type(kb: &KnowledgeBase, op_qn: &str) -> crate::eval::value::Value {
        let op = kb
            .try_resolve_symbol(op_qn)
            .unwrap_or_else(|| panic!("resolve {op_qn}"));
        let rec = crate::kb::op_info::lookup_operation_info(kb, op)
            .unwrap_or_else(|| panic!("opinfo {op_qn}"));
        rec.params.into_iter().next().expect("a param").1
    }

    #[test]
    fn same_position_callback_binders_are_alpha_equivalent() {
        let src = r#"
namespace anthill.test.wi341alpha
  import anthill.prelude.{Unit, Cell}
  operation op1(f: (a: Cell) -> Unit @ Modify[a]) -> Unit
  operation op2(g: (c: Cell) -> Unit @ Modify[c]) -> Unit
end
"#;
        let mut kb = load_stdlib(Some(src));
        let f_arrow = first_param_type(&kb, "anthill.test.wi341alpha.op1");
        let g_arrow = first_param_type(&kb, "anthill.test.wi341alpha.op2");
        // The denoted-bearing callback arrows are `Value::Node` (Stage A).
        assert!(
            matches!(f_arrow, crate::eval::value::Value::Node(_)),
            "op1.f must be Value::Node"
        );
        assert!(
            matches!(g_arrow, crate::eval::value::Value::Node(_)),
            "op2.g must be Value::Node"
        );
        let mut subst = Substitution::new();
        assert!(
            super::super::unify_types(&mut kb, &mut subst, &f_arrow, &g_arrow),
            "`(a) -> Unit @ Modify[a]` and `(c) -> Unit @ Modify[c]` are alpha-equivalent"
        );
    }

    #[test]
    fn different_position_callback_binders_do_not_unify() {
        let src = r#"
namespace anthill.test.wi341alpha2
  import anthill.prelude.{Unit, Cell}
  operation op3(f: (a: Cell, b: Cell) -> Unit @ Modify[a]) -> Unit
  operation op4(g: (c: Cell, d: Cell) -> Unit @ Modify[d]) -> Unit
end
"#;
        let mut kb = load_stdlib(Some(src));
        let f_arrow = first_param_type(&kb, "anthill.test.wi341alpha2.op3");
        let g_arrow = first_param_type(&kb, "anthill.test.wi341alpha2.op4");
        let mut subst = Substitution::new();
        assert!(
            !super::super::unify_types(&mut kb, &mut subst, &f_arrow, &g_arrow),
            "a modify on param 0 vs param 1 must NOT unify (binder positions differ)"
        );
    }
}

/// WI-464 — variance-aware parameterized join (LUB) / meet (GLB). The join now
/// CONSTRUCTS a parameterized type per-binding by declared variance instead of only
/// widening the nominal side, and `meet_types` is its lattice dual (GLB down to the
/// `nothing` bottom). Loads the real stdlib (for the proposal-035 variance facts:
/// Option/Function covariance, Function.A contravariance) plus a small Animal/Box
/// fixture, then drives the private lattice ops directly.
#[cfg(test)]
mod wi464_variance_join_meet_tests {
    use super::super::{
        extract_sort_ref_sym, extract_type, join_types, meet_types, type_dispatch_name_view,
        TypeExtractor,
    };
    use crate::eval::value::Value;
    use crate::intern::Symbol;
    use crate::kb::term::TermId;
    use crate::kb::test_support::load_stdlib;
    use crate::kb::KnowledgeBase;

    const SRC: &str = r#"namespace test.wi464
  import anthill.prelude.{Option, Function, Int64}

  sort Animal
    entity cat
    entity dog
  end

  -- No variance fact ⇒ INVARIANT in T (the safe default for a mutable-shaped sort).
  sort Box
    sort T = ?
    entity box(v: T)
  end
end
"#;

    fn load_kb() -> KnowledgeBase {
        load_stdlib(Some(SRC))
    }

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// A bare `sort_ref` Value for the sort named `qn`.
    fn bare(kb: &mut KnowledgeBase, qn: &str) -> Value {
        let s = sym(kb, qn);
        Value::term(kb.make_sort_ref(s))
    }

    /// A parameterized Value `Base[param = arg, …]`, each arg a bare sort named by qn.
    /// Keys are interned BARE (`"T"` → the bare `T` symbol) — the spelling a written
    /// annotation lowers to.
    fn param(kb: &mut KnowledgeBase, base_qn: &str, binds: &[(&str, &str)]) -> Value {
        let base_sym = sym(kb, base_qn);
        let keyed: Vec<(Symbol, &str)> = binds.iter().map(|(p, a)| (kb.intern(p), *a)).collect();
        param_keyed(kb, base_sym, &keyed)
    }

    /// [`param`] with explicit base and binding-key SYMBOLS. WI-769: the two producers
    /// spell one slot's key differently — a rule citation keys `T` with the sort's
    /// CANONICAL param symbol (`anthill.prelude.Option.T`), a written annotation with
    /// the BARE last segment (`T`) — and a sort's base itself interns under multiple
    /// Symbol copies; this builder lets a test pick each spelling exactly.
    fn param_keyed(kb: &mut KnowledgeBase, base: Symbol, binds: &[(Symbol, &str)]) -> Value {
        let base_ref = kb.make_sort_ref(base);
        let term_binds: Vec<(Symbol, TermId)> = binds
            .iter()
            .map(|(p, arg_qn)| {
                let arg_sym = sym(kb, arg_qn);
                (*p, kb.make_sort_ref(arg_sym))
            })
            .collect();
        Value::term(kb.make_parameterized_type(base_ref, &term_binds))
    }

    /// Decompose a parameterized result into (base sort, bindings).
    fn as_param(kb: &KnowledgeBase, v: &Value) -> (Symbol, Vec<(Symbol, Value)>) {
        match extract_type(kb, v) {
            TypeExtractor::Parameterized { base, bindings } => (base, bindings),
            other => panic!("expected a parameterized type, got {other:?}"),
        }
    }

    /// The value bound to the parameter whose short name is `name`.
    fn binding<'a>(kb: &KnowledgeBase, binds: &'a [(Symbol, Value)], name: &str) -> &'a Value {
        binds
            .iter()
            .find(|(p, _)| kb.local_name_of(*p) == name)
            .map(|(_, v)| v)
            .unwrap_or_else(|| panic!("no `{name}` binding among the result bindings"))
    }

    fn is_sort(kb: &KnowledgeBase, v: &Value, want: Symbol) -> bool {
        extract_sort_ref_sym(kb, v) == Some(want)
    }
    fn is_nothing(kb: &KnowledgeBase, v: &Value) -> bool {
        type_dispatch_name_view(kb, v) == Some("nothing")
    }

    /// COVARIANT: `join(Option[T = cat], Option[T = dog]) = Option[T = Animal]` — the
    /// element parameter's two incomparable values join up the sort lattice to their
    /// common parent, and the result is a freshly CONSTRUCTED parameterized type (the
    /// behaviour join never had before WI-464).
    #[test]
    fn covariant_join_builds_parameterized_lub() {
        let mut kb = load_kb();
        let (animal, option) = (
            sym(&kb, "test.wi464.Animal"),
            sym(&kb, "anthill.prelude.Option"),
        );
        let a = param(
            &mut kb,
            "anthill.prelude.Option",
            &[("T", "test.wi464.Animal.cat")],
        );
        let b = param(
            &mut kb,
            "anthill.prelude.Option",
            &[("T", "test.wi464.Animal.dog")],
        );
        let j = join_types(&mut kb, a, b).expect("Option[cat] and Option[dog] have a join");
        let (base, binds) = as_param(&kb, &j);
        assert_eq!(base, option, "join base sort is Option");
        assert!(
            is_sort(&kb, binding(&kb, &binds, "T"), animal),
            "T binding joins cat/dog to Animal"
        );
    }

    /// INVARIANT: `Box` has no variance fact, so its `T` is invariant. The two
    /// binding values differ, so there is no parameterized LUB — the join falls back
    /// to the conservative common supertype, the bare base sort `Box`.
    #[test]
    fn invariant_join_falls_back_to_bare_base() {
        let mut kb = load_kb();
        let box_sym = sym(&kb, "test.wi464.Box");
        let a = param(&mut kb, "test.wi464.Box", &[("T", "test.wi464.Animal.cat")]);
        let b = param(&mut kb, "test.wi464.Box", &[("T", "test.wi464.Animal.dog")]);
        let j = join_types(&mut kb, a, b).expect("the bare base sort is a common supertype");
        assert!(
            is_sort(&kb, &j, box_sym),
            "an unequal invariant binding widens to bare Box, got {j:?}"
        );
    }

    /// CONTRAVARIANT: `Function.A` is contravariant, so its arm of the join takes the
    /// MEET of the two argument types — `meet(cat, dog) = nothing` — while the
    /// covariant `B` joins normally: `join(Function[A=cat,B=Int], Function[A=dog,B=Int])
    /// = Function[A = nothing, B = Int]`.
    #[test]
    fn contravariant_join_uses_meet() {
        let mut kb = load_kb();
        let (function, int) = (
            sym(&kb, "anthill.prelude.Function"),
            sym(&kb, "anthill.prelude.Int64"),
        );
        let a = param(
            &mut kb,
            "anthill.prelude.Function",
            &[
                ("A", "test.wi464.Animal.cat"),
                ("B", "anthill.prelude.Int64"),
            ],
        );
        let b = param(
            &mut kb,
            "anthill.prelude.Function",
            &[
                ("A", "test.wi464.Animal.dog"),
                ("B", "anthill.prelude.Int64"),
            ],
        );
        let j = join_types(&mut kb, a, b).expect("two Function types have a join");
        let (base, binds) = as_param(&kb, &j);
        assert_eq!(base, function, "join base sort is Function");
        assert!(
            is_nothing(&kb, binding(&kb, &binds, "A")),
            "contravariant A meets cat/dog to nothing"
        );
        assert!(
            is_sort(&kb, binding(&kb, &binds, "B"), int),
            "covariant B joins Int/Int to Int"
        );
    }

    /// GLB basics — `meet_types` is total (the lattice has a `nothing` bottom):
    /// `meet(Animal, cat) = cat` (the subtype), `meet(cat, dog) = nothing`
    /// (incomparable siblings), and a covariant parameterized meet recurses:
    /// `meet(Option[T=cat], Option[T=dog]) = Option[T = nothing]`.
    #[test]
    fn meet_glb_basics() {
        let mut kb = load_kb();
        let (cat, option) = (
            sym(&kb, "test.wi464.Animal.cat"),
            sym(&kb, "anthill.prelude.Option"),
        );

        let animal_v = bare(&mut kb, "test.wi464.Animal");
        let cat_v = bare(&mut kb, "test.wi464.Animal.cat");
        let m1 = meet_types(&mut kb, animal_v, cat_v);
        assert!(
            is_sort(&kb, &m1, cat),
            "meet(Animal, cat) is the subtype cat, got {m1:?}"
        );

        let cat_v = bare(&mut kb, "test.wi464.Animal.cat");
        let dog_v = bare(&mut kb, "test.wi464.Animal.dog");
        let m2 = meet_types(&mut kb, cat_v, dog_v);
        assert!(
            is_nothing(&kb, &m2),
            "meet(cat, dog) is the bottom type nothing, got {m2:?}"
        );

        let oa = param(
            &mut kb,
            "anthill.prelude.Option",
            &[("T", "test.wi464.Animal.cat")],
        );
        let ob = param(
            &mut kb,
            "anthill.prelude.Option",
            &[("T", "test.wi464.Animal.dog")],
        );
        let m3 = meet_types(&mut kb, oa, ob);
        let (base, binds) = as_param(&kb, &m3);
        assert_eq!(base, option, "meet base sort is Option");
        assert!(
            is_nothing(&kb, binding(&kb, &binds, "T")),
            "covariant T meets cat/dog to nothing"
        );
    }

    /// WI-769 — the binding-key rule ([`binding_for_param`]) in the LUB. One side keys
    /// `T` with Option's CANONICAL param symbol (the spelling a rule citation's
    /// `sort_type_params_as_pairs` produces), the other with the BARE `T` (the spelling
    /// a written annotation lowers to — [`param`] builds it). Raw `q == param` missed
    /// the pair, so the join silently dropped the whole schema to the bare base sort —
    /// which a downstream check then accepted against ANY parameterization (a bare `S`
    /// conforms to `S[anything]`), with no diagnostic. The join must bridge the
    /// spellings and keep `T = Animal` in BOTH argument orders, and the result must
    /// carry the CANONICAL key in both — the producer-canonicalized construction that
    /// keeps `join_types`' documented commutativity structural.
    #[test]
    fn wi769_join_bridges_canonical_vs_bare_param_keys() {
        let mut kb = load_kb();
        let (animal, option) = (
            sym(&kb, "test.wi464.Animal"),
            sym(&kb, "anthill.prelude.Option"),
        );
        let canon_t = sym(&kb, "anthill.prelude.Option.T");
        assert_ne!(
            canon_t,
            kb.intern("T"),
            "the two key spellings must be distinct symbols"
        );
        let a = param_keyed(&mut kb, option, &[(canon_t, "test.wi464.Animal.cat")]);
        let b = param(
            &mut kb,
            "anthill.prelude.Option",
            &[("T", "test.wi464.Animal.dog")],
        );
        for (x, y) in [(a.clone(), b.clone()), (b, a)] {
            let j = join_types(&mut kb, x, y)
                .expect("cross-spelled Option[cat] / Option[dog] must still join");
            let (base, binds) = as_param(&kb, &j);
            assert_eq!(base, option, "join base sort is Option");
            assert!(
                is_sort(&kb, binding(&kb, &binds, "T"), animal),
                "T must join cat/dog to Animal across the two key spellings — not be \
                 dropped to the bare base sort",
            );
            assert_eq!(
                binds[0].0, canon_t,
                "the result key is the canonical param symbol in both orders \
                 (structural commutativity)",
            );
        }
    }

    /// WI-769 — the same cross-spelled pair through the GLB. Pre-fix the key miss
    /// dropped the meet to the WHOLE-type bottom (`nothing`); it must instead keep the
    /// parameterized shape and meet per-binding (`Option[T = meet(cat, dog)]` =
    /// `Option[T = nothing]`), canonically keyed, in both argument orders.
    #[test]
    fn wi769_meet_bridges_canonical_vs_bare_param_keys() {
        let mut kb = load_kb();
        let option = sym(&kb, "anthill.prelude.Option");
        let canon_t = sym(&kb, "anthill.prelude.Option.T");
        assert_ne!(
            canon_t,
            kb.intern("T"),
            "the two key spellings must be distinct symbols"
        );
        let a = param_keyed(&mut kb, option, &[(canon_t, "test.wi464.Animal.cat")]);
        let b = param(
            &mut kb,
            "anthill.prelude.Option",
            &[("T", "test.wi464.Animal.dog")],
        );
        for (x, y) in [(a.clone(), b.clone()), (b, a)] {
            let m = meet_types(&mut kb, x, y);
            let (base, binds) = as_param(&kb, &m);
            assert_eq!(base, option, "meet base sort is Option");
            assert!(
                is_nothing(&kb, binding(&kb, &binds, "T")),
                "the meet must keep the parameterized shape (T meets to nothing), not \
                 bottom out the whole type",
            );
            assert_eq!(binds[0].0, canon_t, "canonical result key in both orders");
        }
    }

    /// WI-769 — the BASE guard: canonical sort identity, not raw symbol identity. A
    /// sort interns under multiple Symbol copies (a scan-time unresolved copy vs the
    /// resolved canonical — the wi617 twin pattern); the enrolled unify/subtype twins
    /// compare bases through the full type relation, which canonicalizes, but the raw
    /// `a_base != b_base` guard here read a twin pair as different sorts and turned a
    /// same-sort combine into a spurious no-join. Both argument orders, because the
    /// construction must land on the CANONICAL base (canonicalize at the producer,
    /// WI-581) whichever side carries the twin — a regression routing construction
    /// through either side's RAW symbol fails exactly one of the two orders.
    #[test]
    fn wi769_join_matches_base_sorts_canonically() {
        let mut kb = load_kb();
        let (animal, option) = (
            sym(&kb, "test.wi464.Animal"),
            sym(&kb, "anthill.prelude.Option"),
        );
        let canon_t = sym(&kb, "anthill.prelude.Option.T");
        let twin = kb.intern("anthill.prelude.Option");
        assert_ne!(twin, option, "the twin must be a distinct Symbol copy");
        assert_eq!(
            kb.canonical_sort_sym(twin),
            option,
            "…that canonicalizes to Option"
        );
        let bare_t = kb.intern("T");
        let a = param_keyed(&mut kb, twin, &[(bare_t, "test.wi464.Animal.cat")]);
        let b = param(
            &mut kb,
            "anthill.prelude.Option",
            &[("T", "test.wi464.Animal.dog")],
        );
        for (x, y) in [(a.clone(), b.clone()), (b, a)] {
            let j = join_types(&mut kb, x, y)
                .expect("Option under a twin base Symbol must still join with Option");
            let (base, binds) = as_param(&kb, &j);
            assert_eq!(base, option, "the combine constructs on the CANONICAL base");
            assert!(
                is_sort(&kb, binding(&kb, &binds, "T"), animal),
                "T joins cat/dog to Animal"
            );
            assert_eq!(binds[0].0, canon_t, "…and on the canonical param key");
        }
    }

    /// WI-769 (review) — label-bridging is not injective: a DUPLICATE-keyed side (the
    /// duplicate-slot producer defect class WI-764 recorded) resolves BOTH its entries
    /// to b's single `A` slot and never consults b's `B` — a constructed result would
    /// be a duplicate-keyed type that silently drops `B`, not even a bound of `b`. The
    /// combine must bow out to the conservative whole-type bound (the bare base sort).
    /// (The duplicate is built value-equal deliberately: `extract_type` reads named
    /// args BY KEY, so a duplicate-keyed term always PRESENTS as its first value
    /// repeated — a values-differing duplicate cannot reach the lattice as such. And
    /// `b`'s `A` must be a SIBLING of `a`'s, else `b <: a` holds and `join_types`
    /// returns `a` before the same-base combine runs at all.)
    #[test]
    fn wi769_duplicate_keyed_side_falls_back_conservatively() {
        let mut kb = load_kb();
        let function = sym(&kb, "anthill.prelude.Function");
        let canon_a = sym(&kb, "anthill.prelude.Function.A");
        let a = param_keyed(
            &mut kb,
            function,
            &[
                (canon_a, "test.wi464.Animal.cat"),
                (canon_a, "test.wi464.Animal.cat"),
            ],
        );
        let b = param(
            &mut kb,
            "anthill.prelude.Function",
            &[
                ("A", "test.wi464.Animal.dog"),
                ("B", "anthill.prelude.Int64"),
            ],
        );
        let j = join_types(&mut kb, a, b).expect("the bare base sort is a common supertype");
        assert!(
            is_sort(&kb, &j, function),
            "a duplicate-keyed side must fall back to the bare base sort, not mint a \
             duplicate-keyed type that drops B, got {j:?}",
        );
    }

    /// WI-769 (review sweep) — BOTH sides carrying both spellings of one slot: each
    /// a-key identity-hits its own b slot (the used-guard can't see it), and both
    /// re-key to the same declared symbol. The re-key COLLISION check must bow out
    /// to the conservative bound rather than mint `Option[Option.T = .., Option.T
    /// = ..]` — a duplicate-keyed type whose by-key reads silently drop the second
    /// value.
    #[test]
    fn wi769_symmetric_mixed_spelling_duplicates_fall_back() {
        let mut kb = load_kb();
        let option = sym(&kb, "anthill.prelude.Option");
        let canon_t = sym(&kb, "anthill.prelude.Option.T");
        let bare_t = kb.intern("T");
        let a = param_keyed(
            &mut kb,
            option,
            &[
                (canon_t, "test.wi464.Animal.cat"),
                (bare_t, "anthill.prelude.Int64"),
            ],
        );
        let b = param_keyed(
            &mut kb,
            option,
            &[
                (canon_t, "test.wi464.Animal.dog"),
                (bare_t, "anthill.prelude.Int64"),
            ],
        );
        let j = join_types(&mut kb, a, b).expect("the bare base sort is a common supertype");
        assert!(
            is_sort(&kb, &j, option),
            "symmetric mixed-spelling duplicates must fall back to the bare base \
             sort, not mint a duplicate-keyed result, got {j:?}",
        );
    }

    /// WI-769 (review sweep) — a FOREIGN dotted key (another sort's `T`: here
    /// `Box.T` riding an `Option`) must keep its spelling: re-keying it to
    /// `Option.T` by short name would be a guess (the Identity-mode doc calls that
    /// pairing out), and the declared-scan gate keeps `same_label`'s both-dotted
    /// `debug_assert` off this path — pre-gate, this input PANICKED debug builds.
    #[test]
    fn wi769_foreign_dotted_key_keeps_its_spelling() {
        let mut kb = load_kb();
        let (animal, option) = (
            sym(&kb, "test.wi464.Animal"),
            sym(&kb, "anthill.prelude.Option"),
        );
        let box_t = sym(&kb, "test.wi464.Box.T");
        let a = param_keyed(&mut kb, option, &[(box_t, "test.wi464.Animal.cat")]);
        let b = param_keyed(&mut kb, option, &[(box_t, "test.wi464.Animal.dog")]);
        let j = join_types(&mut kb, a, b).expect("same-keyed Option[cat]/Option[dog] joins");
        let (base, binds) = as_param(&kb, &j);
        assert_eq!(base, option, "join base sort is Option");
        assert!(
            is_sort(&kb, binding(&kb, &binds, "T"), animal),
            "T joins cat/dog to Animal"
        );
        assert_eq!(
            binds[0].0, box_t,
            "a foreign dotted key keeps its spelling — no short-name re-key hijack",
        );
    }
}

#[cfg(test)]
mod wi617_canonical_provider_match_tests {
    //! WI-617 — `spec_has_any_providers` must compare a provider fact's spec base
    //! against the queried spec symbol under `canonical_sort_sym`, matching its
    //! sibling `impl_sorts_providing_spec`. A sort interns under multiple `Symbol`
    //! ids (a scan-time unresolved copy vs the resolved load-time copy). When a
    //! `SortProvidesInfo` fact's spec base interns under the NON-canonical copy, a
    //! raw `==` reads false, `carrier_is_abstract_spec` returns false, and the
    //! abstract-spec-carrier dispatch gates (WI-598/601/608/609/614) spuriously
    //! skip — regressing a legitimately-abstract spec value (a `FiniteCollection`
    //! `map`/`filter` result) to a loud "no such member (dot dispatch)" error.
    //!
    //! The load pipeline canonicalizes at the producer (WI-581), so this divergent
    //! interning is not reproducible through a source-level load — the test injects
    //! it directly, which is the level at which the gap is observable.
    use super::super::{carrier_is_abstract_spec, spec_has_any_providers};
    use crate::intern::SymbolKind;
    use crate::kb::term::Term;
    use crate::kb::ClauseKind;
    use crate::kb::KnowledgeBase;
    use smallvec::SmallVec;

    #[test]
    fn provider_fact_spec_base_under_noncanonical_symbol_still_counts() {
        let mut kb = KnowledgeBase::new();

        // The reflection functor `spec_has_any_providers` resolves by QN. Defined
        // (not merely interned) so `try_resolve_symbol` finds it AND so the fact's
        // head functor is canonical (satisfying the WI-581 assert on assert_fact).
        let root_scope = kb.global_scope();
        let provides_sym = kb.define_symbol(
            "SortProvidesInfo",
            "anthill.reflect.SortProvidesInfo",
            SymbolKind::Entity,
            root_scope,
        );

        // S_alt: an unresolved scan-time interning of the spec's QN. Interned
        // BEFORE the `define` below so the resolved copy becomes the canonical
        // `by_qualified_name` entry and S_alt is the non-canonical twin.
        let s_alt = kb.intern("test.finite.FiniteCollection");
        // S_canon: the resolved copy — registered in `by_qualified_name`, hence
        // the canonical symbol for the QN. No entity children ⇒ a spec sort.
        let s_canon = kb.define_symbol(
            "FiniteCollection",
            "test.finite.FiniteCollection",
            SymbolKind::Sort,
            root_scope,
        );

        // Precondition that makes the test discriminate raw `==` from canonical:
        // the two internings are distinct symbols yet canonicalize equal.
        assert_ne!(
            s_alt, s_canon,
            "the two internings must be distinct symbols"
        );
        assert_eq!(
            kb.canonical_sort_sym(s_alt),
            s_canon,
            "S_alt must canonicalize to S_canon",
        );

        // A provider fact `SortProvidesInfo(spec: Ref(S_alt))` — the spec base
        // carries the NON-canonical symbol, while the head functor stays canonical.
        let spec_key = kb.intern("spec");
        let spec_ref = kb.alloc(Term::Ref(s_alt));
        let head = kb.alloc(Term::Fn {
            functor: provides_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(spec_key, spec_ref)]),
        });
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        kb.assert_fact(head, sort, domain, None);

        // Query with the canonical symbol. Pre-fix `view_base_sym == spec_sort`
        // (S_alt == S_canon) is false; the canonical comparison is true.
        assert!(
            spec_has_any_providers(&kb, s_canon),
            "a provider fact whose spec base interns non-canonically must still \
             count as a provider (WI-617)",
        );
        // Query side is canonicalized symmetrically: querying with the
        // non-canonical twin also matches (both sides pass through
        // `canonical_sort_sym`).
        assert!(
            spec_has_any_providers(&kb, s_alt),
            "querying with the non-canonical twin must also match (query-side \
             canonicalization, WI-617)",
        );
        // The load-bearing consumer: the abstract-spec-carrier dispatch gate.
        assert!(
            carrier_is_abstract_spec(&kb, s_canon),
            "carrier_is_abstract_spec must see the non-canonical provider (WI-617)",
        );

        // Negative control: an unrelated sort with NO provider fact must read
        // false — pinning that the predicate is not vacuously true (a future
        // refactor that always returned true would be caught here).
        let unrelated = kb.define_symbol(
            "Unrelated",
            "test.finite.Unrelated",
            SymbolKind::Sort,
            root_scope,
        );
        assert!(
            !spec_has_any_providers(&kb, unrelated),
            "a sort with no provider fact must not count as having providers",
        );
    }
}

#[cfg(test)]
mod wi621_carrier_neutral_goal_subst {
    //! WI-621 — the σ substitution ([`substitute_ref_terms`]) and the conjunction
    //! split ([`clause_conjuncts`]) over a value precondition / guard / postcondition
    //! goal are CARRIER-NEUTRAL: a DENOTED `Value::Node` goal grounds its `var_ref`
    //! parameters and decomposes its `conjunction` through the View layer, never
    //! reifying to a `TermId` (the retired `value_goal_term`) and never converting
    //! term↔occurrence. The common `Value::Term` goal rides the term fast path
    //! unchanged (covered by wi067 / wi539 / wi557); these tests exercise precisely
    //! the `Value::Node` carrier that fast path skips.
    use super::super::{clause_conjuncts, substitute_ref_terms};
    use crate::eval::value::Value;
    use crate::intern::{Symbol, SymbolKind};
    use crate::kb::load::register_prelude;
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use crate::kb::term::{Literal, Term};
    use crate::kb::term_view::{TermView, ViewHead};
    use crate::kb::KnowledgeBase;
    use crate::span::{SourceId, SourceSpan};
    use std::collections::HashMap;
    use std::rc::Rc;

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 1)
    }

    fn e(x: Expr) -> Rc<NodeOccurrence> {
        NodeOccurrence::new_expr(x, span(), None)
    }

    /// A `register_prelude` KB with the two reflect functors these tests build by
    /// hand (`var_ref`, `conjunction`) registered — `register_prelude` covers
    /// `eq` / literals but not the reflect `Expr` constructors a full stdlib load
    /// would. `name` is interned so a `var_ref`'s `name` child reads.
    fn kb() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let global = kb.global_scope();
        kb.symbols.define_qualified_only(
            "var_ref",
            "anthill.reflect.Expr.var_ref",
            SymbolKind::Entity,
            global,
        );
        kb.symbols
            .define_qualified_only("conjunction", "conjunction", SymbolKind::Entity, global);
        kb.intern("name");
        kb
    }

    /// σ grounds a `var_ref` parameter inside a DENOTED `Value::Node` goal:
    /// `eq(var_ref(b), 0)` with σ = {b ↦ 5} becomes `eq(5, 0)` — read + rebuilt
    /// through the View layer as a carrier-neutral `Value::Entity` (NOT a reified
    /// opaque `Value::Term` of the whole goal), with the parameter grounded.
    #[test]
    fn node_goal_var_ref_grounds_carrier_neutrally() {
        let mut kb = kb();
        let b = kb.intern("b");
        let eq = kb.eq_functor();
        let goal = Value::Node(e(Expr::Apply {
            recv_type: None,
            functor: eq,
            pos_args: vec![e(Expr::VarRef { name: b }), e(Expr::Const(Literal::Int(0)))],
            named_args: vec![],
            type_args: vec![],
        }));

        let mut sigma: HashMap<Symbol, _> = HashMap::new();
        sigma.insert(b, kb.alloc(Term::Const(Literal::Int(5))));
        let grounded = substitute_ref_terms(&mut kb, &goal, &sigma);

        // A transient goal is legitimately a non-hash-consed `Value::Entity` — never
        // reified whole to an opaque `Value::Term`.
        assert!(
            matches!(grounded, Value::Entity { .. }),
            "expected Entity, got {grounded:?}"
        );
        // Structurally `eq(5, 0)`.
        match grounded.head(&kb) {
            ViewHead::Functor {
                functor: Some(f),
                pos_arity,
                ..
            } => {
                assert_eq!(f, eq);
                assert_eq!(pos_arity, 2);
            }
            other => panic!("expected Functor{{eq}}, got {other:?}"),
        }
        match grounded.pos_arg(&kb, 0).expect("operand 0").head(&kb) {
            ViewHead::Const(Literal::Int(5)) => {}
            other => panic!("var_ref(b) must ground to 5, got {other:?}"),
        }
        match grounded.pos_arg(&kb, 1).expect("operand 1").head(&kb) {
            ViewHead::Const(Literal::Int(0)) => {}
            other => panic!("second operand must stay 0, got {other:?}"),
        }
    }

    /// An UNMAPPED `var_ref` (a parameter with no σ binding — a symbolic argument)
    /// survives substitution intact: the open-world variable the resolver flounders
    /// on, so nothing is spuriously grounded.
    #[test]
    fn node_goal_unmapped_var_ref_survives() {
        let mut kb = kb();
        let b = kb.intern("b");
        let var_ref_sym = kb.resolve_symbol("anthill.reflect.Expr.var_ref");
        let eq = kb.eq_functor();
        let goal = Value::Node(e(Expr::Apply {
            recv_type: None,
            functor: eq,
            pos_args: vec![e(Expr::VarRef { name: b }), e(Expr::Const(Literal::Int(0)))],
            named_args: vec![],
            type_args: vec![],
        }));
        // σ binds a DIFFERENT symbol, so `b` stays symbolic.
        let mut sigma: HashMap<Symbol, _> = HashMap::new();
        sigma.insert(kb.intern("other"), kb.alloc(Term::Const(Literal::Int(9))));
        let out = substitute_ref_terms(&mut kb, &goal, &sigma);
        match out.pos_arg(&kb, 0).expect("operand 0").head(&kb) {
            ViewHead::Functor {
                functor: Some(f), ..
            } => {
                assert_eq!(
                    f, var_ref_sym,
                    "an unmapped var_ref must survive, not ground"
                )
            }
            other => panic!("expected surviving var_ref, got {other:?}"),
        }
    }

    /// `clause_conjuncts` decomposes `conjunction(g1, g2)` carrier-neutrally when it
    /// is a DENOTED `Value::Node`, yielding the two goal conjuncts carrier-faithful
    /// (each still a `Value::Node`) — never reifying the wrapper.
    #[test]
    fn node_conjunction_splits_carrier_faithfully() {
        let mut kb = kb();
        let conjunction = kb.resolve_symbol("conjunction");
        let eq = kb.eq_functor();
        let goal = |n: i64| {
            e(Expr::Apply {
                recv_type: None,
                functor: eq,
                pos_args: vec![
                    e(Expr::Const(Literal::Int(n))),
                    e(Expr::Const(Literal::Int(0))),
                ],
                named_args: vec![],
                type_args: vec![],
            })
        };
        let conj = Value::Node(e(Expr::Apply {
            recv_type: None,
            functor: conjunction,
            pos_args: vec![goal(1), goal(2)],
            named_args: vec![],
            type_args: vec![],
        }));

        let parts = clause_conjuncts(&kb, &conj);
        assert_eq!(
            parts.len(),
            2,
            "conjunction(g1, g2) must split into 2 conjuncts"
        );
        assert!(
            parts.iter().all(|p| matches!(p, Value::Node(_))),
            "conjuncts stay carrier-faithful (Node), not reified",
        );

        // A non-conjunction goal is its own single conjunct.
        assert_eq!(clause_conjuncts(&kb, &Value::Node(goal(7))).len(), 1);
    }

    /// The rebuilt `Value::Entity` re-canonicalizes named args: a DENOTED `Value::Node`
    /// goal whose named children are in NON-canonical source order (which a
    /// non-entity-functor occurrence keeps) is rebuilt with `canonicalize_record_named_args`
    /// order — the invariant the order-sensitive discrim tree matches against. Without
    /// the sort the goal would descend a different trie path than a canonically-keyed
    /// KB fact and spuriously miss.
    #[test]
    fn node_goal_named_args_rebuilt_canonically() {
        let mut kb = kb();
        // Intern `a` before `z` so `a` has the lower Symbol index (the canonical
        // fallback order for a non-entity functor). `pred` is a plain (non-entity)
        // functor, so its occurrence keeps source order.
        let a = kb.intern("a");
        let z = kb.intern("z");
        let b = kb.intern("b");
        let pred = kb.intern("pred");
        // Build the goal with named args in NON-canonical order: `z` before `a`.
        let goal = Value::Node(e(Expr::Apply {
            recv_type: None,
            functor: pred,
            pos_args: vec![],
            named_args: vec![
                (z, e(Expr::VarRef { name: b })),
                (a, e(Expr::Const(Literal::Int(0)))),
            ],
            type_args: vec![],
        }));
        assert_eq!(
            goal.named_keys(&kb),
            vec![z, a],
            "source order is non-canonical (z, a)"
        );

        let mut sigma: HashMap<Symbol, _> = HashMap::new();
        sigma.insert(b, kb.alloc(Term::Const(Literal::Int(5))));
        let grounded = substitute_ref_terms(&mut kb, &goal, &sigma);

        // The rebuild must match canonicalize_record_named_args order for `pred`.
        let mut expected = vec![(z, ()), (a, ())];
        kb.canonicalize_record_named_args(pred, &mut expected);
        let expected_keys: Vec<Symbol> = expected.iter().map(|(k, _)| *k).collect();
        assert_ne!(
            expected_keys,
            vec![z, a],
            "canonical order must differ from source"
        );
        assert_eq!(
            grounded.named_keys(&kb),
            expected_keys,
            "rebuilt Entity named args must be canonically ordered",
        );
    }

    /// A σ-parameter nested inside a native `Value::Tuple` operand of a goal is
    /// grounded — the functor-less-aggregate arm recurses into the tuple (parity with
    /// the term-side walk descending a tuple `Term::Fn`), not the verbatim `_` clone.
    #[test]
    fn tuple_operand_var_ref_grounds() {
        let mut kb = kb();
        let b = kb.intern("b");
        let pred = kb.intern("pred");
        let var_ref_b = kb.make_var_ref_term(b);
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        // Goal `pred((var_ref(b), 0))` with a native tuple operand.
        let tuple = Value::Tuple {
            pos: Rc::from(vec![Value::term(var_ref_b), Value::term(zero)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };
        let goal = Value::Entity {
            functor: pred,
            pos: Rc::from(vec![tuple]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
        };

        let mut sigma: HashMap<Symbol, _> = HashMap::new();
        sigma.insert(b, kb.alloc(Term::Const(Literal::Int(5))));
        let grounded = substitute_ref_terms(&mut kb, &goal, &sigma);

        let tuple_out = grounded.pos_arg(&kb, 0).expect("tuple operand");
        assert!(
            matches!(tuple_out.head(&kb), ViewHead::Functor { functor: None, .. }),
            "operand stays a functor-less tuple",
        );
        match tuple_out.pos_arg(&kb, 0).expect("tuple elem 0").head(&kb) {
            ViewHead::Const(Literal::Int(5)) => {}
            other => panic!("var_ref(b) inside the tuple must ground to 5, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod wi799_tuple_align_policy {
    //! WI-799/WI-803 — [`TupleAlign`] is a POLICY over three axes, and the equality
    //! relation gets its own discipline.
    //!
    //! These drive [`align_named_tuple_slots`] and [`unify_named_tuple`]
    //! DIRECTLY rather than through a surface program, deliberately. The
    //! asymmetry this ticket fixes is not reachable from source: the only caller
    //! that reaches a width-mismatched `unify_named_tuple` is `check_apply_iter`'s
    //! INFERENCE unify, whose failure is tolerated because conformance
    //! ([`types_compatible`], which legitimately keeps width) decides acceptance
    //! separately — measured, by instrumenting every `unify_named_tuple` call in
    //! the suite (8254 of them; 4 width-mismatched, all from that one site, and
    //! flipping the mode changed no test outcome). So a surface test would pin
    //! nothing, and the relation has to be pinned where it lives.
    use super::super::*;
    use crate::kb::load::register_prelude;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    /// `(a: Int64, b: Int64)` and `(a: Int64)` as field lists.
    fn fields(kb: &mut KnowledgeBase, names: &[&str]) -> Vec<(Symbol, Value)> {
        let int = kb.resolve_symbol("anthill.prelude.Int64");
        let int_ref = kb.alloc(Term::Ref(int));
        names
            .iter()
            .map(|n| (kb.intern(n), Value::Term { id: int_ref }))
            .collect()
    }

    fn aligns(kb: &mut KnowledgeBase, a: &[&str], b: &[&str], mode: TupleAlign) -> bool {
        slots(kb, a, b, mode).is_some()
    }

    fn slots(
        kb: &mut KnowledgeBase,
        a: &[&str],
        b: &[&str],
        mode: TupleAlign,
    ) -> Option<AlignedSlots> {
        let (af, bf) = (fields(kb, a), fields(kb, b));
        align_named_tuple_slots(kb, &af, &bf, mode)
    }

    /// WI-800 — WHICH slot of `a` each `b` component lands on, now that the
    /// alignment returns the correspondence itself rather than the type pairs.
    /// [`thread_expected_tuple_fields`] writes back into those slots, so the
    /// indices are load-bearing and not merely an implementation detail of the
    /// field-wise relations (which only ever consume them in order).
    #[test]
    fn alignment_reports_the_slot_each_component_matched() {
        let mut kb = kb_with_prelude();
        // Compared as SLICES so the assertion reads the returned `AlignedSlots`
        // itself rather than a `Vec` copy of it — the inline capacity can change
        // without touching this test.
        assert_eq!(
            slots(&mut kb, &["a", "b", "c"], &["a", "c"], TupleAlign::DATA).as_deref(),
            Some([0usize, 2].as_slice()),
            "a width drop must report the SURVIVING components' own slots",
        );
        // WI-803: DATA is `TupleOrder::Free`, so a PERMUTATION aligns — and the
        // slots report where each component actually sits, which is the whole
        // content of the correspondence for a reader that fetches by name.
        assert_eq!(
            slots(
                &mut kb,
                &["a", "b", "c"],
                &["c", "a"].as_slice(),
                TupleAlign::DATA
            )
            .as_deref(),
            Some([2usize, 0].as_slice()),
            "a permuted b-list reports each component's own slot in `a`",
        );
        // WI-803 INVERTED THIS. The scan used to RESUME after the previous match,
        // so a repeated label was taken by the match after the previous one —
        // `["a", "b", "a"]` against `["b", "a"]` gave slots [1, 2], the SECOND `a`.
        // `TupleOrder::Free` looks each name up from the start, which is
        // `field_access`' own rule, so it now takes the FIRST — and the relation
        // and the reader stop disagreeing on a duplicate label (WI-805).
        assert_eq!(
            slots(&mut kb, &["a", "b", "a"], &["b", "a"], TupleAlign::DATA).as_deref(),
            Some([1usize, 0].as_slice()),
            "each name is looked up from the START, so `a` is the FIRST one",
        );
        // ORDER still binds where position is load-bearing: the same permutation
        // is REFUSED for a parameter list and for an equality.
        assert!(
            !aligns(&mut kb, &["a", "b"], &["b", "a"], TupleAlign::PARAM_LIST),
            "a parameter list is applied positionally — no permutation",
        );
        assert!(
            !aligns(&mut kb, &["a", "b"], &["b", "a"], TupleAlign::EQUALITY),
            "order is part of a tuple's IDENTITY, so a permutation is not an equality",
        );
    }

    /// THE DEFECT. An equality relation that answers differently depending on
    /// which side the caller passed first. Under the old `ByName` mode — width
    /// SUBTYPING — the first of these succeeded and the second failed.
    #[test]
    fn equality_is_symmetric_under_width() {
        let mut kb = kb_with_prelude();
        assert!(
            !aligns(&mut kb, &["a", "b"], &["a"], TupleAlign::EQUALITY),
            "EQUALITY must not take a width step in the wide→narrow direction",
        );
        assert!(
            !aligns(&mut kb, &["a"], &["a", "b"], TupleAlign::EQUALITY),
            "EQUALITY must not take a width step in the narrow→wide direction",
        );
    }

    /// The control for the test above: the SUBTYPING discipline is where width
    /// belongs, and it is directional BY DESIGN there — `<:` is not symmetric.
    /// If this ever goes symmetric, width subtyping has been broken, and §4.5's
    /// "its inhabitants arrive by width subtyping from a wider tuple" (the only
    /// way a one-component tuple type is inhabited) goes with it.
    #[test]
    fn data_subtyping_keeps_its_direction() {
        let mut kb = kb_with_prelude();
        assert!(
            aligns(&mut kb, &["a", "b"], &["a"], TupleAlign::DATA),
            "DATA <: must admit width — a wider actual satisfies a narrower expected",
        );
        assert!(
            !aligns(&mut kb, &["a"], &["a", "b"], TupleAlign::DATA),
            "DATA <: must NOT invent components the actual does not have",
        );
    }

    /// WI-804: the width drop is NAME-KEYED, from anywhere, not a prefix.
    #[test]
    fn data_width_drops_from_the_middle() {
        let mut kb = kb_with_prelude();
        assert!(aligns(
            &mut kb,
            &["a", "b", "c"],
            &["a", "c"],
            TupleAlign::DATA
        ));
    }

    /// The SECOND axis, which WI-788 shipped a comment denying existed. Granting
    /// the synthetic escape to a data tuple would relate `(a: Int64, b: Int64)` to
    /// `(Int64, Int64)` — proposal 004 rule 4 makes those different types.
    #[test]
    fn synthetic_escape_is_the_param_lists_alone() {
        let mut kb = kb_with_prelude();
        assert!(
            aligns(&mut kb, &["a", "b"], &["_1", "_2"], TupleAlign::PARAM_LIST),
            "a named-binder callback must accept a multi-param op's eta arrow",
        );
        assert!(
            !aligns(&mut kb, &["a", "b"], &["_1", "_2"], TupleAlign::DATA),
            "a DATA tuple must not relate to its positional spelling",
        );
        assert!(
            !aligns(&mut kb, &["a", "b"], &["_1", "_2"], TupleAlign::EQUALITY),
            "EQUALITY must not inherit the param-list escape along with exact width",
        );
    }

    /// The fourth combination — `Subset` width with the synthetic escape — is
    /// UNCONSTRUCTIBLE outside `mod tuple_align`, which is load-bearing rather
    /// than tidy: the escape branch zips, and `zip` truncates, so that policy
    /// would relate `(a, b, c)` to the positional `(_1, _2)` by dropping `c`.
    /// This test pins that no discipline HAS that pairing; the seal (private
    /// fields, three consts as the only constructors) is what stops one being
    /// written, and the `debug_assert` in the escape branch is what would catch
    /// it if the seal were ever reopened.
    #[test]
    fn no_discipline_pairs_subset_width_with_the_synthetic_escape() {
        for (name, m) in [
            ("DATA", TupleAlign::DATA),
            ("PARAM_LIST", TupleAlign::PARAM_LIST),
            ("EQUALITY", TupleAlign::EQUALITY),
        ] {
            assert!(
                !(m.width() == TupleWidth::Subset && m.names() == TupleNames::ExactOrSynthetic),
                "{name} pairs subset width with the synthetic escape — that aligns by truncation",
            );
        }
    }

    /// The axes are INDEPENDENT, which is the whole point of the struct: no two
    /// disciplines agree on ALL of them, so no single enum over one axis can
    /// express the three.
    ///
    /// WI-803 weakened the original claim, which was "each differs from the other
    /// two in exactly ONE axis". With `order` added that is false — DATA and
    /// EQUALITY now differ on width AND order — and the assertions below were
    /// blind to it, testing only `width()` and `names()`. A test whose stated job
    /// is pinning the grid must cover the axis a ticket just added, or the axis
    /// ships unpinned.
    #[test]
    fn the_three_disciplines_are_distinct_points_in_the_grid() {
        assert_eq!(TupleAlign::EQUALITY.width(), TupleAlign::PARAM_LIST.width());
        assert_ne!(TupleAlign::EQUALITY.names(), TupleAlign::PARAM_LIST.names());
        assert_eq!(TupleAlign::EQUALITY.names(), TupleAlign::DATA.names());
        assert_ne!(TupleAlign::EQUALITY.width(), TupleAlign::DATA.width());
        // WI-803's axis: DATA is the only order-free discipline, and it is what
        // separates DATA from EQUALITY on a second coordinate.
        assert_eq!(TupleAlign::DATA.order(), TupleOrder::Free);
        assert_eq!(TupleAlign::PARAM_LIST.order(), TupleOrder::Preserved);
        assert_eq!(TupleAlign::EQUALITY.order(), TupleOrder::Preserved);
        assert_ne!(TupleAlign::EQUALITY.order(), TupleAlign::DATA.order());
    }
}

/// WI-802 — the `anthill.prelude.Function` recognizer has ONE owner.
///
/// The convention was hand-compared at three independent sites, so a rename or
/// namespace move of the stdlib sort could fix two and leave the third matching
/// nothing — and the third's failure is SILENT: the `Function`-slot argument
/// check simply stops firing, reverting to the no-check state WI-788 fixed, with
/// no test failing on the recognizer ITSELF. These tests are that missing
/// coverage: they fail at the recognizer, naming the cause, instead of leaving a
/// reader to infer it from the downstream callable-typing failures a broken
/// constant produces (44 in the `wi_tests` binary alone, measured by breaking
/// it; the workspace figure is higher).
#[cfg(test)]
mod wi802_function_spec_owner_tests {
    use super::super::{
        extract_sort_ref_sym, function_spec_parts, is_function_spec, FUNCTION_SPEC_QNAME,
    };
    use crate::eval::value::Value;
    use crate::intern::SymbolKind;
    use crate::kb::test_support::load_stdlib;

    /// THE guard the ticket asks for: the constant must name a sort the stdlib
    /// actually DECLARES. Rename or move `anthill.prelude.Function` and this
    /// fails here, pointing at the one line to update.
    #[test]
    fn the_recognizer_names_a_sort_the_stdlib_declares() {
        let kb = load_stdlib(None);
        let f = kb
            .try_resolve_symbol(FUNCTION_SPEC_QNAME)
            .unwrap_or_else(|| {
                panic!(
                    "the stdlib declares no `{FUNCTION_SPEC_QNAME}` — if the sort was \
                    renamed or moved, update FUNCTION_SPEC_QNAME, which is the ONE \
                    place kb/typing.rs spells it"
                )
            });
        assert_eq!(kb.kind_of(f), Some(SymbolKind::Sort), "it must be a SORT");
        assert!(
            is_function_spec(&kb, f),
            "the owner recognizes its own referent"
        );
    }

    /// Identity is by QUALIFIED name, never by last segment (spec §8.6, the
    /// WI-672 direction): a bare `Function` is a DIFFERENT sort. Loosening the
    /// owner to a short-name compare would conflate a user's top-level
    /// `sort Function` with the stdlib spec and make it callable.
    ///
    /// Split from its sibling below because the two bare spellings reach
    /// `qualified_name_of` through DIFFERENT branches: an UNRESOLVED symbol
    /// falls back to its short name (this test), while a namespace-less
    /// top-level declaration is RESOLVED with a bare qualified name (the next).
    /// They need separate KBs — once a fixture declares `sort Function`,
    /// `intern("Function")` resolves to it and the unresolved branch is
    /// unreachable.
    #[test]
    fn an_unresolved_function_name_is_not_the_stdlib_sort() {
        let mut kb = load_stdlib(None);
        let unresolved = kb.intern("Function");
        assert_eq!(
            kb.kind_of(unresolved),
            None,
            "no such declaration ⇒ unresolved"
        );
        assert_eq!(
            kb.qualified_name_of(unresolved),
            "Function",
            "falls back to short name"
        );
        assert!(!is_function_spec(&kb, unresolved));
    }

    /// The case the doc actually warns about: a REAL user sort. A namespace-less
    /// top-level `sort Function` lands in `<global>` with the bare qualified name
    /// `Function`, so it is resolved — and must still not be the stdlib spec.
    #[test]
    fn a_user_declared_top_level_function_sort_is_not_the_stdlib_sort() {
        let kb = load_stdlib(Some("sort Function\n  sort A = ?\n  sort B = ?\nend\n"));

        let declared = kb
            .try_resolve_symbol("Function")
            .expect("top-level `sort Function`");
        assert_eq!(kb.kind_of(declared), Some(SymbolKind::Sort));
        assert_eq!(
            kb.qualified_name_of(declared),
            "Function",
            "resolved, bare QN"
        );
        assert!(
            !is_function_spec(&kb, declared),
            "a user's own sort is NOT the stdlib spec"
        );

        // ... and the stdlib one still is, in the very same KB.
        let stdlib = kb
            .try_resolve_symbol(FUNCTION_SPEC_QNAME)
            .expect("stdlib Function");
        assert!(is_function_spec(&kb, stdlib));
        assert_ne!(declared, stdlib, "two distinct symbols");
    }

    /// Both readers now inherit ONE rule about what counts as a callable rather
    /// than each restating it: a `Function` binding no `B` names no result type.
    /// `E` is genuinely optional — omitting it is effect-polymorphism, not a
    /// malformed type — so it must NOT be folded into the same refusal.
    #[test]
    fn a_result_binding_is_required_but_an_effect_row_is_not() {
        let mut kb = load_stdlib(None);
        let f = kb
            .try_resolve_symbol(FUNCTION_SPEC_QNAME)
            .expect("Function");
        let int_sym = kb
            .try_resolve_symbol("anthill.prelude.Int64")
            .expect("Int64");
        let int = Value::term(kb.make_sort_ref(int_sym));
        let (a, b, e) = (kb.intern("A"), kb.intern("B"), kb.intern("E"));

        assert!(
            function_spec_parts(&kb, f, &[(a, int.clone())]).is_none(),
            "no B ⇒ not a callable"
        );
        let bindings = [(a, int.clone()), (b, int.clone())];
        let (param, _result, effects) =
            function_spec_parts(&kb, f, &bindings).expect("A + B is a callable");
        assert!(param.is_some(), "A is read");
        assert!(
            effects.is_none(),
            "a Function without E is effect-polymorphic"
        );

        // E PRESENT — the positive half. Without this, a reader that always
        // returned `None` for E would satisfy the assertion above, and E is what
        // `arrow_parts_extracted` hands to the effect-row conformance checks.
        let with_e = [(a, int.clone()), (b, int.clone()), (e, int.clone())];
        let (_, _, effects) =
            function_spec_parts(&kb, f, &with_e).expect("A + B + E is a callable");
        assert_eq!(
            effects.and_then(|v| extract_sort_ref_sym(&kb, v)),
            Some(int_sym),
            "E is read back, not dropped",
        );

        // Same bindings under a NON-Function base: the recognizer, not the
        // binding names, is what admits this shape.
        let opt = kb
            .try_resolve_symbol("anthill.prelude.Option")
            .expect("Option");
        assert!(function_spec_parts(&kb, opt, &[(a, int.clone()), (b, int)]).is_none());
    }

    /// WI-708 / WI-726: a type param has TWO symbol spellings — the BARE last
    /// segment (`A`, what a written annotation lowers to) and the sort-CANONICAL
    /// one (`anthill.prelude.Function.A`, what a rule citation keys with). The
    /// reader matches by SHORT name precisely so both reach the same slot, which
    /// is why the doc cites [`same_label`]'s lookup rule rather than an identity
    /// comparison.
    ///
    /// Nothing pinned this: swapping `local_name_of` for `qualified_name_of` in
    /// `function_spec_parts` left ALL 3318 workspace tests green (measured), so
    /// the canonical spelling had zero coverage at this reader. It is a live
    /// spelling — `anthill.prelude.Function.A` resolves in a stdlib KB — so the
    /// tolerance is real, not dead generality.
    #[test]
    fn a_canonically_spelled_binding_key_reaches_the_same_slot() {
        let mut kb = load_stdlib(None);
        let f = kb
            .try_resolve_symbol(FUNCTION_SPEC_QNAME)
            .expect("Function");
        let int_sym = kb
            .try_resolve_symbol("anthill.prelude.Int64")
            .expect("Int64");
        let int = Value::term(kb.make_sort_ref(int_sym));

        let canon_a = kb
            .try_resolve_symbol("anthill.prelude.Function.A")
            .expect("canonical `A` param symbol");
        let canon_b = kb
            .try_resolve_symbol("anthill.prelude.Function.B")
            .expect("canonical `B` param symbol");
        assert_ne!(
            canon_a,
            kb.intern("A"),
            "canonical and bare are distinct symbols"
        );
        assert_eq!(kb.qualified_name_of(canon_a), "anthill.prelude.Function.A");

        let bindings = [(canon_a, int.clone()), (canon_b, int.clone())];
        let (param, result, _) =
            function_spec_parts(&kb, f, &bindings).expect("canonically-keyed bindings are read");
        assert_eq!(
            param.and_then(|v| extract_sort_ref_sym(&kb, v)),
            Some(int_sym),
            "canonical `A` binds the param slot",
        );
        assert_eq!(
            extract_sort_ref_sym(&kb, result),
            Some(int_sym),
            "canonical `B` binds the result slot",
        );
    }
}

#[cfg(test)]
mod wi842_bracketless_reader_tests {
    //! WI-842 (proposal 058 §4.9) — the two halves of the hardening rule, asked of
    //! the readers directly: a read that asks EXISTENCE stays boolean when a carrier
    //! has two providers, and a read that SELECTS sees BOTH of them.
    //!
    //! In-crate because both readers are `pub(crate)`, and asked of one KB so the two
    //! answers are about the same program — the integration pins
    //! (`wi842_bracketless_readers_test.rs`) drive what the eval and load surfaces then
    //! DO with those answers.
    use super::super::{sort_provides, spec_op_suppliers_for_carrier};
    use crate::kb::load::{self, NullResolver};
    use crate::kb::KnowledgeBase;

    /// `Leaf` self-provides `Desc` and owns `describe`; `Rival` provides `Desc` for
    /// `Leaf` too, with its own. The pair LOADS because `Rival` is CONCRETE and so
    /// exempt from the witness rule, leaving `Leaf`'s SELF-PROVIDER candidate alone in
    /// its group — so both readers can be asked about a genuinely two-provider
    /// carrier. (WI-855 measured a second reason, that a self-provider was a candidate
    /// of no kind at all; WI-859 retired that one and the exemption still holds.)
    const SRC: &str = r#"
namespace wi842u
  sort Desc
    sort T = ?
    operation describe(x: T) -> T
  end
  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Leaf = x
  end
  sort Rival
    entity rival
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Leaf = x
  end
  sort Stranger
    entity stranger
  end
end
"#;

    fn kb() -> KnowledgeBase {
        let parsed = crate::parse::parse(SRC).expect("parse");
        let mut kb = KnowledgeBase::new();
        if let Err(errs) = load::load_all(&mut kb, &[&parsed], &NullResolver) {
            panic!(
                "the two-provider program must LOAD — it is the only way to put two \
                 providers in front of a bracket-less read before phase 3b:\n{}",
                errs.iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
        kb
    }

    #[test]
    fn an_existence_read_stays_boolean_with_two_providers() {
        let kb = kb();
        let leaf = kb.resolve_symbol("wi842u.Leaf");
        let desc = kb.resolve_symbol("wi842u.Desc");
        let stranger = kb.resolve_symbol("wi842u.Stranger");
        assert!(
            sort_provides(&kb, leaf, desc),
            "two providers satisfy `provides Desc` as well as one — an existence read \
             (the WI-300 `find_dictionary` / `[simp]` guards) must stay TRUE and hand \
             the real choice to a selecting read (§4.9)"
        );
        assert!(
            !sort_provides(&kb, stranger, desc),
            "`Stranger` declares no provision at all — without this the assertion \
             above would pass for a reader that answers true for anything"
        );
    }

    #[test]
    fn a_selecting_read_sees_both_providers() {
        let mut kb = kb();
        let leaf = kb.resolve_symbol("wi842u.Leaf");
        let desc = kb.resolve_symbol("wi842u.Desc");
        let spec_op = kb.resolve_symbol("wi842u.Desc.describe");
        let short = kb.intern("describe");
        let cands = spec_op_suppliers_for_carrier(&kb, desc, leaf, spec_op, short);
        assert_eq!(
            cands.len(),
            2,
            "the carrier's OWN member and the WITNESS sort's member both supply \
             `describe` for `Leaf`; a length of 1 is the `or_else` chain this ticket \
             replaced, which stopped at its first hit"
        );
        let names: Vec<String> = cands
            .iter()
            .map(|c| kb.qualified_name_of(c.target).to_string())
            .collect();
        assert!(
            names.iter().any(|n| n.ends_with("Leaf.describe"))
                && names.iter().any(|n| n.ends_with("Rival.describe")),
            "both suppliers must be named, by their own operations; got {names:?}"
        );
    }
}

/// WI-955/WI-954 — [`reconstruct_sort_params`] reports a sort's DECLARED parameters
/// and nothing else, and its answer does not depend on the `SortAlias` index.
///
/// WI-955 wrote these to pin two data sources against each other: the WI-657(7)
/// `by_parent` index once the type-check had built it, and a live scan of the
/// `SortAlias` facts before it had. They disagreed — the scan read `<Holder>.mk.C`, an
/// OPERATION's WI-402 existential carrier, as a parameter named `mk.C` OF `Holder` and
/// injected a spurious `mk.C = ?_` binding into every constructor type built for it —
/// and WI-955 joined them onto one keying rule.
///
/// WI-954 REMOVED THE SECOND SOURCE. The reconstruction reads the parameters the loader
/// published, so there is no index to be present or absent and no window before it is
/// built. The tests keep TOGGLING `kb.sort_alias_index` because that is now the
/// experiment: the two answers must be the same because nothing here consults it. And
/// the property they were written for is the sharper one — `mk.C` is still not a
/// parameter of `Holder`, reached through the scope link on the declaration rather than
/// through a rule shared between two decoders.
#[cfg(test)]
mod wi955_one_alias_keying_tests {
    use super::super::{reconstruct_sort_params, value_type_term};
    use crate::eval::value::Value;
    use crate::kb::subst::Substitution;
    use crate::kb::term::Term;
    use crate::kb::test_support::load_stdlib;
    use crate::kb::KnowledgeBase;
    use crate::kb::Symbol;

    /// `Holder` is the ticket's shape: a parametric sort (`T`) whose constructor pins
    /// that param, PLUS a member whose WI-402 existential carrier `C` is declared one
    /// scope deeper (`…Holder.mk.C`). `Spec` and its `= spec` witness are the minimum
    /// that makes `mk` an existential return — `detect_existential_carrier` needs an
    /// `ensures` atom whose first positional is the declared return name.
    const SRC: &str = r#"
namespace test.wi955
  sort Spec
    entity spec
  end
  sort Holder
    sort T = ?
    entity holder(item: T)
    operation mk() -> C ensures Spec[C] = spec
  end
end
"#;

    /// The reconstruction's params for `sort_qn`, by name, from whichever data source
    /// `kb.sort_alias_index` currently selects.
    fn param_names(kb: &mut KnowledgeBase, sort: Symbol) -> Vec<String> {
        let params = reconstruct_sort_params(kb, sort, &Substitution::new());
        params
            .iter()
            .map(|(s, _)| kb.local_name_of(*s).to_string())
            .collect()
    }

    /// The reconstruction reports the DECLARED params, exactly, with the index present
    /// and with it cleared.
    ///
    /// WHAT IT CAUGHT (WI-955): with the pre-WI-954 scan's `.`-boundary prefix slice,
    /// the cleared-index answer was `["T", "mk.C"]` against a declared `["T"]`.
    /// WHAT IT CATCHES NOW: a reconstruction that reads a sort's parameters from
    /// anything but the declaration would go back to varying with the index — and one
    /// that merely LOSES them fails the `== declared` assertion rather than letting two
    /// sources agree at zero.
    #[test]
    fn both_paths_report_the_declared_params_and_nothing_else() {
        let mut kb = load_stdlib(Some(SRC));
        let holder = kb.try_resolve_symbol("test.wi955.Holder").expect("Holder");
        let declared = kb.type_params_of_sort(holder);
        assert_eq!(
            declared,
            vec!["T".to_string()],
            "the sort declares exactly `T`"
        );

        assert!(
            kb.sort_alias_index.is_some(),
            "the type-check built the index"
        );
        let indexed = param_names(&mut kb, holder);

        // The load-time window, where `load_phase_inner` has reset the index. Before
        // WI-954 this selected a different data source; now it must select nothing.
        kb.sort_alias_index = None;
        let scanned = param_names(&mut kb, holder);

        assert_eq!(
            indexed, declared,
            "with the index built: the declared params, exactly"
        );
        assert_eq!(
            scanned, declared,
            "with the index cleared: the same — and `mk.C` is the OPERATION's \
             existential carrier, not a param of the sort",
        );
    }

    /// The same property where a caller meets it: the constructor TYPE the value-typer
    /// builds. `holder(item: 42)` types as `Holder[T = Int64]` — the same hash-consed
    /// term with the index built and with it cleared.
    ///
    /// WHAT IT CAUGHT (WI-955): the pre-index build carried an extra `mk.C = ?_` named
    /// arg, so the two `TermId`s differed; the `T = Int64` binding itself passed either
    /// way (the spurious param was added, not substituted), which is why the render
    /// assertion below spells the WHOLE type rather than checking for the binding.
    #[test]
    fn the_constructor_type_is_identical_before_and_after_the_index() {
        let mut kb = load_stdlib(Some(SRC));
        let ctor = kb
            .try_resolve_symbol("test.wi955.Holder.holder")
            .expect("holder ctor");
        let item = kb.intern("item");
        let value = Value::Entity {
            functor: ctor,
            pos: vec![].into(),
            named: vec![(item, Value::Int(42))].into(),
        };
        let subst = Substitution::new();

        let indexed = value_type_term(&mut kb, &subst, &value);
        kb.sort_alias_index = None;
        let scanned = value_type_term(&mut kb, &subst, &value);

        let (i_tid, s_tid) = (indexed.expect_term(), scanned.expect_term());
        assert_eq!(
            i_tid,
            s_tid,
            "one written value, one type — whichever data source answered; got {} vs {}",
            render_type(&kb, i_tid),
            render_type(&kb, s_tid),
        );
        // Renders the BINDINGS, not just the keys: `Holder[T]` would pass a keys-only
        // check while carrying no `Int64` at all, so the field-driven pinning this
        // reconstruction exists for would go unmeasured.
        assert_eq!(
            render_type(&kb, i_tid),
            "test.wi955.Holder[T = anthill.prelude.Int64]",
            "the sort's own param, pinned by the field — and nothing else",
        );
    }

    /// `Sort[k1 = v1, …]` with each binding's sort head named, for an assertion whose
    /// failure message says what the type actually was.
    fn render_type(kb: &KnowledgeBase, tid: crate::kb::term::TermId) -> String {
        match kb.get_term(tid) {
            Term::Fn {
                functor,
                named_args,
                ..
            } => format!(
                "{}[{}]",
                kb.qualified_name_of(*functor),
                named_args
                    .iter()
                    .map(|(k, v)| format!(
                        "{} = {}",
                        kb.local_name_of(*k),
                        super::super::sort_functor_of(kb, *v)
                            .map(|s| kb.qualified_name_of(s).to_string())
                            .unwrap_or_else(|| format!("{:?}", kb.get_term(*v))),
                    ))
                    .collect::<Vec<_>>()
                    .join(", "),
            ),
            other => format!("{other:?}"),
        }
    }
}

/// WI-963 — the three checkable facts behind [`KnowledgeBase::make_type_var`]'s doc:
/// why an under-determined type is a TERM in the declared reflect vocabulary, why a
/// bare logic `Var` is not enough, and why interning it per NAME is right.
///
/// The question was asked twice about this code. A prose answer rots; these drive it.
#[cfg(test)]
mod wi963_type_var_representation_tests {
    use super::super::{type_head, unify_types, TypeHead};
    use crate::eval::value::Value;
    use crate::kb::subst::Substitution;
    use crate::kb::term::{Term, TermId, Var};
    use crate::kb::test_support::load_stdlib;
    use crate::kb::KnowledgeBase;

    fn sort_ty(kb: &mut KnowledgeBase, qn: &str) -> TermId {
        let s = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("{qn}"));
        kb.make_sort_ref(s)
    }

    /// A bare logic `Var` in TYPE position is a DIFFERENT type form from `type_var`, not a
    /// malformed one. Both are in the vocabulary and each says its own thing: `type_var` is
    /// the PLACEHOLDER (`entity TypeVar(name: Symbol)` — a type the extractor could not name,
    /// minted for an un-annotated lambda binder), while a logic variable is the ENGINE's, and
    /// its flex/rigid kind is the whole of what it means.
    ///
    /// WI-1079 REVERSED THIS ROW'S SECOND HALF, and the old text is worth keeping in view:
    /// "a bare `Var` has no functor, so it is not in the type vocabulary at all". That was
    /// true of the CODE (`type_head` bailed on `functor_sym()` being `None`) and false of the
    /// LANGUAGE — a skolem is a perfectly well-formed type, and reporting it through a variant
    /// whose payload its own doc calls "the offending input" made reflect unable to tell an
    /// opaque constant from a unifiable hole. The reflect layer's job is to represent the
    /// language's types, so a form it cannot express is a defect whether or not a corpus
    /// reaches it.
    ///
    /// CONTROL — three verdicts on three terms built in one test, so none passes vacuously,
    /// and the flex/rigid pair is built from the SAME name so the assertion cannot be
    /// satisfied by rendering. `TypeVar` fails if the stdlib entity is renamed or moved out of
    /// `TypeExtractor`; the other two fail on the WI-1079 back-out (deleting the `ViewHead::
    /// Var` arm in `type_head`), which puts both back to `Error` — that is this file's half of
    /// the measurement, and `wi1079_variable_forms_reflect_test` carries the rest.
    #[test]
    fn a_bare_logic_var_is_its_own_type_form_not_a_placeholder() {
        let mut kb = load_stdlib(None);
        let name = kb.intern("?_");
        let tv = kb.make_type_var(name);
        let flex_vid = kb.fresh_var(name);
        let flex_term = kb.alloc(Term::Var(Var::Global(flex_vid)));
        let rigid_vid = kb.fresh_var(name);
        let rigid_term = kb.alloc(Term::Var(Var::Rigid(rigid_vid)));

        match type_head(&kb, &Value::term(tv)) {
            TypeHead::TypeVar(s) => assert_eq!(kb.local_name_of(s), "?_", "carries its name"),
            _ => panic!("a type_var must classify as TypeHead::TypeVar"),
        }
        match type_head(&kb, &Value::term(flex_term)) {
            TypeHead::FlexVar(v) => assert_eq!(v.raw(), flex_vid.raw(), "carries its identity"),
            _ => panic!("a flexible logic var classifies as `TypeHead::FlexVar`"),
        }
        match type_head(&kb, &Value::term(rigid_term)) {
            TypeHead::Skolem(v) => assert_eq!(v.raw(), rigid_vid.raw(), "carries its identity"),
            _ => panic!("a rigid logic var classifies as `TypeHead::Skolem`"),
        }
    }

    /// THE load-bearing difference. A `type_var` is compatible-with-anything WITHOUT
    /// committing (the M6 flounder posture): it unifies with `Int64` and then, in the
    /// SAME substitution, with `String`, binding nothing either time. A logic `Var`
    /// unifies with `Int64` by BINDING itself, and that substitution then REFUSES
    /// `String` — "this type is undetermined" has silently become "it is `Int64`".
    ///
    /// CONTROL — all four verdicts were measured before being written here, and the two
    /// blocks are each other's control: they assert OPPOSITE outcomes for the same pair
    /// of unifications, so neither can pass by accident.
    ///
    /// The whole-system backout is stronger than this test and worth recording, because
    /// it says the representation is load-bearing for real code rather than only for
    /// these synthetic unifications: making `make_type_var` return a bare
    /// `Var::Global` stops THE STDLIB FROM LOADING, with exactly the commitment this
    /// test describes — `62:39 type mismatch in match.rule: expected Option[T = Pair[A =
    /// ?T, …]], got Option[T = Pair[A = ??_, …]]` (measured, `stream.anthill` and
    /// `list.anthill`). So these tests fail under that backout at their FIXTURE, not at
    /// their assertions; the assertions exist to name WHY, which a load error does not.
    #[test]
    fn a_type_var_never_commits_where_a_logic_var_does() {
        let mut kb = load_stdlib(None);
        let int_ty = sort_ty(&mut kb, "anthill.prelude.Int64");
        let str_ty = sort_ty(&mut kb, "anthill.prelude.String");
        let name = kb.intern("?_");
        let tv = kb.make_type_var(name);

        let mut s = Substitution::new();
        assert!(unify_types(
            &mut kb,
            &mut s,
            &Value::term(tv),
            &Value::term(int_ty)
        ));
        assert!(
            s.bindings.is_empty(),
            "a type_var matches without binding anything"
        );
        assert!(
            unify_types(&mut kb, &mut s, &Value::term(tv), &Value::term(str_ty)),
            "and still matches an INCOMPATIBLE second type — it never committed to Int64",
        );
        assert!(s.bindings.is_empty(), "still nothing bound");

        let vid = kb.fresh_var(name);
        let var_term = kb.alloc(Term::Var(Var::Global(vid)));
        let mut s2 = Substitution::new();
        assert!(unify_types(
            &mut kb,
            &mut s2,
            &Value::term(var_term),
            &Value::term(int_ty)
        ));
        assert_eq!(
            s2.bindings.len(),
            1,
            "a logic var unifies by BINDING itself"
        );
        assert!(
            !unify_types(
                &mut kb,
                &mut s2,
                &Value::term(var_term),
                &Value::term(str_ty)
            ),
            "and is then committed: the same var now REFUSES String — which is why an \
             under-determined type must not be carried as a logic var",
        );
    }

    /// A `type_var`'s identity is its NAME. Interning is therefore nominal identity —
    /// what CLAUDE.md's representation note reserves hash-consing FOR — not the
    /// per-site transient it would be if each unknown carried its own `VarId`.
    ///
    /// CONTROL — the third assertion is the one that fails if this reader ever moves to
    /// logic vars: two independently-minted `?_` VARS are distinct terms, so two
    /// undetermined types would stop being structurally equal. The first two would pass
    /// under any interning scheme and are here to say what the identity IS.
    #[test]
    fn a_type_vars_identity_is_its_name() {
        let mut kb = load_stdlib(None);
        let wildcard = kb.intern("?_");
        let named = kb.intern("?T");
        assert_eq!(
            kb.make_type_var(wildcard),
            kb.make_type_var(wildcard),
            "same name ⇒ one shared hash-consed term",
        );
        assert_ne!(
            kb.make_type_var(wildcard),
            kb.make_type_var(named),
            "different names stay distinct",
        );

        let (v1, v2) = (kb.fresh_var(wildcard), kb.fresh_var(wildcard));
        let t1 = kb.alloc(Term::Var(Var::Global(v1)));
        let t2 = kb.alloc(Term::Var(Var::Global(v2)));
        assert_ne!(
            t1, t2,
            "two logic vars of the SAME name are distinct terms — the contrast: as \
             logic vars, two undetermined types would never be structurally equal",
        );
    }
}

/// WI-958 — "which symbol declares this operation" now has ONE owner
/// ([`impl_parent_of_op`]), and "the parametric sort that declares it" has one more
/// on top of it ([`spec_op_parent_sort`]), which [`self_receiver_spec_sort`] narrows
/// rather than re-derives. Three qualified-name splits became one.
///
/// CONTROL, stated plainly: **no test here fails when the merge is backed out.** The
/// merge is behaviour-preserving by construction — each of the three sites computed
/// the same parent already, and the one gate it ADDS (`has_kind(Sort)` on
/// `self_receiver_spec_sort`) is unreachable, as [`spec_op_parent_sort`]'s doc records.
/// The ticket said as much: the value is that three copies cannot DRIFT.
///
/// So these are drift guards, and each test's own doc names the edit it catches and
/// what that edit actually does when MEASURED — which in two cases is not what this
/// module's first draft predicted. Read those, not a summary here.
#[cfg(test)]
mod wi958_one_op_parent_tests {
    use super::super::{
        impl_parent_of_op, lookup_operation_info_full, self_receiver_spec_sort, spec_op_parent_sort,
    };
    use crate::intern::SymbolKind;
    use crate::kb::test_support::load_stdlib_and_stl;
    use crate::kb::{KnowledgeBase, Symbol};

    /// The four shapes the three readers must tell apart, in one namespace:
    /// a parametric sort's op WITH a self-receiver (`take`) and WITHOUT one (`make`),
    /// a NON-parametric sort's op (`describe`), and a FREE op (`loose`).
    const SRC: &str = r#"
namespace test.wi958
  sort Spec
    sort T = ?
    operation take(s: Spec) -> T
    operation make(x: T) -> Spec
  end

  sort Plain
    entity plain(n: Int64)
    operation describe(p: Plain) -> Int64
  end

  operation loose(n: Int64) -> Int64
end
"#;

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// All three readers on one op, as qualified names — `None` renders as `-`.
    fn readers(kb: &KnowledgeBase, op_qn: &str) -> (String, String, String) {
        let op_sym = sym(kb, op_qn);
        let info = lookup_operation_info_full(kb, op_sym)
            .unwrap_or_else(|| panic!("{op_qn} has no OperationInfo"));
        let name = |s: Option<Symbol>| {
            s.map(|s| kb.qualified_name_of(s).to_string())
                .unwrap_or_else(|| "-".into())
        };
        (
            name(impl_parent_of_op(kb, op_sym)),
            name(spec_op_parent_sort(kb, op_sym)),
            name(self_receiver_spec_sort(kb, &info, op_sym)),
        )
    }

    /// DRIVES each reader's own gate, on the shape that gate exists to reject.
    ///
    /// CONTROLS, each MEASURED by making the edit and re-running:
    ///  - collapse `self_receiver_spec_sort` into `spec_op_parent_sort`: BOTH tests
    ///    fail, and not on an assertion — THE STDLIB STOPS LOADING (`collect.effects`
    ///    undeclared, `FiniteCollection.collect.requires` missing, `Stream` vs
    ///    `MappedStream` rule mismatch). The self-receiver gate is what keeps the
    ///    WI-357 carrier bind and effect-close off a non-receiver op. Any test using
    ///    the stdlib fixture catches this; it is here to say WHICH gate did it.
    ///  - drop the parametric gate from `spec_op_parent_sort`: row 3 fails (`Plain`,
    ///    a sort with no `sort <P> = ?`, would report as a spec sort).
    ///  - drop the `has_kind(Sort)` gate: NOTHING fails, here or in the workspace.
    ///    Expected — that gate is unreachable, exactly as its own doc says. It is not
    ///    dead code but an unmet precondition stated where it belongs; no test can
    ///    justify it, so this comment does.
    ///
    /// The merge itself is not controlled by this test: it passed before the merge too,
    /// since all three copies of the split agreed.
    #[test]
    fn each_reader_narrows_the_one_before_it() {
        let kb = load_stdlib_and_stl(Some(SRC));
        let spec = "test.wi958.Spec";

        assert_eq!(
            readers(&kb, "test.wi958.Spec.take"),
            (spec.into(), spec.into(), spec.into()),
            "a parametric sort's op with a self-receiver param: all three answer the sort",
        );
        assert_eq!(
            readers(&kb, "test.wi958.Spec.make"),
            (spec.into(), spec.into(), "-".into()),
            "still a spec op — but no param is typed `Spec`, so it has no self-receiver",
        );
        assert_eq!(
            readers(&kb, "test.wi958.Plain.describe"),
            ("test.wi958.Plain".into(), "-".into(), "-".into()),
            "`Plain` declares no `sort <P> = ?`: the owner is a sort, but not a SPEC sort",
        );
        assert_eq!(
            readers(&kb, "test.wi958.loose"),
            ("test.wi958".into(), "-".into(), "-".into()),
            "a free op's owner is its NAMESPACE — deliberately returned, and gated off \
             by both spec readers",
        );
    }

    /// The evidence [`impl_parent_of_op`]'s doc rests on, re-measured rather than
    /// re-argued: the qualified-name split and the symbol table's scope link agree for
    /// every OPERATION — and disagree for the dot-less kernel-vocab names, where the
    /// split correctly finds no parent and the scope link offers the top-level scope.
    ///
    /// CONTROL, MEASURED — point `impl_parent_of_op` at `declaring_scope_symbol` and
    /// the second half fails (`` `Rule` has no parent to strip; declaring_scope_symbol
    /// answers Some("<global>") ``). It is the ONLY thing that fails: the whole
    /// workspace ran 4084 tests under that edit, 4083 of them green. That is the point
    /// of writing it — the reason `impl_parent_of_op` keeps the split is a domain
    /// argument no other test can hear, so without this the next reader would make the
    /// swap, see green, and land it.
    ///
    /// The first half (operations agree) is what makes the split legitimate at all,
    /// and passes either way by design.
    #[test]
    fn the_split_and_the_scope_link_agree_on_operations_only() {
        let kb = load_stdlib_and_stl(None);
        // By SYMBOL, read through `qualified_name_of` — the same string
        // `impl_parent_of_op` splits. Walking `by_qualified_name`'s KEYS instead would
        // measure the wrong thing: one symbol can be registered under several (`BigInt`
        // and `anthill.prelude.BigInt` are one `Symbol`), and only the canonical name
        // is the one that gets split.
        let mut seen: std::collections::HashSet<Symbol> = Default::default();
        let mut names: Vec<(String, Symbol)> = Vec::new();
        for &s in kb.symbols.by_qualified_name.values() {
            if seen.insert(s) {
                names.push((kb.qualified_name_of(s).to_string(), s));
            }
        }

        let mut ops = 0usize;
        let mut disagreeing_ops: Vec<String> = Vec::new();
        // Dot-less names live directly in the `<global>` pseudo-scope: the split sees no
        // parent at all, the scope link sees that scope.
        let mut dotless_global: Vec<String> = Vec::new();
        for (qn, sym) in &names {
            let split = qn
                .rsplit_once('.')
                .and_then(|(p, _)| kb.try_resolve_symbol(p));
            let scope = kb.declaring_scope_symbol(*sym);
            if kb.has_kind(*sym, SymbolKind::Operation) {
                ops += 1;
                if split != scope {
                    disagreeing_ops.push(format!(
                        "{qn}: split={:?} scope={:?}",
                        split.map(|s| kb.qualified_name_of(s).to_string()),
                        scope.map(|s| kb.qualified_name_of(s).to_string()),
                    ));
                }
            }
            if !qn.contains('.') && split.is_none() && scope.is_some() {
                dotless_global.push(qn.clone());
            }
        }

        assert!(
            ops > 300,
            "the stdlib fixture must actually carry operations; got {ops}"
        );
        assert_eq!(
            disagreeing_ops,
            Vec::<String>::new(),
            "for an OPERATION the two answers are the same — the subject is a direct \
             child of the scope it wants, so the split has nothing to decide",
        );
        assert!(
            dotless_global.contains(&"Fact".to_string()),
            "the kernel vocabulary must still hold dot-less names — they are why \
             `impl_parent_of_op` cannot become `declaring_scope_symbol`; got \
             {dotless_global:?}",
        );
        for qn in &dotless_global {
            let s = sym(&kb, qn);
            assert_eq!(
                impl_parent_of_op(&kb, s),
                None,
                "`{qn}` has no parent to strip; `declaring_scope_symbol` answers \
                 {:?} instead, which a carrier-sort caller would take at face value",
                kb.declaring_scope_symbol(s)
                    .map(|p| kb.qualified_name_of(p).to_string()),
            );
        }
    }
}

/// WI-956 item 4 — `kind_of` vs `has_kind` at the gates that ask "is this a SORT".
///
/// The ticket asked whether the two are the same question. They are not, and the
/// difference is REACHABLE from source, not just in principle: `kind_of` reports the
/// FIRST-declared of a symbol's categories, so a sort whose ENTITY role registered
/// first does not look like a sort to it. The fixture below is the smallest program
/// that builds one WITH type parameters and an operation, which is what turns the
/// asymmetry from inert into a wrong answer.
///
/// Everything here fails on the pre-WI-956 code, and the failures were MEASURED by
/// restoring each `kind_of`, not predicted — see each test.
#[cfg(test)]
mod wi956_kind_gate_tests {
    use super::super::{
        call_bracket_scopes, impl_parent_of_op, impl_parent_sort_of_op, lookup_operation_info_full,
        sort_type_params_as_pairs,
    };
    use crate::intern::SymbolKind;
    use crate::kb::test_support::load_stdlib_and_stl;
    use crate::kb::{KnowledgeBase, Symbol};

    /// `Rec` is a sort whose symbol was registered under ANOTHER KIND FIRST, so
    /// `kind_of` reports something that is not `Sort` while `has_kind(Sort)` holds.
    /// That asymmetry is the whole subject of this module — the gates below must read
    /// membership, not the display head.
    ///
    /// THE FIXTURE WAS REPLACED WHEN 059 R1 LANDED (WI-997), exactly as the original
    /// note here anticipated. It used to write `entity Rec(n)` beside `sort Rec … end`,
    /// which is now refused as two declarations of one type. The shape that survives is
    /// 059 R2's SECONDARY ENTRY — `namespace Rec` at the address of `sort Rec` — and it
    /// poses the identical question: the namespace declaration lands first, so the
    /// symbol carries `Namespace` at its head and gains `Sort` from the reuse arm
    /// (WI-979). It is also the better fixture, being the pair the language blesses
    /// rather than one it was about to refuse.
    ///
    /// `peek` reads `Rec`'s own type parameter `T` from inside the secondary entry —
    /// 059 R2's measured symmetry, and what makes the type-param row below live.
    ///
    /// IT CARRIES A BODY BECAUSE 059 R3 REQUIRES ONE (WI-1000): an operation
    /// INTRODUCED by a secondary entry adds a complete new member, and a body-less
    /// declaration there would reserve an implementation slot on a type the entry is
    /// extending. `= x` changes nothing this module measures — the question is
    /// whether `peek` can SEE `T`, and its signature is untouched. `Ord.look` beside
    /// it stays body-less deliberately: it sits in a MAIN entry, where a body-less
    /// declaration remains legal, so the pair is also the control for that.
    ///
    /// `Ord` is the control: the same sort with nothing declared ahead of it, so its
    /// head IS `Sort`. Nothing else about it differs.
    const SRC: &str = r#"
namespace test.wi956
  namespace Rec
    operation peek(x: T) -> T = x
  end
  sort Rec
    sort T = ?
    entity Rec(n: Int64)
  end

  sort Ord
    sort U = ?
    operation look(x: U) -> U
  end
  entity Ord2(n: Int64)

  operation loose(n: Int64) -> Int64
end
"#;

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// The premise the rest of the module rests on: this fixture really does build a
    /// sort that `kind_of` calls something else, and it really is parametric. If the
    /// loader ever refuses the re-declaration, THIS is the test that says so — the
    /// others would then be passing over a fixture that no longer poses the question.
    #[test]
    fn a_sort_can_be_registered_under_another_kind_first() {
        let kb = load_stdlib_and_stl(Some(SRC));
        let rec = sym(&kb, "test.wi956.Rec");
        assert_eq!(
            kb.symbols.get(rec).kinds(),
            &[SymbolKind::Namespace, SymbolKind::Sort, SymbolKind::Entity],
            "the secondary entry registers Namespace first; `sort Rec` adds Sort \
             through the reuse arm, and its eponymous constructor adds Entity",
        );
        assert!(
            kb.has_kind(rec, SymbolKind::Sort),
            "`Rec` PLAYS the sort role"
        );
        assert_ne!(
            kb.kind_of(rec),
            Some(SymbolKind::Sort),
            "…and `kind_of` says otherwise — the whole asymmetry, in one assert",
        );
        assert_eq!(
            kb.type_params_of_sort(rec),
            vec!["T".to_string()],
            "and it is PARAMETRIC, which is what makes the misread cost something",
        );
        // The control sort, same shape, opposite declaration order.
        let ord = sym(&kb, "test.wi956.Ord");
        assert_eq!(kb.kind_of(ord), Some(SymbolKind::Sort));
        assert_eq!(kb.type_params_of_sort(ord), vec!["U".to_string()]);
    }

    /// The live consequence, and the reason item 4 is a FIX rather than a hardening:
    /// an operation of `Rec` could not see `Rec`'s own type parameter, so a written
    /// `peek[T = …]` had no `T` to bind.
    ///
    /// CONTROL, MEASURED by putting `kind_of(parent) == Some(Sort)` back into
    /// `call_bracket_scopes`: `peek` reports `[]` and this test fails; `look` reports
    /// `["U"]` either way. Nothing else in the workspace fails, which is exactly why
    /// the divergence survived two tickets that both looked at it.
    #[test]
    fn an_operation_sees_its_sorts_type_params_whichever_way_the_sort_was_declared() {
        let mut kb = load_stdlib_and_stl(Some(SRC));
        let scopes = |kb: &mut KnowledgeBase, op_qn: &str| -> Vec<String> {
            let op = sym(kb, op_qn);
            let info = lookup_operation_info_full(kb, op)
                .unwrap_or_else(|| panic!("{op_qn} has no OperationInfo"));
            call_bracket_scopes(kb, &info, op)
                .iter()
                .map(|(s, _)| kb.local_name_of(*s).to_string())
                .collect()
        };
        assert_eq!(
            scopes(&mut kb, "test.wi956.Rec.peek"),
            vec!["T".to_string()],
            "`peek` is declared in `Rec`, which declares `T` — the bracket scopes must \
             carry it. Under `kind_of` this was empty.",
        );
        assert_eq!(
            scopes(&mut kb, "test.wi956.Ord.look"),
            vec!["U".to_string()],
            "the control: identical sort, declared sort-first. It passed before too — \
             which is the point, the answer must not depend on declaration order.",
        );
    }

    /// One gate, five readers. Each of the five sites that used to spell
    /// `impl_parent_of_op(..)` + a kind test now calls [`impl_parent_sort_of_op`], so
    /// this pins the gate itself rather than re-driving each caller: it answers the
    /// parent for a member op of EITHER declaration order, and `None` for a free op.
    ///
    /// CONTROL, MEASURED — restore `kind_of` inside `impl_parent_sort_of_op` and the
    /// `Rec.peek` row fails (`None`, where `impl_parent_of_op` alone answers `Rec`).
    /// The free-op row passes either way by design; it is here because it is the
    /// reason the gate exists at all, and a "fix" that dropped the gate entirely would
    /// let a NAMESPACE through and only this row would notice.
    #[test]
    fn the_parent_sort_gate_admits_a_sort_and_refuses_a_namespace() {
        let kb = load_stdlib_and_stl(Some(SRC));
        let row = |op_qn: &str| -> (Option<String>, Option<String>) {
            let op = sym(&kb, op_qn);
            let name = |s: Option<Symbol>| s.map(|s| kb.qualified_name_of(s).to_string());
            (
                name(impl_parent_of_op(&kb, op)),
                name(impl_parent_sort_of_op(&kb, op)),
            )
        };
        assert_eq!(
            row("test.wi956.Rec.peek"),
            (Some("test.wi956.Rec".into()), Some("test.wi956.Rec".into())),
            "`Rec` IS the declaring sort; the gate must not lose it over registration \
             order",
        );
        assert_eq!(
            row("test.wi956.Ord.look"),
            (Some("test.wi956.Ord".into()), Some("test.wi956.Ord".into())),
        );
        // A FREE operation: the split answers its NAMESPACE, and the gate must drop it.
        let free = sym(&kb, "test.wi956.loose");
        assert!(
            kb.has_kind(
                impl_parent_of_op(&kb, free).expect("a namespace parent"),
                SymbolKind::Namespace
            ),
            "the fixture for this row must really be a free op",
        );
        assert_eq!(
            impl_parent_sort_of_op(&kb, free),
            None,
            "a namespace declares no type params and owns no requirement slots — \
             letting it through is what the gate exists to stop",
        );
    }

    /// The measurement `impl_parent_sort_of_op`'s doc rests on, re-run rather than
    /// re-argued: on the LIBRARIES the two spellings agree, so the fix is inert there
    /// and the fixture above is what makes it observable.
    ///
    /// This one passes either way by design. It is here so that a future library
    /// change which DOES introduce a kind-hidden parametric sort trips a test that
    /// names the reason, instead of surfacing as a missing type param somewhere else.
    #[test]
    fn on_the_libraries_the_two_spellings_still_agree() {
        let mut kb = load_stdlib_and_stl(None);
        let mut seen: std::collections::HashSet<Symbol> = Default::default();
        let mut syms: Vec<Symbol> = Vec::new();
        for &s in kb.symbols.by_qualified_name.values() {
            if seen.insert(s) {
                syms.push(s);
            }
        }
        let hidden: Vec<Symbol> = syms
            .iter()
            .copied()
            .filter(|&s| {
                kb.has_kind(s, SymbolKind::Sort) && kb.kind_of(s) != Some(SymbolKind::Sort)
            })
            .collect();
        assert!(
            hidden.len() > 40,
            "kind-hidden sorts must exist for this to measure anything (the top-level \
             `entity X(…)` sugar makes them); got {}",
            hidden.len(),
        );
        let mut carrying: Vec<String> = Vec::new();
        for &h in &hidden {
            if !kb.type_params_of_sort(h).is_empty()
                || !kb.named_requirement_slots(h).is_empty()
                || !sort_type_params_as_pairs(&mut kb, h).is_empty()
            {
                carrying.push(kb.qualified_name_of(h).to_string());
            }
        }
        assert_eq!(
            carrying,
            Vec::<String>::new(),
            "no LIBRARY sort is both kind-hidden and parametric — the sugar that hides \
             a sort desugars to a body of exactly one entity. That is why the fix needed \
             a hand-written re-declaration to drive, and why it was inert for two tickets.",
        );
        let ops: Vec<Symbol> = syms
            .iter()
            .copied()
            .filter(|&s| kb.has_kind(s, SymbolKind::Operation))
            .collect();
        assert!(
            ops.len() > 300,
            "the library fixture must carry operations; got {}",
            ops.len()
        );
        for &op in &ops {
            assert_eq!(
                impl_parent_of_op(&kb, op).filter(|p| kb.kind_of(*p) == Some(SymbolKind::Sort)),
                impl_parent_sort_of_op(&kb, op),
                "`{}`: the two gates disagree on a LIBRARY operation",
                kb.qualified_name_of(op),
            );
        }
    }
}

/// WI-956 — AN ALIAS IS FOUND BY ITS OWN SYMBOL, NEVER BY ITS LOCAL NAME.
///
/// [`resolve_sort_alias`] had a second pass keyed on the source's LOCAL name, run
/// whenever the exact one missed. A local name means nothing outside the scope that
/// declares it, so that pass answered with whichever same-named alias happened to come
/// first — an unrelated declaration's variable. WI-943 measured it doing exactly that
/// to a bracket parameter and fixed the caller; WI-956 deleted the pass.
///
/// MEASURED before deleting: with it forced to `None`, the FULL WORKSPACE ran 4091
/// tests, 0 failures. Nothing depended on the guess — which also means nothing but this
/// module notices if it comes back, and that is why this module exists.
#[cfg(test)]
mod wi956_alias_identity_tests {
    use super::super::{resolve_sort_alias, type_param_global_var};
    use crate::kb::term::{Term, Var};
    use crate::kb::test_support::load_stdlib_and_stl;
    use crate::kb::KnowledgeBase;

    /// Three declarations sharing ONE local name, `Wi956T`, in three different scopes:
    /// a type parameter, an alias to a concrete sort, and an ENTITY that is not an
    /// alias at all. The name is fixture-unique so nothing from the stdlib (which
    /// declares 37 sources short-named `T`) can answer in their place.
    ///
    /// The PARAMETER is declared FIRST on purpose. A restored by-name pass takes the
    /// first match in `rules_by_functor` order, so this order makes the borrowed answer
    /// a `Var` — which is what lets the second test below feel the difference at all.
    /// Written the other way round, the borrowed target is a `sort_ref`, `as_global`
    /// rejects it, and `type_param_global_var` answers `None` for the right result by
    /// the wrong route. (Measured: the first draft was written that way, and its
    /// control claim was false.)
    const SRC: &str = r#"
namespace test.wi956.alias
  import anthill.prelude.Int64
  sort Wi956Param
    sort Wi956T = ?
  end
  sort Wi956Fixed
    sort Wi956T = Int64
  end
  sort Wi956Other
    entity Wi956T(n: Int64)
  end
end
"#;

    fn is_var(kb: &KnowledgeBase, t: crate::kb::term::TermId) -> bool {
        matches!(kb.get_term(t), Term::Var(Var::Global(_)))
    }

    /// CONTROL, MEASURED by restoring the by-name pass (`.or_else(|| scan by local
    /// name)`) on `resolve_sort_alias`: the third row fails — `Wi956Other.Wi956T` is
    /// answered with `Wi956Fixed`'s `Int64` target, an alias belonging to a different
    /// declaration in a different scope. The first two rows pass either way by design;
    /// they are what says the deletion did not simply break the reader.
    #[test]
    fn an_alias_is_found_only_by_its_own_symbol() {
        let kb = load_stdlib_and_stl(Some(SRC));
        let sym = |qn: &str| {
            kb.try_resolve_symbol(qn)
                .unwrap_or_else(|| panic!("resolve {qn}"))
        };

        let fixed = resolve_sort_alias(&kb, sym("test.wi956.alias.Wi956Fixed.Wi956T"))
            .expect("`sort Wi956T = Int64` asserts an alias");
        assert!(
            !is_var(&kb, fixed),
            "an alias to a concrete sort targets a sort_ref"
        );

        let param = resolve_sort_alias(&kb, sym("test.wi956.alias.Wi956Param.Wi956T"))
            .expect("`sort Wi956T = ?` asserts an alias");
        assert!(is_var(&kb, param), "a type param targets its backing Var");
        assert_ne!(
            fixed, param,
            "two declarations, two answers — not one name, one answer"
        );

        // THE POINT. Same local name, no alias of its own: the only truthful answer is
        // `None`. The deleted pass answered `fixed` here.
        assert_eq!(
            resolve_sort_alias(&kb, sym("test.wi956.alias.Wi956Other.Wi956T")),
            None,
            "`Wi956Other.Wi956T` is an entity, not an alias — sharing a LOCAL name with \
             one declared in another scope must not lend it that scope's target",
        );
    }

    /// The same removal seen through [`type_param_global_var`], whose LAST rung the
    /// deleted pass was — the rung WI-943 measured answering `cmp[T]` and `cmp2[T]`
    /// with one shared `anthill.kernel.T` var. Its two surviving rungs are both
    /// identities, so a symbol that is neither an alias nor a bracket parameter now
    /// resolves to nothing instead of to someone else's variable.
    ///
    /// CONTROL, MEASURED with the same edit as above: this fails, answering
    /// `Wi956Param`'s var for a symbol that is not a type parameter at all. The
    /// first row passes either way; it is here so a regression that merely EMPTIES
    /// the reader cannot be mistaken for the fix.
    #[test]
    fn a_type_param_reader_answers_nothing_rather_than_someone_elses_var() {
        let kb = load_stdlib_and_stl(Some(SRC));
        let sym = |qn: &str| {
            kb.try_resolve_symbol(qn)
                .unwrap_or_else(|| panic!("resolve {qn}"))
        };
        assert!(
            type_param_global_var(&kb, sym("test.wi956.alias.Wi956Param.Wi956T")).is_some(),
            "a declared type param still resolves to its own var",
        );
        assert_eq!(
            type_param_global_var(&kb, sym("test.wi956.alias.Wi956Other.Wi956T")),
            None,
            "an entity that merely SHARES a type param's local name has no canonical \
             var, and must not borrow one",
        );
    }
}

/// WI-1083 — THE ∀ ITSELF, driven where it is minted. The integration rows
/// (`wi1083_polytype_test`) drive the CAPABILITY: a type-parameterized operation passed as a
/// function value and run. They cannot see the ∀, because `check_bare_ref` eliminates it at
/// the reference and each of their programs has one reference per operation — so a build that
/// skipped the wrapper entirely and freshened nothing would still pass every one of them.
/// These rows are what makes the form load-bearing rather than decorative: the binder list is
/// asserted to BE the signature-bound set, and two instantiations of one operation are
/// asserted to share no variable.
#[cfg(test)]
mod wi1083_poly_type_tests {
    use super::super::{
        extract_type, instantiate_poly_type, operation_as_function_value, type_head, TypeExtractor,
        TypeHead,
    };
    use crate::eval::value::Value;
    use crate::kb::node_occurrence::{empty_span, Expr, NodeOccurrence};
    use crate::kb::test_support::load_stdlib;
    use crate::kb::KnowledgeBase;
    use std::rc::Rc;

    const SRC: &str = "namespace test.wi1083.unit\n\
        \x20 import anthill.prelude.{Int64, List}\n\
        \x20 operation idp[A](x: A) -> A = x\n\
        \x20 operation mono(x: Int64) -> Int64 = x\n\
        end\n";

    fn eta(kb: &mut KnowledgeBase, qn: &str) -> Value {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("no symbol {qn}"));
        let occ: Rc<NodeOccurrence> = NodeOccurrence::new_expr(Expr::Ref(sym), empty_span(), None);
        operation_as_function_value(kb, sym, &occ)
            .unwrap_or_else(|| panic!("{qn} must be an eta candidate"))
    }

    /// A type-parameterized operation's function-value type is a ∀; a MONOMORPHIC one's is the
    /// bare arrow it always was. Both halves together, because either alone is satisfied by a
    /// build that wraps everything or nothing — and wrapping everything would put a form every
    /// reader must see through on the path of every eta lift in the corpus.
    ///
    /// The binder is asserted by IDENTITY (`id`), never by name: WI-1079's rule is that two
    /// variables minted for one parameter name are different types that render alike, so a
    /// name comparison here could be satisfied by an unrelated `?A`.
    #[test]
    fn a_type_parameterized_operation_lifts_to_a_forall_and_a_monomorphic_one_does_not() {
        let mut kb = load_stdlib(Some(SRC));
        let poly = eta(&mut kb, "test.wi1083.unit.idp");
        let TypeExtractor::PolyType { binders, body } = extract_type(&kb, &poly) else {
            panic!("a type-parameterized operation's value type must be a PolyType");
        };
        assert_eq!(binders.len(), 1, "exactly the operation's own `[A]`");
        let sym = kb.try_resolve_symbol("test.wi1083.unit.idp").expect("idp");
        let declared = crate::kb::op_info::lookup_operation_info(&kb, sym)
            .expect("op info")
            .type_params
            .clone();
        let crate::kb::term::Var::Global(want) = declared[0].1 else {
            panic!("an operation's `[A]` is a Global var");
        };
        match type_head(&kb, &binders[0]) {
            TypeHead::FlexVar(got) => assert_eq!(
                got.raw(),
                want.raw(),
                "the binder IS the variable the signature declares, by identity",
            ),
            _ => panic!("a binder is a variable"),
        }
        assert!(
            matches!(type_head(&kb, &body), TypeHead::Arrow),
            "and it quantifies an ARROW",
        );

        let mono = eta(&mut kb, "test.wi1083.unit.mono");
        assert!(
            matches!(type_head(&kb, &mono), TypeHead::Arrow),
            "a signature that binds nothing keeps the bare arrow — `PolyType([], …)` and the \
             arrow are the same type, and minting the wrapper anyway would cost every \
             monomorphic lift a form to see through",
        );
    }

    /// TWO INSTANTIATIONS SHARE NO VARIABLE — the property the deleted gate said an arrow could
    /// not have ("unfreshened type-param vars that alias across multiple eta-lifts of the same
    /// op"). Asserted on the parameter's variable IDENTITY, and against the DECLARED variable
    /// as a third value, so neither instantiation can pass by accidentally being the original.
    #[test]
    fn two_instantiations_of_one_operation_share_no_variable() {
        let mut kb = load_stdlib(Some(SRC));
        let poly = eta(&mut kb, "test.wi1083.unit.idp");
        let a = instantiate_poly_type(&mut kb, &poly).expect("a ∀ instantiates");
        let b = instantiate_poly_type(&mut kb, &poly).expect("a ∀ instantiates");
        let param_var = |kb: &KnowledgeBase, t: &Value| -> u32 {
            let TypeExtractor::Arrow { param, .. } = extract_type(kb, t) else {
                panic!("an instantiated ∀ over an arrow is an arrow");
            };
            match type_head(kb, &param) {
                TypeHead::FlexVar(v) => v.raw(),
                _ => panic!("the parameter is the instantiated variable"),
            }
        };
        let result_var = |kb: &KnowledgeBase, t: &Value| -> u32 {
            let TypeExtractor::Arrow { result, .. } = extract_type(kb, t) else {
                panic!("an instantiated ∀ over an arrow is an arrow");
            };
            match type_head(kb, &result) {
                TypeHead::FlexVar(v) => v.raw(),
                _ => panic!("the result is the instantiated variable"),
            }
        };
        let (ia, ib) = (param_var(&kb, &a), param_var(&kb, &b));
        assert_ne!(ia, ib, "each instantiation mints its own variable");
        // AND THE TIE SURVIVES: `idp`'s parameter and result are ONE variable, so an
        // instantiation that minted a fresh variable per OCCURRENCE instead of per BINDER
        // would break the very thing the signature says — that the result is the argument's
        // type. Asserted inside each instantiation, so it cannot be satisfied by the two
        // instantiations happening to agree.
        assert_eq!(
            ia,
            result_var(&kb, &a),
            "one binder, one fresh variable — `∀A. (x: A) -> A` instantiates to `(x: ?A1) -> \
             ?A1`, not to two unrelated variables",
        );
        assert_eq!(ib, result_var(&kb, &b));
        let TypeExtractor::PolyType { binders, .. } = extract_type(&kb, &poly) else {
            unreachable!("asserted a PolyType above");
        };
        let declared = match type_head(&kb, &binders[0]) {
            TypeHead::FlexVar(v) => v.raw(),
            _ => panic!("a binder is a variable"),
        };
        assert_ne!(ia, declared, "and neither of them is the declared one");
        assert_ne!(ib, declared);
    }

    /// NO BINDER SURVIVES INTO AN INSTANTIATION — asserted over the WHOLE type rather than
    /// at one position, on a MULTI-PARAMETER, HIGHER-ORDER operation, because that is the
    /// shape the sibling rows above cannot see.
    ///
    /// `idp` has ONE parameter, so its eta arrow's `param` is a bare `Term` and every
    /// rewriter reaches it. A parameter LIST is a `named_tuple`, and it rides the
    /// `Value::Node` carrier as soon as one field's type does — which a callback declaring
    /// `@ {EffP, -Modify[x]}` always does, because a `denoted`-bearing label cannot
    /// hash-cons. The first cut instantiated through `walk_type_deep_value`, whose
    /// `NamedTuple` arm answers "unchanged", so every binder in a PARAMETER position was
    /// left SHARED between references while the result position was correctly freshened —
    /// and both rows above stayed green throughout.
    ///
    /// ON THE STDLIB'S OWN `Iterable.map`, not a fixture: a hand-written
    /// `hof[A, B](x: A, f: (v: A) -> B)` does NOT reproduce it (its declared arrow field
    /// hash-conses, so the tuple stays Term-carried and the old walk reaches it), and a row
    /// built on one passed under the back-out. The corpus operation is the shape that
    /// actually leaks.
    ///
    /// CONTROL: with the walk put back to `walk_type_deep_value` this fails with
    /// `leaked [452, 453] of [452, 453, 51, 52, 53]` — `Dst` and `EffP`, the operation's own
    /// two binders, surviving into what is supposed to be a fresh instance. It asserts an
    /// ABSENCE, so it is paired with the positive assertion that the instantiation carries
    /// variables at all — an empty collect would otherwise satisfy it vacuously.
    #[test]
    fn no_declared_binder_survives_into_an_instantiation() {
        let mut kb = load_stdlib(Some(SRC));
        let poly = eta(&mut kb, "anthill.prelude.Iterable.map");
        let TypeExtractor::PolyType { binders, .. } = extract_type(&kb, &poly) else {
            panic!("a multi-parameter type-parameterized operation lifts to a PolyType");
        };
        let binder_ids: Vec<u32> = binders
            .iter()
            .map(|b| match type_head(&kb, b) {
                TypeHead::FlexVar(v) => v.raw(),
                _ => panic!("a binder is a variable"),
            })
            .collect();
        assert!(
            binder_ids.len() >= 2,
            "`map[Dst, EffP]` binds at least its own two: {binder_ids:?}",
        );
        let inst = instantiate_poly_type(&mut kb, &poly).expect("a ∀ instantiates");
        let mut seen_in_inst: Vec<crate::kb::term::VarId> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        crate::kb::node_occurrence::collect_value_type(&kb, &inst, &mut seen_in_inst, &mut seen);
        assert!(
            !seen_in_inst.is_empty(),
            "the instantiation carries variables — without this the absence below is vacuous",
        );
        let leaked: Vec<u32> = seen_in_inst
            .iter()
            .map(|v| v.raw())
            .filter(|v| binder_ids.contains(v))
            .collect();
        assert!(
            leaked.is_empty(),
            "every binder must be freshened, including the ones inside the parameter LIST \
             (a `named_tuple` on the Node carrier); leaked {leaked:?} of {binder_ids:?}",
        );
    }
}

/// WI-1084 — UNIFICATION ACROSS THE TWO SPELLINGS OF ONE TYPE, driven at the relation
/// itself. `docs/kernel-language.md` §4.4 says `Function[A, B, E]` and `arrow` ARE the same
/// type; `unify_types` had an arm for `(arrow, arrow)` only, so the mixed pair fell to the
/// `_ =>` subtype fallback — which decomposes but cannot BIND — and answered `false` with
/// ZERO bindings whether the pair agreed or not.
///
/// THE ARROW ROWS ARE THE CONTROL and were always correct. They are asserted beside the
/// `Function` rows so "false" cannot pass for a verdict: the whole finding is that one of
/// these four answers was false where the truth is TRUE, which is only visible as a
/// disagreement between two spellings of one question.
///
/// ## THREE LEVELS, each independently load-bearing — DRIVEN, one revert each, whole crate
///
/// | revert | cost |
/// |---|---|
/// | the two `unify_types` dispatch arms | **2** — this row, and `wi1083_polytype_test::a_result_type_disagreement_is_refused` (nothing binds `?A1`, so the result comparison has nothing to see) |
/// | `validate_arrow_param_result`'s σ-resolution of the RESULT | **1** — `…::a_result_type_disagreement_is_refused` (the binding exists but the groundness test reads the component as written) |
/// | `validate_callback_effect_row`'s no-places-to-align widening | **1** — `…::an_effect_row_disagreement_is_refused` |
///
/// So the RESULT-type hole needed the first two TOGETHER and the EFFECT-ROW hole needed the
/// third ALONE — three withholdings stacked over one root, which is why the first fix
/// changed no end-to-end verdict at all and why measuring each level separately was the only
/// way to know that.
///
/// NOTHING THE SUITE OR THE SEVEN CORPUS TIERS REACH MOVES under any of the three. That is
/// weaker than "nothing moves", deliberately — see
/// [`the_arms_make_unify_stricter_than_the_subtype_fallback_it_replaced`], which pins the one
/// judgement that genuinely CHANGES.
#[cfg(test)]
mod wi1084_arrow_function_unify_tests {
    use super::super::{instantiate_poly_type, operation_as_function_value, unify_types};
    use crate::kb::node_occurrence::{empty_span, Expr, NodeOccurrence};
    use crate::kb::subst::Substitution;
    use crate::kb::test_support::load_stdlib;
    use crate::kb::KnowledgeBase;
    use std::rc::Rc;

    const SRC: &str = "namespace test.wi1084\n\
        \x20 import anthill.prelude.{Int64, String, Function}\n\
        \x20 operation idp[A](x: A) -> A = x\n\
        \x20 operation arrowOk(f: (v: Int64) -> Int64) -> Int64 = f(3)\n\
        \x20 operation arrowBad(f: (v: Int64) -> String) -> String = f(3)\n\
        \x20 operation funOk(f: Function[A = Int64, B = Int64, E = {}]) -> Int64 = f(3)\n\
        \x20 operation funBad(f: Function[A = Int64, B = String, E = {}]) -> String = f(3)\n\
        end\n";

    /// `(verdict, bindings)` of unifying a fresh instance of `idp`'s ∀ against `callee`'s
    /// sole declared parameter type.
    fn unify_against_param(kb: &mut KnowledgeBase, callee: &str) -> (bool, usize) {
        let idp = kb.try_resolve_symbol("test.wi1084.idp").expect("idp");
        let occ: Rc<NodeOccurrence> = NodeOccurrence::new_expr(Expr::Ref(idp), empty_span(), None);
        let poly = operation_as_function_value(kb, idp, &occ).expect("idp eta-lifts");
        let inst = instantiate_poly_type(kb, &poly).expect("a ∀ instantiates");
        let sym = kb
            .try_resolve_symbol(callee)
            .unwrap_or_else(|| panic!("{callee}"));
        let param = crate::kb::op_info::lookup_operation_info(kb, sym)
            .expect("op info")
            .params[0]
            .1
            .clone();
        let mut subst = Substitution::new();
        let verdict = unify_types(kb, &mut subst, &inst, &param);
        (verdict, subst.bindings.len())
    }

    /// THE HEADLINE, all four rows in one test so none can pass vacuously. Before this
    /// ticket the two `Function` rows were `(false, 0)` — indistinguishable from each other
    /// and both wrong about the agreeing one.
    #[test]
    fn the_two_spellings_of_one_slot_answer_alike() {
        let mut kb = load_stdlib(Some(SRC));
        assert_eq!(
            unify_against_param(&mut kb, "test.wi1084.arrowOk"),
            (true, 1),
            "CONTROL: the arrow spelling of an AGREEING slot unifies and binds `A := Int64`",
        );
        assert_eq!(
            unify_against_param(&mut kb, "test.wi1084.arrowBad"),
            (false, 1),
            "CONTROL: the arrow spelling of a DISAGREEING slot binds `A := Int64` from the \
             parameter and then refuses on the result",
        );
        assert_eq!(
            unify_against_param(&mut kb, "test.wi1084.funOk"),
            (true, 1),
            "the `Function` spelling of the SAME agreeing slot must answer the same — it \
             answered `(false, 0)` before, which is not a verdict but a fall-through",
        );
        assert_eq!(
            unify_against_param(&mut kb, "test.wi1084.funBad"),
            (false, 1),
            "and the disagreeing one must refuse HAVING BOUND `A` — the binding is what lets \
             the checks downstream see that the result contradicts the parameter",
        );
    }

    /// THE ONE JUDGEMENT THAT CHANGES, pinned because it is a real tightening and not a
    /// side effect. Before these arms `(arrow, parameterized)` was a form MISMATCH and took
    /// `unify_types`' `_ =>` fallback — which is [`types_compatible`], the SUBTYPE relation.
    /// So for this pair unify was literally equal to subtyping, and effects were compared
    /// COVARIANTLY: a pure arrow "unified" with a slot declaring `E = {Error}`.
    ///
    /// With an arm, unification means what it means everywhere else — EQUALITY, the same
    /// reading the `(arrow, arrow)` arm has always had (`unify_effect_rows`, not
    /// `subtype_effect_rows`). Subtyping is unchanged and still says yes, which is also
    /// right: a pure function IS usable where an effectful one is expected.
    ///
    /// WHY IT IS WORTH A ROW: three callers act on the verdict rather than discarding it —
    /// `constrain_vid` (which marks the substitution CONTRADICTORY on a false),
    /// `hint_instantiation_subst` (which drops the pin) and `unify_parameterized_view`
    /// (which fails a whole binding set). The argument path is not among them; it discards
    /// the boolean by design. Nothing in the suite or the corpus reaches the difference —
    /// which is exactly why it needs asserting here rather than left to be discovered.
    #[test]
    fn the_arms_make_unify_stricter_than_the_subtype_fallback_it_replaced() {
        let src = "namespace test.wi1084b\n\
            \x20 import anthill.prelude.{Int64, Function, Error}\n\
            \x20 operation idm(x: Int64) -> Int64 = x\n\
            \x20 operation wider(f: Function[A = Int64, B = Int64, E = {Error}]) -> Int64 \
             effects {Error} = f(3)\n\
            end\n";
        let mut kb = load_stdlib(Some(src));
        let idm = kb.try_resolve_symbol("test.wi1084b.idm").expect("idm");
        let occ: Rc<NodeOccurrence> = NodeOccurrence::new_expr(Expr::Ref(idm), empty_span(), None);
        let arrow = operation_as_function_value(&mut kb, idm, &occ).expect("idm eta-lifts");
        let sym = kb.try_resolve_symbol("test.wi1084b.wider").expect("wider");
        let param = crate::kb::op_info::lookup_operation_info(&kb, sym)
            .expect("op info")
            .params[0]
            .1
            .clone();
        let mut s1 = Substitution::new();
        assert!(
            !unify_types(&mut kb, &mut s1, &arrow, &param),
            "UNIFY is equality: a pure arrow is not the same type as an `E = {{Error}}` slot. \
             This answered TRUE before the arms, because the pair fell through to the subtype \
             relation",
        );
        let mut s2 = Substitution::new();
        assert!(
            super::super::types_compatible(&mut kb, &mut s2, &arrow, &param),
            "SUBTYPING is unchanged and still accepts it — a pure function is usable where an \
             effectful one is expected. Asserted beside the row above so the two relations \
             are seen to DISAGREE on purpose rather than one of them being broken",
        );
    }
}

/// WI-864 — [`ProvidesIndex::carrier_edges`] is a MEMO OF [`provides_out_edges`], and a
/// memo is only sound while it answers what the function answers. These tests are that
/// equality, driven at the two states the KB is ever in (index live / index dropped) and
/// over EVERY sort the KB names rather than the handful the fixture writes.
///
/// A wrong answer here is not a slow one. `provides_out_edges` is the step relation of
/// [`sort_provides`], which decides subtype admissibility (`sort_provides_admissibly`),
/// the dispatch carrier filter, and requires-coverage — so an edge that falls out of the
/// memo is a PROVISION THAT STOPS EXISTING: a value of a carrier stops conforming to a
/// spec it provides, and a program that should load is refused. An edge that lingers
/// fails the other way, admitting a value nothing licenses. That is WI-954's failure mode
/// on the provides side, which is why the memo lives INSIDE `ProvidesIndex` (one
/// lifecycle, nothing new to remember) and why its agreement with the decode is tested
/// rather than argued.
#[cfg(test)]
mod wi864_provides_edges_tests {
    use super::super::{build_provides_index, provides_out_edges, sort_provides};
    use crate::kb::term::Term;
    use crate::kb::test_support::load_stdlib;
    use crate::kb::{KnowledgeBase, Symbol};

    /// A THREE-FLOOR provides tower plus a non-provider sibling. `Bottom` reaches `Top`
    /// only through `Mid`, so the answer is produced by the TRANSITIVE walk — the code
    /// WI-864 rewrote — and not by a single direct edge.
    const SRC: &str = r#"
namespace test.wi864
  import anthill.prelude.{Int64}
  sort Top
    sort T = ?
  end
  sort Mid
    sort T = ?
    provides Top[T = T]
  end
  sort Bottom
    sort T = ?
    provides Mid[T = T]
  end
  sort Unrelated
    sort T = ?
  end
end
"#;

    /// Every sort the KB names — the POPULATION, so the memo/decode comparison is not
    /// scoped to the fixture's four sorts. The stdlib alone contributes the diamond
    /// (`Ordered` → `Eq` + `PartialOrd` → `PartialEq`) this ticket is about.
    fn all_sorts(kb: &KnowledgeBase) -> Vec<Symbol> {
        let Some(sort_info) = kb.try_resolve_symbol("anthill.reflect.SortInfo") else {
            panic!("the stdlib declares SortInfo");
        };
        let mut out = Vec::new();
        for rid in kb.rules_by_functor(sort_info) {
            if !kb.is_fact(rid) {
                continue;
            }
            let head = kb.rule_head_value(rid);
            let Some(name_tid) = crate::kb::op_info::head_field_term(kb, head, "name") else {
                continue;
            };
            match kb.get_term(name_tid) {
                Term::Ref(s) => out.push(*s),
                Term::Fn { functor, .. } => out.push(*functor),
                _ => {}
            }
        }
        out
    }

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("{qn} resolves"))
    }

    /// THE MEMO IS THE FUNCTION, over the whole population. With the index live every
    /// `provides_out_edges` answer comes from `carrier_edges`; with it dropped every one
    /// is decoded live. The two lists must agree per carrier, ORDER INCLUDED — the walk
    /// takes the first reaching edge, so a permuted list is a different search.
    ///
    /// CONTROL, AND TWO OF THE THREE I EXPECTED DO NOT FIRE — measured, not predicted:
    ///
    ///  * Building `carrier_edges` from the `unwrap_spec_view` base beside it (the OTHER
    ///    spec decode in `build_provides_index`) instead of `provides_spec_base_sym`:
    ///    ALL THREE TESTS STILL PASS. The two decodes agree on every provides fact this
    ///    corpus holds, so which one the memo is built from is unobservable today. Using
    ///    the consumer's own decode therefore ships on the rule that a memo should BE its
    ///    function rather than a lookalike — not on a failing case.
    ///  * Filing the edge under the RAW carrier instead of `canonical_sort_sym(carrier)`:
    ///    the whole workspace stays green (4984 tests). Every provides carrier here is a
    ///    resolved sort functor that is already its own canonical form — which is what
    ///    `build_provides_index`' own `debug_assert` asserts — so the two keys coincide.
    ///    Canonical keying ships because the lookup key IS canonical (the walk
    ///    canonicalizes once and carries it) and because the sibling `by_carrier` bucket
    ///    keys that way for WI-672's reason. MEASURED INERT on this corpus; no test covers
    ///    it.
    ///
    /// The one control that DOES fire is the retraction test below. And none of the three
    /// fails with WI-864 backed out, nor can it: backed out, both arms ARE the decode.
    /// What these guard is the risk the memo introduces, which is the only new risk.
    #[test]
    fn the_memo_answers_what_the_live_decode_answers_for_every_carrier() {
        let mut kb = load_stdlib(Some(SRC));
        assert!(
            kb.provides_index.is_some(),
            "premise: a full load leaves the provides index BUILT — without this the test \
             would compare the decode with itself and measure nothing",
        );
        let sorts = all_sorts(&kb);
        assert!(
            sorts.len() > 50,
            "premise: the population is the KB's sorts, not the fixture's ({} found)",
            sorts.len(),
        );

        let via_memo: Vec<_> = sorts
            .iter()
            .map(|&s| provides_out_edges(&kb, kb.canonical_sort_sym(s)))
            .collect();
        kb.provides_index = None;
        let via_decode: Vec<_> = sorts
            .iter()
            .map(|&s| provides_out_edges(&kb, kb.canonical_sort_sym(s)))
            .collect();

        let mut with_edges = 0usize;
        for (i, s) in sorts.iter().enumerate() {
            if !via_memo[i].is_empty() {
                with_edges += 1;
            }
            assert_eq!(
                via_memo[i].as_slice(),
                via_decode[i].as_slice(),
                "provides out-edges of `{}` disagree between the memo and the live decode",
                kb.qualified_name_of(*s),
            );
        }
        assert!(
            with_edges >= 10,
            "premise: the comparison is not vacuous — only {with_edges} carriers have any \
             out-edge at all, so an all-empty agreement would prove nothing",
        );
    }

    /// THE CONSUMER, DRIVEN TRANSITIVELY. `Bottom provides Mid provides Top` is two hops:
    /// the walk must canonicalize, follow, and answer — and answer the same with the memo
    /// and without it. `Unrelated` is the negative in the same run, so a walk that said
    /// `true` for everything would fail here rather than pass silently.
    #[test]
    fn a_two_hop_chain_resolves_identically_with_and_without_the_memo() {
        let mut kb = load_stdlib(Some(SRC));
        let bottom = sym(&kb, "test.wi864.Bottom");
        let mid = sym(&kb, "test.wi864.Mid");
        let top = sym(&kb, "test.wi864.Top");
        let unrelated = sym(&kb, "test.wi864.Unrelated");

        for (label, index_live) in [("memo", true), ("decode", false)] {
            if !index_live {
                kb.provides_index = None;
            }
            assert!(
                kb.provides_index.is_some() == index_live,
                "the {label} arm runs in the state it names",
            );
            assert!(
                sort_provides(&kb, bottom, mid),
                "{label}: Bottom provides Mid directly",
            );
            assert!(
                sort_provides(&kb, bottom, top),
                "{label}: Bottom provides Top TRANSITIVELY (Bottom -> Mid -> Top)",
            );
            assert!(
                !sort_provides(&kb, bottom, unrelated),
                "{label}: Bottom does not provide Unrelated — the negative that says the \
                 walk discriminates",
            );
            assert!(
                !sort_provides(&kb, top, bottom),
                "{label}: the relation is directed — Top does not provide Bottom",
            );
        }
    }

    /// THE PRECONDITION IS DRIVABLE, so it is driven rather than merely asserted. A guard
    /// nothing can fire is a guard nobody has measured (and would be dead weight); this one
    /// fires, because `intern` mints a symbol WITHOUT registering its qualified name
    /// (`define_qualified_only` is the registering door), so an interned copy of a name the
    /// stdlib already owns is a genuine non-canonical symbol — precisely the shape WI-617
    /// says the KB grows on its own.
    ///
    /// WITHOUT the guard this call returns an EMPTY edge list — "this carrier provides
    /// nothing" — which is a wrong verdict, not a refusal. MEASURED: with the
    /// `debug_assert_eq!` removed, this test fails on the `should_panic` instead of the
    /// lookup, and the bare call answers `[]` for a carrier that provides `Top`.
    #[test]
    #[should_panic(expected = "is not canonical")]
    fn a_non_canonical_carrier_is_refused_loudly_not_answered_empty() {
        let mut kb = load_stdlib(Some(SRC));
        let mid_canon = kb.canonical_sort_sym(sym(&kb, "test.wi864.Mid"));
        // Premise: canonically, `Mid` HAS an out-edge — so an empty answer below would be
        // wrong rather than merely uninformative.
        assert!(
            !provides_out_edges(&kb, mid_canon).is_empty(),
            "premise: Mid provides Top, so the canonical lookup is non-empty",
        );

        // A second interned copy of the SAME qualified name: `intern` does not register it
        // in `by_qualified_name`, so the registered canonical stays the loader's symbol and
        // this copy is not its own canonical form.
        let twin = kb.intern("test.wi864.Mid");
        assert_ne!(
            twin,
            kb.canonical_sort_sym(twin),
            "premise: the interned twin is genuinely non-canonical — without this the test \
             would assert nothing",
        );
        let _ = provides_out_edges(&kb, twin);
    }

    /// A RETRACTED PROVISION IS NOT IN THE RELATION, AND THE MEMO MUST AGREE — the
    /// provides-side twin of WI-1112's `a_retracted_requires_fact_is_dropped_by_the_index`.
    /// `carrier_edges` is frozen at build time, so it carries the `RuleId` for exactly this
    /// question; `rules_by_functor` (the decode arm) filters retracted at query time.
    ///
    /// THIS SIDE FAILS UPWARD: without the filter the edge OUTLIVES its declaration, and a
    /// value keeps conforming to a spec nothing says it provides.
    ///
    /// CONTROL: drop the `is_rule_alive` filter from `provides_out_edges`' memo arm and the
    /// first assertion below fails while the decode arm still passes — the disagreement
    /// stated as a test. NO REBUILD between the retract and the read: `build_provides_index`
    /// reads `rules_by_functor`, so rebuilding would refresh the bucket and measure nothing.
    #[test]
    fn a_retracted_provision_is_dropped_by_the_memo_as_it_is_by_the_decode() {
        let mut kb = load_stdlib(Some(SRC));
        let bottom = kb.canonical_sort_sym(sym(&kb, "test.wi864.Bottom"));
        let mid = kb.canonical_sort_sym(sym(&kb, "test.wi864.Mid"));
        build_provides_index(&mut kb);
        assert!(
            provides_out_edges(&kb, bottom).contains(&mid),
            "premise: Bottom -> Mid is an edge before the retraction",
        );

        let provides_sym = kb.resolve_symbol("anthill.reflect.SortProvidesInfo");
        let rid = kb
            .rules_by_functor(provides_sym)
            .into_iter()
            .find(|rid| {
                if !kb.is_fact(*rid) {
                    return false;
                }
                let Some(named) = kb.fact_head_named_args(*rid) else {
                    return false;
                };
                let Some(c) = super::super::get_named_arg(&kb, &named, "sort_ref")
                    .and_then(|t| crate::kb::load::sort_ref_functor(&kb, t))
                else {
                    return false;
                };
                // BOTH ENDS, not the carrier alone. Selecting by carrier picks the right
                // fact only while `Bottom` has exactly one provision — and later passes DO
                // emit extra ones (`eq_derive` derives `NonEq`/`PartialEq` provisions for
                // other carriers today). Unpinned, this would one day retract an unrelated
                // edge and then fail at the assertion below naming the wrong cause.
                let Some(dst) = super::super::get_named_arg(&kb, &named, "spec")
                    .and_then(|t| crate::kb::load::provides_spec_base_sym(&kb, t))
                else {
                    return false;
                };
                kb.canonical_sort_sym(c) == bottom && kb.canonical_sort_sym(dst) == mid
            })
            .expect("the `Bottom provides Mid` fact");

        // A retractor that does NOT invalidate — the case the filter has to survive.
        kb.retract(rid);
        assert!(
            kb.provides_index.is_some(),
            "the index built above is still the live one — nothing rebuilt or dropped it",
        );
        assert!(
            !provides_out_edges(&kb, bottom).contains(&mid),
            "through the MEMO built BEFORE the retraction: a retracted provision must not \
             be served",
        );

        kb.provides_index = None;
        assert!(
            !provides_out_edges(&kb, bottom).contains(&mid),
            "through the DECODE: `rules_by_functor` already filtered it — the answer the \
             memo has to match",
        );
    }
}

/// WI-1112 — [`build_requires_index`] and the consumer it serves,
/// [`collect_sort_requires`], must answer the SAME chain the `rules_by_functor` scan
/// answered, and must keep answering it when the relation changes after the build.
///
/// A wrong answer here is not a slow one. `SortRequiresInfo` is where a sort's dictionary
/// slots come from, so a fact that falls out of a bucket is a REQUIREMENT THAT STOPS
/// EXISTING: the program loads clean, the slot is never synthesized, and the failure
/// surfaces at eval as an unbound `__req_*`. That is WI-954's measured failure mode, and
/// these tests are its entrances: the index disagreeing with the scan; the index missing a
/// carrier it cannot READ; the index outliving an assert; the index outliving a RETRACT
/// (the one that fails upward — a slot that will not stop existing); and the index and the
/// chain memos outliving a whole ENTRY POINT that writes. The last three were found by
/// review, not by the corpus.
#[cfg(test)]
mod wi1112_requires_index_tests {
    use super::super::{build_requires_index, direct_requires};
    use crate::eval::value::Value;
    use crate::kb::node_occurrence::{Expr, NodeOccurrence};
    use crate::kb::term::{Literal, Term};
    use crate::kb::term_view::views_structurally_equal;
    use crate::kb::test_support::load_stdlib;
    use crate::kb::{ClauseKind, KnowledgeBase, Symbol};
    use crate::span::{SourceId, SourceSpan};

    /// `Carrier` requires `Foo`, written in surface syntax so the ordinary loader path
    /// (`load_requires_decl` → `resolve_requires_bindings`) is the producer.
    const SRC: &str = r#"
namespace test.wi1112
  import anthill.prelude.{Int64}
  sort Foo
    sort T = ?
  end
  sort Bar
    sort T = ?
  end
  sort Carrier
    requires Foo[T = Int64]
    entity c(x: Int64)
  end
end
"#;

    /// Every sort the KB names, so the scan/index comparison is over the whole relation
    /// rather than the one sort the fixture wrote.
    fn all_sorts(kb: &KnowledgeBase) -> Vec<Symbol> {
        let Some(sort_info) = kb.try_resolve_symbol("anthill.reflect.SortInfo") else {
            panic!("the stdlib declares SortInfo");
        };
        let mut out = Vec::new();
        for rid in kb.rules_by_functor(sort_info) {
            if !kb.is_fact(rid) {
                continue;
            }
            let head = kb.rule_head_value(rid);
            let Some(name_tid) = crate::kb::op_info::head_field_term(kb, head, "name") else {
                continue;
            };
            match kb.get_term(name_tid) {
                Term::Ref(s) => out.push(*s),
                Term::Fn { functor, .. } => out.push(*functor),
                _ => {}
            }
        }
        out
    }

    /// `sort`'s direct requires as (required sort, spec), for comparing two data sources.
    fn entries(kb: &KnowledgeBase, sort: Symbol) -> Vec<(Symbol, Value)> {
        direct_requires(kb, sort)
            .into_iter()
            .map(|e| (e.required_sort, e.spec))
            .collect()
    }

    /// Clear the chain memos AND leave the index built — the state the load pipeline is
    /// in from `type_check_sorts` onward. `invalidate_requires_chain_cache` drops the
    /// index by design (that is test 3's subject), so the rebuild is explicit here.
    fn fresh_with_index(kb: &mut KnowledgeBase) {
        kb.invalidate_requires_chain_cache();
        build_requires_index(kb);
        assert!(kb.requires_index.is_some(), "the index is built");
    }

    /// Clear the chain memos and leave the index DROPPED — the load-time window, and the
    /// pre-WI-1112 behaviour of every call.
    fn fresh_with_scan(kb: &mut KnowledgeBase) {
        kb.invalidate_requires_chain_cache();
        assert!(
            kb.requires_index.is_none(),
            "invalidating the chain caches drops the index with them"
        );
    }

    /// THE EQUIVALENCE. For every sort in a fully-loaded KB, the indexed lookup and the
    /// live scan return the same requires entries, in the same order.
    ///
    /// NOT VACUOUS: the run asserts that the sorts compared number in the hundreds and
    /// that the entries found number in the dozens, so an index (or a scan) that answered
    /// EMPTY everywhere could not agree its way to a pass — the shape WI-1042 measured,
    /// where a domain restriction made agreement meaningless.
    ///
    /// CONTROL: fails on any keying change that is not the consumer's own — key the
    /// bucket on the raw `sort_ref` symbol instead of `canonical_sort_sym`, or on a last
    /// segment, and the sorts whose two spellings differ drop out.
    #[test]
    fn the_index_answers_exactly_what_the_scan_answers() {
        let mut kb = load_stdlib(Some(SRC));
        let sorts = all_sorts(&kb);
        assert!(
            sorts.len() > 100,
            "the stdlib names hundreds of sorts; got {}",
            sorts.len()
        );

        fresh_with_scan(&mut kb);
        let scanned: Vec<Vec<(Symbol, Value)>> = sorts.iter().map(|s| entries(&kb, *s)).collect();
        fresh_with_index(&mut kb);
        let indexed: Vec<Vec<(Symbol, Value)>> = sorts.iter().map(|s| entries(&kb, *s)).collect();

        let total: usize = scanned.iter().map(|e| e.len()).sum();
        assert!(
            total > 20,
            "the comparison must have entries to compare; got {total}"
        );
        for ((sort, s), i) in sorts.iter().zip(&scanned).zip(&indexed) {
            assert_eq!(
                s.len(),
                i.len(),
                "{}: scan and index must find the same number of requires entries \
                 (scan {:?}, index {:?})",
                kb.qualified_name_of(*sort),
                s.iter()
                    .map(|(r, _)| kb.qualified_name_of(*r))
                    .collect::<Vec<_>>(),
                i.iter()
                    .map(|(r, _)| kb.qualified_name_of(*r))
                    .collect::<Vec<_>>(),
            );
            for ((sr, ss), (ir, is)) in s.iter().zip(i) {
                assert_eq!(
                    sr,
                    ir,
                    "{}: same required sort in the same position",
                    kb.qualified_name_of(*sort)
                );
                assert!(
                    views_structurally_equal(&kb, ss, is),
                    "{}: same spec for {}",
                    kb.qualified_name_of(*sort),
                    kb.qualified_name_of(*sr),
                );
            }
        }
    }

    /// A VALUE-FACT `SortRequiresInfo` — a denoted-bearing spec (WI-662) — must land in a
    /// bucket. It has no `fact_head_named_args`, so a builder written the way
    /// `build_sort_info_index` writes its own (term-only named args) leaves it in NO
    /// bucket, and the requirement silently stops existing once the index is live.
    ///
    /// CONTROL: this is the ONE test that fails if `build_requires_index` reads the head
    /// term-only instead of through `rule_head_value` + `head_field_term`.
    /// `wi662_carrier_agnostic_requires_test` does NOT cover it — it reads the chain right
    /// after `invalidate_requires_chain_cache`, i.e. with the index dropped, so it
    /// measures the scan. The `requires_index.is_some()` assertion below is what makes
    /// this test measure the index instead.
    #[test]
    fn a_denoted_requires_fact_is_bucketed_not_dropped() {
        let mut kb = load_stdlib(Some(SRC));
        let carrier = kb
            .try_resolve_symbol("test.wi1112.Carrier")
            .expect("Carrier");
        let bar = kb.try_resolve_symbol("test.wi1112.Bar").expect("Bar");

        // The head shape `assert_fact_carrier` emits for a spec carrying a `Value::Node`
        // binding — not producible from surface syntax (WI-390 lowers every
        // term-representable spec), so it is built directly, exactly as wi662 does.
        let requires_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
        let sort_ref_field = kb.intern("sort_ref");
        let spec_field = kb.intern("spec");
        kb.register_entity_fields(requires_sym, vec![sort_ref_field, spec_field]);
        let sortview = kb.resolve_symbol("anthill.reflect.SortView");
        let k = kb.intern("k");
        let sort_ref = Value::term(kb.make_name_term_from_sym(carrier));
        let bar_base = Value::term(kb.make_name_term_from_sym(bar));
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);
        let node = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span, None);
        let spec = Value::Entity {
            functor: sortview,
            pos: vec![bar_base].into(),
            named: vec![(k, Value::Node(node))].into(),
        };
        let domain = kb.intern("test.wi1112");
        kb.assert_fact_carrier(
            requires_sym,
            Vec::new(),
            vec![(sort_ref_field, sort_ref), (spec_field, spec)],
            ClauseKind::Requirement,
            domain,
            None,
        );

        fresh_with_index(&mut kb);
        let found = entries(&kb, carrier);
        assert!(
            found.iter().any(|(r, _)| *r == bar),
            "the denoted `Carrier requires Bar[...]` must be reachable THROUGH the index; \
             got {:?}",
            found
                .iter()
                .map(|(r, _)| kb.qualified_name_of(*r))
                .collect::<Vec<_>>(),
        );
        // …and the surface-syntax requirement beside it, so the value fact did not
        // displace the term one in its bucket.
        let foo = kb.try_resolve_symbol("test.wi1112.Foo").expect("Foo");
        assert!(
            found.iter().any(|(r, _)| *r == foo),
            "the ordinary `requires Foo[T = Int64]` is still there"
        );
    }

    /// THE STALE-INDEX GUARD (WI-954's shape). A `SortRequiresInfo` fact asserted AFTER
    /// the index was built is still found, because the one call every producer already
    /// owes — `invalidate_requires_chain_cache` — drops the index with the chain memos.
    ///
    /// CONTROL: back out that one line in `KnowledgeBase::invalidate_requires_chain_cache`
    /// and this fails — the post-load index is live and `Carrier`'s bucket is the one
    /// built before the write, so the new requirement is invisible. The
    /// `requires_index.is_none()` assertion inside `fresh_with_scan` fails FIRST, which is
    /// the point: it names the mechanism rather than the symptom. Both
    /// `wi662_carrier_agnostic_requires_test` tests fail on the same back-out, for the
    /// same reason.
    #[test]
    fn a_requires_asserted_after_the_build_is_still_found() {
        let mut kb = load_stdlib(Some(SRC));
        let carrier = kb
            .try_resolve_symbol("test.wi1112.Carrier")
            .expect("Carrier");
        let bar = kb.try_resolve_symbol("test.wi1112.Bar").expect("Bar");
        assert!(
            kb.requires_index.is_some(),
            "the load leaves the index BUILT — otherwise this test's premise is empty \
             and it would pass on a scan that never had an index to go stale",
        );
        assert!(
            !entries(&kb, carrier).iter().any(|(r, _)| *r == bar),
            "premise: Carrier does not require Bar yet",
        );

        let requires_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
        let sort_ref_field = kb.intern("sort_ref");
        let spec_field = kb.intern("spec");
        let sort_ref = Value::term(kb.make_name_term_from_sym(carrier));
        let bar_base = Value::term(kb.make_name_term_from_sym(bar));
        let domain = kb.intern("test.wi1112");
        kb.assert_fact_carrier(
            requires_sym,
            Vec::new(),
            vec![(sort_ref_field, sort_ref), (spec_field, bar_base)],
            ClauseKind::Requirement,
            domain,
            None,
        );

        // What every producer of this relation owes, and all it owes.
        fresh_with_scan(&mut kb);
        assert!(
            entries(&kb, carrier).iter().any(|(r, _)| *r == bar),
            "the newly asserted requirement must be found",
        );

        // And the rebuild picks it up, so the index is not merely bypassed forever.
        fresh_with_index(&mut kb);
        assert!(
            entries(&kb, carrier).iter().any(|(r, _)| *r == bar),
            "the rebuilt index contains the fact asserted after the first build",
        );
    }

    /// A RETRACTED FACT IS NOT IN THE RELATION, AND THE BUCKET MUST AGREE. The two arms of
    /// `SymbolKeyedFactIndex::rids_or_scan` are only interchangeable if they answer alike,
    /// and retraction is the one input where they did not: `rules_by_functor` filters
    /// `retracted` at query time (its doc says "all ACTIVE"), while a bucket is frozen at
    /// build time and `is_fact` — the consumer's only per-fact guard — reads
    /// `body_nodes.is_empty()` and says `true` for a retracted slot.
    ///
    /// THIS SIDE FAILS UPWARD, which is what makes it worth a test of its own: everything
    /// else in this module guards against a requirement that stops existing, and this
    /// guards against one that will not stop — a dictionary slot outliving the declaration
    /// it came from. `KnowledgeBase::retract` is a RETRACTOR, and nothing made it owe
    /// `invalidate_requires_chain_cache`; the fix is therefore in `rids_or_scan` itself
    /// rather than in a rule someone must remember.
    ///
    /// CONTROL: drop the `is_rule_alive` filter from `rids_or_scan`'s index arm and the
    /// indexed half of this fails while the scanned half still passes — which is the
    /// disagreement stated as a test. Found by review, not by the corpus: eval's retract
    /// path refuses a `constant` functor and no `FactRef` exists for a load-time fact, so
    /// only a direct `kb.retract` reaches it.
    #[test]
    fn a_retracted_requires_fact_is_dropped_by_the_index_as_it_is_by_the_scan() {
        let mut kb = load_stdlib(Some(SRC));
        let carrier = kb
            .try_resolve_symbol("test.wi1112.Carrier")
            .expect("Carrier");
        let foo = kb.try_resolve_symbol("test.wi1112.Foo").expect("Foo");
        assert!(
            entries(&kb, carrier).iter().any(|(r, _)| *r == foo),
            "premise: Carrier requires Foo before the retraction",
        );

        let requires_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
        let rid = kb
            .rules_by_functor(requires_sym)
            .into_iter()
            .find(|rid| {
                if !kb.is_fact(*rid) {
                    return false;
                }
                let head = kb.rule_head_value(*rid);
                let Some(sr) = crate::kb::op_info::head_field_term(&kb, head, "sort_ref") else {
                    return false;
                };
                let Term::Fn { functor, .. } = kb.get_term(sr) else {
                    return false;
                };
                kb.canonical_sort_sym(*functor) == kb.canonical_sort_sym(carrier)
            })
            .expect("the `requires Foo[T = Int64]` fact");

        // A retractor that does NOT invalidate — the case the fix has to survive. NO
        // REBUILD AFTER IT, and that is the whole experiment: `build_requires_index` reads
        // `rules_by_functor`, which filters retracted, so rebuilding here would refresh the
        // bucket and measure nothing. MEASURED — the first cut of this test did call
        // `fresh_with_index` and passed with the fix backed out. What has to be read is the
        // bucket built during the load, with the rid still in it.
        kb.retract(rid);
        assert!(
            kb.requires_index.is_some(),
            "the load's index is still the live one — nothing has rebuilt or dropped it",
        );
        assert!(
            !entries(&kb, carrier).iter().any(|(r, _)| *r == foo),
            "through the INDEX built BEFORE the retraction: a retracted requires fact must \
             not be served",
        );

        // The arm the index has to agree with, at the same KB state.
        kb.requires_index = None;
        assert!(
            !entries(&kb, carrier).iter().any(|(r, _)| *r == foo),
            "through the SCAN: `rules_by_functor` already filtered it",
        );
    }

    /// THE OTHER DOOR. The PARTIAL load path (`LoadOptions { run_typer: false }`, which
    /// replaced the retired single-file `load::load`) asserts
    /// `SortRequiresInfo` twice over (`load_requires_decl`, then
    /// `resolve_requires_bindings`' retract-and-re-assert) and NEVER reaches
    /// `type_check_sorts`, so nothing downstream of it would correct an index it
    /// inherited. Called on a KB that has already been through `load_all`, that index is
    /// live, and every requirement in the file being loaded is filed under a bucket that
    /// was built before the file existed.
    ///
    /// CONTROL, RE-MEASURED AT THIS DOOR (WI-20260901-Q8NH5). THREE writers leave the index
    /// `None` on the partial path — `load_phase_inner`'s opening `kb.requires_index = None`
    /// and the two pre-typer `invalidate_requires_chain_cache()` calls around
    /// `derive_forwarded_provisions` — and they are REDUNDANT with each other, which they
    /// were not while `load::load` ran none of them. So no single back-out names one of
    /// them: back out the reset alone and this passes (the full workspace too); back out
    /// BOTH invalidations and keep the reset and this still passes, only the memo row below
    /// failing; back out all three and this fails at the `is_none` assertion, and then,
    /// with that assertion removed too, at the requirement itself, which is the shape the
    /// user meets. What this row pins is therefore the RESULT — a partial load leaves no
    /// index a later reader can trust — and not any one line. The comment it used to carry
    /// ("this is the DRIVEN half of the rule; the equivalent reset in `load_phase_inner` is
    /// measured unobservable") split a rule across two doors that no longer exist.
    #[test]
    fn a_single_file_load_does_not_read_a_stale_index() {
        use crate::kb::load::{self, NullResolver};

        let mut kb = load_stdlib(Some(SRC));
        assert!(
            kb.requires_index.is_some(),
            "premise: the full load leaves the index BUILT",
        );

        let src = r#"
namespace test.wi1112b
  import anthill.prelude.{Int64}
  sort Spec
    sort T = ?
  end
  sort Client
    requires Spec[T = Int64]
    entity c(x: Int64)
  end
end
"#;
        let parsed = crate::parse::parse(src).expect("parse fixture");
        // WI-20260901-Q68AK — the PARTIAL path, which is what `load::load` used to be.
        // `build_requires_index` runs inside `type_check_sorts`, so `run_typer: false` is
        // the shape with no rebuild point — the one this pair is about.
        load::load_all_with(
            &mut kb,
            &[&parsed],
            &NullResolver,
            load::LoadOptions {
                run_typer: false,
                ..Default::default()
            },
        )
        .expect("partial load");

        assert!(
            kb.requires_index.is_none(),
            "a partial load asserts into the relation and has no rebuild point, so it must leave \
             the index dropped",
        );
        let client = kb
            .try_resolve_symbol("test.wi1112b.Client")
            .expect("Client");
        let spec = kb.try_resolve_symbol("test.wi1112b.Spec").expect("Spec");
        assert!(
            entries(&kb, client).iter().any(|(r, _)| *r == spec),
            "`Client requires Spec[T = Int64]`, declared through the partial entry \
             point, must be in the chain",
        );
    }

    /// AND THE CLOSING HALF OF THAT PAIR. The partial path also has to invalidate AFTER it
    /// writes, because the derived state it can invalidate is not only the index:
    /// `direct_requires` reads TWO relations (WI-1110), the memoized `requires_tree` is
    /// keyed per sort, and a load onto a KB whose chains are already warm — which is every
    /// load after a `load_all`, since `check_provider_requires` builds a chain for every
    /// provider — would otherwise serve the pre-load memo for a sort whose requirements the
    /// loaded file just changed.
    ///
    /// The file writes the reflect fact DIRECTLY, which is the shape that lets a second
    /// file change a first file's chain at all (a `requires` clause can only be written
    /// inside its own sort's block). That is a legal source-level producer of this
    /// relation, and one of the four enumerated in the ticket.
    ///
    /// `Carrier()` / `Bar()` WITH THE PARENTHESES, and that is not decoration. MEASURED:
    /// spelled bare, the fields convert to `Term::Ref` and `collect_sort_requires` skips
    /// the fact outright (`let Term::Fn { .. } = … else { continue }`) — the fixture then
    /// fails for a reason that has nothing to do with the memo. A hand-written
    /// `fact SortRequiresInfo` with a bare `sort_ref` is invisible to the requires chain;
    /// the loader's own producer never hits it because `make_name_term_from_sym` builds
    /// the application form.
    ///
    /// CONTROL: back out BOTH PRE-TYPER `invalidate_requires_chain_cache()` calls in
    /// `load_phase_inner` — the pair around `derive_forwarded_provisions`; the third one,
    /// at the end of the pipeline, is below the `run_typer` return and never runs here —
    /// and this fails: `requires_tree` answers from the memo warmed before the load.
    /// MEASURED, and not what a first reading predicts: EITHER call alone keeps it green,
    /// because the opening one clears the memo and nothing in this fixture re-warms it
    /// during the walk. So this test drives the PAIR, not a half; the two are kept for the
    /// two windows the pre-typer stretch would otherwise leave open, stated at their site.
    /// (Re-measured at this door under WI-20260901-Q8NH5: the fixture reached the pair
    /// through the retired `load::load` before Q68AK, and reaches it through
    /// `load_phase_inner` now.)
    #[test]
    fn a_single_file_load_drops_the_chain_memo_it_invalidates() {
        use crate::kb::load::{self, NullResolver};
        use crate::kb::typing::requires_tree;

        let mut kb = load_stdlib(Some(SRC));
        let carrier = kb
            .try_resolve_symbol("test.wi1112.Carrier")
            .expect("Carrier");
        let bar = kb.try_resolve_symbol("test.wi1112.Bar").expect("Bar");

        // Warm the memo, as a full load does for every provider.
        let warm = requires_tree(&mut kb, carrier);
        assert!(
            !warm.iter().any(|n| n.entry.required_sort == bar),
            "premise: Carrier does not require Bar before the second file",
        );
        assert!(
            kb.requires_chain_cache_contains(carrier),
            "premise: the chain is MEMOIZED — otherwise a stale read is unreachable and \
             this test measures nothing",
        );

        let src = r#"
namespace test.wi1112c
  import anthill.reflect.{SortRequiresInfo}
  import test.wi1112.{Carrier, Bar}
  fact SortRequiresInfo(sort_ref: Carrier(), spec: Bar())
end
"#;
        let parsed = crate::parse::parse(src).expect("parse fixture");
        // WI-20260901-Q68AK — the PARTIAL path, which is what `load::load` used to be.
        // `build_requires_index` runs inside `type_check_sorts`, so `run_typer: false` is
        // the shape with no rebuild point — the one this pair is about.
        load::load_all_with(
            &mut kb,
            &[&parsed],
            &NullResolver,
            load::LoadOptions {
                run_typer: false,
                ..Default::default()
            },
        )
        .expect("partial load");

        let after = requires_tree(&mut kb, carrier);
        assert!(
            after.iter().any(|n| n.entry.required_sort == bar),
            "the requirement the second file declares must reach the chain — the memo from \
             before the load must not be served",
        );
    }
}

#[cfg(test)]
mod wi866_dict_layout_agreement_tests {
    use super::super::{dict_layout, DictLayout};
    use crate::kb::test_support::load_stdlib_and_stl;
    use crate::kb::{KnowledgeBase, Symbol};

    /// Two sorts with DIFFERENT `requires` chain lengths, so a swapped split is a
    /// different pair of numbers and not a self-cancelling one. `Ord` declares one
    /// (`provides WeakOrd`, WI-1110), `Holder` declares two.
    const SRC: &str = r#"
namespace test.wi866
  import anthill.prelude.{Int64, Bool, Eq, Ord}

  sort Holder
    sort T = ?
    requires Eq[T]
    requires Ord[T]
    entity holder(v: T)
  end
end
"#;

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// THE SYNTHETIC DIVERGENCE the ticket asks for, and the reason it is synthetic:
    /// no program can drive it. Both halves are produced by walking the very chains
    /// `dict_layout` counts, so production and prediction agree by construction and
    /// only an EDIT to one of those four functions can part them — which is exactly
    /// what the always-on check in `dict_sub_goals` exists to catch. So the divergence
    /// is built here by hand, at `divergence_from`, the one function that decides it.
    ///
    /// THE ROW THAT MATTERS IS `swapped`: it has the same ARITY as the prediction, so
    /// the pre-WI-866 `debug_assert_eq!` on `arity()` passes it, as do BOTH of
    /// `expand_dispatching_dict`'s own guards — and every frame slice then reads the
    /// other half's slots. `wrong_total` is the case that assert did cover; it is here
    /// to show this check is a superset, not a replacement.
    ///
    /// BACKED OUT (compare `arity()` instead of the halves): `swapped` fails and
    /// `agrees`/`wrong_total` pass — which is the whole finding.
    #[test]
    fn wi866_a_swapped_split_is_a_divergence() {
        let mut kb = load_stdlib_and_stl(Some(SRC));
        let holder = sym(&kb, "test.wi866.Holder");
        let int64 = sym(&kb, "anthill.prelude.Int64");

        // The prediction for a `Holder` dictionary supplied by `Int64`: `Holder`'s two
        // `requires` then `Int64`'s (none), which is what makes a swap observable.
        let predicted = dict_layout(&mut kb, holder, int64);
        assert_eq!(
            (predicted.spec_len, predicted.provider_len),
            (2, 0),
            "the fixture must give the two halves DIFFERENT lengths, or a swap is not \
             a divergence: {}",
            predicted.describe(&kb),
        );

        let agrees = DictLayout::from_halves(&kb, holder, int64, 2, 0);
        assert!(
            agrees.divergence_from(&kb, &predicted).is_none(),
            "the CONTROL: a producer that built what `dict_layout` predicts diverges \
             from nothing",
        );

        let swapped = DictLayout::from_halves(&kb, holder, int64, 0, 2);
        assert_eq!(
            swapped.arity(),
            predicted.arity(),
            "the swap must be arity-preserving, or it is the case the OLD assert \
             already caught and this test measures nothing new",
        );
        let why = swapped
            .divergence_from(&kb, &predicted)
            .expect("a swapped split is a divergence even at equal arity");
        assert!(
            why.contains("2 for spec") && why.contains("0 for spec"),
            "the message must name BOTH halves of BOTH layouts — a bare `expected 2` \
             cannot say which half is short, which is the whole difficulty \
             `DictLayout` resolves; got: {why}",
        );

        let wrong_total = DictLayout::from_halves(&kb, holder, int64, 1, 0);
        assert!(
            wrong_total.divergence_from(&kb, &predicted).is_some(),
            "this check is a SUPERSET of the arity-only one it replaced",
        );
    }

    /// THE SELF CASE IS ONE LIST IN TWO ENCODINGS, and `from_halves` folds it to the
    /// layout's — without which the always-on check in `dict_sub_goals` would fire on
    /// every self-provision in the stdlib, since the producer hands in `(0, n)` there
    /// (it skips the spec half outright) while `dict_layout` counts `(n, 0)`.
    ///
    /// BACKED OUT (drop the fold from `from_halves`): this row fails and NOTHING ELSE
    /// does — measured, the whole `anthill-core` suite stays green at 4533 of 4534,
    /// with zero of the always-on layout raises. That is not the fold being harmless,
    /// it is the self case never reaching `dict_sub_goals` at all (480_537 reaches
    /// across `wi_tests`, none of them self-provided — a self-provision and a WI-415
    /// parent bundle build their dictionaries elsewhere). The fold is what keeps the
    /// FIRST such dispatch, whenever one arrives, from raising a false divergence
    /// instead of running; no fixture can stand in for it, so this row is what says
    /// the two encodings are one list.
    #[test]
    fn wi866_the_self_case_folds_to_one_list() {
        let mut kb = load_stdlib_and_stl(Some(SRC));
        let holder = sym(&kb, "test.wi866.Holder");

        let predicted = dict_layout(&mut kb, holder, holder);
        assert_eq!(
            (predicted.spec_len, predicted.provider_len),
            (2, 0),
            "`dict_layout`'s self branch counts the ONE list as the spec half",
        );
        // What `dict_sub_goals` hands in for the same pair: no spec half at all.
        let produced = DictLayout::from_halves(&kb, holder, holder, 0, 2);
        assert!(
            produced.divergence_from(&kb, &predicted).is_none(),
            "the producer's `(0, n)` and the layout's `(n, 0)` are ONE list: {}",
            produced.describe(&kb),
        );
        assert_eq!(
            produced.spec_len, 2,
            "and the FOLDED value is the layout's, because `slots_for` indexes by it",
        );
    }
}

/// WI-20260820-CTD6D — THE ROW'S CARRIER SET, driven where the row machinery reads it.
///
/// The ticket asked whether an effect row can reach [`wrap_bare_effect_expr_as_row`] on a
/// carrier other than `Value::Term` / `Value::Node`, and said not to close it by widening
/// the match on a guess. The answer is no, BY CONSTRUCTION — every row-structural position
/// in the occurrence IR is a `TypeChild`, which has exactly those two variants, and the
/// wrapper's doc carries the full census. It is now TOTAL, and these rows keep that honest.
///
/// WHAT EACH ROW MEASURES, PER BACK-OUT. The back-out is restoring the `Option<Value>`
/// return with its `_ => None` arm, and the `.flatten()` / `?` the two callers used to
/// discharge it:
///
///  * [`a_row_shaped_value_on_a_third_carrier_is_refused_loudly`] — FAILS on the back-out
///    (the wrapper answers `None` and nothing panics). It is the ticket's deliverable: a
///    carrier the row IR does not admit is REPORTED, not silently declassified to an atom.
///  * [`a_zero_ary_row_on_the_symbolref_carrier_is_refused_loudly`] — also FAILS on the
///    back-out. It drives the OTHER way in, found by review: WI-436 reads a 0-ary row
///    constructor as a bare `ViewHead::Ref`, so a `Value::SymbolRef(empty_row)` is
///    row-shaped without ever having been in the row IR. Its verdict rests on a PRODUCER
///    census (`SymbolRef` has three minters, none of them an `EffectExpression` symbol)
///    rather than on the structural argument, which is why it gets its own row.
///  * [`the_classifier_admits_a_third_carrier_the_wrapper_must_refuse`] — passes EITHER
///    WAY, by design. It pins the ticket's premise rather than its fix: classification is
///    by FUNCTOR HEAD, which every carrier answers, so the wrapper really is the only thing
///    between a third-carrier row and the flatten. Without it the refusal row above could
///    be dismissed as unreachable by a different route.
///  * [`a_term_carried_bare_row_wraps_and_stays_ground`] and
///    [`a_node_carried_bare_row_wraps_and_stays_an_occurrence`] — pass either way, by
///    design. They drive the two LIVE arms and assert the wrap is carrier-PRESERVING,
///    which is the property the totality claim rests on. The `Node` one is not redundant
///    with the corpus: the probe that measured this ticket saw 97 799 values reach this
///    function across the whole workspace suite and EVERY one was `Value::Term`, so before
///    this row the `Value::Node` arm was executed by no test in the repo.
///
/// One guard cannot be driven from a test at all, and is stated here instead: the wrapper's
/// third arm is an or-pattern with no `_`, so a NEW `Value` variant is a COMPILE error at
/// that site rather than a silent inheritance of the old fallback.
#[cfg(test)]
mod ctd6d_row_carrier_tests {
    use super::super::{type_head, value_is_bare_row_expr, wrap_bare_effect_expr_as_row, TypeHead};
    use crate::eval::value::Value;
    use crate::kb::load::register_prelude;
    use crate::kb::node_occurrence::TypeChild;
    use crate::kb::KnowledgeBase;
    use crate::span::{SourceId, SourceSpan};
    use std::rc::Rc;

    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        kb
    }

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 1)
    }

    /// `merge(present(L), empty_row)` hash-consed — the bare shape a BOUND row tail walks
    /// to at a call site, and 24 of the 97 799 values the probe saw reach the wrapper.
    fn term_bare_row(kb: &mut KnowledgeBase) -> Value {
        let label_sym = kb.intern("CtdLabel");
        let label = kb.make_sort_ref(label_sym);
        let present = kb.make_effect_expression_present(label);
        let empty = kb.make_effect_expression_empty_row();
        Value::term(kb.make_effect_expression_merge(present, empty))
    }

    /// The same row as an OCCURRENCE — the carrier a denoted-bearing row (`{Modify[c] | ρ}`)
    /// takes, built through the `make_*_occ` family exactly as `fold_effect_row_occ` does.
    fn node_bare_row(kb: &mut KnowledgeBase) -> Value {
        let label_sym = kb.intern("CtdLabel");
        let label = kb.make_sort_ref(label_sym);
        let present = kb.make_present_occ(TypeChild::Ground(label), span(), None);
        let empty = kb.make_empty_row_occ(span(), None);
        Value::Node(kb.make_merge_occ(
            TypeChild::Node(present),
            TypeChild::Node(empty),
            span(),
            None,
        ))
    }

    /// The SAME `merge(left, right)` on a THIRD carrier — an ordinary `Value::Entity` over
    /// the prelude's `EffectExpression.merge` functor. Nothing in the kernel mints this
    /// (that is the ticket's verdict), so the test mints it by hand: no producer is being
    /// asserted to exist, only that the wrapper answers loudly if one ever does.
    fn entity_bare_row(kb: &mut KnowledgeBase) -> Value {
        let merge = kb.resolve_symbol("anthill.prelude.EffectExpression.merge");
        let left_key = kb.intern("left");
        let right_key = kb.intern("right");
        let label_sym = kb.intern("CtdLabel");
        let label = kb.make_sort_ref(label_sym);
        let present = Value::term(kb.make_effect_expression_present(label));
        let empty = Value::term(kb.make_effect_expression_empty_row());
        Value::Entity {
            functor: merge,
            pos: Rc::from(Vec::<Value>::new()),
            named: Rc::from(vec![(left_key, present), (right_key, empty)]),
        }
    }

    /// `empty_row` on a `Value::SymbolRef` — the OTHER way a value can be row-shaped, and
    /// the one the IR argument does not reach. WI-436 reads a 0-ary row constructor as a
    /// bare `ViewHead::Ref`, and `Value::SymbolRef` is contracted to be indistinguishable
    /// from its `Term::Ref` twin to every structural consumer, so it answers `functor_sym`
    /// exactly as the hash-consed spelling does. Found by review of this ticket.
    fn symbolref_bare_row(kb: &mut KnowledgeBase) -> Value {
        Value::SymbolRef(kb.resolve_symbol("anthill.prelude.EffectExpression.empty_row"))
    }

    /// THE PREMISE, not the fix — passes with the change backed out. `value_is_bare_row_expr`
    /// reads only `head(kb).functor_sym()`, and a `Value::Entity` answers that as readily as
    /// a term does, so the Entity-carried `merge(…)` IS classified as a row and IS handed to
    /// the wrapper. That is what made the old `_ => None` a silent declassification rather
    /// than an unreachable arm.
    #[test]
    fn the_classifier_admits_a_third_carrier_the_wrapper_must_refuse() {
        let mut kb = kb_with_prelude();
        let entity = entity_bare_row(&mut kb);
        assert!(
            value_is_bare_row_expr(&kb, &entity),
            "an Entity-carried `merge(…)` classifies as a bare row by functor head",
        );
        // And the two live carriers classify the same way, so the classifier is not what
        // separates them — only the wrapper is.
        let term = term_bare_row(&mut kb);
        let node = node_bare_row(&mut kb);
        assert!(value_is_bare_row_expr(&kb, &term), "term row classifies");
        assert!(value_is_bare_row_expr(&kb, &node), "node row classifies");
    }

    /// THE SECOND ESCAPE, driven — fails on the back-out for the same reason as the Entity
    /// row. `empty_row` is by volume the most common row shape reaching the wrapper (27 621
    /// of 97 799 probed calls), and on the `Value::SymbolRef` carrier it classifies as a row
    /// through WI-436's bare-`Ref` canonicalization while the IR argument never sees it. The
    /// verdict is the same — no producer of `SymbolRef` mints an `EffectExpression` symbol —
    /// but it is a PRODUCER census, not a structural one, so it is pinned here.
    #[test]
    #[should_panic(expected = "THIRD carrier")]
    fn a_zero_ary_row_on_the_symbolref_carrier_is_refused_loudly() {
        let mut kb = kb_with_prelude();
        let sref = symbolref_bare_row(&mut kb);
        assert!(
            value_is_bare_row_expr(&kb, &sref),
            "a `SymbolRef(empty_row)` classifies as a bare row via the WI-436 `Ref` head",
        );
        let _ = wrap_bare_effect_expr_as_row(&mut kb, &sref);
    }

    /// THE DELIVERABLE — fails on the back-out. A row-shaped value on a carrier the row IR
    /// cannot mint is a kernel invariant violation, and it is now reported at the site with
    /// the offending value named, instead of being answered `None` and carried whole into
    /// the enclosing row as one opaque atom.
    #[test]
    #[should_panic(expected = "THIRD carrier")]
    fn a_row_shaped_value_on_a_third_carrier_is_refused_loudly() {
        let mut kb = kb_with_prelude();
        let entity = entity_bare_row(&mut kb);
        let _ = wrap_bare_effect_expr_as_row(&mut kb, &entity);
    }

    /// A LIVE arm — passes either way. A ground row wraps to a ground `effects_rows(…)`.
    #[test]
    fn a_term_carried_bare_row_wraps_and_stays_ground() {
        let mut kb = kb_with_prelude();
        let row = term_bare_row(&mut kb);
        let wrapped = wrap_bare_effect_expr_as_row(&mut kb, &row);
        assert!(
            matches!(wrapped, Value::Term { .. }),
            "a hash-consed row stays hash-consed, got {wrapped:?}",
        );
        assert!(
            matches!(type_head(&kb, &wrapped), TypeHead::EffectsRows),
            "and it is the canonical `effects_rows(…)` wrapper the row machinery consumes",
        );
    }

    /// THE OTHER LIVE ARM — passes either way, and is the one NO other test in the repo
    /// reaches (see this module's doc: 0 of 97 799 corpus values took it). An occurrence row
    /// wraps to an OCCURRENCE `effects_rows(…)`; re-grounding it here would undo the WI-341
    /// occurrence preservation both callers exist to respect.
    #[test]
    fn a_node_carried_bare_row_wraps_and_stays_an_occurrence() {
        let mut kb = kb_with_prelude();
        let row = node_bare_row(&mut kb);
        let wrapped = wrap_bare_effect_expr_as_row(&mut kb, &row);
        assert!(
            matches!(wrapped, Value::Node(_)),
            "an occurrence row stays an occurrence — never re-grounded, got {wrapped:?}",
        );
        assert!(
            matches!(type_head(&kb, &wrapped), TypeHead::EffectsRows),
            "and reads as `effects_rows(…)` through the view, exactly as the term twin does",
        );
    }
}
