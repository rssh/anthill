//! WI-20260820-8RJK8 — a GUARDED equation fires.
//!
//! `lhs <=> rhs :- guard` was accepted, indexed when tagged, and read by no firing
//! site: every one of them gated on `KnowledgeBase::is_equation`, whose first clause
//! is `body_nodes.is_empty()`. A guard is now what proposal 043 §4.6 and
//! `docs/design/constrained-term-substrate.md` always said it was — the THIRD tier of
//! firing, evaluated POST-MATCH, after the discrimination tree has narrowed on the LHS
//! and the type-side guards have had their say.
//!
//! THREE DECISIONS ARE PINNED HERE, each with the row that measures it.
//!
//! 1. `[simp]` IS STILL THE ENABLEMENT (WI-881/884/888). A guard does not enable a
//!    rewrite; the tag does. `guard_decides_a_tagged_equation` runs the full
//!    (connective × tag) matrix and the untagged rows do not fire — the same verdict
//!    an untagged BODYLESS equation gets, so the tag means one thing.
//! 2. EVERY FIRING SITE ANSWERS ALIKE, and there are THREE of them — the resolver
//!    (`fire_simp_equation`), the typer's applicative pass (`simp_rewrite::try_fire`)
//!    and the typer's DOT-rule pass (`typing::try_fire_dot_rule`). All three call ONE
//!    guard evaluator, so a tagged rule means the same at a resolution goal, in an
//!    operation body, and at a method call
//!    (`the_typer_fires_a_guarded_equation_in_an_operation_body`; the dot site has no
//!    row, because no guarded dot rule is written anywhere today — see the note at
//!    its call, which says so rather than letting a green suite imply coverage).
//! 3. AN UNDETERMINED GUARD SUSPENDS, IT DOES NOT DECIDE (WI-067). The guard search
//!    is `definite_only`, so a floundered `not(…)` yields nothing and the redex is
//!    left standing (`an_undetermined_guard_suspends_rather_than_naf_deciding`); and a
//!    guard over an OPEN-WORLD operand — a compile-time `var_ref` a scalar builtin
//!    would read as a ground constant — declines before the search runs at all
//!    (`a_guard_over_symbolic_parameters_declines_at_the_typer`).
//! 4. WHAT THE GUARD BINDS IS PART OF THE ANSWER. A variable bound only by the guard
//!    and used in the right-hand side carries the guard's witness into the rewrite
//!    (`a_variable_the_guard_binds_reaches_the_right_hand_side`) — before the fix it
//!    carried an unbound variable, which is a wrong value rather than a missing one.
//!
//! WHAT FAILS WHEN EACH PIECE IS BACKED OUT — RUN, not predicted. Each row below is the
//! measured result of mutating that one site and re-running this file (9 tests).
//!
//! | back out | red | green |
//! |---|---|---|
//! | `has_equational_head` → `is_equation` in `is_directional_equation` | 7: everything except the two named opposite | `control_an_unguarded_…`, `the_typer_fires_…` |
//! | the same in `simp_rewrite::is_simp_equation` | 1: `the_typer_fires_a_guarded_equation_in_an_operation_body` | the other 8 |
//! | the `guard_holds` call in `fire_simp_equation` | 5: `guard_decides_…`, `a_guard_reads_…`, `an_undetermined_…`, `a_value_guard_and_a_requires_guard_compose`, `stdlib_indexed_seq_…` | `control_…`, `the_typer_…`, `an_unfold_…`, the tag census |
//! | `definite_only: true` in `guard_holds` | 1: `an_undetermined_guard_suspends_rather_than_naf_deciding` | the other 8 — including its OWN two control rows, which is the point |
//! | the `[simp]` tag on `indexed_seq.anthill`'s `nth_oob_lo` | 2: `stdlib_indexed_seq_…` and the tag census | the other 7 |
//! | `guard_verdict`'s `HoldsWith` arm (drop the witness) | 1: `a_variable_the_guard_binds_reaches_the_right_hand_side` | the other 10 |
//! | `guard_verdict`'s open-world test | 1: `a_guard_over_symbolic_parameters_declines_at_the_typer` | the other 10 |
//!
//! TWO AXES, TWO CALL SITES: the first two rows show that `is_directional_equation` and
//! `is_simp_equation` are separate widenings with separate coverage — backing out either
//! one leaves the other's row green, so neither is credited to the other's work.
//!
//! `control_an_unguarded_equation_fires_either_way` is in its OWN fixture (no guard
//! anywhere in it) and survives every back-out above: it is the row that says the
//! harness — load, `simplify`, the value assertion — was working all along, and it can
//! therefore credit nothing to this ticket.
//!
//! A SIXTH AXIS IS OWNED ELSEWHERE, and named here so it is not looked for in this file:
//! the LOADER had to install a guarded equation's written RHS occurrence too (it gated
//! on `body_nodes.is_empty()`, and `parse_equation_rhs` further narrowed to `<=>`), or a
//! guarded `=` law fires off the term-derived RHS and loses the author's spans. The
//! population census `wi_fcz3n_simp_rhs_occurrence_test::
//! every_fireable_source_equation_keeps_its_rhs_occurrence` is the row: backed out, it
//! names the three stdlib laws this ticket tagged, which is how the gap was found rather
//! than reasoned about.

use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

// ── helpers ─────────────────────────────────────────────────────────────

fn sym(kb: &KnowledgeBase, qn: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("resolve {qn}"))
}

fn int(kb: &mut KnowledgeBase, n: i64) -> TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

fn call(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let f = sym(kb, qn);
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// `qn(a, b, …)` over integer literals — the args are allocated BEFORE the call so the
/// `&mut kb` borrows do not overlap.
fn call_ints(kb: &mut KnowledgeBase, qn: &str, ns: &[i64]) -> TermId {
    let args: Vec<TermId> = ns.iter().map(|&n| int(kb, n)).collect();
    call(kb, qn, &args)
}

/// The outer functor of a term, as a short name — what an assertion about "did it
/// rewrite" needs to read without caring which `TermId` the store handed out.
fn head_name(kb: &KnowledgeBase, t: TermId) -> String {
    match kb.get_term(t) {
        Term::Fn { functor, .. } => kb.qualified_name_of(*functor).to_string(),
        Term::Ref(s) | Term::Ident(s) => kb.qualified_name_of(*s).to_string(),
        other => format!("{other:?}"),
    }
}

// ── 1. the guard decides, and only on a TAGGED equation ─────────────────

fn guarded_src(conn: &str, tag: &str) -> String {
    format!(
        r#"
namespace test.wi8rjk8
  import anthill.prelude.{{Int64}}
  import anthill.prelude.Ord.{{gt}}

  sort Lib
    operation pick(x: Int64, y: Int64) -> Int64
    rule pk: pick(?a, ?b) {conn} ?a :- gt(?a, ?b) {tag}
  end
end
"#
    )
}

/// The ticket's own fixture, driven to a VALUE across the full (connective × tag)
/// matrix and both guard verdicts.
///
/// `gt(?a, ?b)` is decided at the redex by the ordinary builtin, so `pick(9, 2)` has a
/// TRUE guard and `pick(2, 9)` a FALSE one — one rule, two answers, which is what
/// makes this a guard test and not a firing test.
///
/// THE TAG IS THE ENABLEMENT and the untagged rows are how that is measured: the same
/// rule, the same true guard, no `[simp]` — and the redex stands. Both connectives are
/// run because the two live in different functor buckets (`PartialEq.eq` vs
/// `kernel.unify`) and a selection widened in only one of them would pass half of this.
#[test]
fn guard_decides_a_tagged_equation() {
    for conn in ["<=>", "="] {
        for tag in ["[simp]", ""] {
            let mut kb = crate::common::load_kb_with(&guarded_src(conn, tag));
            let fires = tag == "[simp]";

            let t = call_ints(&mut kb, "test.wi8rjk8.Lib.pick", &[9, 2]);
            let out = kb.simplify(t);
            if fires {
                assert_eq!(
                    kb.get_term(out),
                    &Term::Const(Literal::Int(9)),
                    "`pick(?a, ?b) {conn} ?a :- gt(?a, ?b) [simp]` with the guard TRUE at \
                     the redex must fire to the VALUE 9; got {:?}",
                    kb.get_term(out),
                );
            } else {
                assert_eq!(
                    out, t,
                    "an UNTAGGED guarded equation is inert — `[simp]` is the enablement \
                     (WI-881), and a guard does not substitute for it",
                );
            }

            // Guard FALSE: `gt(2, 9)` is refuted, so the SAME rule leaves the redex.
            let t2 = call_ints(&mut kb, "test.wi8rjk8.Lib.pick", &[2, 9]);
            assert_eq!(
                kb.simplify(t2),
                t2,
                "the guard is REFUTED at `pick(2, 9)` (conn={conn}, tag={tag:?}), so the \
                 rewrite must not fire — otherwise the `:- guard` is decoration",
            );
        }
    }
}

/// THE CONTROL, in its own fixture with no guard anywhere in it: the same shape of
/// rule, tagged, fires for BOTH argument orders. If this goes red the harness is
/// broken (loading, `simplify`, the value read) and nothing above measures a guard.
#[test]
fn control_an_unguarded_equation_fires_either_way() {
    const SRC: &str = r#"
namespace test.wi8rjk8ctl
  import anthill.prelude.{Int64}

  sort Lib
    operation pick(x: Int64, y: Int64) -> Int64
    rule pk: pick(?a, ?b) <=> ?a [simp]
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    for (a, b) in [(9, 2), (2, 9)] {
        let t = call_ints(&mut kb, "test.wi8rjk8ctl.Lib.pick", &[a, b]);
        let out = kb.simplify(t);
        assert_eq!(
            kb.get_term(out),
            &Term::Const(Literal::Int(a)),
            "the UNGUARDED control must fire for both orders: pick({a}, {b}) → {a}",
        );
    }
}

/// The guard reads values the head match bound THROUGH STRUCTURE, not just top-level
/// argument slots — `?a` here is under a constructor. This is the row that says the
/// guard is opened against the rule's own frame (`open_equation`'s `fresh`) and
/// σ-applied with the match, rather than proved against the stored pattern.
#[test]
fn a_guard_reads_values_bound_through_the_matched_structure() {
    const SRC: &str = r#"
namespace test.wi8rjk8deep
  import anthill.prelude.{Int64}
  import anthill.prelude.Ord.{gt}

  sort Boxed
    entity box(v: Int64)
  end

  sort Lib
    operation peel(b: Boxed) -> Int64
    rule pl: peel(box(v: ?a)) <=> ?a :- gt(?a, 3) [simp]
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    for (v, fires) in [(5i64, true), (1i64, false)] {
        let boxed = {
            let f = sym(&kb, "test.wi8rjk8deep.Boxed.box");
            let vt = int(&mut kb, v);
            let key = kb.intern("v");
            kb.alloc(Term::Fn {
                functor: f,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(key, vt)]),
            })
        };
        let t = call(&mut kb, "test.wi8rjk8deep.Lib.peel", &[boxed]);
        let out = kb.simplify(t);
        if fires {
            assert_eq!(
                kb.get_term(out),
                &Term::Const(Literal::Int(v)),
                "gt({v}, 3) holds → peel(box(v: {v})) → {v}",
            );
        } else {
            assert_eq!(out, t, "gt({v}, 3) is refuted → the redex stands");
        }
    }
}

/// `[unfold]` is a directional rewrite too (`is_directional_equation` is
/// `[simp] OR [unfold]`), so a guarded `[unfold]` equation fires in the RESOLVER.
/// It does NOT fire in the typer, which selects `[simp]` alone — that asymmetry is
/// older than this ticket and untouched by it.
#[test]
fn an_unfold_tagged_guarded_equation_fires() {
    let mut kb = crate::common::load_kb_with(&guarded_src("<=>", "[unfold]"));
    let t = call_ints(&mut kb, "test.wi8rjk8.Lib.pick", &[9, 2]);
    let out = kb.simplify(t);
    assert_eq!(
        kb.get_term(out),
        &Term::Const(Literal::Int(9)),
        "a guarded `[unfold]` equation fires in the resolver",
    );
}

// ── 2. the typer fires it too ───────────────────────────────────────────

/// The SECOND firing site. `[simp]` is one enablement, so a tagged guarded equation
/// must mean the same thing in an operation BODY as at a resolution goal — this is
/// the site where a `[simp]` equation gives a body-less operation a meaning (§5.3),
/// and leaving it out would have made a guarded law fire for a goal and not for the
/// call that spells it.
///
/// `caller`'s body is `pick(9, 2)`; the typer's simp pass rewrites it to `9` before
/// dispatch, so the stored body's head is a constant rather than a `pick` apply.
/// The guard-FALSE sibling `caller_no` keeps its call.
#[test]
fn the_typer_fires_a_guarded_equation_in_an_operation_body() {
    const SRC: &str = r#"
namespace test.wi8rjk8typer
  import anthill.prelude.{Int64}
  import anthill.prelude.Ord.{gt}

  sort Lib
    operation pick(x: Int64, y: Int64) -> Int64
    rule pk: pick(?a, ?b) <=> ?a :- gt(?a, ?b) [simp]

    operation caller() -> Int64 = pick(9, 2)
    operation caller_no() -> Int64 = pick(2, 9)
  end
end
"#;
    let kb = crate::common::load_kb_with(SRC);
    let yes = sym(&kb, "test.wi8rjk8typer.Lib.caller");
    let body = kb.op_body_node(yes).expect("caller has a body node");
    assert!(
        matches!(body.as_expr(), Some(Expr::Const(Literal::Int(9)))),
        "the typer must rewrite the guard-TRUE call `pick(9, 2)` in the body to the \
         VALUE 9; the stored body is {:?}",
        body.as_expr(),
    );
    let no = sym(&kb, "test.wi8rjk8typer.Lib.caller_no");
    let body_no = kb.op_body_node(no).expect("caller_no has a body node");
    assert_eq!(
        crate::common::head_short(&kb, &body_no),
        "pick",
        "the guard-FALSE call must keep its `pick` apply — the typer's guard is the \
         same three-valued decision the resolver's is",
    );
}

// ── 3. an UNDETERMINED guard suspends ───────────────────────────────────

/// THE SOUNDNESS ROW (WI-067) — the reason the guard search is `definite_only`.
///
/// `not(p_flounder(?a))` is the shape that laundered an undecidable goal into a
/// success: `p_flounder`'s body is an undecidable `eq(?b, ?c)`, so the inner search
/// FLOUNDERS, and ordinary negation-as-failure over a floundered goal residualizes —
/// which a caller that reads only `is_empty()` reads as "the guard holds". It must
/// not fire.
///
/// THE TWO CONTROL ROWS SHARE THE FIXTURE DELIBERATELY, because what they control for
/// is that the NEGATION is not what blocks the suspend row:
///   * `ctl(999, 2)` — `p_def(999)` has no fact, so the inner search REFUTES
///     definitely, `not(…)` succeeds definitely, and the rewrite fires.
///   * `ctl(1, 2)` — `p_def(1)` holds, `not(…)` fails, and it does not.
/// So the same negated guard fires, does not fire, and suspends, over one program.
///
/// BACK OUT `definite_only: true` in `guard_holds` and the FIRST assertion below goes
/// red while both control rows stay green — that is the whole point of the row.
#[test]
fn an_undetermined_guard_suspends_rather_than_naf_deciding() {
    const SRC: &str = r#"
namespace test.wi8rjk8naf
  import anthill.prelude.{Int64}
  import anthill.prelude.PartialEq.{eq}

  sort Thing
    entity thing(id: Int64)
  end
  fact thing(id: 1)

  rule p_def(?x) :- thing(id: ?x)
  rule p_flounder(?x) :- eq(?b, ?c)

  sort Lib
    operation susp(x: Int64, y: Int64) -> Int64
    operation ctl(x: Int64, y: Int64) -> Int64
    rule s: susp(?a, ?b) <=> ?a :- not(p_flounder(?a)) [simp]
    rule c: ctl(?a, ?b) <=> ?a :- not(p_def(?a)) [simp]
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);

    let t = call_ints(&mut kb, "test.wi8rjk8naf.Lib.susp", &[9, 2]);
    assert_eq!(
        kb.simplify(t),
        t,
        "an UNDETERMINED guard must SUSPEND — `not(p_flounder(9))` is undecided, not \
         true, and firing on it is the WI-067 hazard this row exists for",
    );

    let fires = call_ints(&mut kb, "test.wi8rjk8naf.Lib.ctl", &[999, 2]);
    let out = kb.simplify(fires);
    assert_eq!(
        kb.get_term(out),
        &Term::Const(Literal::Int(999)),
        "control: `not(p_def(999))` is DEFINITELY true (no such fact), so a negated \
         guard is not itself what blocks the suspend row",
    );

    let refuted = call_ints(&mut kb, "test.wi8rjk8naf.Lib.ctl", &[1, 2]);
    assert_eq!(
        kb.simplify(refuted),
        refuted,
        "control: `not(p_def(1))` is definitely FALSE, so the rewrite does not fire",
    );
}

// ── 4. a STDLIB guarded law, driven to a value ──────────────────────────

/// `indexed_seq.anthill`'s `nth_oob_lo: nth(?_, ?i) = none :- lt(?i, 0)` — one of the
/// fifteen guarded equations that were dead in the stdlib — tagged `[simp]` by this
/// ticket and driven END TO END: the spec-op term `IndexedSeq.nth(nil(), -1)`
/// rewrites to `none`.
///
/// "It loads" is not the evidence and neither is "the tag is present": this asserts
/// the VALUE the law computes. The guard `lt(-1, 0)` is discharged by the ordinary
/// `PartialOrd` builtin, which is why THIS law is the one driven — `nth_oob_hi`'s
/// `gte(?i, length(?xs))` needs `IndexedSeq.length` to run on a bare spec-op term,
/// which is WI-567's wall and is asserted as UNDISCHARGED below rather than assumed
/// either way.
///
/// `IndexedSeq` declares no `requires`, so `equation_is_requires_guarded` is false for
/// it and the resolver fires without needing a carrier that provides the spec — unlike
/// `Map`'s law, whose sort-level `requires Eq[T = K]` keeps it to real providers.
#[test]
fn stdlib_indexed_seq_out_of_bounds_law_fires_to_a_value() {
    let mut kb = crate::common::load_stdlib_kb();
    let nil = call(&mut kb, "anthill.prelude.List.nil", &[]);

    let neg = int(&mut kb, -1);
    let oob = call(&mut kb, "anthill.prelude.IndexedSeq.nth", &[nil, neg]);
    let out = kb.simplify(oob);
    assert_eq!(
        head_name(&kb, out),
        "anthill.prelude.Option.none",
        "the stdlib `nth_oob_lo` law must fire at a NEGATIVE index: \
         IndexedSeq.nth(nil, -1) → none; got {:?}",
        kb.get_term(out),
    );

    // The guard direction, on the same law: index 0 refutes `lt(0, 0)`.
    let zero = int(&mut kb, 0);
    let in_range = call(&mut kb, "anthill.prelude.IndexedSeq.nth", &[nil, zero]);
    assert_eq!(
        kb.simplify(in_range),
        in_range,
        "`lt(0, 0)` is refuted, so `nth_oob_lo` must not fire — and `nth_oob_hi`'s \
         `gte(0, length(nil))` is UNDISCHARGED on a bare spec-op term (WI-567), so \
         nothing else fires here either",
    );
}

/// `map.anthill`'s `get(put(?m, ?k2, ?v), ?k) = get(?m, ?k) :- neq(?k, ?k2)` is the law
/// whose own file named this ticket as the reason it stayed untagged, and it is now
/// `[simp]`. It composes TWO guards: the value guard this ticket added, and the
/// sort-level `requires Eq[T = K]` that `equation_is_requires_guarded` keys on — so it
/// fires only over a carrier that provides `Map`.
///
/// WHAT IS DRIVEN HERE IS THE COMPOSITION, NOT THE STDLIB RULE, and the distinction is
/// stated rather than blurred. The corpus contains NO `Map` provider (`grep 'provides
/// Map\['` over stdlib, examples and tests: zero), and building one means backing
/// `eq` — which `map.anthill` says outright has no backing but a host bridge (WI-650) —
/// so the real law has no redex to fire on anywhere. `Bag` below is `wi596`'s
/// self-representing container spec with `Map`'s shape: `requires Eq[T]`, a concrete
/// carrier that provides it, and the same `get(put(…))` reducing law under the same
/// `neq` guard. It measures that a value guard and a `requires` guard hold at once.
///
/// `stdlib_map_get_law_is_simp_tagged` pins the tag itself; the end-to-end drive of an
/// actual stdlib guarded law is `stdlib_indexed_seq_out_of_bounds_law_fires_to_a_value`,
/// whose sort declares no `requires` and so needs no provider.
#[test]
fn a_value_guard_and_a_requires_guard_compose() {
    const SRC: &str = r#"
namespace test.wi8rjk8req
  import anthill.prelude.{Int64, Option, Eq}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.PartialEq.{neq}

  sort Bag
    sort K = ?
    requires Eq[T = K]
    operation {
      put(b: Bag, key: K) -> Bag
      get(b: Bag, key: K) -> Option[K]
    }
    -- ONE law, and guarded: `Map`'s unguarded `hit` sibling is deliberately absent, so
    -- that the guard-FALSE row below has nothing else to fire and measures THIS rule.
    rule miss: get(put(?b, ?k2), ?k) <=> get(?b, ?k) :- neq(?k, ?k2) [simp]
  end

  sort Plain
    entity plain
  end

  sort IntBag
    entity ibag
    provides Bag[K = Int64]
    operation put(b: IntBag, key: Int64) -> IntBag = b
    operation get(b: IntBag, key: Int64) -> Option[Int64] = none
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    let ibag = call(&mut kb, "test.wi8rjk8req.IntBag.ibag", &[]);
    let two = int(&mut kb, 2);
    let one = int(&mut kb, 1);
    // get(put(ibag, 2), 1): the keys differ, so `miss` strips the `put` …
    let put2 = call(&mut kb, "test.wi8rjk8req.Bag.put", &[ibag, two]);
    let g = call(&mut kb, "test.wi8rjk8req.Bag.get", &[put2, one]);
    let out = kb.simplify(g);
    assert_eq!(
        head_name(&kb, out),
        "test.wi8rjk8req.Bag.get",
        "`miss` must fire over a carrier that provides Bag AND with `neq(1, 2)` proved, \
         leaving `get(ibag, 1)`; got {:?}",
        kb.get_term(out),
    );
    match kb.get_term(out) {
        Term::Fn { pos_args, .. } => assert_eq!(
            pos_args[0], ibag,
            "the surviving `get` must be over the STRIPPED bag, which is what makes this \
             a rewrite and not a no-op",
        ),
        other => panic!("expected a `get` apply, got {other:?}"),
    }
    // … and the SAME key does not: `neq(2, 2)` is refuted, so the redex stands even
    // though the `requires` guard holds. Both guards must pass, not either.
    let g_same = call(&mut kb, "test.wi8rjk8req.Bag.get", &[put2, two]);
    assert_eq!(
        kb.simplify(g_same),
        g_same,
        "with the keys EQUAL the value guard is refuted, so `miss` must not strip the \
         `put` — the `requires` guard holding is not enough",
    );

    // And the value guard holding is not enough either: over a carrier that does NOT
    // provide `Bag`, `equation_is_requires_guarded` keeps the law dormant.
    let plain = call(&mut kb, "test.wi8rjk8req.Plain.plain", &[]);
    let put_plain = call(&mut kb, "test.wi8rjk8req.Bag.put", &[plain, two]);
    let g_plain = call(&mut kb, "test.wi8rjk8req.Bag.get", &[put_plain, one]);
    assert_eq!(
        kb.simplify(g_plain),
        g_plain,
        "`neq(1, 2)` holds, but `Plain` does not provide `Bag`, so the sort-level \
         `requires Eq[T = K]` guard declines — the composition is a conjunction",
    );
}

/// THE STDLIB LAWS THIS TICKET WOKE, asked through the firing site's OWN predicate
/// (`is_directional_equation`) rather than through a restatement of its two conjuncts —
/// so this cannot claim a law "will fire" on a rule the rewriter would skip.
///
/// It is the SECOND half of a pair, never the whole claim: `nth_oob_lo` is driven to a
/// value in `stdlib_indexed_seq_out_of_bounds_law_fires_to_a_value`, and `Map.get`'s
/// composition with the `requires` guard in `a_value_guard_and_a_requires_guard_compose`.
/// What this adds is the two the drives cannot reach — `nth_oob_hi`, whose guard needs
/// `length` to run (WI-567), and `Map.get`, which has no provider in the corpus to fire
/// over — plus the NEGATIVE rows, which are the point: the laws that stay untagged are
/// asserted untagged, so "wake everything" would go red here and not merely unmeasured.
#[test]
fn the_stdlib_guarded_laws_this_ticket_woke_are_selected_and_the_rest_are_not() {
    let kb = crate::common::load_stdlib_kb();

    for qn in [
        "anthill.prelude.IndexedSeq.nth_oob_lo",
        "anthill.prelude.IndexedSeq.nth_oob_hi",
    ] {
        let rid = kb
            .rule_id_by_qn(qn)
            .unwrap_or_else(|| panic!("{qn} loaded"));
        assert!(
            kb.is_directional_equation(rid),
            "{qn} is a REDUCING guarded law (its RHS is a constant) and must be selected \
             by the firing site's own predicate",
        );
    }
    // `euclid_div` is the labelled member of the untagged family — a LAW, whose LHS is
    // the larger term. Tagging it would orient a non-reduction.
    let euclid = kb
        .rule_id_by_qn("anthill.prelude.EuclideanDomain.euclid_div")
        .expect("euclid_div loaded");
    assert!(
        !kb.is_directional_equation(euclid),
        "`euclid_div` must stay a law: a guard makes an equation CONDITIONAL, the tag \
         makes it a rewrite, and this one does not reduce",
    );

    // The unlabelled ones, found by their LHS functor: `Map.get`'s guarded law is tagged
    // (WI-596's siblings plus this ticket's), `Field.div`'s is not.
    assert_eq!(
        guarded_equation_verdicts(&kb, "anthill.prelude.Map.get"),
        vec![true],
        "the one GUARDED `Map.get` law must be selected — its own file named this ticket \
         as the reason it was untagged",
    );
    assert_eq!(
        guarded_equation_verdicts(&kb, "anthill.prelude.Divisible.div"),
        vec![false],
        "`Field`'s `div(?a, ?b) = mul(?a, recip(?b)) :- neq(?b, 0)` (the `div` here is \
         `Divisible.div`, the one spec that declares it) must NOT be selected: oriented \
         it rewrites every division in the program into a reciprocal multiply",
    );
}

/// `is_directional_equation` for every GUARDED equation whose LHS functor is `op_qn`, in
/// rule order. The census shape `wi596_container_guard_test::simp_law_present` uses,
/// narrowed to the bodied ones and returning the firing verdict rather than a tag read.
fn guarded_equation_verdicts(kb: &KnowledgeBase, op_qn: &str) -> Vec<bool> {
    let op = sym(kb, op_qn);
    let mut out = Vec::new();
    for rid in kb.live_rule_ids_iter() {
        if !kb.has_equational_head(rid) || kb.rule_body_nodes(rid).is_empty() {
            continue;
        }
        let Some(head) = kb.fact_head_term(rid) else {
            continue;
        };
        let lhs = match kb.get_term(head) {
            Term::Fn { pos_args, .. } if pos_args.len() == 2 => pos_args[0],
            _ => continue,
        };
        let lhs_functor = match kb.get_term(lhs) {
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        if lhs_functor == op {
            out.push(kb.is_directional_equation(rid));
        }
    }
    out
}

// ── 5. what the guard BINDS, and where it must not decide ───────────────
//
// All three rows below come from the `/code-review` pass on this ticket. Each names a
// site the widening reached that the first cut did not guard, and each was DRIVEN both
// ways before the fix went in — none is a code-read.

/// A variable bound ONLY BY THE GUARD and used in the RHS is the standard conditional-
/// rewrite idiom (`stream.anthill` writes six of them), and the first cut of this ticket
/// threw the witness away.
///
/// MEASURED BEFORE THE FIX: this fired to `wrap(v: <unbound Global>)` — a WRONG value,
/// not an absent rewrite, which is the worse half of that pair. `guard_verdict` now
/// returns the proof's bindings for the RHS variables the head match left open, and the
/// fire site builds the RHS with them.
///
/// BACK OUT the `HoldsWith` arm (return `HoldsUnchanged` unconditionally) and this row
/// goes red while every other row in this file stays green: nothing else in the suite
/// writes a guard that BINDS.
#[test]
fn a_variable_the_guard_binds_reaches_the_right_hand_side() {
    const SRC: &str = r#"
namespace test.wi8rjk8bind
  import anthill.prelude.{Int64}

  sort Boxed
    entity wrap(v: Int64)
  end

  fact src(1, 42)

  sort Lib
    operation pick(x: Int64) -> Boxed
    rule h: pick(?a) <=> wrap(v: ?p) :- src(?a, ?p) [simp]
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    let t = call_ints(&mut kb, "test.wi8rjk8bind.Lib.pick", &[1]);
    let out = kb.simplify(t);
    assert_eq!(
        head_name(&kb, out),
        "test.wi8rjk8bind.Boxed.wrap",
        "the guard holds at `pick(1)`, so the rewrite must fire",
    );
    let field = match kb.get_term(out) {
        Term::Fn { named_args, .. } => named_args
            .iter()
            .find(|(k, _)| kb.local_name_of(*k) == "v")
            .map(|(_, v)| *v)
            .expect("the `v` field"),
        other => panic!("expected a `wrap` entity, got {other:?}"),
    };
    assert_eq!(
        kb.get_term(field),
        &Term::Const(Literal::Int(42)),
        "`?p` is bound by the GUARD (`src(1, ?p)`), so the RHS must carry 42 — an \
         unbound variable here is a wrong value, not a declined rewrite; got {:?}",
        kb.get_term(field),
    );

    // …and the guard-FALSE direction on the same rule: no `src` row for 2.
    let miss = call_ints(&mut kb, "test.wi8rjk8bind.Lib.pick", &[2]);
    assert_eq!(
        kb.simplify(miss),
        miss,
        "no `src(2, ?p)` row, so the guard is refuted and nothing fires",
    );
}

/// A guard over SYMBOLIC OPERATION PARAMETERS must not be decided at compile time.
///
/// At the typer a parameter reaches a guard as a `var_ref` reflect term, and a scalar
/// builtin reads one as an ordinary ground constant — so `neq(var_ref(p), var_ref(q))`
/// succeeds STRUCTURALLY over two parameters that may be equal at run time.
/// `step_init` has this guard (WI-537/WI-067) but only under a Γ overlay, which a guard
/// search does not carry, so `guard_verdict` makes the test itself.
///
/// THE FIXTURE IS HETEROGENEOUS ON PURPOSE, which is what makes it a measurement rather
/// than an observation that nothing happened: the GROUND sibling `pick(1, 2)` folds to
/// `1` in the same program, so "the symbolic one did not fire" cannot be the typer
/// declining to fire `pk` at all.
///
/// MEASURED BOTH WAYS. Back out the open-world test in `guard_verdict` and
/// `caller_sym`'s body becomes `var_ref(p)` — the rewrite applied — while
/// `caller_ground` is `Const(1)` either way.
#[test]
fn a_guard_over_symbolic_parameters_declines_at_the_typer() {
    const SRC: &str = r#"
namespace test.wi8rjk8ow
  import anthill.prelude.{Int64}
  import anthill.prelude.PartialEq.{neq}

  sort Lib
    operation pick(x: Int64, y: Int64) -> Int64
    rule pk: pick(?a, ?b) <=> ?a :- neq(?a, ?b) [simp]

    operation caller_ground() -> Int64 = pick(1, 2)
    operation caller_sym(p: Int64, q: Int64) -> Int64 = pick(p, q)
  end
end
"#;
    let kb = crate::common::load_kb_with(SRC);

    let ground = kb
        .op_body_node(sym(&kb, "test.wi8rjk8ow.Lib.caller_ground"))
        .expect("caller_ground has a body");
    assert!(
        matches!(ground.as_expr(), Some(Expr::Const(Literal::Int(1)))),
        "the CONTROL: `neq(1, 2)` is decidable from the program text, so the guard \
         holds and the call folds to 1; got {:?}",
        ground.as_expr(),
    );

    let symbolic = kb
        .op_body_node(sym(&kb, "test.wi8rjk8ow.Lib.caller_sym"))
        .expect("caller_sym has a body");
    assert_eq!(
        crate::common::head_short(&kb, &symbolic),
        "pick",
        "`neq(p, q)` over two PARAMETERS is not decidable at compile time — `p` and `q` \
         may be equal at run time — so the call must be left standing. A `var_ref(p)` \
         body here is the structural mis-decision this row exists for; got {:?}",
        symbolic.as_expr(),
    );
}
