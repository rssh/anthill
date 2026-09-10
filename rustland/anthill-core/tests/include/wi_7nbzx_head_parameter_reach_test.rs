//! WI-20260910-7NBZX — the §2.1 sigil-free head parameter reaches an EQUATION's LHS and
//! a BODY-LESS head, not only a relational clause's head atom.
//!
//! §2.1 says `name: Type` in the head of the predicate a rule DEFINES is the same thing
//! `?name: Type` is. The reclassifier was reached from one place — the head atom of a
//! clause — so two other head shapes took the sigil spelling and silently disagreed with
//! it. THREE divergences, measured on the tree that delivered WI-20260909-C7ANM:
//!
//!  1. A `[simp]` EQUATION: `pick(?a: Red, ?b) <=> 7` rewrote `pick(red(), 1)` to `7`;
//!     `pick(a: Red, ?b) <=> 7` loaded clean and was INERT. A DEAD RULE, one character
//!     away from a live one — an equation's head is the CONNECTIVE (`Fn{<=>, [lhs,
//!     rhs]}`, no named args), so the reclassifier declined at it and never saw the LHS
//!     that does the matching.
//!  2. An UNTAGGED equation: the sigil spelling is REFUSED loudly (the bound has no
//!     enforcer — nothing fires an untagged equation, WI-903/881), and the sigil-free
//!     spelling escaped that refusal for the same reason as (1).
//!  3. A BODY-LESS head: `rule f(?d, ?x: Red)` is refused (a DECLARATION stores no
//!     clause for the bound's one enforcer to run in); `rule f(?d, x: Red)` loaded clean
//!     and declared `f` with its written parameter enforcing nothing — the
//!     "accepted and ignored" case that refusal's own doc says must not exist. It hits
//!     the LONE parameter too, so it is not about columns at all.
//!
//! THE SIGIL TWIN IS THE YARDSTICK in every row: each `*_sigil` assertion passes BOTH
//! with the repair and without it BY DESIGN, and what the suite claims is that the
//! sigil-free spelling answers EXACTLY what its twin answers — to a VALUE for the
//! rewrite rows, and to the SAME refusal for the refusal rows.
//!
//! WHICH ROWS FAIL WHEN THE REPAIR IS BACKED OUT. Two axes, backed out separately
//! against these eleven rows — MEASURED, not predicted.
//!
//! AXIS 1 — THE EQUATION-LHS PRE-PASS at the head-conversion site (the
//! `convert_rule_head_with_params(lhs)` call removed). 4 of 11 fail:
//! `a_tagged_equation_reclassifies_its_lhs_in_both_spellings`,
//! `an_untagged_equation_refuses_both_spellings` (each on its sigil-FREE half only — the
//! sigil half of both passes either way, which is what makes it the yardstick),
//! `an_equation_rhs_reads_a_parameter_bare`, and
//! `a_guarded_equals_equation_reclassifies_its_lhs_too`.
//!
//! AXIS 2 — THE SHARED CLASSIFICATION at the declaration refusal
//! (`classify_rule_head_params(head).is_some()` dropped from
//! `declaration_clause_carrier`). 1 of 11 fails:
//! `a_body_less_parameter_head_is_refused_like_its_sigil_twin`.
//!
//! A THIRD ARRANGEMENT, measured because axis 1's own rows do not rule it out: gating
//! the pre-pass on `parse_equation_lhs` — the DEFINING subset, `<=>` alone since WI-888
//! — instead of the whole equality family. 1 of 11 fails,
//! `a_guarded_equals_equation_reclassifies_its_lhs_too`, and that is the row's entire
//! reason to exist: every other equation row passes under it.
//!
//! PASS EITHER WAY UNDER ALL THREE, BY DESIGN — the rows that say what the repair must
//! NOT do, each naming a widening that would satisfy every failing row above:
//! `an_unannotated_tagged_equation_still_fires` (fire everything),
//! `an_untagged_unannotated_equation_still_loads` (refuse every untagged equation),
//! `a_body_less_head_with_nothing_to_enforce_still_declares` (refuse every declaration),
//! `a_clause_on_an_entity_constructor_head_is_untouched` (reclassify by spelling), and
//! `a_structural_identity_head_is_unchanged_in_both_spellings` (make `===` define).
//!
//! `the_bound_on_a_reclassified_lhs_is_ENFORCED` passes under every arrangement above,
//! and is NOT dead weight: it is the control for a repair that reclassifies the LHS but
//! installs no bound, or installs one nothing reads. Under axis 1 the sigil-free rule
//! never matches at all, so it stays green there for a reason unrelated to what it
//! measures — stated so the count above is not read as covering it.
//!
//! WHY THE SECOND IS A SPLIT AND NOT A SECOND TEST. `declaration_clause_carrier` asked
//! `head_carries_typed_column`, a parse-level test that detects only the minted
//! `typed_var` node `?x: T` lowers to. Restating §2.1's gates beside it would be a
//! second copy of a four-part discriminator (surface, head category, aux filter, "does
//! this name a sort?") free to drift from the converter's. So the converter's gates were
//! split out as `classify_rule_head_params` and both readers now call it.

use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

fn sym(kb: &KnowledgeBase, qn: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("resolve {qn}"))
}

/// One equation under test. `lhs` is the only thing that varies between a row and its
/// control; `tag` carries `[simp]` or nothing, which is the ENABLEMENT (WI-881) and so
/// the axis the untagged rows measure.
fn equation_src(lhs: &str, tag: &str) -> String {
    connective_src(lhs, "<=>", "", tag)
}

/// The same equation over any of the three equality-family connectives, with or without
/// a guard. `Blue` is here so a row can put a NON-CONFORMING value at the redex.
fn connective_src(lhs: &str, conn: &str, guard: &str, tag: &str) -> String {
    format!(
        r#"
namespace test.n7bzx.eq
  import anthill.prelude.{{Int64}}
  sort Red
    entity red
  end
  sort Blue
    entity blue
  end
  fact seed(red())
  sort Lib
    operation pick(x: Red, y: Int64) -> Int64
    rule pk: {lhs} {conn} 7 {guard} {tag}
  end
end
"#
    )
}

/// `pick(red(), 1)` put through the rewriter — the REDEX, so a row says whether the rule
/// FIRED rather than whether it loaded. Returns the outer term after `simplify`.
fn simplify_pick(kb: &mut KnowledgeBase) -> Term {
    simplify_pick_of(kb, "test.n7bzx.eq.Red.red")
}

/// [`simplify_pick`] over a chosen first argument, so a row can put a `Blue` where the
/// bound says only a `Red` may go.
fn simplify_pick_of(kb: &mut KnowledgeBase, ctor: &str) -> Term {
    let red_sym = sym(kb, ctor);
    let red: TermId = kb.alloc(Term::Fn {
        functor: red_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let f = sym(kb, "test.n7bzx.eq.Lib.pick");
    let t = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(&[red, one]),
        named_args: SmallVec::new(),
    });
    let out = kb.simplify(t);
    kb.get_term(out).clone()
}

#[test]
fn a_tagged_equation_reclassifies_its_lhs_in_both_spellings() {
    // THE HEADLINE ROW, driven to a VALUE. `7` is the RHS, so this is the rewrite
    // having fired — not a clean load, and not a count.
    for lhs in ["pick(?a: Red, ?b)", "pick(a: Red, ?b)"] {
        let mut kb = crate::common::load_kb_with(&equation_src(lhs, "[simp]"));
        assert_eq!(
            simplify_pick(&mut kb),
            Term::Const(Literal::Int(7)),
            "`rule pk: {lhs} <=> 7 [simp]` must rewrite `pick(red(), 1)` to 7"
        );
    }
}

#[test]
fn an_unannotated_tagged_equation_still_fires() {
    // PASSES EITHER WAY BY DESIGN, and it is the control that says the row above
    // measures the ANNOTATION and not the tag: the same equation with no `: Red` on it
    // fires before and after the repair. Without it, "both spellings rewrite to 7" is
    // also what a change that broke annotations entirely and fired everything would say.
    let mut kb = crate::common::load_kb_with(&equation_src("pick(?a, ?b)", "[simp]"));
    assert_eq!(simplify_pick(&mut kb), Term::Const(Literal::Int(7)));
}

#[test]
fn an_untagged_equation_refuses_both_spellings() {
    // The bound's refusal, not its enforcement — an untagged equation has no reader, so
    // WI-903 refuses the annotation rather than loading a rule that ignores it. The
    // sigil-free spelling used to LOAD CLEAN here, which is the same escape as the
    // rewrite row seen from the other side.
    for lhs in ["pick(?a: Red, ?b)", "pick(a: Red, ?b)"] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with(&equation_src(lhs, "")),
            &["WI-582: a typed rule pattern"],
        );
    }
}

#[test]
fn an_untagged_unannotated_equation_still_loads() {
    // PASSES EITHER WAY BY DESIGN. The refusal above must be about the ANNOTATION; an
    // untagged equation with none is inert but perfectly legal, and a repair that
    // refused every untagged equation would pass the row above and fail here.
    crate::common::load_kb_with(&equation_src("pick(?a, ?b)", ""));
}

#[test]
fn an_equation_rhs_reads_a_parameter_bare() {
    // The ORDER claim at the call site: the LHS's parameters enter `rule_param_vars`
    // BEFORE the RHS converts, so an RHS reading one bare gets the clause variable —
    // exactly as `?a` is shared across an equation today. Driven: `idr(red())` rewrites
    // to `wrap(…)`, which can only happen if the RHS's bare `a` matched the LHS's
    // parameter. Were it a symbolic constant instead, `wrap` would receive that constant
    // and the rule would still fire, so the row reads the ARGUMENT, not just the head.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.n7bzx.rhs
  import anthill.prelude.{Int64}
  sort Red
    entity red
  end
  sort Lib
    operation idr(x: Red) -> Red
    operation wrap(x: Red) -> Red
    rule pk: idr(a: Red) <=> wrap(a) [simp]
  end
end
"#,
    );
    let red_sym = sym(&kb, "test.n7bzx.rhs.Red.red");
    let red: TermId = kb.alloc(Term::Fn {
        functor: red_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let f = sym(&kb, "test.n7bzx.rhs.Lib.idr");
    let t = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(&[red]),
        named_args: SmallVec::new(),
    });
    let out = kb.simplify(t);
    let Term::Fn {
        functor, pos_args, ..
    } = kb.get_term(out)
    else {
        panic!("expected `wrap(…)`, got {:?}", kb.get_term(out))
    };
    assert_eq!(kb.local_name_of(*functor), "wrap");
    assert_eq!(pos_args.len(), 1, "wrap must have received the parameter");
    assert_eq!(
        crate::common::entity_functor(&kb, &anthill_core::eval::Value::Term { id: pos_args[0] })
            .map(|s| kb.local_name_of(s).to_string()),
        Some("red".to_owned()),
        "the RHS's bare `a` must be the LHS parameter the match bound to `red`"
    );
}

// ── the body-less declaration ────────────────────────────────────────────────

fn declaration_src(items: &str) -> String {
    format!(
        r#"
namespace test.n7bzx.decl
  sort Red
    entity red
  end
  fact seedr(red())
{items}end
"#
    )
}

#[test]
fn a_body_less_parameter_head_is_refused_like_its_sigil_twin() {
    // FOUR SPELLINGS OF ONE CLAIM: two columns and one, each written both ways. The LONE
    // rows matter because they say this is not about column order — a single parameter
    // has no order to get wrong and still escaped the refusal.
    for head in [
        "  rule f(?d, ?x: Red)\n",
        "  rule f(?d, x: Red)\n",
        "  rule g(?x: Red)\n",
        "  rule g(x: Red)\n",
    ] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with(&declaration_src(head)),
            &["DECLARES the predicate and stores no clause"],
        );
    }
}

#[test]
fn a_body_less_head_with_nothing_to_enforce_still_declares() {
    // PASSES EITHER WAY BY DESIGN — the two shapes a widened refusal would swallow.
    //
    // A plain declaration claims no bound at all (061's whole point), and a named
    // argument whose value is a VARIABLE is not the parameter form (spec: `rule
    // reaches(from: ?a, to: ?b)` keeps its keys), so neither may be refused. Without
    // these, "the parameter head is refused" is also what refusing every body-less rule
    // would say.
    crate::common::load_kb_with(&declaration_src("  rule plain(?a, ?b)\n"));
    crate::common::load_kb_with(&declaration_src("  rule reaches(from: ?a)\n"));
}

#[test]
fn a_clause_on_an_entity_constructor_head_is_untouched() {
    // THE HEAD-CATEGORY GATE, still discriminating. `palette` is an entity constructor,
    // so `c: Red` is a sort passed as DATA (055) and stays a named argument — the row
    // `wi742_typed_relational_head_test::parameter_form_leaves_entity_constructor_heads_alone`
    // owns, driven here through the shape this ticket touches.
    //
    // Two rows for `palette(c: ?c)`: the `fact`, and this clause whose `c: Red` stayed a
    // named argument. Had the clause been reclassified its head would carry ONE
    // POSITIONAL argument and match neither.
    //
    // NOTE WHAT THIS IS NOT: the same text with the body removed IS refused, and
    // correctly — a body-less head DECLARES its own name (061), so `palette` there
    // resolves to a NEW namespace-level predicate rather than to the constructor, and
    // its `c: Red` is a genuine parameter. Measured both ways round, and both spellings
    // of it agree.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.n7bzx.ctor
  sort Red
    entity red
  end
  sort Palette
    entity palette(c: Red)
  end
  fact palette(c: red())
  rule any(?c) :- palette(c: ?c)
  rule palette(c: Red) :- true
end
"#,
    );
    assert_eq!(
        crate::common::query_unary(&mut kb, "test.n7bzx.ctor.any").len(),
        2
    );
}

#[test]
fn the_bound_on_a_reclassified_lhs_is_ENFORCED() {
    // THE NEGATIVE HALF, and without it the headline row measures only that something
    // fires. `pick(blue(), 1)` must NOT rewrite: `x: Red` is the bound, and a reclassified
    // parameter that installed no bound — or installed one nothing reads — would rewrite
    // here and pass every other equation row in this file. Raised by /code-review.
    //
    // Both spellings, because "the sigil-free spelling answers what its twin answers" is
    // a claim about the REFUSAL as much as about the rewrite.
    for lhs in ["pick(?a: Red, ?b)", "pick(a: Red, ?b)"] {
        let mut kb = crate::common::load_kb_with(&equation_src(lhs, "[simp]"));
        let out = simplify_pick_of(&mut kb, "test.n7bzx.eq.Blue.blue");
        let Term::Fn { functor, .. } = &out else {
            panic!("`{lhs}` rewrote a non-conforming redex to {out:?}")
        };
        assert_eq!(
            kb.local_name_of(*functor),
            "pick",
            "`rule pk: {lhs} <=> 7 [simp]` must leave `pick(blue(), 1)` standing — \
             `blue` is not a `Red`"
        );
    }
}

#[test]
fn a_guarded_equals_equation_reclassifies_its_lhs_too() {
    // THE DEFINING SUBSET IS NOT THE POPULATION. `parse_equation_lhs` — "is this a
    // DEFINING equation" — is `<=>` alone since WI-888, but a GUARDED `=` is a firing
    // rewrite (WI-20260820-8RJK8) and three ship in the stdlib. Gating on the defining
    // subset left this spelling dead; the gate is the whole equality family, which is
    // what the sigil form effectively uses (its `typed_var` strip tests no connective).
    //
    // MEASURED before the widening: the sigil row rewrote and the sigil-free row did
    // not. Found by /code-review.
    for lhs in ["pick(?a: Red, ?b)", "pick(a: Red, ?b)"] {
        let mut kb =
            crate::common::load_kb_with(&connective_src(lhs, "=", ":- seed(red())", "[simp]"));
        assert_eq!(
            simplify_pick(&mut kb),
            Term::Const(Literal::Int(7)),
            "a GUARDED `=` equation must fire in both spellings; `{lhs}` did not"
        );
    }
}

#[test]
fn a_structural_identity_head_is_unchanged_in_both_spellings() {
    // PASSES EITHER WAY BY DESIGN, and it is why the widened gate needs no carve-out for
    // `===`. It is a structural identity TEST, not a defining connective: bodyless it is
    // refused, and guarded it fires in NEITHER spelling. Reclassifying its LHS therefore
    // puts the sigil-free spelling on the path its twin already took, rather than giving
    // it a new behaviour — which is the claim this row pins.
    for lhs in ["pick(?a: Red, ?b)", "pick(a: Red, ?b)"] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with(&connective_src(lhs, "===", "", "[simp]")),
            &["structural identity TEST"],
        );
        let mut kb =
            crate::common::load_kb_with(&connective_src(lhs, "===", ":- seed(red())", "[simp]"));
        let out = simplify_pick(&mut kb);
        let Term::Fn { functor, .. } = &out else {
            panic!("`{lhs} === 7` rewrote to {out:?}; a `===` head defines nothing")
        };
        assert_eq!(kb.local_name_of(*functor), "pick");
    }
}
