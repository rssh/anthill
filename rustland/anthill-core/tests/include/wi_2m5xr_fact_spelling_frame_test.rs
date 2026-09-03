//! WI-20260903-2M5XR — A `[simp]` EQUATION'S OWN FRAME, IN BOTH ITS SPELLINGS.
//!
//! `rule lhs <=> rhs [simp]` and `fact lhs <=> rhs [simp]` are the same thing — a
//! bodyless, tagged, directional equation — and both FIRE. They did not agree about
//! whether the rule is well-formed:
//!
//! ```text
//!   rule fu(?x) <=> sink(?y) [simp]  + a consumer  ->  1 error (refused)
//!   fact fu(?x) <=> sink(?y) [simp]  + a consumer  ->  0 errors (loaded clean)
//! ```
//!
//! `?y` is named by the RHS and bound by nothing, so instantiating the equation
//! left-to-right has no value to splice. WI-20260903-FCZ3N's `bottom_out_unbound` writes
//! `⊥` there — and the `fact` spelling slipped past it.
//!
//! ── THE ROOT, TRACED RATHER THAN READ OFF THE TICKET ────────────────────────
//!
//! Measured with a probe on `simp_rewrite::open_equation`, both spellings of the same
//! equation: `rule` opens `arity=2, fresh=2`; `fact` opens `arity=0, fresh=0`. The two
//! reach the KB by different asserters — `load_rule` through
//! `assert_rule_debruijn_with_nodes`, which closes the clause's variables into DeBruijn
//! slots, and `load_fact` through `assert_fact`, which leaves `arity`/`globals` at their
//! ground-fact defaults so the variables stay `Var::Global`. `open_equation` then had
//! nothing to open and answered `Vec::new()` — as though the rule had no frame, rather
//! than a frame in the other representation.
//!
//! `bottom_out_unbound` keys on that set, so for every `fact` equation it returned
//! immediately and the verdict was never reached.
//!
//! ── WHY THE FRAME, AND NOT A LOAD REFUSAL ───────────────────────────────────
//!
//! Because FCZ3N settled that, and its reason still holds: an equation is logically
//! symmetric and citable both ways with `using` (§8.3), so `f(?x) <=> g(?y)` is a strange
//! but not meaningless LAW. What is broken is instantiating it LEFT-TO-RIGHT, which is
//! what a fire does — so the verdict belongs at the fire. This ticket does not move it;
//! it makes the fire's own notion of "the rule's variables" cover both representations.
//!
//! ── ONE QUESTION, TWO REPRESENTATIONS ───────────────────────────────────────
//!
//! The set was never ambiguous — `resolve.rs` already spells it out at the match:
//! `match_view_oneway` binds "the opened `fresh` globals for a DeBruijn rule, **or the
//! head's own `Global` vars for a legacy arity-0 head**". The matcher had both cases; the
//! `fresh` channel carrying that set onward had one. `open_equation` now returns
//! `kb.collect_vars(head)` for the arity-0 arm, so matcher and channel agree by
//! construction rather than by convention.
//!
//! THE OTHER READER OF `fresh` CANNOT BE REACHED WITH AN ARITY-0 HEAD, measured rather
//! than assumed: `typed_pattern_bounds_hold` keys WI-582 bounds by the same set, but a
//! typed pattern on a `fact` head is refused at load first — `fact tp(?x: Int64) <=> …`
//! reports "WI-582: a variable type annotation (`?x: T`) is only meaningful in a rule
//! head pattern". So widening the channel changes exactly one reader's answer.
//! `open_debruijn_node`, which also takes `fresh`, acts only on `Expr::Var(DeBruijn)` and
//! is a no-op on a head that has none — which [`a_well_formed_equation_still_fires`]
//! drives rather than merely asserts.
//!
//! ── THE POPULATION IT REACHES, CENSUSED ─────────────────────────────────────
//!
//! A probe on `open_equation` over the whole `wi_tests` corpus records **709 opens: 517
//! take the DeBruijn arm and 192 the arity-0 one**. Of those 192, **111 now receive a
//! NON-EMPTY frame** where they previously received `Vec::new()` — 101 of two variables
//! and 10 of one; the remaining 81 are genuinely ground and unchanged. So this is not a
//! repair that only its own fixture exercises: it changes what the fire knows on 111
//! openings the corpus already performs, and the binary stays green across all of them.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ───────────────────────────
//!
//! Backed out PRESENT-BUT-WRONG at `open_equation`'s `else` arm (`(head, Vec::new())`,
//! the state this ticket found). **EXACTLY ONE ROW FAILS**:
//! [`a_malformed_equation_is_refused_in_both_spellings`], and only on its `fact` half —
//! which is the defect stated exactly: one spelling was covered and the other was not.
//!
//! GREEN UNDER THE BACK-OUT, BY DESIGN, and each is here for the opposite risk — that the
//! widened frame bottoms out a variable the LHS DID bind, which would break a working
//! rewrite rather than a broken one:
//! [`a_well_formed_equation_still_fires`] (both spellings must still COMPUTE) and
//! [`a_projecting_equation_still_rewrites`] (WI-634's shape, whose RHS variable is
//! legitimately the redex's).

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

fn errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// Call `op` with one `Int` argument on a freshly built interpreter.
fn drive(src: &str, op: &str, arg: i64) -> Value {
    let mut interp = interp_for(src);
    interp
        .call(op, &[Value::Int(arg)])
        .unwrap_or_else(|e| panic!("{op}({arg}) must evaluate: {e:?}"))
}

/// **A — THE HEADLINE.** The two spellings are one equation and must give one verdict.
///
/// Asserted as an AGREEMENT, not as two independent expectations: the defect was
/// precisely that the `rule` half was already right, so a row pinning only the `fact`
/// half would pass for a fix that broke the other one, and a row pinning only `rule`
/// measures nothing at all. The messages are compared byte-for-byte because both come
/// from the same `⊥` and there is no reason for them to differ.
///
/// RED UNDER THE BACK-OUT on the `fact` half: 0 errors, the malformed rule loading clean.
#[test]
fn a_malformed_equation_is_refused_in_both_spellings() {
    let program = |kw: &str| {
        format!(
            "namespace zz2ma\n  import anthill.prelude.Int64\n  \
             operation sink(r: Int64) -> Int64 = r\n  \
             {kw} fu(?x) <=> sink(?y) [simp]\n  \
             operation c(n: Int64) -> Int64 = fu(n)\nend\n"
        )
    };
    let by_rule = errs(&program("rule"));
    let by_fact = errs(&program("fact"));

    assert_eq!(
        by_rule.len(),
        1,
        "`?y` is named by the RHS and bound by nothing — the `rule` spelling's verdict, \
         which was already right: {by_rule:#?}"
    );
    assert_eq!(
        by_fact.len(),
        1,
        "…and the `fact` spelling is the SAME equation, and fires. It loaded clean: \
         {by_fact:#?}"
    );
    assert_eq!(
        by_rule, by_fact,
        "one equation, one verdict — the two spellings must not differ in a word"
    );
    assert!(
        by_fact[0].contains("bottom"),
        "…and the verdict is the `⊥` a fire splices for a variable nothing supplies: {:?}",
        by_fact[0]
    );
}

/// **B — THE CAPABILITY, DRIVEN, AND THE GUARD ON THE OTHER SIDE.** The frame now covers
/// every `Var::Global` the head carries, and a frame that over-collects would bottom out
/// a variable the LHS DID bind — turning a working rewrite into a refusal. So this row
/// calls the operation and asserts the VALUE, in both spellings.
///
/// It also drives the `open_debruijn_node` question this change raises: that opener now
/// receives a non-empty `fresh` for an arity-0 rule, whose RHS node holds no DeBruijn
/// vars at all. Reading its code says it is a no-op; `drive(5) == 10` is what says so.
///
/// GREEN UNDER THE BACK-OUT by design — a narrower frame cannot break a rewrite. It is
/// this ticket's own risk that it measures, not the defect.
#[test]
fn a_well_formed_equation_still_fires() {
    for kw in ["rule", "fact"] {
        let src = format!(
            "namespace zz2mc\n  import anthill.prelude.Int64\n  \
             {kw} dbl(?x) <=> ?x + ?x [simp]\n  \
             operation drive(n: Int64) -> Int64 = dbl(n)\nend\n"
        );
        assert!(
            errs(&src).is_empty(),
            "the `{kw}` spelling of a WELL-FORMED equation must load: {:?}",
            errs(&src)
        );
        let got = drive(&src, "zz2mc.drive", 5);
        assert!(
            matches!(got, Value::Int(10)),
            "`{kw} dbl(?x) <=> ?x + ?x [simp]` must still FIRE and compute — `?x` is \
             bound by the LHS, so no `⊥` may reach it; got {got:?}"
        );
    }
}

/// **C — THE WI-634 CONTROL.** A PROJECTING equation, whose RHS variable rides in from
/// the redex rather than from the rule. `bottom_out_unbound`'s doc names this as the
/// shape that must not be bottomed out ("only the RULE's own frame is the rule's
/// obligation"), and widening the frame is exactly the change that could reach it.
///
/// GREEN UNDER THE BACK-OUT by design, for the same reason as B.
#[test]
fn a_projecting_equation_still_rewrites() {
    for kw in ["rule", "fact"] {
        let src = format!(
            "namespace zz2md\n  import anthill.prelude.Int64\n  \
             {kw} pk(?q) <=> ?q [simp]\n  \
             operation drive(n: Int64) -> Int64 = pk(n)\nend\n"
        );
        assert!(
            errs(&src).is_empty(),
            "a projecting `{kw}` equation must load: {:?}",
            errs(&src)
        );
        let got = drive(&src, "zz2md.drive", 7);
        assert!(
            matches!(got, Value::Int(7)),
            "`{kw} pk(?q) <=> ?q [simp]` projects its argument — the rewrite must \
             survive; got {got:?}"
        );
    }
}
