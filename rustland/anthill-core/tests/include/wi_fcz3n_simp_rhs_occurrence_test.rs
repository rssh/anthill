//! WI-20260903-FCZ3N — A `[simp]` RULE KEEPS ITS RHS OCCURRENCE.
//!
//! THE THIRD TERM→OCCURRENCE ROUND-TRIP, and the same repair as the first two.
//! WI-20260902-2SZ88 took ENTITY CONSTRUCTORS off `materialize_from_handle_spanned` and
//! WI-20260902-2NXAC took the COLLECTION LITERALS, both by building the occurrence where
//! the PARSE NODE is instead of re-deriving it from the KB term. `simp_rewrite`'s
//! `subst_visit` was the same shape in a different walk: it resolved a FIRED rule's RHS
//! from a TERM (`kb.walk_view`) and rebuilt every node with
//! `NodeOccurrence::synthesized_expr`.
//!
//! ── WHERE THE RHS OCCURRENCE NOW LIVES, WHICH THE TICKET ASKED FIRST ─────────
//!
//! NOT among `rule_body_nodes`, and it never could be: `KnowledgeBase::is_equation`
//! REQUIRES an empty body, so a clause with an RHS in its body list is by construction
//! not an equation and nothing fires it. So the RHS occurrence is a THIRD thing a rule
//! carries — `RuleEntry.rhs_node`, De Bruijn-closed beside the head and the (empty) body,
//! installed by the loader after the assert exactly as `head_span` and `type_bounds` are.
//! `open_equation` still returns the head TERM's operands; the fire opens the stored
//! occurrence against the SAME `fresh` globals and substitutes into THAT.
//!
//! ── TWO LOSSES IN ONE, MEASURED ─────────────────────────────────────────────
//!
//! On the delivered 2NXAC tree, `rule trig(?x) <=> sink(zzfc.inner.rel) [simp]` beside
//! `rule rel(1) :- base(1)`, with `operation consumer() -> Int64 = trig(5)`:
//!
//! ```text
//!   11:35: type mismatch in zzfc.name:  expected resolved name, got unresolved
//!   11:35: type mismatch in inner.name: expected resolved name, got unresolved
//!   11:35: type mismatch in rel.name:   expected resolved name, got unresolved
//! ```
//!
//! THREE errors, and all three at line 11 — the CONSUMER, where the name `zzfc.inner.rel`
//! does not appear. The count was WI-20260902-4NEKZ's per-leaf cascade, back because the
//! spliced node arrived with `dot_chain` clear so `loader_chain_dotted_name`'s provenance
//! gate refused to read the chain as the name it cites; the location was the redex's,
//! because `synthesized_expr` copies `from.span`. Now:
//!
//! ```text
//!   10:21: type mismatch in sink.r (op-arg): expected Int64, got Relation[T = Unit, …]
//! ```
//!
//! ONE error, naming the relation, AT THE CITATION — the same sentence, at the same kind
//! of place, that both direct spellings already gave.
//!
//! ── THE FIX IS NOT `synthesized_expr` ───────────────────────────────────────
//!
//! That constructor hardcodes `dot_chain: false` DELIBERATELY: a SYNTHESIS is a node a
//! pass decided to build, and it is not the dot the author wrote even when it expands
//! one. Flipping it would re-admit WI-20260901-92VA4's silent acceptance by another door
//! — which is what [`a_written_field_access_in_a_simp_rhs_is_still_not_a_citation`] is
//! for, and it is the row that separates this repair from that one.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ───────────────────────────
//!
//! **AXIS 1 — KEEPING THE RHS OCCURRENCE.** Backed out PRESENT-BUT-WRONG at
//! `simp_rewrite::build_rhs_template`, whose `kb.rule_equation_rhs_node(rid)` arm is made
//! to answer `None` so every fire re-derives the RHS from the head term — the state this
//! ticket found. **EXACTLY 4 ROWS FAIL** of 4 066 over the whole `wi_tests` binary:
//!
//! * [`a_dotted_citation_in_a_fired_simp_rhs_reports_once_at_the_name`] — 3 errors, at
//!   the redex.
//! * [`the_spliced_rhs_keeps_the_authors_span`] — the error moves to the redex.
//! * `wi873_dispatch_rewrite_completeness_test::a_simp_expansion_with_two_calls_is_two_entries`
//!   — its two spliced calls share the redex's span again.
//! * `wi873_dispatch_rewrite_completeness_test::one_rule_fired_at_two_redexes_collides_on_one_span`
//!   — the mirror: two fires of ONE written call take their two redexes' spans, so the
//!   collision that row exists for stops happening. Those two wi873 rows are this
//!   ticket's effect read from the OTHER side, by a file that had predicted it.
//!
//! GREEN UNDER THAT BACK-OUT, EACH BY DESIGN and each for its own reason:
//! [`the_four_controls_are_unmoved`] (its rows are the yardsticks — none of them fires a
//! `[simp]` rule carrying a citation); [`a_fired_simp_rhs_still_computes`] (a
//! term-derived RHS always evaluated correctly — what it lost was provenance, not
//! meaning; this row is instead what fails if the occurrence path builds a DIFFERENT
//! tree); and [`a_written_field_access_in_a_simp_rhs_is_still_not_a_citation`].
//!
//! **AXIS 2 — THE PROVENANCE RE-PARENT.** `reparent_spliced` returning `reassemble(...)`
//! WITHOUT `reparented_from`, so a spliced node keeps the rule's `Source` origin.
//! **EXACTLY 4 ROWS FAIL**, all four arms of `wi_5r2xt_macro_spliced_call_name_test` —
//! `join(p, q, λ)` reports the macro's own name because the chain stops inside the rule
//! instead of reaching the redex. Every row in THIS file passes under it, which is what
//! says the re-parent is a second decision and not a restatement of axis 1. (It is also
//! what stops a fire sharing the stored rule's `Rc`, and so its typer stamps, across two
//! call sites — see `reparent_spliced`'s doc; no fixture here drives that half.)
//!
//! **AXIS 3 — THE UNBOUND-VARIABLE VERDICT.** `simp_rewrite::bottom_out_unbound` made to
//! return its input, so a rule variable the match did not bind survives as a variable
//! instead of `⊥`. **EXACTLY 1 ROW FAILS**:
//! [`an_unbound_rule_variable_in_a_fired_rhs_is_still_refused`], and it goes to ZERO
//! errors — a malformed rule loading clean. Its own axis because it is a separate
//! decision from either of the two above: routing σ through the shared owner
//! (`node_occurrence::substitute_occurrence`, which is right — σ over an occurrence must
//! have ONE owner) silently dropped a verdict the term path had, and this is what puts it
//! back. Found by measuring the leaf verdicts after `/code-review`, not by an arm.
//!
//! **THE WRONG FIX.** `synthesized_expr` stamped `dot_chain: true` — which would also
//! make row A report ONE error — is refused by
//! [`a_written_field_access_in_a_simp_rhs_is_still_not_a_citation`], the only row here
//! that goes red under it and green under both back-outs above.
//!
//! ── WHAT MOVING THE LOCATION COSTS, AND WHO OWNS IT ─────────────────────────
//!
//! ONE authored mistake fired at N sites is now reported N times, byte-identical in text
//! AND location — measured: `rule bad(?x) <=> sink("nope") [simp]` under
//! `c(n) = bad(n) + bad(n)` gives two `4:20: … expected Int64, got String`, where two
//! DIRECTLY-written copies give two messages at their two spans. Before this ticket the N
//! copies carried their N redexes' distinct spans, so they were distinguishable and every
//! one of them pointed at a line the mistake is not written on. The location is now right
//! and the COUNT is the residue; collapsing identical `(span, message)` diagnostics is a
//! change to the whole error channel and is **WI-20260903-W9D4Z**. NO ROW HERE PINS THE
//! 2 — it would go red on that ticket's fix.
//!
//! A RULE VARIABLE IN A TYPE POSITION of the RHS is still never instantiated
//! (`Map[K = ?k, …].empty()`): the typer's fire binds `Value::Node` and a type position's
//! σ is term-world. UNMOVED by this ticket — 0 errors before and after — while its GROUND
//! twin went 0 → 1, which is this ticket's gain and the asymmetry that made the gap
//! visible. **WI-20260903-H054K**; `build_rhs_template`'s doc carries the measurement.
//!
//! ── ONE SHAPE THIS SURFACED AND DOES NOT OWN ────────────────────────────────
//!
//! A LAMBDA in a `[simp]` RHS is refused, before and after, with two different bogus
//! messages: the term path said `x.name: expected resolved name, got unresolved` twice,
//! and the occurrence path says `1:1: <bottom>.expr: expected surface expression` once.
//! The second is exactly what the SAME lambda in a plain RULE BODY has always said —
//! measured, on a walk this ticket does not touch — because `build_body_atom_occurrence`
//! builds `Expr::Lambda`'s `param` as a reflect `Expr::Apply` instead of a
//! `NodeKind::Pattern`, so the parameter never becomes a binder. This ticket only made
//! the two positions AGREE; the defect is the walk's own and is
//! **WI-20260903-FC2X4**. NO ROW HERE ASSERTS IT — a fixture pinning the current refusal
//! would go red the day that ticket lands.

use anthill_core::eval::Value;
use anthill_core::kb::load::meta_has_flag;

/// The shared fixture: `zzfc.inner.rel` is a real one-clause relation, `zzfc.two.rel2`
/// its one-segment twin, `sink` an `Int64`-taking operation to write it into, and `extra`
/// whatever the row adds to `zzfc.two`.
///
/// ONE skeleton for every row on purpose (WI-20260902-4NEKZ's lesson): the rows quote
/// each other's counts and one of them quotes a LINE AND COLUMN, so a forked copy would
/// let a rename move the location under an assertion taken on a different program.
fn program(extra: &str) -> String {
    format!(
        "namespace zzfc.inner\n  fact base(1)\n  rule rel(1) :- base(1)\nend\n\
         namespace zzfc.two\n  import anthill.prelude.Int64\n  \
         fact base2(1)\n  rule rel2(1) :- base2(1)\n  \
         operation sink(r: Int64) -> Int64 = r\n\
{extra}end\n"
    )
}

fn errs(extra: &str) -> Vec<String> {
    crate::common::try_load_kb_with(&program(extra))
        .err()
        .unwrap_or_default()
}

/// `line:col` of `needle`'s first occurrence in `src`, in the 1-based form the loader's
/// error strings are prefixed with. Computed from the fixture rather than written out, so
/// an edit to the skeleton moves the expectation with it instead of silently asserting
/// about a line that is now something else.
fn line_col(src: &str, needle: &str) -> String {
    let idx = src
        .find(needle)
        .unwrap_or_else(|| panic!("fixture does not contain {needle:?}"));
    let line = src[..idx].matches('\n').count() + 1;
    let col = idx - src[..idx].rfind('\n').map_or(0, |p| p + 1) + 1;
    format!("{line}:{col}")
}

/// The row every other row here is read against: a `[simp]` rule whose RHS cites a
/// relation by its dotted paren-less name, plus a consumer that makes it FIRE.
const CITING_RULE_AND_CONSUMER: &str = "  rule trig(?x) <=> sink(zzfc.inner.rel) [simp]\n  \
                                        operation consumer() -> Int64 = trig(5)\n";

/// **A — THE HEADLINE.** ONE diagnosis, and it is at the NAME.
///
/// Both halves are asserted because the defect was both: THREE errors (the per-leaf
/// cascade) reported at the REDEX. A repair that only stopped the cascade would leave one
/// error pointing at `trig(5)`, and a repair that only moved the span would leave three.
///
/// RED under the back-out, on every assertion: 3 errors instead of 1, each saying a name
/// that resolves is unresolved, all at the consumer's line.
#[test]
fn a_dotted_citation_in_a_fired_simp_rhs_reports_once_at_the_name() {
    let src = program(CITING_RULE_AND_CONSUMER);
    let e = errs(CITING_RULE_AND_CONSUMER);
    assert_eq!(
        e.len(),
        1,
        "one written citation, one diagnosis — it was THREE, one per segment of a name \
         that RESOLVES: {e:#?}"
    );
    assert!(
        e[0].contains("sink.r (op-arg)") && e[0].contains("Relation"),
        "…and it names the CALL and the relation type, not a segment: {:?}",
        e[0]
    );
    assert!(
        !e[0].contains("unresolved"),
        "…and it does not call a name that resolves unresolved: {:?}",
        e[0]
    );

    // THE LOCATION. The spliced node used to take the REDEX's span (`synthesized_expr`
    // copies `from.span`), so the error landed on `trig(5)` — a line on which the name it
    // blames does not occur. Both places are named, so the assertion cannot pass by the
    // two happening to coincide.
    let at_citation = line_col(&src, "sink(zzfc.inner.rel)");
    let at_redex = line_col(&src, "trig(5)");
    assert_ne!(
        at_citation, at_redex,
        "the fixture must put the citation and the redex on different lines, else this \
         row measures nothing"
    );
    assert!(
        e[0].starts_with(&format!("{at_citation}: ")),
        "the diagnosis belongs at the citation ({at_citation}), not at the redex \
         ({at_redex}) where the name does not appear: {:?}",
        e[0]
    );
}

/// **B — THE FOUR CONTROLS, UNMOVED.** Each is a way the headline row could have been
/// green for the wrong reason.
///
/// GREEN UNDER THE BACK-OUT, all four, BY DESIGN — that is what makes them controls. The
/// no-consumer row says the three errors came from the FIRE and not from loading the
/// rule; the two direct spellings are the yardstick the headline is read against; the
/// one-segment citation says the fire does not lose name resolution in general (its
/// COUNT is 1 either way — its LOCATION moves onto the written call with this ticket,
/// which is the headline's claim and is asserted there, not here).
#[test]
fn the_four_controls_are_unmoved() {
    for (label, extra, expected) in [
        (
            "the same simp rule with NO consumer never fires",
            "  rule trig(?x) <=> sink(zzfc.inner.rel) [simp]\n",
            0,
        ),
        (
            "the citation written directly in an OPERATION body",
            "  operation direct() -> Int64 = sink(zzfc.inner.rel)\n",
            1,
        ),
        (
            "the citation written directly in a RULE body",
            "  rule dr(1) :- sink(zzfc.inner.rel) = 7\n",
            1,
        ),
        (
            "a ONE-SEGMENT citation in the same simp fire",
            "  rule trig2(?x) <=> sink(rel2) [simp]\n  \
             operation consumer2() -> Int64 = trig2(5)\n",
            1,
        ),
    ] {
        let e = errs(extra);
        assert_eq!(e.len(), expected, "{label}: {e:#?}");
    }
}

/// **C — AND THE SPLICED NODE CARRIES THE AUTHOR'S SPAN, not the redex's.**
///
/// Separate from row A because A's subject is a CITATION, whose repair needs the
/// `dot_chain` bit as well; this one is an ordinary type error inside a fired RHS, so it
/// isolates the SPAN half. The RHS writes a `Str` where `sink` declares `Int64`, and the
/// error must point at the string the author wrote.
///
/// RED under the back-out, MEASURED: `11:36: … sink.r (op-arg): expected Int64, got
/// String` — the consumer's `trig3(5)`, on a line where no string is written — against
/// `10:22` now.
#[test]
fn the_spliced_rhs_keeps_the_authors_span() {
    const EXTRA: &str = "  rule trig3(?x) <=> sink(\"nope\") [simp]\n  \
                         operation consumer3() -> Int64 = trig3(5)\n";
    let src = program(EXTRA);
    let e = errs(EXTRA);
    assert_eq!(e.len(), 1, "one written mistake, one diagnosis: {e:#?}");
    let at_rhs = line_col(&src, "sink(\"nope\")");
    let at_redex = line_col(&src, "trig3(5)");
    assert_ne!(at_rhs, at_redex, "the fixture must separate the two places");
    assert!(
        e[0].starts_with(&format!("{at_rhs}: ")),
        "the mistake is written at {at_rhs}; it was reported at the redex {at_redex}: {:?}",
        e[0]
    );
}

/// **D — THE CAPABILITY, DRIVEN.** A fired `[simp]` rule must still COMPUTE, not merely
/// diagnose better: the RHS is now a different tree (the author's occurrence, not one
/// re-derived from the head term), and a wrong tree would evaluate wrong or not at all.
///
/// GREEN UNDER THE BACK-OUT, BY DESIGN — a term-derived RHS always evaluated correctly;
/// what it lost was provenance. This row is the guard on the OTHER side: it goes red if
/// the occurrence path builds a tree that differs from the term in anything but span and
/// provenance (a dropped named argument, a nullary call left as a bare `Ref`, a lowered
/// list rebuilt in the pattern shape).
#[test]
fn a_fired_simp_rhs_still_computes() {
    const SRC: &str = "\
namespace zzfcd
  import anthill.prelude.Int64
  import anthill.prelude.List
  operation twice(n: Int64) -> Int64 = n + n
  operation seven() -> Int64 = 7
  operation pair(a: Int64, b: Int64) -> Int64 = a + b
  rule boost(?x) <=> twice(?x) [simp]
  rule named(?x) <=> pair(a: ?x, b: 10) [simp]
  rule nullary(?x) <=> pair(a: ?x, b: seven) [simp]
  operation driveBoost(n: Int64) -> Int64 = boost(n)
  operation driveNamed(n: Int64) -> Int64 = named(n)
  operation driveNullary(n: Int64) -> Int64 = nullary(n)
end
";
    let mut interp = crate::common::interp_for(SRC);
    for (op, expected) in [
        ("zzfcd.driveBoost", 10),
        ("zzfcd.driveNamed", 15),
        ("zzfcd.driveNullary", 12),
    ] {
        let got = interp
            .call(op, &[Value::Int(5)])
            .unwrap_or_else(|e| panic!("{op}(5) must evaluate: {e:?}"));
        assert_eq!(
            matches!(got, Value::Int(n) if n == expected),
            true,
            "{op}(5) fires a `[simp]` rule whose RHS is now the author's occurrence — \
             expected Int({expected}), got {got:?}"
        );
    }
}

/// **E — AND THE WRONG FIX IS REFUSED.** A HAND-WRITTEN `anthill.reflect.field_access`
/// call in a `[simp]` RHS is a call to whatever that name denotes, NOT the name
/// `ns.rel` — WI-20260901-92VA4's rule, and the reason `synthesized_expr` hardcodes
/// `dot_chain: false`.
///
/// GREEN UNDER THE BACK-OUT (a synthesized node has the bit clear either way) and RED
/// under the WRONG fix — flipping `synthesized_expr`'s `dot_chain` to `true`, which would
/// make the fired RHS report ONE error too, by laundering a written call into a citation.
/// So this row is what says the repair is "keep what the author wrote" and not "claim
/// everything is a dot".
///
/// PAIRED with the dot that spells the same chain, which DOES load-and-cite (row A), so
/// the measurement is of PROVENANCE and not of the recognizer being switched off.
#[test]
fn a_written_field_access_in_a_simp_rhs_is_still_not_a_citation() {
    for (label, receiver) in [
        ("two-segment receiver", "zzfc.inner"),
        // The one-segment receiver is the shape a resolved-segments test would MISS —
        // measured identical to a real dot at the typer (WI-20260902-4NEKZ).
        ("one-segment receiver", "zzfc"),
    ] {
        let extra = format!(
            "  rule trigw(?x) <=> sink(anthill.reflect.field_access({receiver}, rel)) [simp]\n  \
             operation consumerw() -> Int64 = trigw(5)\n"
        );
        let e = errs(&extra);
        assert!(
            !e.is_empty(),
            "{label}: a WRITTEN `field_access` call is a call, not the name \
             `{receiver}.rel` — it must stay refused inside a fired `[simp]` RHS too"
        );
        assert!(
            e.iter().all(|m| !m.contains("Relation")),
            "{label}: …and nothing about it is typed as a relation: {e:#?}"
        );
    }
}

/// **F — THE POPULATION, NOT THE FIXTURE.** Every equation a firing site can reach must
/// keep its RHS occurrence, or the repair holds only for the shape row A happens to
/// write. Censused over a full stdlib load plus one `[simp]` fixture.
///
/// MEASURED at delivery: **192** live equations, **90** of them carrying a written RHS,
/// and **21** tagged `[simp]` / `[unfold]` — the only ones `simp_rewrite::try_fire`,
/// `typing::try_fire_dot_rule` and `resolve::fire_simp_equation` will ever open — **all
/// 21** with one. So `build_rhs_template`'s term arm serves the 102 UNTAGGED (inert)
/// equations and any clause a host or a runtime `assert` built, of which this corpus has
/// none tagged.
///
/// ASSERTED AS A ZERO, NOT AS THE COUNTS: the numbers above will drift with the stdlib
/// and would make this a maintenance chore that says nothing. What must not drift is that
/// no FIREABLE equation is left on the term path — which is exactly what goes red if a
/// third spelling of a bodyless equation appears and nobody wires it. (`rule` and `fact`
/// are the two that exist; `fact tau() <=> 7 [simp]` loads clean, measured, and is wired
/// for that reason.) The floor beneath it is what stops a vacuous pass: a corpus with no
/// tagged equations at all would satisfy "none missing" trivially.
///
/// GREEN UNDER BOTH BACK-OUTS in the header? NO — under axis 1 the loader still installs
/// the occurrence (the back-out is at the READER), so this row keeps passing. It fails
/// instead when a PRODUCER is missed, which is the thing no per-program row can see.
#[test]
fn every_fireable_source_equation_keeps_its_rhs_occurrence() {
    let kb = crate::common::load_kb_with(
        "namespace zzfcp\n  import anthill.prelude.Int64\n  \
         operation twice(n: Int64) -> Int64 = n + n\n  \
         rule boost(?x) <=> twice(?x) [simp]\n  \
         operation drive(n: Int64) -> Int64 = boost(n)\nend\n",
    );
    let mut tagged = 0usize;
    let mut missing: Vec<String> = Vec::new();
    for rid in kb.live_rule_ids_iter() {
        if !kb.is_equation(rid) {
            continue;
        }
        let meta = kb.rule_meta(rid);
        if !meta_has_flag(&kb, meta, "simp") && !meta_has_flag(&kb, meta, "unfold") {
            continue;
        }
        tagged += 1;
        if kb.rule_equation_rhs_node(rid).is_none() {
            missing.push(format!(
                "{rid:?} in domain `{}`",
                kb.local_name_of(kb.rule_domain(rid))
            ));
        }
    }
    assert!(
        tagged >= 20,
        "the census must actually reach the tagged equations — it found {tagged}, so \
         `missing.is_empty()` below would be vacuous"
    );
    assert!(
        missing.is_empty(),
        "every source-written equation a firing site can open must keep its RHS \
         occurrence; these {} are on the term path: {missing:#?}",
        missing.len()
    );
}

/// **G — AND A RULE VARIABLE NOTHING BINDS IS STILL CAUGHT.** `rule f(?x) <=> g(?y)
/// [simp]` names `?y` on the right and binds it nowhere on the left, so instantiating it
/// has no value to put there. The term path said so by writing `⊥`; this ticket had to
/// say so again, because the shared σ owner it now routes through
/// (`node_occurrence::substitute_occurrence`) answers a DIFFERENT question about a free
/// variable — in a resolver GOAL one is ordinary, and `subst_var_leaf` keeps the leaf.
///
/// MEASURED, and this row exists because the reuse silently lost it: with
/// `simp_rewrite::bottom_out_unbound` removed, the malformed rule LOADS CLEAN (0 errors).
/// With the whole ticket backed out (axis 1) it also answers 1 — at the REDEX, where `?y`
/// is not written — so the COUNT is what step 4 restores and the LOCATION is what the
/// ticket moves, exactly as row A and row C. The `⊥` lands on `?y` itself rather than on
/// the enclosing call, because `rebuilt_expr` keeps the variable node's own span.
///
/// THE CONTROL IS THE BOUND TWIN, green throughout: it is what says the gate keys on the
/// rule's own frame and has not simply started bottoming out every variable. The
/// projecting case it must not touch — a REDEX variable riding into the RHS (`pick(?q, 7)
/// → ?q`, WI-634) — is not in `fresh` and is left alone; the resolver suites cover it.
#[test]
fn an_unbound_rule_variable_in_a_fired_rhs_is_still_refused() {
    const UNBOUND: &str = "  rule fu(?x) <=> sink(?y) [simp]\n  \
                           operation cu(n: Int64) -> Int64 = fu(n)\n";
    const BOUND: &str = "  rule fb(?x) <=> sink(?x) [simp]\n  \
                         operation cb(n: Int64) -> Int64 = fb(n)\n";
    let src = program(UNBOUND);
    let e = errs(UNBOUND);
    assert_eq!(
        e.len(),
        1,
        "`?y` is bound by nothing, so the fired RHS has no value to splice — it must \
         still be refused: {e:#?}"
    );
    // AT THE VARIABLE ITSELF, not merely on the rule's line: the `⊥` is built with
    // `rebuilt_expr` from the `?y` occurrence, so it keeps that node's own span.
    let at_var = line_col(&src, "?y)");
    let at_redex = line_col(&src, "fu(n)");
    assert_ne!(at_var, at_redex, "the fixture must separate the two places");
    assert!(
        e[0].starts_with(&format!("{at_var}: ")),
        "…and at the `?y` the author wrote ({at_var}), not at the redex ({at_redex}): {:?}",
        e[0]
    );

    assert!(
        errs(BOUND).is_empty(),
        "THE CONTROL: the same rule with `?x` on both sides is well-formed and loads — \
         the gate keys on the rule's OWN frame, not on every variable"
    );
}
